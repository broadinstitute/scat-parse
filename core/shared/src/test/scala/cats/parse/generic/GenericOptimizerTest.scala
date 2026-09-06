/*
 * Copyright (c) 2021 Typelevel
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package cats.parse.generic

import munit.ScalaCheckSuite
import org.scalacheck.{Gen, Prop}
import org.scalacheck.Prop.forAll

/** The `oneOf`/`seqIn` fusion optimizer ([[Optimizer]], spec S5.3): structural checks that fusion
  * actually happens where it is safe, the pinned divergent case that must stay unfused, a soundness
  * property against a naive reference over the non-injective [[ToyAlphabet]], and char parity
  * examples. Construction-time capture (spec S9.2) is checked here too: which node `void` and
  * `slice` build is a construction-time question, and the answer is what keeps the flip off the
  * parse path.
  */
class GenericOptimizerTest extends ScalaCheckSuite {

  private implicit val toy: ToyAlphabet.type = ToyAlphabet

  // ---- structural: fusion actually happens where it is safe ----

  test("TokenIn alternatives fuse into one TokenIn, unioning their sets") {
    val a = Parser.tokenIn(ToyAlphabet)(1 << 1)
    val b = Parser.tokenIn(ToyAlphabet)(1 << 2)
    val fused = Parser.oneOf(a :: b :: Nil)
    assertEquals(fused, Parser.tokenIn(ToyAlphabet)((1 << 1) | (1 << 2)))
  }

  test("same-length literal alternatives always fuse (the length guard)") {
    // both length 1: neither can ever outrank the other in a longest-match structure
    val fused = Parser.oneOf(Parser.seq(ByteSeq(0x1)) :: Parser.seq(ByteSeq(0x2)) :: Nil)
    val expected = Parser.seqIn(List(ByteSeq(0x1), ByteSeq(0x2))).void
    assertEquals(fused, expected)
  }

  // The disjoint guard is unreachable via this alphabet's own `pattern`: every submask-pattern set
  // it builds contains token 0 (0 | p == p for any p), so two literal patterns can never truly
  // diverge at a position. It fires routinely for char instead, where a literal's pattern is
  // singleton per position -- see the char tests below, e.g. "foo"/"bar" diverging at position 0.

  test("a shadowed literal alternative is dropped, not fused") {
    // [15] accepts every single token (submasks of 15 = 0..15); [15, 1] can never be reached
    val broad = Parser.seq(ByteSeq(0xf))
    val narrow = Parser.seq(ByteSeq(0xf, 0x1))
    val fused = Parser.oneOf(broad :: narrow :: Nil)
    assertEquals(fused, broad)
  }

  test("seqIn alternative sets fuse together, dropping members shadowed by the other side") {
    val ls = Parser.seqIn(List(ByteSeq(0x1), ByteSeq(0x2))) // both length 1
    val rs = Parser.seqIn(List(ByteSeq(0x4), ByteSeq(0x8)))
    val fused = Parser.oneOf(ls :: rs :: Nil)
    val expected =
      Parser.seqIn(List(ByteSeq(0x1), ByteSeq(0x2), ByteSeq(0x4), ByteSeq(0x8)))
    assertEquals(fused, expected)
  }

  // ---- the pinned divergent case: must stay unfused ----

  test(
    "the known-divergent ambiguous case stays unfused: left bias wins over the longer alternative"
  ) {
    // [1]'s pattern accepts input tokens {0,1}; [3,1]'s pattern accepts {0,1,2,3} then {0,1}.
    // On input (1,1): both match -- [1] with length 1, [3,1] with length 2. Left-biased oneOf
    // must return [1]'s (shorter) match; a wrongly-fused longest-match SeqIn would return [3,1]'s.
    val p = Parser.oneOf(Parser.seq(ByteSeq(0x1)) :: Parser.seq(ByteSeq(0x3, 0x1)) :: Nil)
    assertEquals(p.parse(ByteSeq(0x1, 0x1)), Right((ByteSeq(0x1), ())))
  }

  // ---- soundness property: fused oneOf agrees with a naive try-in-order reference ----

  private val genToken: Gen[Byte] =
    Gen.frequency(
      (3, Gen.oneOf(1, 2, 4, 8).map(_.toByte)),
      (3, Gen.oneOf(3, 5, 10, 12, 15).map(_.toByte)),
      (1, Gen.choose(0, 15).map(_.toByte))
    )

  private def genLit(maxLen: Int): Gen[ByteSeq] =
    Gen
      .choose(1, maxLen)
      .flatMap(n => Gen.listOfN(n, genToken))
      .map(l => ByteSeq.fromBytes(l.toArray))

  private val genAlts: Gen[List[ByteSeq]] = Gen.choose(2, 4).flatMap(n => Gen.listOfN(n, genLit(3)))

  private val genInput: Gen[ByteSeq] =
    Gen.choose(0, 5).flatMap(n => Gen.listOfN(n, genToken)).map(l => ByteSeq.fromBytes(l.toArray))

  /** The naive reference: try each alternative in order, return the first whose pattern fully
    * matches (every alternative here is a pure literal match, which never partially consumes on
    * failure, so "first that matches" is exactly what a left-biased `oneOf` of these leaves does).
    */
  private def referenceMatch(alts: List[ByteSeq], input: ByteSeq): Option[Int] =
    alts.iterator
      .map { lit =>
        val pat = ToyAlphabet.pattern(lit)
        if (pat.zipWithIndex.forall { case (set, i) => ToyAlphabet.matchesAt(set, input, i) })
          Some(pat.length)
        else None
      }
      .find(_.isDefined)
      .flatten

  property("fused oneOf agrees with the naive left-biased reference") {
    forAll(genAlts, genInput) { (alts, input) =>
      val p = Parser.oneOf(alts.map(Parser.seq(_)))
      val got = p.parse(input) match {
        case Right((rem, ())) => Some(ToyAlphabet.length(input) - ToyAlphabet.length(rem))
        case Left(_) => None
      }
      val expected = referenceMatch(alts, input)
      if (got == expected) Prop.proved
      else Prop.falsified :| s"oneOf($alts) on $input = $got, reference says $expected"
    }
  }

  // ---- char parity: representative cases from cats.parse.Parser's own regression suite ----

  test("char: no-common-prefix literals fuse the same way stringIn does (ParserTest 2528)") {
    val fused = Parser.oneOf(
      Parser.seq("foo").slice :: Parser.seq("quux").slice :: Parser.seq("bar").slice :: Nil
    )
    assertEquals(fused, Parser.seqIn(List("foo", "quux", "bar")))
  }

  test("char: stringIn(List(s, s)) == string(s) (ParserTest 2497), also true post-fusion") {
    assertEquals(Parser.seqIn(List("ab", "ab")), Parser.seq("ab").slice)
  }

  test("char: a shadowing prefix drops the longer alternative, as stringIn's dedup does") {
    // "ab" shadows "abc": whenever "abc" matches, "ab" (its prefix) already matches and wins first
    val fused = Parser.oneOf(Parser.seq("ab").slice :: Parser.seq("abc").slice :: Nil)
    assertEquals(fused, Parser.seq("ab").slice)
  }

  test(
    "char differential: generic fusion agrees with cats.parse.Parser.stringIn on sample inputs"
  ) {
    val lits = List("foo", "quux", "bar")
    val genericP: Parser[String, String] =
      Parser.oneOf(lits.map(Parser.seq(_).slice))
    val charP = cats.parse.Parser.stringIn(lits)

    val inputs = List("foo", "quux", "bar", "foobar", "barn", "xyz", "", "fo")
    inputs.foreach { input =>
      assertEquals(
        genericP.parse(input).toOption,
        charP.parse(input).toOption,
        s"disagreement on input $input"
      )
    }
  }

  // ---- capture as a construction-time property (spec S9.2) ----

  private def isVoidWrapped(p: Parser0[ByteSeq, Any]): Boolean =
    p.isInstanceOf[Parser.Impl.Void[_, _]] || p.isInstanceOf[Parser.Impl.Void0[_, _]]

  private val captureLeaves: List[(String, Parser0[ByteSeq, ByteSeq])] =
    ("seqIn", Parser.seqIn(List(ByteSeq(0x1), ByteSeq(0x2)))) ::
      ("tokensIn", Parser.tokensIn(ToyAlphabet)(1 << 1)) ::
      ("tokensIn0", Parser.tokensIn0(ToyAlphabet)(1 << 1)) ::
      ("length", Parser.length(2)) ::
      Nil

  test("voiding a region-capturing leaf builds the bare leaf, not a Void around it") {
    captureLeaves.foreach { case (name, p) =>
      val v = p.void
      assert(!isVoidWrapped(v), s"$name.void is still Void-wrapped: $v")
      assert(v.isInstanceOf[Parser.Impl.CaptureLeaf[_]], s"$name.void is not a leaf: $v")
      assertEquals(
        v.asInstanceOf[Parser.Impl.CaptureLeaf[ByteSeq]].capturing,
        false,
        s"$name.void still captures"
      )
    }
    // the same for the one the fusion optimizer builds itself
    val fused = Parser.oneOf(Parser.seq(ByteSeq(0x1)) :: Parser.seq(ByteSeq(0x2)) :: Nil)
    assert(!isVoidWrapped(fused), s"fused unit alternatives are Void-wrapped: $fused")
  }

  test("voiding a leaf is idempotent and yields unit without consuming differently") {
    captureLeaves.foreach { case (name, p) =>
      assertEquals(p.void.void, p.void, s"$name.void is not idempotent")
      val input = ByteSeq(0x1, 0x1)
      assertEquals(
        p.void.parse(input).map { case (rem, u) => (rem, u: Any) },
        p.parse(input).map { case (rem, _) => (rem, (): Any) },
        s"$name.void disagrees with $name on what it consumes"
      )
    }
  }

  test("slicing a voided leaf rebuilds the capturing leaf, so p.void.slice == p.slice") {
    captureLeaves.foreach { case (name, p) =>
      assertEquals(p.void.slice, p.slice, s"$name.void.slice is not $name.slice")
    }
  }

  test("the voided twin is memoized, so a leaf in both positions does not double per void") {
    val p = Parser.seqIn(List(ByteSeq(0x1), ByteSeq(0x2)))
    assert(p.void eq p.void, "seqIn's voided twin is rebuilt per void")
    // and a capturing and a voided leaf stay distinguishable to the optimizer's dedup
    assertNotEquals(p.void: Parser0[ByteSeq, Any], p: Parser0[ByteSeq, Any])
  }

  test("char differential: a shadowed alternative behaves the same as cats.parse.Parser's merge") {
    val genericP: Parser[String, String] =
      Parser.oneOf(Parser.seq("ab").slice :: Parser.seq("abc").slice :: Nil)
    val charP = cats.parse.Parser.oneOf(
      cats.parse.Parser.string("ab").string :: cats.parse.Parser.string("abc").string :: Nil
    )

    List("ab", "abc", "abcd", "a", "xy").foreach { input =>
      assertEquals(
        genericP.parse(input).toOption,
        charP.parse(input).toOption,
        s"disagreement on input $input"
      )
    }
  }
}
