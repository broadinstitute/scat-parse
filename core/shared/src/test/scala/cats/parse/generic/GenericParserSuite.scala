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

import cats.data.NonEmptyVector
import cats.parse.BitSetUtil
import cats.parse.ParserGen.biasSmall
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll

import scala.annotation.tailrec

/** The alphabet-independent property suite (spec S8), written once over [[Alphabet]] and
  * instantiated twice: at char, where it proves the alias facade and the generic engine agree, and
  * at [[ToyAlphabet]], where it proves the non-injective, non-`String`-slice path.
  *
  * Where `cats.parse.ParserTest` recovers a parser's end offset with `str.lastIndexOf(rest)`, this
  * suite reads it off `Parser.index` instead: the remainder of a generic parse is an
  * `Alphabet.Slice`, which need not be the input type and carries no search operation.
  *
  * Failures are compared by `failedAtOffset` rather than by expectation set: which expectations a
  * rewrite keeps is the alphabet's business (`Alphabet.mergeOfAlphabet`), and the char suite
  * already pins char's own.
  */
abstract class GenericParserSuite[S](val g: GenericParserGen[S]) extends munit.ScalaCheckSuite {
  import g.{P0, P1, Sl, alpha, gen, gen0, genFusableLeaf, genInput}

  private implicit val alphaI: g.alpha.type = g.alpha

  override def scalaCheckTestParameters =
    super.scalaCheckTestParameters
      .withMinSuccessfulTests(if (BitSetUtil.isScalaJvm) 200 else 20)
      .withMaxDiscardRatio(10)

  /** The whole input as a slice: what a parser consuming nothing leaves behind. */
  private def whole(input: S): Sl = alpha.slice(input, 0, alpha.length(input))

  /** Success compared exactly, failure only by where it failed. */
  private def outcome[A](r: Either[Error[S], (Sl, A)]): Either[Int, (Sl, A)] =
    r.left.map(_.failedAtOffset)

  /** The offset a parser reached, alongside its result. */
  private def withOffset[A](p: P0[A], input: S): Either[Error[S], (A, Int)] =
    (p ~ Parser.index[S]).parse(input).map(_._2)

  // ---- monad/functor (ParserTest 1597, 1198, 1219, 1242) ----

  property("Monad.pure is an identity function") {
    forAll(genInput, Gen.choose(0, 100)) { (input, i) =>
      assertEquals(Parser.pure[S, Int](i).parse(input), Right((whole(input), i)))
    }
  }

  property("a.map(identity) == a") {
    forAll(gen0, genInput) { (a, input) =>
      assertEquals(a.fa.map(identity[a.A]).parse(input), a.fa.parse(input))
    }
  }

  property("a.flatMap(b) composes as expected (0 -> 0)") {
    forAll(gen0, genInput) { (p1, input) =>
      forAll(Gen.function1(gen0)(p1.cogen)) { fn =>
        val direct = p1.fa.flatMap { a => fn(a).fa.void }.parse(input)

        val indirect = withOffset(p1.fa, input) match {
          case Left(err) => Left(err)
          // re-run the continuation on the same input, skipping what the first parser consumed
          case Right((a, off)) => (Parser.length0(off) *> fn(a).fa.void).parse(input)
        }

        assertEquals(outcome(direct), outcome(indirect))
      }
    }
  }

  property("a.flatMap(b) composes as expected (1 -> 0)") {
    forAll(gen, genInput) { (p1, input) =>
      forAll(Gen.function1(gen0)(p1.cogen)) { fn =>
        val direct = p1.fa.flatMap { a => fn(a).fa.void }.parse(input)

        val indirect = withOffset(p1.fa, input) match {
          case Left(err) => Left(err)
          case Right((a, off)) => (Parser.length0(off) *> fn(a).fa.void).parse(input)
        }

        assertEquals(outcome(direct), outcome(indirect))
      }
    }
  }

  property("a.with1.flatMap(b) composes as expected (0 -> 1)") {
    forAll(gen0, genInput) { (p1, input) =>
      forAll(Gen.function1(gen)(p1.cogen)) { fn =>
        val direct = p1.fa.with1.flatMap { a => fn(a).fa.void }.parse(input)

        val indirect = withOffset(p1.fa, input) match {
          case Left(err) => Left(err)
          case Right((a, off)) => (Parser.length0(off).with1 *> fn(a).fa.void).parse(input)
        }

        assertEquals(outcome(direct), outcome(indirect))
      }
    }
  }

  property("a ~ b composes as expected") {
    forAll(gen0, gen0, genInput) { (p1, p2, input) =>
      val composed = (p1.fa.void ~ p2.fa.void).parse(input)

      val sequenced = withOffset(p1.fa, input) match {
        case Left(err) => Left(err)
        case Right((_, off)) =>
          (Parser.length0(off) *> p2.fa.void).parse(input).map { case (rest, _) =>
            (rest, ((), ()))
          }
      }

      assertEquals(outcome(composed), outcome(sequenced))
    }
  }

  // ---- oneOf (ParserTest 843, 853, 931, 944, 1603, 1611) ----

  property("oneOf0 nesting doesn't change results") {
    forAll(Gen.listOf(gen0), Gen.listOf(gen0), genInput) { (ps1, ps2, input) =>
      val flat = Parser.oneOf0((ps1 ++ ps2).map(_.fa.void))
      val nested =
        Parser.oneOf0(Parser.oneOf0(ps1.map(_.fa.void)) :: Parser.oneOf0(ps2.map(_.fa.void)) :: Nil)

      assertEquals(flat.parse(input).toOption, nested.parse(input).toOption)
    }
  }

  property("oneOf nesting doesn't change results") {
    forAll(Gen.listOf(gen), Gen.listOf(gen), genInput) { (ps1, ps2, input) =>
      val flat = Parser.oneOf((ps1 ++ ps2).map(_.fa.void))
      val nested =
        Parser.oneOf(Parser.oneOf(ps1.map(_.fa.void)) :: Parser.oneOf(ps2.map(_.fa.void)) :: Nil)

      assertEquals(flat.parse(input).toOption, nested.parse(input).toOption)
    }
  }

  property("oneOf0 same as foldLeft(fail)(_.orElse(_))") {
    forAll(Gen.listOf(gen0), genInput) { (ps, input) =>
      val oneOf = Parser.oneOf0(ps.map(_.fa.void))
      val folded = ps.foldLeft(Parser.fail[S, Unit]: P0[Unit]) { (acc, p) => acc.orElse(p.fa.void) }

      assertEquals(oneOf.parse(input).toOption, folded.parse(input).toOption)
    }
  }

  property("oneOf same as foldLeft(fail)(_.orElse(_))") {
    forAll(Gen.listOf(gen), genInput) { (ps, input) =>
      val oneOf = Parser.oneOf(ps.map(_.fa.void))
      val folded = ps.foldLeft(Parser.fail[S, Unit]) { (acc, p) => acc.orElse(p.fa.void) }

      assertEquals(oneOf.parse(input).toOption, folded.parse(input).toOption)
    }
  }

  property("p orElse p == p") {
    forAll(gen, genInput) { (p, input) =>
      val p0 = p.fa.void
      assertEquals(outcome(p0.orElse(p0).parse(input)), outcome(p0.parse(input)))
    }
  }

  property("p orElse p == p (0)") {
    forAll(gen0, genInput) { (p, input) =>
      val p0 = p.fa.void
      assertEquals(outcome(p0.orElse(p0).parse(input)), outcome(p0.parse(input)))
    }
  }

  // ---- backtrack and soft (ParserTest 980, 2061, 1844) ----

  property("a.backtrack either succeeds or fails at 0") {
    forAll(gen0, genInput) { (a, input) =>
      a.fa.backtrack.parse(input) match {
        case Right(_) => ()
        case Left(err) => assertEquals(err.failedAtOffset, 0)
      }
    }
  }

  property("a.backtrack.orElse(b) parses iff b.backtrack.orElse(a)") {
    forAll(gen0, gen0, genInput) { (a, b, input) =>
      val ab = a.fa.void.backtrack.orElse(b.fa.void)
      val ba = b.fa.void.backtrack.orElse(a.fa.void)

      assertEquals(ab.parse(input).isRight, ba.parse(input).isRight)
    }
  }

  property("(a.soft ~ b) == (a ~ b) whenever the hard product succeeds") {
    forAll(gen0, gen0, genInput) { (a, b, input) =>
      val hard = (a.fa.void ~ b.fa.void).parse(input)
      if (hard.isRight) assertEquals((a.fa.void.soft ~ b.fa.void).parse(input), hard)
      else ()
    }
  }

  property("a.soft ~ b rewinds when b fails without consuming") {
    forAll(gen, genInput) { (a, input) =>
      // the second parser fails immediately, so a soft product that got past `a` must rewind to
      // where `a` started -- offset 0 here. If `a` itself failed, the error is its own.
      if (a.fa.parse(input).isRight) {
        (a.fa.void.soft ~ Parser.fail[S, Unit]).parse(input) match {
          case Right(res) => fail(s"expected a failure, got $res")
          case Left(err) => assertEquals(err.failedAtOffset, 0)
        }
      } else ()
    }
  }

  // ---- rep (ParserTest 1385, 1396, 1404) ----

  property("rep0 is consistent with rep") {
    forAll(gen, biasSmall(1), genInput) { (p, min, input) =>
      val repA = p.fa.rep0(min)
      val repB = p.fa.rep(min).map(_.toList)

      assertEquals(repA.parse(input), repB.parse(input))
    }
  }

  property("repExactlyAs is consistent with repAs") {
    forAll(gen, Gen.choose(1, 100), genInput) { (p, n, input) =>
      val repA = p.fa.repAs[NonEmptyVector[_]](n, n)
      val repB = p.fa.repExactlyAs[NonEmptyVector[_]](n)

      assertEquals(repA.parse(input), repB.parse(input))
    }
  }

  property("rep parses n entries, min <= n <= max") {
    val validMinMax = for {
      min <- biasSmall(1)
      max <- biasSmall(min)
    } yield (min, max)

    forAll(gen, validMinMax, genInput) { case (p, (min, max), input) =>
      p.fa.rep(min, max).parse(input).foreach { case (_, l) =>
        assert(l.length <= max)
        assert(l.length >= min)
      }
    }
  }

  property("repSep with a unit separator is the same as rep") {
    forAll(gen, genInput) { (p, input) =>
      val sep = Parser.unit[S]
      assertEquals(p.fa.repSep(sep).parse(input), p.fa.rep.parse(input))
    }
  }

  // ---- error offsets (ParserTest 830, 1619) ----

  property("expectations sit at valid offsets") {
    forAll(gen0, genInput) { (a, input) =>
      a.fa.parse(input) match {
        case Right(_) => ()
        case Left(err) =>
          val len = alpha.length(input)
          assert(err.failedAtOffset >= 0 && err.failedAtOffset <= len, s"bad offset in $err")
          err.expected.toList.foreach { e =>
            assert(e.offset >= 0 && e.offset <= len, s"bad expectation offset in $e")
          }
      }
    }
  }

  property("a Parser fails or consumes 1 or more") {
    forAll(gen, genInput) { (a, input) =>
      withOffset(a.fa, input) match {
        case Right((_, off)) => assert(off >= 1, s"consumed nothing on $input")
        case Left(_) => ()
      }
    }
  }

  property("parseAll law") {
    forAll(gen0, genInput) { (a, input) =>
      val pall = (a.fa <* Parser.end[S]).parse(input).map(_._2)

      assertEquals(a.fa.parseAll(input), pall)
    }
  }

  // ---- void and slice (ParserTest 2766, 2773, 2577, 3048) ----

  property("P0.void is idempotent") {
    forAll(gen0) { a => assertEquals(a.fa.void.void, a.fa.void) }
  }

  property("P.void is idempotent") {
    forAll(gen) { a => assertEquals(a.fa.void.void, a.fa.void) }
  }

  property("a.slice returns exactly the input a consumed") {
    forAll(gen0, genInput) { (a, input) =>
      val sliced = a.fa.slice.parse(input).map(_._2)
      val viaIndex = withOffset(a.fa, input).map { case (_, off) => alpha.slice(input, 0, off) }

      assertEquals(sliced.toOption, viaIndex.toOption)
    }
  }

  property("a.slice.slice == a.slice") {
    forAll(gen0, genInput) { (a, input) =>
      assertEquals(a.fa.slice.slice.parse(input), a.fa.slice.parse(input))
    }
  }

  property("a.withSlice is a paired with the input it consumed") {
    forAll(gen0, genInput) { (a, input) =>
      val direct = a.fa.withSlice.parse(input).map { case (rest, (av, sl)) => (rest, av, sl) }
      val viaIndex = withOffset(a.fa, input).map { case (av, off) =>
        (alpha.slice(input, off, alpha.length(input)), av, alpha.slice(input, 0, off))
      }

      assertEquals(direct.toOption, viaIndex.toOption)
    }
  }

  // ---- peek and not (ParserTest 2156, 2209, 2235) ----

  property("a.peek == a.peek.peek") {
    forAll(gen0, genInput) { (a, input) =>
      assertEquals(a.fa.peek.peek.parse(input), a.fa.peek.parse(input))
    }
  }

  property("!(!a) == a.peek") {
    forAll(gen0, genInput) { (a, input) =>
      val notNot = Parser.not(Parser.not(a.fa))
      assertEquals(notNot.parse(input).toOption, a.fa.peek.parse(input).toOption)
    }
  }

  property("!anyToken == end") {
    forAll(genInput) { input =>
      val notAny = Parser.not(Parser.anyToken(alpha))
      assertEquals(notAny.parse(input).toOption, Parser.end[S].parse(input).toOption)
    }
  }

  // ---- fusion soundness (spec S8 layer 3) ----

  /** Left-biased try-in-order: the semantics `oneOf` has to keep whether or not it fuses its
    * alternatives into one leaf. An alternative that fails having consumed input is arresting, so
    * it fails the whole `oneOf` rather than falling through.
    */
  private def referenceOneOf(
      alts: List[P1[Unit]],
      input: S
  ): Option[Either[Error[S], (Sl, Unit)]] = {
    @tailrec
    def loop(rest: List[P1[Unit]]): Option[Either[Error[S], (Sl, Unit)]] =
      rest match {
        case Nil => None
        case h :: t =>
          h.parse(input) match {
            case r @ Right(_) => Some(r)
            case l @ Left(err) => if (err.failedAtOffset > 0) Some(l) else loop(t)
          }
      }

    loop(alts)
  }

  property("oneOf agrees with the try-in-order reference, fused or not") {
    forAll(Gen.choose(2, 4).flatMap(Gen.listOfN(_, genFusableLeaf)), genInput) { (alts, input) =>
      val fused = Parser.oneOf(alts).parse(input)
      val reference = referenceOneOf(alts, input)

      assertEquals(fused.toOption, reference.flatMap(_.toOption))
    }
  }

  property("oneOf of a leaf with itself is that leaf") {
    forAll(genFusableLeaf, genInput) { (leaf, input) =>
      assertEquals(
        outcome(Parser.oneOf(leaf :: leaf :: Nil).parse(input)),
        outcome(leaf.parse(input))
      )
    }
  }
}

/** Char: every property above, at the alphabet the alias facade publishes. */
class CharGenericParserSuite extends GenericParserSuite(CharParserGen)

/** Toy: every property above, at a non-injective alphabet whose `Slice` is not its input type. */
class ToyGenericParserSuite extends GenericParserSuite(ToyParserGen)
