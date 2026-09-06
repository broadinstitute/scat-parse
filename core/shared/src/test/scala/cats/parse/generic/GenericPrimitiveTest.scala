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

import cats.data.NonEmptyList

/** The primitive and leaf surface a real grammar needs, over the non-injective [[ToyAlphabet]] and
  * over the char alphabet: predicate matching, bulk scanning, multi-literal longest match, slice
  * capture, repetition, and backtrack/soft semantics.
  */
class GenericPrimitiveTest extends munit.FunSuite {

  private implicit val toy: ToyAlphabet.type = ToyAlphabet

  /** Under the toy alphabet a literal token `p` accepts any input token that is a submask of it, so
    * literal `[3]` accepts `{0,1,2,3}` and literal `[5]` accepts `{0,1,4,5}`.
    */
  private val anchorLit: ByteSeq = ByteSeq(0x3, 0x5)

  /** The set holding tokens 1, 2 and 4. */
  private val regionSet: Int = (1 << 1) | (1 << 2) | (1 << 4)

  private val regionToken: Parser[ByteSeq, Byte] = Parser.tokenIn(ToyAlphabet)(regionSet)

  private def assertFailsAt[S, A](parsed: Either[Error[S], A])(
      offset: Int,
      expected: NonEmptyList[Expectation[S]]
  )(implicit loc: munit.Location): Unit =
    parsed match {
      case Left(err) =>
        assertEquals(err.failedAtOffset, offset)
        assertEquals(err.expected, expected)
      case Right(res) => fail(s"expected a failure, got $res")
    }

  test("seqIn returns the consumed input, not the alternative that matched") {
    // [3 5] matches the input [1 4] without being equal to it, and is longer than [1]
    val p = Parser.seqIn(List(ByteSeq(0x1), anchorLit))
    assertEquals(p.parse(ByteSeq(0x1, 0x4, 0x8)), Right((ByteSeq(0x8), ByteSeq(0x1, 0x4))))
  }

  test("seqIn takes the longest match even when a shorter alternative comes first") {
    val alts = List(ByteSeq(0x1), ByteSeq(0x1, 0x1), ByteSeq(0x3, 0x5, 0x3))
    val p = Parser.seqIn(alts)

    // all three match at 0; the three-token alternative wins
    assertEquals(p.parse(ByteSeq(0x1, 0x1, 0x1)), Right((ByteSeq(), ByteSeq(0x1, 0x1, 0x1))))
    // only the one- and two-token alternatives match here
    assertEquals(p.parse(ByteSeq(0x1, 0x0, 0x8)), Right((ByteSeq(0x8), ByteSeq(0x1, 0x0))))
  }

  test("a failed seqIn reports every alternative at the offset") {
    val alts = List(ByteSeq(0x1), anchorLit)
    assertFailsAt(Parser.seqIn(alts).parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(Expectation.OneOfSeq(0, List(ByteSeq(0x1), anchorLit)))
    )
  }

  test("a single-alternative seqIn still captures the input rather than the literal") {
    assertEquals(
      Parser.seqIn(List(ByteSeq(0x3))).parse(ByteSeq(0x2, 0x8)),
      Right((ByteSeq(0x8), ByteSeq(0x2)))
    )
  }

  test("seqIn over the char alphabet keeps String slices") {
    val p: Parser[String, String] = Parser.seqIn(List("ab", "abc"))
    assertEquals(p.parse("abcd"), Right(("d", "abc")))
    assertFailsAt(p.parse("xy"))(
      0,
      NonEmptyList.one(Expectation.OneOfSeq(0, List("ab", "abc")))
    )
  }

  test("tokensIn scans a run with one scanWhile call and no per-token probes") {
    val counting = new CountingToyAlphabet
    val p = Parser.tokensIn(counting)(regionSet)

    assertEquals(
      p.parse(ByteSeq(0x1, 0x2, 0x4, 0x8)),
      Right((ByteSeq(0x8), ByteSeq(0x1, 0x2, 0x4)))
    )
    assertEquals(counting.scans, 1)
    assertEquals(counting.probes, 0)
  }

  test("tokensIn fails on an empty run, tokensIn0 succeeds with an empty slice") {
    assertFailsAt(Parser.tokensIn(ToyAlphabet)(regionSet).parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(0, regionSet))
    )

    assertEquals(
      Parser.tokensIn0(ToyAlphabet)(regionSet).parse(ByteSeq(0x8)),
      Right((ByteSeq(0x8), ByteSeq()))
    )
  }

  test("tokensWhile scans by predicate; with no token satisfying it, it fails and its 0 is empty") {
    val odd = Parser.tokensWhile(ToyAlphabet)(t => (t & 1) != 0)
    assertEquals(odd.parse(ByteSeq(0x1, 0x3, 0x2)), Right((ByteSeq(0x2), ByteSeq(0x1, 0x3))))

    assertFailsAt(Parser.tokensWhile(ToyAlphabet)(_ => false).parse(ByteSeq(0x1)))(
      0,
      NonEmptyList.one(Expectation.Fail(0))
    )
    assertEquals(
      Parser.tokensWhile0(ToyAlphabet)(_ => false).parse(ByteSeq(0x1)),
      Right((ByteSeq(0x1), ByteSeq()))
    )
  }

  test("tokenWhere matches by predicate and fails when no token satisfies it") {
    val odd = Parser.tokenWhere(ToyAlphabet)(t => (t & 1) != 0)
    assertEquals(odd.parse(ByteSeq(0x3, 0x8)), Right((ByteSeq(0x8), 0x3.toByte)))
    assertFailsAt(odd.parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(0, 0xaaaa))
    )

    assertFailsAt(Parser.tokenWhere(ToyAlphabet)(_ => false).parse(ByteSeq(0x1)))(
      0,
      NonEmptyList.one(Expectation.Fail(0))
    )
  }

  test("tokenWhere and tokensWhile over the char alphabet are char parsers") {
    val digit = Parser.tokenWhere(StringAlphabet)(_.isDigit)
    assertEquals(digit.parse("1a"), Right(("a", '1')))
    assertEquals(Parser.tokensWhile(StringAlphabet)(_.isDigit).parse("12a"), Right(("a", "12")))

    // a Set is a Char => Boolean, and char takes it as the set rather than sweeping the domain
    assertEquals(
      Parser.tokensWhile(StringAlphabet)(Set('a', 'b')).parse("aba1"),
      Right(("1", "aba"))
    )
  }

  test("slice capture returns the alphabet's Slice: ByteSeq for the toy, String for char") {
    val toySlice: Parser[ByteSeq, ByteSeq] = (Parser.seq(anchorLit) ~ regionToken).slice
    assertEquals(
      toySlice.parse(ByteSeq(0x1, 0x4, 0x2, 0x8)),
      Right((ByteSeq(0x8), ByteSeq(0x1, 0x4, 0x2)))
    )

    // the ascription is the point: Alphabet.Aux fixes Slice = String for char
    val digit = Parser.tokenIn(StringAlphabet)(StringAlphabet.charSet('0' to '9'))
    val charSlice: Parser[String, String] = (Parser.seq("ab") ~ digit).slice
    assertEquals(charSlice.parse("ab1c"), Right(("c", "ab1")))
  }

  test("void discards the result and slice of what it wraps") {
    val p: Parser[ByteSeq, Unit] = (Parser.seq(anchorLit) ~ regionToken).slice.void
    assertEquals(p.parse(ByteSeq(0x1, 0x4, 0x2, 0x8)), Right((ByteSeq(0x8), ())))
  }

  test("backtrack turns an arresting failure into an epsilon failure") {
    // [3] accepts token 2, so `first` consumes one token before failing on [4] against token 8
    val first = (Parser.seq(ByteSeq(0x3)) ~ Parser.seq(ByteSeq(0x4))).map(_ => "first")
    val second = Parser.seq(ByteSeq(0x2, 0x8)).map(_ => "second")

    // without backtrack this is the arresting failure asserted in GenericParserTest
    val p = Parser.oneOf(first.backtrack :: second :: Nil)
    assertEquals(p.parse(ByteSeq(0x2, 0x8)), Right((ByteSeq(), "second")))
  }

  test("soft rewinds when the second parser fails without consuming") {
    val soft = Parser.softProduct10(Parser.seq(ByteSeq(0x3)), Parser.seq(ByteSeq(0x4)))
    val second = Parser.seq(ByteSeq(0x2, 0x8)).map(_ => "second")
    val p = Parser.oneOf(soft.map(_ => "soft") :: second :: Nil)

    assertEquals(p.parse(ByteSeq(0x2, 0x8)), Right((ByteSeq(), "second")))
    // and it is still a soft product: when the second parser matches, both are consumed
    assertEquals(soft.void.parse(ByteSeq(0x2, 0x4)), Right((ByteSeq(), ())))
  }

  test("soft does not rewind when the second parser fails having consumed input") {
    val tail = (Parser.seq(ByteSeq(0x8)) ~ Parser.seq(ByteSeq(0x1))).void
    val soft = Parser.softProduct10(Parser.seq(ByteSeq(0x3)), tail)

    assertFailsAt(soft.parse(ByteSeq(0x2, 0x8, 0x9)))(
      2,
      NonEmptyList.one(Expectation.OneOfSeq(2, ByteSeq(0x1) :: Nil))
    )
  }

  test("rep and rep0 collect the values they parse") {
    assertEquals(
      regionToken.rep.parse(ByteSeq(0x1, 0x2, 0x4, 0x8)),
      Right((ByteSeq(0x8), NonEmptyList.of(0x1.toByte, 0x2.toByte, 0x4.toByte)))
    )
    assertEquals(regionToken.rep0.parse(ByteSeq(0x8)), Right((ByteSeq(0x8), Nil)))
    assertEquals(
      regionToken.rep0.parse(ByteSeq(0x1, 0x8)),
      Right((ByteSeq(0x8), List(0x1.toByte)))
    )
  }

  test("rep(min) fails when it cannot read min values") {
    assertEquals(
      regionToken.rep(2).parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x8), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertFailsAt(regionToken.rep(2).parse(ByteSeq(0x1, 0x8)))(
      1,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(1, regionSet))
    )
  }

  test("rep composes with slice capture") {
    val p: Parser[ByteSeq, ByteSeq] = regionToken.rep.slice
    assertEquals(p.parse(ByteSeq(0x1, 0x2, 0x8)), Right((ByteSeq(0x8), ByteSeq(0x1, 0x2))))
  }

  test("length consumes exactly its count and reports what was left") {
    assertEquals(
      Parser.length[ByteSeq](2).parse(ByteSeq(0x1, 0x2, 0x3)),
      Right((ByteSeq(0x3), ByteSeq(0x1, 0x2)))
    )
    assertFailsAt(Parser.length[ByteSeq](4).parse(ByteSeq(0x1, 0x2)))(
      0,
      NonEmptyList.one(Expectation.Length[ByteSeq](0, 4, 2))
    )
    assertEquals(
      Parser.length0[ByteSeq](0).parse(ByteSeq(0x1)),
      Right((ByteSeq(0x1), ByteSeq()))
    )
  }

  test("start and end anchor the parse without consuming") {
    val p = Parser.start[ByteSeq] ~ Parser.tokensIn(ToyAlphabet)(regionSet) ~ Parser.end[ByteSeq]
    assertEquals(p.void.parse(ByteSeq(0x1, 0x2)), Right((ByteSeq(), ())))

    assertFailsAt(p.parse(ByteSeq(0x1, 0x8)))(
      1,
      NonEmptyList.one(Expectation.EndOfString[ByteSeq](1, 2))
    )

    val notStart = (regionToken ~ Parser.start[ByteSeq]).void
    assertFailsAt(notStart.parse(ByteSeq(0x1)))(
      1,
      NonEmptyList.one(Expectation.StartOfString[ByteSeq](1))
    )
  }

  test("index reports the offset without consuming") {
    val p = Parser.index[ByteSeq] ~ regionToken ~ Parser.index[ByteSeq]
    assertEquals(p.parse(ByteSeq(0x1, 0x8)), Right((ByteSeq(0x8), ((0, 0x1.toByte), 1))))
  }

  test("fail and failWith always fail where they stand") {
    assertFailsAt(Parser.fail[ByteSeq, Int].parse(ByteSeq(0x1)))(
      0,
      NonEmptyList.one(Expectation.Fail(0))
    )
    assertFailsAt((regionToken ~ Parser.failWith[ByteSeq, Int]("nope")).parse(ByteSeq(0x1)))(
      1,
      NonEmptyList.one(Expectation.FailWith(1, "nope"))
    )
  }

  test("a Fail alternative is the zero of oneOf") {
    val p =
      Parser.oneOf(Parser.fail[ByteSeq, String] :: Parser.seq(ByteSeq(0x3)).map(_ => "s") :: Nil)
    assertEquals(p.parse(ByteSeq(0x2)), Right((ByteSeq(), "s")))

    // when every alternative fails, the real expectation survives and Fail does not
    assertFailsAt(p.parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(Expectation.OneOfSeq(0, ByteSeq(0x3) :: Nil))
    )

    // ... unless there is nothing else to report
    assertFailsAt(Parser.oneOf(List.empty[Parser[ByteSeq, String]]).parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(Expectation.Fail(0))
    )
  }

  test("defer allows a recursive grammar") {
    lazy val p: Parser[ByteSeq, Int] =
      (regionToken ~ Parser.defer(p).rep0).map { case (_, rest) => 1 + rest.sum }

    assertEquals(Parser.defer(p).parse(ByteSeq(0x1, 0x2, 0x8)), Right((ByteSeq(0x8), 2)))
  }

  test("the same leaves over the char alphabet behave as the char parser always has") {
    val digit = Parser.tokenWhere(StringAlphabet)(_.isDigit)

    assertEquals(digit.rep.parse("12a"), Right(("a", NonEmptyList.of('1', '2'))))
    assertEquals(digit.rep0.parse("a"), Right(("a", Nil)))
    assertEquals(digit.rep.slice.parse("12a"), Right(("a", "12")))
    assertEquals(Parser.length[String](2).parse("abc"), Right(("c", "ab")))
    assertEquals(Parser.length0[String](0).parse("a"), Right(("a", "")))
    assertEquals(
      (Parser.start[String] ~ Parser.seq("ab") ~ Parser.end[String]).void.parseAll("ab"),
      Right(())
    )
    assertEquals((Parser.index[String] ~ digit).parse("1"), Right(("", (0, '1'))))

    // backtrack lets the alternation recover from a partly-consumed alternative
    val ab = (Parser.seq("a") ~ Parser.seq("b")).map(_ => "ab")
    assertEquals(
      Parser.oneOf(ab.backtrack :: Parser.seq("ac").map(_ => "ac") :: Nil).parse("ac"),
      Right(("", "ac"))
    )
    // and soft rewinds the same way when the second parser fails without consuming
    val softAb = Parser.softProduct10(Parser.seq("a"), Parser.seq("b")).map(_ => "ab")
    assertEquals(
      Parser.oneOf(softAb :: Parser.seq("ac").map(_ => "ac") :: Nil).parse("ac"),
      Right(("", "ac"))
    )

    assertFailsAt(Parser.failWith[String, Int]("nope").parse("a"))(
      0,
      NonEmptyList.one(Expectation.FailWith(0, "nope"))
    )

    lazy val digits: Parser[String, Int] =
      (digit ~ Parser.defer(digits).rep0).map { case (_, rest) => 1 + rest.sum }
    assertEquals(Parser.defer(digits).parse("12a"), Right(("a", 2)))
  }
}
