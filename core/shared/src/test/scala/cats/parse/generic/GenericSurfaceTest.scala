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

/** The rest of today's char companion surface, generalized (spec S3.3): `not`/`peek`/`until`,
  * `repSep*`/`repUntil*`/`repExactlyAs`/`rep` with `max`, `select`, `tailRecM`, `recursive`,
  * `align`, `withContext`, `?`, `filter`/`mapFilter`/`collect`, and the `soft`/`with1` syntax --
  * over the non-injective [[ToyAlphabet]] and, per test, a char twin.
  */
class GenericSurfaceTest extends munit.FunSuite {

  private implicit val toy: ToyAlphabet.type = ToyAlphabet

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

  test("unary_! (not) succeeds without consuming exactly when the parser would fail") {
    val notRegion = !regionToken
    assertEquals(notRegion.parse(ByteSeq(0x8)), Right((ByteSeq(0x8), ())))
    assertFailsAt(notRegion.parse(ByteSeq(0x1)))(
      0,
      NonEmptyList.one(Expectation.ExpectedFailureAt(0, ByteSeq(0x1)))
    )
  }

  test("peek succeeds without consuming exactly when the parser would succeed") {
    val peeked = regionToken.peek
    assertEquals(peeked.parse(ByteSeq(0x1, 0x8)), Right((ByteSeq(0x1, 0x8), ())))
    assertFailsAt(peeked.parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(0, regionSet))
    )
  }

  // [8]'s pattern accepts only submasks of 8 = {0,8}, disjoint from the region tokens {1,2,4} used
  // as "content" below -- unlike [9] (submasks {0,1,8,9}), which would ambiguously also accept
  // token 1.
  private val stop: Parser[ByteSeq, Unit] = Parser.seq(ByteSeq(0x8))

  test("until/until0 consume tokens up to (not including) a stopping parser") {
    assertEquals(
      Parser.until(ToyAlphabet)(stop).parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x8), ByteSeq(0x1, 0x2)))
    )
    assertEquals(
      Parser.until0(ToyAlphabet)(stop).parse(ByteSeq(0x8)),
      Right((ByteSeq(0x8), ByteSeq()))
    )
  }

  test("repUntil/repUntil0 stop, without consuming, once the end parser succeeds") {
    val p = regionToken.repUntil(stop)
    assertEquals(
      p.parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x8), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertEquals(regionToken.repUntil0(stop).parse(ByteSeq(0x8)), Right((ByteSeq(0x8), Nil)))
  }

  test("repExactlyAs requires exactly that many repetitions") {
    val p = regionToken.repExactlyAs[NonEmptyList[Byte]](2)
    assertEquals(
      p.parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x8), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertFailsAt(p.parse(ByteSeq(0x1, 0x8)))(
      1,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(1, regionSet))
    )
  }

  test("repSep/repSep0 require a separator between repetitions") {
    val sep = Parser.seq(ByteSeq(0x9))
    assertEquals(
      regionToken.repSep(sep).parse(ByteSeq(0x1, 0x9, 0x2, 0x8)),
      Right((ByteSeq(0x8), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertEquals(regionToken.repSep0(sep).parse(ByteSeq(0x8)), Right((ByteSeq(0x8), Nil)))
  }

  test("rep(min, max)/rep0(min, max) enforce both the floor and the cap") {
    // stops at max even though a 3rd region token would still match
    assertEquals(
      regionToken.rep(1, 2).parse(ByteSeq(0x1, 0x2, 0x4)),
      Right((ByteSeq(0x4), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertFailsAt(regionToken.rep(2, 3).parse(ByteSeq(0x1, 0x8)))(
      1,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(1, regionSet))
    )
    assertEquals(regionToken.rep0(0, 1).parse(ByteSeq(0x8)), Right((ByteSeq(0x8), Nil)))
    assertEquals(
      regionToken.rep0(0, 1).parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x2, 0x8), List(0x1.toByte)))
    )
  }

  test("repSep(min, max)/repSep0(min, max) enforce both the floor and the cap") {
    val sep = Parser.seq(ByteSeq(0x9))
    assertEquals(
      regionToken.repSep(1, 2, sep).parse(ByteSeq(0x1, 0x9, 0x2, 0x9, 0x4)),
      Right((ByteSeq(0x9, 0x4), NonEmptyList.of(0x1.toByte, 0x2.toByte)))
    )
    assertEquals(regionToken.repSep0(0, 1, sep).parse(ByteSeq(0x8)), Right((ByteSeq(0x8), Nil)))
  }

  test("select resolves Left through the given function, passes Right through") {
    val p: Parser[ByteSeq, Int] = Parser.select(
      regionToken.map(t => if (t == 0x1.toByte) Left(()) else Right(t.toInt))
    )(Parser.pure[ByteSeq, Unit => Int](_ => -1))
    assertEquals(p.parse(ByteSeq(0x1, 0x8)), Right((ByteSeq(0x8), -1)))
    assertEquals(p.parse(ByteSeq(0x2, 0x8)), Right((ByteSeq(0x8), 2)))
  }

  test("tailRecM loops until Right, consuming as it goes") {
    val p: Parser[ByteSeq, Int] = Parser.tailRecM(0) { acc =>
      Parser.anyToken(ToyAlphabet).map { t =>
        if (t == 0x8.toByte) Right(acc) else Left(acc + 1)
      }
    }
    assertEquals(p.parse(ByteSeq(0x1, 0x2, 0x8)), Right((ByteSeq(), 2)))
  }

  test("recursive builds a self-referential grammar") {
    val digits: Parser[ByteSeq, Int] = Parser.recursive[ByteSeq, Int] { self =>
      (regionToken ~ self.rep0).map { case (_, rest) => 1 + rest.sum }
    }
    assertEquals(digits.parse(ByteSeq(0x1, 0x2, 0x8)), Right((ByteSeq(0x8), 2)))
  }

  test("align combines results, or takes whichever side matched") {
    val a = Parser.tokenIn(ToyAlphabet)(1 << 1)
    val b = Parser.tokenIn(ToyAlphabet)(1 << 2)
    assertEquals(
      Parser.align(a, b).parse(ByteSeq(0x1, 0x2)),
      Right((ByteSeq(), cats.data.Ior.Both(0x1.toByte, 0x2.toByte)))
    )
  }

  test("withContext adds context to a failure") {
    val p = regionToken.withContext("region")
    assertFailsAt(p.parse(ByteSeq(0x8)))(
      0,
      NonEmptyList.one(Expectation.WithContext("region", ToyAlphabet.ExpectedMask(0, regionSet)))
    )
  }

  test("? converts an epsilon failure into None") {
    assertEquals(regionToken.?.parse(ByteSeq(0x1)), Right((ByteSeq(), Some(0x1.toByte))))
    assertEquals(regionToken.?.parse(ByteSeq(0x8)), Right((ByteSeq(0x8), None)))
  }

  test("filter/mapFilter/collect narrow the result or fail") {
    assertEquals(
      regionToken.filter(_ == 0x1.toByte).parse(ByteSeq(0x1)),
      Right((ByteSeq(), 0x1.toByte))
    )
    // filter's failure is arresting (at the offset after the underlying parser already consumed),
    // same as char's -- .filter(fn).backtrack turns it into an epsilon failure if that's wanted
    assertFailsAt(regionToken.filter(_ == 0x1.toByte).parse(ByteSeq(0x2)))(
      1,
      NonEmptyList.one(Expectation.Fail(1))
    )
    assertEquals(
      regionToken.mapFilter(t => if (t == 0x2.toByte) Some(t.toInt) else None).parse(ByteSeq(0x2)),
      Right((ByteSeq(), 2))
    )
    assertEquals(
      regionToken.collect { case t if t == 0x4.toByte => "four" }.parse(ByteSeq(0x4)),
      Right((ByteSeq(), "four"))
    )
  }

  test("eitherOr/withSlice") {
    val p = regionToken.eitherOr(Parser.seq(ByteSeq(0x8)))
    assertEquals(p.parse(ByteSeq(0x1)), Right((ByteSeq(), Right(0x1.toByte))))
    assertEquals(p.parse(ByteSeq(0x8)), Right((ByteSeq(), Left(()))))

    val withS: Parser[ByteSeq, (Byte, ByteSeq)] = regionToken.withSlice
    assertEquals(withS.parse(ByteSeq(0x1, 0x9)), Right((ByteSeq(0x9), (0x1.toByte, ByteSeq(0x1)))))
  }

  test("with1/soft syntax composes a Parser0 with a Parser") {
    val opt = regionToken.?
    val combined = opt.with1 ~ regionToken
    assertEquals(
      combined.parse(ByteSeq(0x1, 0x2, 0x8)),
      Right((ByteSeq(0x8), (Some(0x1.toByte), 0x2.toByte)))
    )

    val soft = (Parser.seq(ByteSeq(0x3)).soft ~ Parser.seq(ByteSeq(0x4))).map(_ => "matched")
    val fallback = Parser.seq(ByteSeq(0x2, 0x8)).map(_ => "fallback")
    assertEquals(
      Parser.oneOf(soft :: fallback :: Nil).parse(ByteSeq(0x2, 0x8)),
      Right((ByteSeq(), "fallback"))
    )
  }

  test("*> and <* discard one side's result") {
    assertEquals(
      (regionToken *> Parser.seq(ByteSeq(0x8))).parse(ByteSeq(0x1, 0x8)),
      Right((ByteSeq(), ()))
    )
    assertEquals(
      (regionToken <* Parser.seq(ByteSeq(0x8))).parse(ByteSeq(0x1, 0x8)),
      Right((ByteSeq(), 0x1.toByte))
    )
  }

  test("between/surroundedBy") {
    val quoted = regionToken.between(Parser.seq(ByteSeq(0x9)), Parser.seq(ByteSeq(0x9)))
    assertEquals(quoted.parse(ByteSeq(0x9, 0x1, 0x9)), Right((ByteSeq(), 0x1.toByte)))
    assertEquals(
      regionToken.surroundedBy(Parser.seq(ByteSeq(0x9))).parse(ByteSeq(0x9, 0x2, 0x9)),
      Right((ByteSeq(), 0x2.toByte))
    )
  }

  test("fromTokenMap converts a matched token via a Map") {
    val p = Parser.fromTokenMap(ToyAlphabet)(Map(0x1.toByte -> "one", 0x2.toByte -> "two"))
    assertEquals(p.parse(ByteSeq(0x1, 0x9)), Right((ByteSeq(0x9), "one")))
    assertFailsAt(p.parse(ByteSeq(0x9)))(
      0,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(0, (1 << 1) | (1 << 2)))
    )
  }

  test("the same surface over the char alphabet behaves as expected") {
    val digit = Parser.tokenIn(StringAlphabet)(StringAlphabet.charSet('0' to '9'))

    assertEquals((!digit).parse("a"), Right(("a", ())))
    assertEquals(digit.peek.parse("1a"), Right(("1a", ())))
    assertEquals(Parser.until(StringAlphabet)(Parser.seq(".")).parse("ab."), Right((".", "ab")))
    assertEquals(
      digit.repUntil(Parser.seq(".")).parse("12."),
      Right((".", NonEmptyList.of('1', '2')))
    )
    assertEquals(
      digit.repExactlyAs[NonEmptyList[Char]](2).parse("12a"),
      Right(("a", NonEmptyList.of('1', '2')))
    )
    assertEquals(
      digit.repSep(Parser.seq(",")).parse("1,2a"),
      Right(("a", NonEmptyList.of('1', '2')))
    )
    assertEquals(digit.?.parse("a"), Right(("a", None)))
    assertEquals(digit.filter(_ == '1').parse("1"), Right(("", '1')))
    assertEquals(digit.withContext("digit").parse("1"), Right(("", '1')))

    val aligned = Parser.align(Parser.seq("a").slice, Parser.seq("b").slice)
    assertEquals(aligned.parse("ab"), Right(("", cats.data.Ior.Both("a", "b"))))

    val digits: Parser[String, Int] =
      Parser.recursive[String, Int](self =>
        (digit ~ self.rep0).map { case (_, rest) => 1 + rest.sum }
      )
    assertEquals(digits.parse("12a"), Right(("a", 2)))
  }
}
