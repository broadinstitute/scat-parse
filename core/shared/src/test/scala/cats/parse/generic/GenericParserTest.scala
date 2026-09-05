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

/** The tracer bullet: the same grammar shape — an anchor literal followed by a region of
  * ambiguous-set tokens — parsed end to end over the deliberately non-injective [[ToyAlphabet]] and
  * over the char alphabet.
  */
class GenericParserTest extends munit.FunSuite {
  import GenericParserTest.Region

  private implicit val toy: ToyAlphabet.type = ToyAlphabet

  /** Literal `[3 5]`: under the toy alphabet a literal token `p` accepts any input token that is a
    * submask of it, so token `3` accepts `{0,1,2,3}` and token `5` accepts `{0,1,4,5}`.
    */
  private val anchorLit: ByteSeq = ByteSeq(0x3, 0x5)

  /** The set holding tokens 1, 2 and 4. */
  private val regionSet: Int = (1 << 1) | (1 << 2) | (1 << 4)

  private val toyGrammar: Parser[ByteSeq, Region] = {
    val token = Parser.tokenIn(ToyAlphabet)(regionSet)
    (Parser.seq(anchorLit) ~ (token ~ token)).map { case (_, (a, b)) => Region(a, b) }
  }

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

  test("toy grammar parses an anchor literal and an ambiguous-set region") {
    // [1 4] is not [3 5], but each of its tokens is a member of the corresponding pattern set
    val input = ByteSeq(0x1, 0x4, 0x2, 0x1, 0x8)
    assert(
      !ToyAlphabet.startsWithAt(input, 0, anchorLit),
      "the anchor is matched by set, not equality"
    )

    assertEquals(toyGrammar.parse(input), Right((ByteSeq(0x8), Region(0x2, 0x1))))
  }

  test("toy grammar still matches the literal against itself") {
    val input = ByteSeq(0x3, 0x5, 0x4, 0x4)
    assertEquals(toyGrammar.parse(input), Right((ByteSeq(), Region(0x4, 0x4))))
  }

  test("the same grammar shape over the char alphabet keeps String slices and Char tokens") {
    val digit = Parser.tokenIn(StringAlphabet)(StringAlphabet.charSet('0' to '9'))
    val charGrammar: Parser[String, (Char, Char)] =
      (Parser.seq("ab") ~ (digit ~ digit)).map(_._2)

    // the ascription is the point of the test: Alphabet.Aux fixes Slice = String
    val parsed: Either[Error[String], (String, (Char, Char))] = charGrammar.parse("ab12rest")
    assertEquals(parsed, Right(("rest", ('1', '2'))))

    assertEquals(charGrammar.parseAll("ab12"), Right(('1', '2')))
  }

  test("a failed literal reports the offset and the expected literal") {
    assertFailsAt(toyGrammar.parse(ByteSeq(0x9, 0x4, 0x2, 0x1)))(
      0,
      NonEmptyList.one(Expectation.OneOfSeq(0, anchorLit :: Nil))
    )
  }

  test(
    "a failed token set reports the offset after the anchor and the alphabet's own expectation"
  ) {
    assertFailsAt(toyGrammar.parse(ByteSeq(0x1, 0x4, 0x8)))(
      2,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(2, regionSet))
    )
  }

  test("a failed char token set reports an InRange like the char parser always has") {
    val digit = Parser.tokenIn(StringAlphabet)(StringAlphabet.charSet('0' to '9'))
    assertFailsAt((Parser.seq("ab") ~ digit).parse("abx"))(
      2,
      NonEmptyList.one(StringAlphabet.InRange(2, '0', '9'))
    )
  }

  test("parseAll fails on unconsumed input") {
    assertFailsAt(toyGrammar.parseAll(ByteSeq(0x1, 0x4, 0x2, 0x1, 0x8)))(
      4,
      NonEmptyList.one(Expectation.EndOfString[ByteSeq](4, 5))
    )
  }

  test("oneOf is left-biased and recovers from alternatives that consumed nothing") {
    val first = Parser.seq(ByteSeq(0x3)).map(_ => "first")
    val second = Parser.seq(ByteSeq(0x4, 0x4)).map(_ => "second")
    val p = Parser.oneOf(first :: second :: Nil)

    assertEquals(p.parse(ByteSeq(0x2)), Right((ByteSeq(), "first")))
    assertEquals(p.parse(ByteSeq(0x4, 0x4)), Right((ByteSeq(), "second")))

    assertFailsAt(p.parse(ByteSeq(0x9)))(
      0,
      NonEmptyList.one(Expectation.OneOfSeq(0, List(ByteSeq(0x3), ByteSeq(0x4, 0x4))))
    )
  }

  test("oneOf stops at an alternative that failed after consuming input") {
    // [3] accepts token 2, so `first` consumes one token before failing on [4] against token 8
    val first = (Parser.seq(ByteSeq(0x3)) ~ Parser.seq(ByteSeq(0x4))).map(_ => "first")
    val second = Parser.seq(ByteSeq(0x2, 0x8)).map(_ => "second")
    val p = Parser.oneOf(first :: second :: Nil)

    // `second` would have matched, but the arresting failure of `first` ends the search
    assertFailsAt(p.parse(ByteSeq(0x2, 0x8)))(
      1,
      NonEmptyList.one(Expectation.OneOfSeq(1, ByteSeq(0x4) :: Nil))
    )
  }

  test("anyToken matches whatever comes next and fails at the end of the input") {
    val two = Parser.anyToken(ToyAlphabet) ~ Parser.anyToken(ToyAlphabet)
    assertEquals(two.parse(ByteSeq(0x9, 0x0, 0x2)), Right((ByteSeq(0x2), (0x9.toByte, 0x0.toByte))))

    assertFailsAt(Parser.anyToken(ToyAlphabet).parse(ByteSeq()))(
      0,
      NonEmptyList.one(ToyAlphabet.ExpectedMask(0, ToyAlphabet.universal))
    )
  }

  test("flatMap chooses the next parser from the token just matched") {
    val p = Parser.tokenIn(ToyAlphabet)(regionSet).flatMap { token =>
      if (token == 0x2.toByte) Parser.seq(ByteSeq(0x1))
      else Parser.pure[ByteSeq, Unit](())
    }

    assertEquals(p.parse(ByteSeq(0x2, 0x1, 0x4)), Right((ByteSeq(0x4), ())))
    assertEquals(p.parse(ByteSeq(0x1, 0x9)), Right((ByteSeq(0x9), ())))
  }
}

object GenericParserTest {
  final case class Region(first: Byte, second: Byte)
}
