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

package cats.parse

import cats.data.NonEmptyList

/** The must-compile-unchanged pin (spec S4).
  *
  * `cats.parse.Parser0`/`Parser` are now aliases for the generic parsers, whose `parse` has the
  * dependent result type `Either[Error[S], (alpha.Slice, A)]`. Char users must never see that: the
  * char instance is published at `Alphabet.Aux[String, String]` so `alpha.Slice` reduces to
  * `String`. This is the one place the generalization could leak into an inferred type, so the
  * checks below assert the inference '''exactly''' — `=:=`, not a subtype ascription, and no type
  * annotation on the expression being measured.
  *
  * These are compile-time assertions; the runtime bodies only exist to keep the values used.
  */
class SourceCompatTest extends munit.FunSuite {

  /** `inferredType(expr).is[T]` compiles only when `expr`'s inferred type is exactly `T`. */
  private def inferredType[A](a: A): SourceCompatTest.InferredType[A] =
    new SourceCompatTest.InferredType(a)

  private val p: Parser[Int] = Parser.charIn('0' to '9').map(_ - '0')
  private val p0: Parser0[Int] = p.?.map(_.getOrElse(0))

  test("parse on a char parser infers (String, A)") {
    inferredType(p.parse("1")).is[Either[Parser.Error, (String, Int)]]
    inferredType(p0.parse("1")).is[Either[Parser.Error, (String, Int)]]
  }

  test("parseAll on a char parser infers A") {
    inferredType(p.parseAll("1")).is[Either[Parser.Error, Int]]
    inferredType(p0.parseAll("1")).is[Either[Parser.Error, Int]]
  }

  test("captures on a char parser infer String") {
    inferredType(p.string).is[Parser[String]]
    inferredType(p0.string).is[Parser0[String]]
    inferredType(p.withString).is[Parser[(Int, String)]]
    inferredType(p0.withString).is[Parser0[(Int, String)]]
  }

  test("the error hierarchy keeps its char shape") {
    val err = p.parseAll("x").swap.getOrElse(fail("should not parse"))
    inferredType(err.expected).is[NonEmptyList[Parser.Expectation]]
    inferredType(err.input).is[Option[String]]

    // the aliased cases still pattern-match by their historical names
    err.expected.head match {
      case Parser.Expectation.InRange(_, lower, upper) =>
        inferredType(lower).is[Char]
        inferredType(upper).is[Char]
      case other => fail(s"expected an InRange, got $other")
    }

    p.parseAll("x") match {
      case Left(Parser.ErrorWithInput(input, offset, expected)) =>
        assertEquals(input, "x")
        assertEquals(offset, 0)
        assertEquals(expected.head, Parser.Expectation.InRange(0, '0', '9'))
      case other => fail(s"expected an ErrorWithInput, got $other")
    }
  }
}

object SourceCompatTest {
  final class InferredType[A](private val a: A) extends AnyVal {
    def is[B](implicit ev: A =:= B): Unit = {
      val _ = ev(a)
      ()
    }
  }
}
