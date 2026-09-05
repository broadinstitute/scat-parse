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
import cats.parse.{Parser => P}
import cats.syntax.all._

/** Parity between the generic error machinery instantiated at the char alphabet and today's
  * char-specific `Parser.Expectation`/`Parser.Error`: same unify results, same ordering, and
  * bit-identical rendered output. This is the char-invisibility bar of the error model, checked
  * while both implementations still coexist.
  */
class GenericErrorTest extends munit.FunSuite {
  import Expectation._
  import StringAlphabet.InRange

  private def toOld(e: Expectation[String]): P.Expectation =
    e match {
      case OneOfSeq(o, seqs) => P.Expectation.OneOfStr(o, seqs)
      case InRange(o, l, u) => P.Expectation.InRange(o, l, u)
      case StartOfString(o) => P.Expectation.StartOfString(o)
      case EndOfString(o, l) => P.Expectation.EndOfString(o, l)
      case Length(o, e1, a) => P.Expectation.Length(o, e1, a)
      case ExpectedFailureAt(o, m) => P.Expectation.ExpectedFailureAt(o, m)
      case Fail(o) => P.Expectation.Fail(o)
      case FailWith(o, m) => P.Expectation.FailWith(o, m)
      case WithContext(c, inner) => P.Expectation.WithContext(c, toOld(inner))
      case other: OfAlphabet[String] =>
        fail(s"unexpected non-InRange OfAlphabet case in char parity test: $other")
    }

  private def assertUnifyParity(input: NonEmptyList[Expectation[String]]): Unit = {
    val generic = Expectation.unify(input).map(toOld(_))
    val old = P.Expectation.unify(input.map(toOld(_)))
    assertEquals(generic, old)
  }

  test("unify merges overlapping and adjacent ranges like the char implementation") {
    assertUnifyParity(
      NonEmptyList.of(
        InRange(0, 'a', 'c'),
        InRange(0, 'b', 'f'),
        InRange(0, 'g', 'g'),
        InRange(0, 'x', 'z')
      )
    )
  }

  test("unify dedups and sorts OneOfSeq alternatives like the char implementation") {
    assertUnifyParity(
      NonEmptyList.of(
        OneOfSeq(1, List("foo", "bar")),
        OneOfSeq(1, List("baz", "foo")),
        InRange(1, 'a', 'b')
      )
    )
  }

  test("unify drops Fail when other expectations exist, keeps it alone otherwise") {
    assertUnifyParity(
      NonEmptyList.of(Fail(2), InRange(2, 'q', 'q'))
    )
    assertUnifyParity(NonEmptyList.of(Fail(2), Fail(2)))
  }

  test("unify groups by offset and context and re-wraps contexts") {
    assertUnifyParity(
      NonEmptyList.of(
        WithContext("ctx", InRange(0, 'a', 'b')),
        WithContext("ctx", InRange(0, 'c', 'd')),
        InRange(0, 'a', 'b'),
        WithContext("other", OneOfSeq(0, List("z"))),
        InRange(3, 'a', 'b')
      )
    )
  }

  test("unify keeps distinct non-mergeable cases like the char implementation") {
    assertUnifyParity(
      NonEmptyList.of(
        StartOfString(0),
        EndOfString(0, 10),
        Length(0, 3, 1),
        ExpectedFailureAt(0, "oops"),
        FailWith(0, "boom"),
        OneOfSeq(0, List("s")),
        InRange(0, 'k', 'm')
      )
    )
  }

  test("expectation ordering matches the char implementation") {
    val samples: List[Expectation[String]] = List(
      OneOfSeq(0, List("b")),
      OneOfSeq(0, List("a", "b")),
      InRange(0, 'a', 'z'),
      InRange(0, 'a', 'b'),
      StartOfString(0),
      EndOfString(0, 5),
      EndOfString(0, 7),
      Length(0, 2, 1),
      Length(0, 2, 3),
      ExpectedFailureAt(0, "m"),
      Fail(0),
      FailWith(0, "a"),
      FailWith(0, "b"),
      WithContext("c1", Fail(0)),
      WithContext("c2", Fail(0)),
      InRange(1, 'a', 'a')
    )
    val genericSorted =
      samples.sorted(Expectation.catsOrderExpectation[String].toOrdering).map(toOld(_))
    val oldSorted =
      samples.map(toOld(_)).sorted(P.Expectation.catsOrderExpectation.toOrdering)
    assertEquals(genericSorted, oldSorted)
  }

  test("expectation show output is bit-identical to the char implementation") {
    val samples: List[Expectation[String]] = List(
      OneOfSeq(0, List("foo")),
      OneOfSeq(0, List("foo", "bar")),
      InRange(0, 'a', 'z'),
      InRange(0, 'q', 'q'),
      StartOfString(0),
      EndOfString(0, 5),
      Length(0, 2, 1),
      ExpectedFailureAt(0, "matched"),
      Fail(0),
      FailWith(0, "boom"),
      WithContext("ctx", InRange(0, 'a', 'b'))
    )
    samples.foreach { e =>
      assertEquals(e.show, toOld(e).show, clue = e.toString)
    }
  }

  private val multiLineInput =
    (1 to 8).map(i => s"line number $i with some content").mkString("\n")

  test("error show with input renders the caret block bit-identically") {
    // an offset in the middle: context lines and elipsis on both sides
    val midOffset = multiLineInput.indexOf("line number 4") + 5
    // an offset on the first line: no before-context
    val startOffset = 3
    // an offset on the last line: no after-context
    val endOffset = multiLineInput.length - 2

    List(startOffset, midOffset, endOffset).foreach { offset =>
      val expectations = NonEmptyList.of[Expectation[String]](
        InRange(offset, 'a', 'c'),
        OneOfSeq(offset, List("foo", "bar"))
      )
      val generic = Error(multiLineInput, offset, expectations)
      val old = P.Error(multiLineInput, offset, expectations.map(toOld(_)))
      assertEquals(generic.show, old.show, clue = s"offset $offset")
    }
  }

  test("error show without input is bit-identical") {
    val expectations = NonEmptyList.of[Expectation[String]](InRange(7, 'a', 'c'))
    val generic = Error(7, expectations)
    val old = P.Error(7, expectations.map(toOld(_)))
    assertEquals(generic.show, old.show)
  }

  test("error show with an out-of-range caret offset falls back like the char implementation") {
    val offset = multiLineInput.length + 5
    val expectations = NonEmptyList.of[Expectation[String]](Fail(offset))
    val generic = Error(multiLineInput, offset, expectations)
    val old = P.Error(multiLineInput, offset, expectations.map(toOld(_)))
    assertEquals(generic.show, old.show)
  }

  test("error surface matches: unapply, copy, offsets, toString") {
    val expectations = NonEmptyList.of[Expectation[String]](InRange(3, 'a', 'c'), Fail(5))
    val err = Error("input", 3, expectations)
    err match {
      case Error(offset, exp) =>
        assertEquals(offset, 3)
        assertEquals(exp, expectations)
      case _ => fail("Error unapply did not match")
    }
    err match {
      case ErrorWithInput(input, offset, _) =>
        assertEquals(input, "input")
        assertEquals(offset, 3)
      case _ => fail("ErrorWithInput unapply did not match")
    }
    assertEquals(err.offsets, NonEmptyList.of(3, 5))
    assertEquals(err.copy(failedAtOffset = 4).failedAtOffset, 4)
    // copy drops the input, exactly as the char implementation does today
    assertEquals(err.copy().input, None)
    assertEquals(err.toString, s"Error(3, $expectations)")
  }
}
