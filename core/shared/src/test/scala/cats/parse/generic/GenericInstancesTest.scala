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

import cats.{Align, Alternative, FunctorFilter, Monad, MonoidK}
import munit.ScalaCheckSuite
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll

/** The cats typeclass instances resolve and satisfy the same hand-rolled law shapes
  * `cats.parse.ParserTest` checks for the char parser (see that file's `MonoidK.empty`/`pure`/
  * `orElse`/`FunctorFilter`/`Defer`/`Align` properties), reproduced here at the non-injective
  * [[ToyAlphabet]] plus one char check per shape.
  */
class GenericInstancesTest extends ScalaCheckSuite {

  private implicit val toy: ToyAlphabet.type = ToyAlphabet

  private val genToken: Gen[Byte] =
    Gen.frequency(
      (3, Gen.oneOf(1, 2, 4, 8).map(_.toByte)),
      (3, Gen.oneOf(3, 5, 10, 12, 15).map(_.toByte)),
      (1, Gen.choose(0, 15).map(_.toByte))
    )

  private val genInput: Gen[ByteSeq] =
    Gen.choose(0, 5).flatMap(n => Gen.listOfN(n, genToken)).map(l => ByteSeq.fromBytes(l.toArray))

  // ---- resolution: instances must be found by ordinary implicit search ----

  test("cats instances resolve for Parser0/Parser at the toy alphabet and at char") {
    assert(implicitly[Monad[Parser0[ByteSeq, *]]] ne null)
    assert(implicitly[Alternative[Parser0[ByteSeq, *]]] ne null)
    assert(implicitly[MonoidK[Parser[ByteSeq, *]]] ne null)
    assert(implicitly[FunctorFilter[Parser[ByteSeq, *]]] ne null)
    assert(implicitly[Align[Parser[ByteSeq, *]]] ne null)
    assert(implicitly[Monad[Parser0[String, *]]] ne null)
    assert(implicitly[Align[Parser[String, *]]] ne null)
  }

  // ---- MonoidK.empty never succeeds (ParserTest ~1590) ----

  property("MonoidK[Parser].empty never succeeds") {
    forAll(genInput) { input =>
      MonoidK[Parser[ByteSeq, *]].empty[Int].parse(input).isLeft
    }
  }

  property("MonoidK[Parser0].empty never succeeds") {
    forAll(genInput) { input =>
      MonoidK[Parser0[ByteSeq, *]].empty[Int].parse(input).isLeft
    }
  }

  // ---- pure law (ParserTest ~1597) ----

  property("Monad[Parser0].pure(i).parse(input) == Right((input, i))") {
    forAll(genInput, Gen.choose(0, 100)) { (input, i) =>
      Monad[Parser0[ByteSeq, *]].pure(i).parse(input) == Right((input, i))
    }
  }

  // ---- orElse idempotence (ParserTest ~1603) ----

  property("p orElse p behaves the same as p") {
    forAll(genInput) { input =>
      val p = Parser.tokenIn(ToyAlphabet)((1 << 1) | (1 << 2))
      (p.orElse(p)).parse(input) == p.parse(input)
    }
  }

  // ---- FunctorFilter equations (ParserTest ~2345-2422) ----

  property("p.filter(_ => true) == p") {
    forAll(genInput) { input =>
      val p = Parser.tokenIn(ToyAlphabet)((1 << 1) | (1 << 2))
      FunctorFilter[Parser[ByteSeq, *]].filter(p)(_ => true).parse(input) == p.parse(input)
    }
  }

  test("p.filter(_ => false) always fails") {
    val p = Parser.tokenIn(ToyAlphabet)((1 << 1) | (1 << 2))
    assert(FunctorFilter[Parser[ByteSeq, *]].filter(p)(_ => false).parse(ByteSeq(0x1)).isLeft)
  }

  property("mapFilter is filter + map") {
    forAll(genInput) { input =>
      val p = Parser.tokenIn(ToyAlphabet)((1 << 1) | (1 << 2))
      val viaMapFilter = p.mapFilter(t => if (t == 0x1) Some(t.toInt) else None).parse(input)
      val viaFilterMap = p.filter(_ == 0x1).map(_.toInt).parse(input)
      viaMapFilter == viaFilterMap
    }
  }

  // ---- Defer laziness (ParserTest ~1282) ----

  test("defer Parser0/Parser does not run eagerly") {
    def blowUp: Parser[ByteSeq, Int] = throw new RuntimeException("should not run eagerly")
    // constructing defer must not force blowUp
    val deferred = Parser.defer(blowUp)
    val deferred0 = Parser.defer0(blowUp: Parser0[ByteSeq, Int])
    assert((deferred ne null) && (deferred0 ne null))
  }

  // ---- Align associativity (ParserTest ~3089) ----

  test("align combines both results when both parsers match") {
    val a = Parser.tokenIn(ToyAlphabet)(1 << 1)
    val b = Parser.tokenIn(ToyAlphabet)(1 << 2)
    val aligned = Align[Parser[ByteSeq, *]].align(a, b)
    assertEquals(
      aligned.parse(ByteSeq(0x1, 0x2)),
      Right((ByteSeq(), cats.data.Ior.Both(0x1.toByte, 0x2.toByte)))
    )
  }

  test("align falls back to the right side alone when the left fails without consuming") {
    val a = Parser.tokenIn(ToyAlphabet)(1 << 4) // does not accept token 1
    val b = Parser.tokenIn(ToyAlphabet)(1 << 1)
    val aligned = Align[Parser[ByteSeq, *]].align(a, b)
    assertEquals(aligned.parse(ByteSeq(0x1)), Right((ByteSeq(), cats.data.Ior.Right(0x1.toByte))))
  }
}
