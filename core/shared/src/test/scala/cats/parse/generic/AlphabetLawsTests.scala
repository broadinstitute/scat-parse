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

import scala.collection.immutable.SortedSet

/** Property-tests every [[AlphabetLaws]] check against one [[Alphabet]] instance. Subclasses supply
  * the instance and its generators.
  */
abstract class AlphabetLawsTests extends ScalaCheckSuite {
  type S
  val alpha: Alphabet[S]

  def genS: Gen[S]
  def genSet: Gen[alpha.TokenSet]

  /** Non-empty literals (empty literals are excluded by the seqMatcher precondition). */
  def genLit: Gen[S]

  private def genAlts: Gen[SortedSet[S]] =
    Gen.nonEmptyListOf(genLit).map { ls => SortedSet(ls: _*)(alpha.orderingS) }

  private def law(res: Either[String, Unit]): Prop =
    res.fold(msg => Prop.falsified :| msg, _ => Prop.proved)

  property("scanWhile agrees with matchesAt") {
    forAll(genSet, genS, Gen.choose(0, 8)) { (set, s, from) =>
      law(AlphabetLaws.scanWhileConsistent(alpha)(set, s, from))
    }
  }

  property("matchesAt is false past the end of input") {
    forAll(genSet, genS, Gen.choose(0, 4)) { (set, s, past) =>
      law(AlphabetLaws.matchesAtBounded(alpha)(set, s, past))
    }
  }

  property("startsWithAt is slice equality over the literal window") {
    forAll(genS, Gen.choose(0, 8), genLit) { (s, offset, lit) =>
      law(AlphabetLaws.startsWithAtConsistent(alpha)(s, offset, lit))
    }
  }

  property("startsWithAt agrees with matching an all-singleton pattern") {
    forAll(genLit, genS, Gen.choose(0, 8)) { (lit, s, offset) =>
      law(AlphabetLaws.singletonPatternCoherent(alpha)(lit, s, offset))
    }
  }

  property("a literal satisfies its own pattern") {
    forAll(genLit) { lit =>
      law(AlphabetLaws.patternSelfMatch(alpha)(lit))
    }
  }

  property("subsetOf is sound") {
    forAll(genSet, genSet, genS) { (a, b, s) =>
      law(AlphabetLaws.subsetOfSound(alpha)(a, b, s))
    }
  }

  property("intersects is sound") {
    forAll(genSet, genSet, genS) { (a, b, s) =>
      law(AlphabetLaws.intersectsSound(alpha)(a, b, s))
    }
  }

  property("union membership is the disjunction") {
    forAll(genSet, genSet, genS) { (a, b, s) =>
      law(AlphabetLaws.unionConsistent(alpha)(a, b, s))
    }
  }

  property("universal matches everywhere") {
    forAll(genS) { s =>
      law(AlphabetLaws.universalMatches(alpha)(s))
    }
  }

  property("literalsOf produces single-token members") {
    forAll(genSet) { set =>
      law(AlphabetLaws.literalsOfRoundtrip(alpha)(set))
    }
  }

  property("expectSet reports the requested offset") {
    forAll(Gen.choose(0, 100), genSet) { (offset, set) =>
      law(AlphabetLaws.expectSetOffsets(alpha)(offset, set))
    }
  }

  property("seqMatcher agrees with the naive longest-match reference") {
    forAll(genAlts, genS, Gen.choose(0, 8)) { (alts, s, offset) =>
      law(AlphabetLaws.seqMatcherAgreesWithNaive(alpha)(alts, s, offset))
    }
  }
}

class StringAlphabetLawsTest extends AlphabetLawsTests {
  type S = String
  val alpha: StringAlphabet.type = StringAlphabet

  // a small alphabet with contiguous runs, biased toward collisions
  private val genChar: Gen[Char] =
    Gen.frequency(
      (4, Gen.oneOf('a', 'b', 'c', 'd')),
      (2, Gen.oneOf('x', 'y')),
      (1, Gen.choose('A', 'F'))
    )

  def genS: Gen[String] = Gen.listOf(genChar).map(_.mkString)
  def genLit: Gen[String] = Gen.nonEmptyListOf(genChar).map(_.mkString)
  def genSet: Gen[alpha.TokenSet] =
    Gen.nonEmptyListOf(genChar).map(cs => StringAlphabet.charSet(cs))
}

class ToyAlphabetLawsTest extends AlphabetLawsTests {
  type S = ByteSeq
  val alpha: ToyAlphabet.type = ToyAlphabet

  // biased toward ambiguous masks, the analogue of the char suite's collision bias
  private val genToken: Gen[Byte] =
    Gen.frequency(
      (3, Gen.oneOf(1, 2, 4, 8).map(_.toByte)), // unambiguous base tokens
      (3, Gen.oneOf(3, 5, 10, 12, 15).map(_.toByte)), // ambiguous masks
      (1, Gen.choose(0, 15).map(_.toByte))
    )

  def genS: Gen[ByteSeq] = Gen.listOf(genToken).map(l => ByteSeq.fromBytes(l.toArray))
  def genLit: Gen[ByteSeq] = Gen.nonEmptyListOf(genToken).map(l => ByteSeq.fromBytes(l.toArray))
  def genSet: Gen[alpha.TokenSet] = Gen.choose(0, 0xffff)
}
