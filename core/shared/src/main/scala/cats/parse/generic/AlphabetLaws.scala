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

import scala.collection.immutable.SortedSet

/** The instance contract for [[Alphabet]], as executable checks.
  *
  * Each law is a pure function over an alphabet and caller-supplied sample values, returning
  * `Right(())` when the law holds and `Left(description)` when it does not. There is no
  * test-framework dependency: run these from any harness (this repository property-tests them from
  * ScalaCheck generators; an external instance can do the same). An instance that passes all laws
  * over well-distributed samples honors the contract the generic parser machinery relies on.
  */
object AlphabetLaws {

  /** `scanWhile` agrees with repeated `matchesAt`. */
  def scanWhileConsistent[S](
      alpha: Alphabet[S]
  )(set: alpha.TokenSet, s: S, from: Int): Either[String, Unit] = {
    val len = alpha.length(s)
    var i = from
    while ((i < len) && alpha.matchesAt(set, s, i)) {
      i += 1
    }
    val got = alpha.scanWhile(set, s, from)
    check(
      got == i,
      s"scanWhile($set, $s, $from) = $got, but matchesAt scan stops at $i"
    )
  }

  /** `matchesAt` is false at and beyond the end of the input. */
  def matchesAtBounded[S](
      alpha: Alphabet[S]
  )(set: alpha.TokenSet, s: S, past: Int): Either[String, Unit] = {
    val i = alpha.length(s) + java.lang.Math.max(past, 0)
    check(!alpha.matchesAt(set, s, i), s"matchesAt($set, $s, $i) true past end of input")
  }

  /** `startsWithAt` is exactly slice equality over the literal's window. */
  def startsWithAtConsistent[S](
      alpha: Alphabet[S]
  )(s: S, offset: Int, lit: S): Either[String, Unit] = {
    val litLen = alpha.length(lit)
    val fits = (offset >= 0) && ((offset + litLen) <= alpha.length(s))
    val expected = fits && (alpha.slice(s, offset, offset + litLen) == alpha.slice(lit, 0, litLen))
    val got = alpha.startsWithAt(s, offset, lit)
    check(
      got == expected,
      s"startsWithAt($s, $offset, $lit) = $got but slice comparison says $expected"
    )
  }

  /** When every set of a literal's pattern is a singleton, `startsWithAt` and per-position pattern
    * matching agree — the coherence the `seq` fast path relies on when it substitutes
    * `startsWithAt` for set matching.
    */
  def singletonPatternCoherent[S](
      alpha: Alphabet[S]
  )(lit: S, s: S, offset: Int): Either[String, Unit] = {
    val pat = alpha.pattern(lit)
    val allSingleton = pat.forall(set => alpha.literalsOf(set).lengthCompare(1) == 0)
    if (!allSingleton || (offset < 0) || pat.isEmpty) Right(())
    else {
      val bySets = pat.zipWithIndex.forall { case (set, k) =>
        alpha.matchesAt(set, s, offset + k)
      }
      val byLiteral = alpha.startsWithAt(s, offset, lit)
      check(
        byLiteral == bySets,
        s"all-singleton pattern of $lit: startsWithAt($s, $offset, lit) = $byLiteral " +
          s"but per-position matching says $bySets"
      )
    }
  }

  /** A literal's own tokens satisfy its pattern, position by position. */
  def patternSelfMatch[S](alpha: Alphabet[S])(lit: S): Either[String, Unit] = {
    val pat = alpha.pattern(lit)
    if (pat.length != alpha.length(lit))
      Left(s"pattern($lit) has ${pat.length} sets but length(lit) = ${alpha.length(lit)}")
    else {
      val bad = pat.zipWithIndex.collectFirst {
        case (set, i) if !alpha.matchesAt(set, lit, i) => i
      }
      check(
        bad.isEmpty,
        s"pattern($lit) does not match lit itself at position ${bad.getOrElse(-1)}"
      )
    }
  }

  /** `subsetOf(a, b)` implies membership in `a` implies membership in `b`, checked at every
    * position of the sample input.
    */
  def subsetOfSound[S](
      alpha: Alphabet[S]
  )(a: alpha.TokenSet, b: alpha.TokenSet, s: S): Either[String, Unit] =
    if (!alpha.subsetOf(a, b)) Right(())
    else {
      val bad = (0 until alpha.length(s)).find { i =>
        alpha.matchesAt(a, s, i) && !alpha.matchesAt(b, s, i)
      }
      check(
        bad.isEmpty,
        s"subsetOf($a, $b) holds but position ${bad.getOrElse(-1)} of $s is in a and not in b"
      )
    }

  /** `!intersects(a, b)` implies no position of the sample input is a member of both. */
  def intersectsSound[S](
      alpha: Alphabet[S]
  )(a: alpha.TokenSet, b: alpha.TokenSet, s: S): Either[String, Unit] =
    if (alpha.intersects(a, b)) Right(())
    else {
      val bad = (0 until alpha.length(s)).find { i =>
        alpha.matchesAt(a, s, i) && alpha.matchesAt(b, s, i)
      }
      check(
        bad.isEmpty,
        s"!intersects($a, $b) but position ${bad.getOrElse(-1)} of $s is in both"
      )
    }

  /** `union` membership is the disjunction of the members' memberships. */
  def unionConsistent[S](
      alpha: Alphabet[S]
  )(a: alpha.TokenSet, b: alpha.TokenSet, s: S): Either[String, Unit] = {
    val u = alpha.union(a, b)
    val bad = (0 until alpha.length(s)).find { i =>
      alpha.matchesAt(u, s, i) != (alpha.matchesAt(a, s, i) || alpha.matchesAt(b, s, i))
    }
    check(
      bad.isEmpty,
      s"union($a, $b) disagrees with disjunction at position ${bad.getOrElse(-1)} of $s"
    )
  }

  /** `universal` matches every in-bounds position. */
  def universalMatches[S](alpha: Alphabet[S])(s: S): Either[String, Unit] = {
    val bad = (0 until alpha.length(s)).find(i => !alpha.matchesAt(alpha.universal, s, i))
    check(bad.isEmpty, s"universal does not match position ${bad.getOrElse(-1)} of $s")
  }

  /** Every literal from `literalsOf(set)` is a single token that is a member of `set`. */
  def literalsOfRoundtrip[S](alpha: Alphabet[S])(set: alpha.TokenSet): Either[String, Unit] = {
    val bad = alpha.literalsOf(set).find { lit =>
      (alpha.length(lit) != 1) || !alpha.matchesAt(set, lit, 0)
    }
    check(
      bad.isEmpty,
      s"literalsOf($set) produced ${bad.getOrElse("")}, not a single-token member of the set"
    )
  }

  /** `setWhere(p)` holds exactly the tokens satisfying `p`, checked at every position of the sample
    * input (and empty only when no sampled position satisfies `p`).
    */
  def setWhereMembership[S](
      alpha: Alphabet[S]
  )(p: alpha.Token => Boolean, s: S): Either[String, Unit] = {
    val set = alpha.setWhere(p)
    val bad = (0 until alpha.length(s)).find { i =>
      val wanted = p(alpha.tokenAt(s, i))
      set.fold(wanted)(alpha.matchesAt(_, s, i) != wanted)
    }
    check(
      bad.isEmpty,
      s"setWhere = $set disagrees with the predicate at position ${bad.getOrElse(-1)} of $s"
    )
  }

  /** `expectSet` reports every expectation at the requested offset. */
  def expectSetOffsets[S](
      alpha: Alphabet[S]
  )(offset: Int, set: alpha.TokenSet): Either[String, Unit] = {
    val bad = alpha.expectSet(offset, set).find(_.offset != offset)
    check(bad.isEmpty, s"expectSet($offset, $set) produced $bad at the wrong offset")
  }

  /** `subInput` agrees with `slice` on content, over the same `S` type (both are the alphabet's
    * "capture a window" operation, differing only in result type).
    */
  def subInputCoherent[S](
      alpha: Alphabet[S]
  )(s: S, from: Int, until: Int): Either[String, Unit] = {
    val fits = (from >= 0) && (from <= until) && (until <= alpha.length(s))
    if (!fits) Right(())
    else {
      val got = alpha.subInput(s, from, until)
      check(
        alpha.length(got) == (until - from) && alpha.slice(got, 0, until - from) == alpha
          .slice(s, from, until),
        s"subInput($s, $from, $until) = $got disagrees with slice($s, $from, $until)"
      )
    }
  }

  /** The instance's `seqMatcher` agrees with the naive longest-match reference
    * ([[SeqMatcher.naive]]) at the sampled offset.
    */
  def seqMatcherAgreesWithNaive[S](
      alpha: Alphabet[S]
  )(alts: SortedSet[S], input: S, offset: Int): Either[String, Unit] = {
    val got = alpha.seqMatcher(alts).matchAt(input, offset)
    val expected = SeqMatcher.naive(alpha, alts).matchAt(input, offset)
    check(
      got == expected,
      s"seqMatcher($alts).matchAt($input, $offset) = $got but the naive reference says $expected"
    )
  }

  private def check(cond: Boolean, msg: => String): Either[String, Unit] =
    if (cond) Right(()) else Left(msg)
}
