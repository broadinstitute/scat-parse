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

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet

/** The `oneOf`/`oneOf0` construction-time optimizer (spec S5.3-5.4): fuses left-biased alternation
  * into longest-match [[Parser.Impl.SeqIn]] or a unioned [[Parser.Impl.TokenIn]] wherever that is
  * provably safe, and otherwise leaves the alternation as a plain `OneOf`/`OneOf0` — sound, merely
  * unoptimized. Kept separate from `Parser.scala` so the fusion algorithm is reviewable as one
  * unit.
  *
  * Deliberately out of scope here (ticket notes, not required by this ticket's charter): the
  * `unmap`/`hasKnownResult`-driven micro-optimizations char's optimizer also does (trailing-map
  * stripping, constant-result collapsing, `Void`/`Backtrack` elision) — every combinator here is
  * correct without them, just occasionally holding one extra wrapper node.
  */
private[parse] object Optimizer {
  import Parser.Impl

  //////////////////////////////////////////////////////////////////////
  // merge: the pairwise fusion attempt, and the fold that drives it over a whole alternative list.
  //////////////////////////////////////////////////////////////////////

  def merge[S, A](left: Parser[S, A], right: Parser[S, A]): Parser[S, A] =
    (left, right) match {
      case (Impl.Fail(), _) => right
      case (_, Impl.Fail()) => left
      case (Impl.OneOf(ls), right) =>
        merge(ls.last, right) match {
          case trivial if unfusedPair(ls.last, right, trivial) => Impl.OneOf(ls :+ right)
          case fused => Impl.OneOf(ls.init :+ fused)
        }
      case (left, Impl.OneOf(rs @ (h :: t))) =>
        merge(left, h) match {
          case trivial if unfusedPair(left, h, trivial) => Impl.OneOf(left :: rs)
          case fused => Impl.OneOf(fused :: t)
        }
      case (Impl.TokenIn(a1, s1), Impl.TokenIn(a2, s2)) if sameAlphabet(a1, a2) =>
        // s2's TokenSet is path-dependent on a2, not a1 -- safe to cast, a1 == a2 just checked
        val fused: Parser[S, a1.Token] =
          Impl.TokenIn[S, a1.Token, a1.TokenSet](a1, a1.union(s1, s2.asInstanceOf[a1.TokenSet]))
        fused.asInstanceOf[Parser[S, A]]
      case (UnitLiterals(a1, ls), UnitLiterals(a2, rs)) if sameAlphabet(a1, a2) =>
        fuseLiterals(a1)(ls, rs.asInstanceOf[List[S]]) match {
          case Some(one :: Nil) => Impl.SeqLit(a1, one).asInstanceOf[Parser[S, A]]
          case Some(fused) =>
            val alpha = a1.asInstanceOf[Alphabet.Aux[S, Any]]
            Impl
              .Void(Impl.SeqIn(alpha, SortedSet(fused: _*)(alpha.orderingS)))
              .asInstanceOf[Parser[S, A]]
          case None => Impl.OneOf(left :: right :: Nil)
        }
      case (SliceLiterals(a1, ls), SliceLiterals(a2, rs)) if sameAlphabet(a1, a2) =>
        fuseLiterals(a1)(ls, rs.asInstanceOf[List[S]]) match {
          case Some(one :: Nil) =>
            val alpha = a1.asInstanceOf[Alphabet.Aux[S, Any]]
            Impl.SliceP(alpha, Impl.SeqLit(alpha, one)).asInstanceOf[Parser[S, A]]
          case Some(fused) =>
            val alpha = a1.asInstanceOf[Alphabet.Aux[S, Any]]
            Impl
              .SeqIn(alpha, SortedSet(fused: _*)(alpha.orderingS))
              .asInstanceOf[Parser[S, A]]
          case None => Impl.OneOf(left :: right :: Nil)
        }
      case _ => Impl.OneOf(left :: right :: Nil)
    }

  def merge0[S, A](left: Parser0[S, A], right: Parser0[S, A]): Parser0[S, A] =
    (left, right) match {
      case (l1: Parser[S, A], r1: Parser[S, A]) => merge(l1, r1)
      case (Impl.Fail(), _) => right
      case (_, Impl.Fail()) => left
      case (Impl.OneOf0(ls), right) =>
        merge0(ls.last, right) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(ls :+ right)
          case fused => Impl.OneOf0(ls.init :+ fused)
        }
      case (left, Impl.OneOf0(rs @ (h :: t))) =>
        merge0(left, h) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(left :: rs)
          case fused => Impl.OneOf0(fused :: t)
        }
      case _ => Impl.OneOf0(left :: right :: Nil)
    }

  def oneOfInternal[S, A](parsers: List[Parser[S, A]]): Parser[S, A] =
    parsers match {
      case Nil => Impl.Fail()
      case one :: Nil => one
      case h :: t => t.foldLeft(h)(merge(_, _))
    }

  def oneOf0Internal[S, A](parsers: List[Parser0[S, A]]): Parser0[S, A] =
    parsers match {
      case Nil => Impl.Fail()
      case one :: Nil => one
      case h :: t => t.foldLeft(h)(merge0(_, _))
    }

  //////////////////////////////////////////////////////////////////////
  // Fusion guards (spec 5.3, corrected — see ticket notes: the spec's original two-guard rule
  // rejects fusions char performs today, e.g. oneOf(string("a"), string("ab")); the third,
  // length-based guard below is what closes that gap while still rejecting the {A, RG}-shaped
  // divergence).
  //////////////////////////////////////////////////////////////////////

  /** `r` is dead once `l` precedes it in a left-biased `oneOf`: whenever `r`'s pattern fully
    * matches, `l`'s pattern (no longer than `r`'s) also fully matches over its own length, so the
    * original `oneOf` always resolves via `l` before `r` is ever reached. Safe to drop `r`
    * entirely.
    */
  private[generic] def shadows[S](alpha: Alphabet[S])(l: S, r: S): Boolean = {
    val patL = alpha.pattern(l)
    val patR = alpha.pattern(r)
    (patL.lengthCompare(patR.length) <= 0) &&
    patL.zip(patR).forall { case (sl, sr) => alpha.subsetOf(sr, sl) }
  }

  /** Safe to keep `r` alongside `l` in one longest-match structure even though `r` is not shadowed
    * by `l`: either `l` is already at least as long (so `r` can never wrongly outrank it — and when
    * they tie, both consume the same input, so a longest-match structure's own tie-break is
    * unobservable through [[Parser.seqIn]]'s "return what matched" contract), or some common-prefix
    * position makes them mutually exclusive (so they can never both match).
    */
  private[generic] def fusableKeep[S](alpha: Alphabet[S])(l: S, r: S): Boolean = {
    val patL = alpha.pattern(l)
    val patR = alpha.pattern(r)
    (patL.lengthCompare(patR.length) >= 0) ||
    patL.zip(patR).exists { case (sl, sr) => !alpha.intersects(sl, sr) }
  }

  /** Fuse `rs` (a right-hand alternative group, entirely later in left-biased order) into `ls`.
    * Each `r` is either dropped (shadowed by some `l`), kept (safe against every `l`), or — if
    * neither — the whole fusion is abandoned: `None` tells the caller to leave the pair unfused.
    */
  private[generic] def fuseLiterals[S](
      alpha: Alphabet[S]
  )(ls: List[S], rs: List[S]): Option[List[S]] = {
    @tailrec
    def loop(remaining: List[S], kept: List[S]): Option[List[S]] =
      remaining match {
        case Nil => Some(ls ::: kept.reverse)
        case r :: tail =>
          if (ls.exists(l => shadows(alpha)(l, r))) loop(tail, kept)
          else if (ls.forall(l => fusableKeep(alpha)(l, r))) loop(tail, r :: kept)
          else None
      }
    loop(rs, Nil)
  }

  /** Recognizes a `Parser[S, Unit]` that is one-or-more literal alternatives under one alphabet: a
    * bare [[Parser.Impl.SeqLit]], or a previously fused `Void(SeqIn(...))` (this optimizer's own
    * output, re-examined on a later fold step).
    */
  private object UnitLiterals {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.SeqLit(alpha, lit) => Some((alpha, lit :: Nil))
        case Impl.Void(Impl.SeqIn(alpha, sorted)) => Some((alpha, sorted.toList))
        case _ => None
      }
  }

  /** Recognizes a `Parser[S, alpha.Slice]` that is one-or-more literal alternatives: a bare
    * [[Parser.Impl.SeqIn]], or a single literal captured via `.slice` (`SliceP(alpha, SeqLit(alpha,
    * lit))`, [[Parser.seq]]'s own `.slice` shape) -- the common building block for a `oneOf` of
    * several individually-captured literals, e.g. this file's char parity tests.
    */
  private object SliceLiterals {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.SeqIn(alpha, sorted) => Some((alpha, sorted.toList))
        case Impl.SliceP(alpha, Impl.SeqLit(alpha2, lit)) if sameAlphabet(alpha, alpha2) =>
          Some((alpha, lit :: Nil))
        case _ => None
      }
  }

  private def sameAlphabet[S](a1: Alphabet[S], a2: Alphabet[S]): Boolean =
    (a1.asInstanceOf[AnyRef] eq a2.asInstanceOf[AnyRef]) || (a1 == a2)

  private def unfusedPair[S, A](l: Parser[S, A], r: Parser[S, A], result: Parser[S, A]): Boolean =
    result match {
      case Impl.OneOf(a :: b :: Nil) =>
        (a.asInstanceOf[AnyRef] eq l.asInstanceOf[AnyRef]) &&
        (b.asInstanceOf[AnyRef] eq r.asInstanceOf[AnyRef])
      case _ => false
    }
}
