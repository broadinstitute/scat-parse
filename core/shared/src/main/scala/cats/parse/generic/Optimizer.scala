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

import cats.syntax.traverse._

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet

/** The `oneOf`/`oneOf0` construction-time optimizer (spec S5.3-5.4): fuses left-biased alternation
  * into longest-match [[Parser.Impl.SeqIn]] or a unioned [[Parser.Impl.TokenIn]] wherever that is
  * provably safe, and otherwise leaves the alternation as a plain `OneOf`/`OneOf0` — sound, merely
  * unoptimized. Kept separate from `Parser.scala` so the fusion algorithm is reviewable as one
  * unit; the structural normalization it leans on (`unmap`, `isVoided`, `hasKnownResult`) lives
  * with the leaves, in `Parser.Impl`.
  *
  * char's set-expansion rules — rewriting a `TokenIn(set)` into one literal alternative per member
  * (`allCharsIn`) so it can fuse with a literal alternation — are ported, but gated: the rewrite is
  * unsound for a non-injective alphabet (spec S5.4), so [[expandSet]] applies it only where the
  * alphabet's single-token literals match by equality.
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
      case (Impl.OneOf(ls), Impl.OneOf(rights @ (h :: t))) =>
        merge(ls.last, h) match {
          case Impl.OneOf(_) =>
            // nothing fused across the seam, so just concat
            Impl.OneOf(ls ::: rights)
          case l1 =>
            val newLeft = Impl.OneOf(ls.init :+ l1)
            t match {
              case rlast :: Nil => merge(newLeft, rlast)
              case twoOrMore => merge(newLeft, Impl.OneOf(twoOrMore))
            }
        }
      case (_, Impl.OneOf(rs @ (h :: t))) =>
        merge(left, h) match {
          case Impl.OneOf(_) => Impl.OneOf(left :: rs)
          case h1 =>
            // we made progress on h, so we may be able to make more on t
            if (t.lengthCompare(2) >= 0) merge(h1, Impl.OneOf(t))
            else merge(h1, t.head)
        }
      case (Impl.OneOf(ls), _) =>
        merge(ls.last, right) match {
          case Impl.OneOf(_) => Impl.OneOf(ls :+ right)
          case l1 =>
            val li = ls.init
            if (li.lengthCompare(2) >= 0) merge(Impl.OneOf(li), l1)
            else merge(li.head, l1)
        }
      case (Impl.TokenIn(a1, s1, c1), Impl.TokenIn(a2, s2, c2))
          if (c1 == c2) && Impl.sameAlphabet(a1, a2) =>
        // both always consume exactly one token, so no longest-match ambiguity can arise and the
        // union needs no guard; s2's TokenSet is path-dependent on a2, but a1 == a2 was just checked
        val fused: Parser[S, a1.Token] =
          Impl.TokenIn[S, a1.Token, a1.TokenSet](a1, a1.union(s1, s2.asInstanceOf[a1.TokenSet]), c1)
        fused.asInstanceOf[Parser[S, A]]
      case (Impl.TokenIn(a1, s1, _), Impl.SeqLit(_, _) | Impl.SeqIn(_, _, _))
          if isUniversal(a1)(s1.asInstanceOf[a1.TokenSet]) =>
        // the universal set matches whenever there is a token at all, so a literal alternative
        // after it is unreachable: if this one fails the input is exhausted and so would that be
        left
      case (UnitLiterals(a1, ls), UnitLiterals(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseUnit(a1)(left, right, reuseLeft = true)(ls, rs.asInstanceOf[List[S]])
      case (UnitTokens(a1, ls), UnitLiterals(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseUnit(a1)(left, right, reuseLeft = false)(ls, rs.asInstanceOf[List[S]])
      case (UnitLiterals(a1, ls), UnitTokens(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseUnit(a1)(left, right, reuseLeft = true)(ls, rs.asInstanceOf[List[S]])
      case (SliceLiterals(a1, ls), SliceLiterals(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseSlice(a1)(left, right, reuseLeft = true)(ls, rs.asInstanceOf[List[S]])
      case (SliceTokens(a1, ls), SliceLiterals(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseSlice(a1)(left, right, reuseLeft = false)(ls, rs.asInstanceOf[List[S]])
      case (SliceLiterals(a1, ls), SliceTokens(a2, rs)) if Impl.sameAlphabet(a1, a2) =>
        fuseSlice(a1)(left, right, reuseLeft = true)(ls, rs.asInstanceOf[List[S]])
      case (Impl.SliceP(a1, l1), Impl.SliceP(a2, r1)) if Impl.sameAlphabet(a1, a2) =>
        Parser.slice(a1)(merge[S, Any](l1, r1)).asInstanceOf[Parser[S, A]]
      case (Impl.Void(vl), Impl.Void(vr)) =>
        Parser.void(merge[S, Any](vl, vr)).asInstanceOf[Parser[S, A]]
      case (Impl.Void(vl), _) if Impl.isVoided(right) =>
        Parser.void(merge[S, Any](vl, right)).asInstanceOf[Parser[S, A]]
      case (_, Impl.Void(vr)) if Impl.isVoided(left) =>
        Parser.void(merge[S, Any](left, vr)).asInstanceOf[Parser[S, A]]
      case _ => Impl.OneOf(left :: right :: Nil)
    }

  def merge0[S, A](left: Parser0[S, A], right: Parser0[S, A]): Parser0[S, A] =
    (left, right) match {
      case (l1: Parser[S, A], r1: Parser[S, A]) => merge(l1, r1)
      case (_, _) if Impl.eventuallySucceeds(left) => left
      case (Impl.Fail(), _) => right
      case (_, Impl.Fail()) => left
      case (Impl.OneOf0(_), Impl.OneOf(rs)) =>
        merge0(left, Impl.OneOf0(rs))
      case (Impl.OneOf(ls), Impl.OneOf0(_)) =>
        merge0(Impl.OneOf0(ls), right)
      case (Impl.OneOf0(ls), Impl.OneOf0(rights @ (h :: t))) =>
        merge0(ls.last, h) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) =>
            // nothing fused across the seam, so just concat
            Impl.OneOf0(ls ::: rights)
          case l1 =>
            val newLeft = Impl.OneOf0(ls.init :+ l1)
            t match {
              case rlast :: Nil => merge0(newLeft, rlast)
              case twoOrMore => merge0(newLeft, Impl.OneOf0(twoOrMore))
            }
        }
      case (_, Impl.OneOf0(rs @ (h :: t))) =>
        merge0(left, h) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(left :: rs)
          case h1 => Impl.OneOf0(h1 :: t)
        }
      case (_, Impl.OneOf(rs @ (h :: t))) =>
        merge0(left, h) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(left :: rs)
          case h1: Parser[S, A] => Impl.OneOf(h1 :: t)
          case h1 => Impl.OneOf0(h1 :: t)
        }
      case (Impl.OneOf0(ls), _) =>
        merge0(ls.last, right) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(ls :+ right)
          case l1 => Impl.OneOf0(ls.init :+ l1)
        }
      case (Impl.OneOf(ls), _) =>
        merge0(ls.last, right) match {
          case Impl.OneOf(_) | Impl.OneOf0(_) => Impl.OneOf0(ls :+ right)
          case l1: Parser[S, A] => Impl.OneOf(ls.init :+ l1)
          case l1 => Impl.OneOf0(ls.init :+ l1)
        }
      case (Impl.Void0(vl), Impl.Void0(vr)) =>
        Parser.void0(merge0[S, Any](vl, vr)).asInstanceOf[Parser0[S, A]]
      case (Impl.Void0(vl), _) if Impl.isVoided(right) =>
        Parser.void0(merge0[S, Any](vl, right)).asInstanceOf[Parser0[S, A]]
      case (Impl.Void(vl), _) if Impl.isVoided(right) =>
        Parser.void0(merge0[S, Any](vl, right)).asInstanceOf[Parser0[S, A]]
      case (_, Impl.Void0(vr)) if Impl.isVoided(left) =>
        Parser.void0(merge0[S, Any](left, vr)).asInstanceOf[Parser0[S, A]]
      case (_, Impl.Void(vr)) if Impl.isVoided(left) =>
        Parser.void0(merge0[S, Any](left, vr)).asInstanceOf[Parser0[S, A]]
      case _ => Impl.OneOf0(left :: right :: Nil)
    }

  /** Fold [[merge]] over a whole alternative list, then hoist a capture or void wrapper shared by
    * every surviving alternative out of the alternation.
    *
    * Only adjacent pairs are offered to `merge`: an alternative that refuses to fuse with its
    * neighbour is parked in the accumulator rather than re-offered, because a left-biased
    * alternation may only be reordered where a fusion proved it safe.
    */
  def oneOfInternal[S, A](parsers: List[Parser[S, A]]): Parser[S, A] = {
    @tailrec
    def loop(ps: List[Parser[S, A]], acc: List[Parser[S, A]]): Parser[S, A] =
      ps match {
        case Nil =>
          /* we can still have an inner oneOf if the head items were not oneOf and couldn't be
           * merged, but the last items did have one */
          val flat = acc.reverse.flatMap {
            case Impl.OneOf(inner) => inner
            case one => one :: Nil
          }

          flat match {
            case Nil => Impl.Fail()
            case one :: Nil => one
            case many =>
              hoistSlice(many).orElse(hoistVoid(many)).getOrElse(Impl.OneOf(many))
          }
        case h :: Nil => loop(Nil, h :: acc)
        case h1 :: (t1 @ (h2 :: tail2)) =>
          merge(h1, h2) match {
            case Impl.OneOf(a :: b :: Nil) if (a eq h1) && (b eq h2) =>
              loop(t1, h1 :: acc)
            case h => loop(h :: tail2, acc)
          }
      }

    loop(parsers, Nil)
  }

  def oneOf0Internal[S, A](parsers: List[Parser0[S, A]]): Parser0[S, A] =
    if (parsers.forall(_.isInstanceOf[Parser[_, _]]))
      oneOfInternal(parsers.asInstanceOf[List[Parser[S, A]]])
    else {
      @tailrec
      def loop(ps: List[Parser0[S, A]], acc: List[Parser0[S, A]]): Parser0[S, A] =
        ps match {
          case Nil =>
            val flat = acc.reverse.flatMap {
              case Impl.OneOf(inner) => inner
              case Impl.OneOf0(inner) => inner
              case one => one :: Nil
            }
            Impl.cheapOneOf0(flat)
          case h :: Nil => loop(Nil, h :: acc)
          case h1 :: (t1 @ (h2 :: tail2)) =>
            merge0(h1, h2) match {
              case Impl.OneOf0(a :: b :: Nil) if (a eq h1) && (b eq h2) =>
                loop(t1, h1 :: acc)
              case Impl.OneOf(a :: b :: Nil) if (a eq h1) && (b eq h2) =>
                loop(t1, h1 :: acc)
              case h => loop(h :: tail2, acc)
            }
        }

      loop(parsers, Nil)
    }

  //////////////////////////////////////////////////////////////////////
  // Fusion guards (spec 5.3, corrected -- see ticket notes: the spec's original two-guard rule
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

  /** Fuse two literal groups into one longest-match parser, or leave the pair alone when
    * [[fuseLiterals]] could not prove the fusion safe.
    *
    * `reuseLeft` is `Some(left)` when `left` is itself the parser for exactly `ls` — a literal node
    * rather than a token set this optimizer expanded into literals. Only then can a fusion that
    * dropped every right-hand alternative answer with the original node; an expansion has to build
    * its result, because `left` was never a literal alternation to begin with.
    */
  private def fuse[S, A](alpha: Alphabet[S])(
      reuseLeft: Option[Parser[S, A]],
      unfused: => Parser[S, A],
      one: S => Parser[S, A],
      many: SortedSet[S] => Parser[S, A]
  )(ls: List[S], rs: List[S]): Parser[S, A] =
    fuseLiterals(alpha)(ls, rs) match {
      case Some(fused) if reuseLeft.isDefined && (fused == ls) => reuseLeft.get
      case Some(lit :: Nil) => one(lit)
      case Some(fused) => many(SortedSet(fused: _*)(alpha.orderingS))
      case None => unfused
    }

  /** the [[fuse]] of alternatives that discard what they matched */
  private def fuseUnit[S, A](alpha: Alphabet[S])(
      left: Parser[S, A],
      right: Parser[S, A],
      reuseLeft: Boolean
  )(ls: List[S], rs: List[S]): Parser[S, A] = {
    val aux = alpha.asInstanceOf[Alphabet.Aux[S, Any]]
    fuse(alpha)(
      if (reuseLeft) Some(left) else None,
      Impl.OneOf(left :: right :: Nil),
      lit => Impl.SeqLit(alpha, lit).asInstanceOf[Parser[S, A]],
      sorted => Impl.SeqIn(aux, sorted, capturing = false).asInstanceOf[Parser[S, A]]
    )(ls, rs)
  }

  /** the [[fuse]] of alternatives that capture what they matched */
  private def fuseSlice[S, A](alpha: Alphabet[S])(
      left: Parser[S, A],
      right: Parser[S, A],
      reuseLeft: Boolean
  )(ls: List[S], rs: List[S]): Parser[S, A] = {
    val aux = alpha.asInstanceOf[Alphabet.Aux[S, Any]]
    fuse(alpha)(
      if (reuseLeft) Some(left) else None,
      Impl.OneOf(left :: right :: Nil),
      lit => Parser.slice(alpha)(Impl.SeqLit(alpha, lit)).asInstanceOf[Parser[S, A]],
      sorted => Impl.SeqIn(aux, sorted).asInstanceOf[Parser[S, A]]
    )(ls, rs)
  }

  private def isUniversal[S](alpha: Alphabet[S])(set: alpha.TokenSet): Boolean =
    set == alpha.universal

  /** The members of `set` as one length-1 literal each — char's `allCharsIn`, which is what brings
    * a token alternative into a literal alternation so the two can fuse.
    *
    * None when the rewrite would not be faithful: the alphabet's single-token literals must match
    * by equality (otherwise a member's literal pattern accepts strictly more than the member does,
    * spec S5.4), and a universal set is refused outright — enumerating the whole token domain is
    * never worth it, and a universal set absorbs its literal neighbours anyway.
    */
  private def expandSet[S](alpha: Alphabet[S])(set: alpha.TokenSet): Option[List[S]] =
    if (isUniversal(alpha)(set)) None
    else {
      val lits = alpha.literalsOf(set)
      if (lits.nonEmpty && lits.forall(Impl.exactLiteral(alpha)(_))) Some(lits) else None
    }

  /** Recognizes a `Parser[S, Unit]` that is one-or-more literal alternatives under one alphabet: a
    * bare [[Parser.Impl.SeqLit]], or a previously fused non-capturing `SeqIn` (this optimizer's own
    * output, re-examined on a later fold step).
    */
  private object UnitLiterals {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.SeqLit(alpha, lit) => Some((alpha, lit :: Nil))
        case Impl.SeqIn(alpha, sorted, false) => Some((alpha, sorted.toList))
        case _ => None
      }
  }

  /** the [[UnitLiterals]] a voided token set expands into. Kept apart from [[UnitLiterals]] so that
    * two token sets meet each other as sets — the `TokenIn` union above is both cheaper and tighter
    * than expanding either one into literals.
    */
  private object UnitTokens {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.TokenIn(alpha, set, false) =>
          expandSet(alpha)(set.asInstanceOf[alpha.TokenSet]).map((alpha, _))
        case _ => None
      }
  }

  /** the [[SliceLiterals]] a capturing token set expands into, as [[UnitTokens]] is for
    * [[UnitLiterals]]
    */
  private object SliceTokens {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.SliceP(alpha, Impl.TokenIn(a2, set, _)) if Impl.sameAlphabet(alpha, a2) =>
          expandSet(a2)(set.asInstanceOf[a2.TokenSet]).map((alpha, _))
        case _ => None
      }
  }

  /** Recognizes a `Parser[S, alpha.Slice]` that is one-or-more literal alternatives: a bare
    * [[Parser.Impl.SeqIn]], a single literal whose capture the normalizer already folded to a
    * constant (`Map(SeqLit, ConstFn)`, what `seq(lit).slice` builds for an equality alphabet), or
    * an un-folded `SliceP(alpha, SeqLit(...))` for an alphabet where it isn't constant.
    */
  private object SliceLiterals {
    def unapply[S](p: Parser[S, Any]): Option[(Alphabet[S], List[S])] =
      p match {
        case Impl.SeqIn(alpha, sorted, true) => Some((alpha, sorted.toList))
        case Impl.SliceP(alpha, Impl.SeqLit(alpha2, lit)) if Impl.sameAlphabet(alpha, alpha2) =>
          Some((alpha, lit :: Nil))
        case _ => Impl.definiteSlice(p).map { case (alpha, lit) => (alpha, lit :: Nil) }
      }
  }

  /** every alternative captures its own match under one alphabet, so the capture can wrap the whole
    * alternation instead — char's `StringP` hoist
    */
  private def hoistSlice[S, A](many: List[Parser[S, A]]): Option[Parser[S, A]] =
    many match {
      case Impl.SliceP(alpha, _) :: _ =>
        many
          .traverse[Option, Parser[S, Any]] {
            case Impl.SliceP(a, under) if Impl.sameAlphabet(alpha, a) => Some(under)
            case _ => None
          }
          .map { inner =>
            Impl.SliceP(alpha, Impl.OneOf(inner)).asInstanceOf[Parser[S, A]]
          }
      case _ => None
    }

  /** every alternative discards its own result, so the void can wrap the whole alternation */
  private def hoistVoid[S, A](many: List[Parser[S, A]]): Option[Parser[S, A]] =
    many
      .traverse[Option, Parser[S, Any]] {
        case Impl.Void(under) => Some(under)
        case _ => None
      }
      .map { inner => Impl.Void(Impl.OneOf(inner)).asInstanceOf[Parser[S, A]] }
}
