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

import cats.{Order, Show}
import cats.data.NonEmptyList
import cats.implicits._

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet
import scala.collection.mutable.ListBuffer

/** An expectation reports the kind of parsing error and where it occurred.
  *
  * The hierarchy is sealed except for one open branch: [[Expectation.OfAlphabet]], under which each
  * [[Alphabet]] instance defines its own token-set expectation cases (char's is `InRange`).
  */
sealed abstract class Expectation[S] {
  def offset: Int

  /** This is a reverse order stack (most recent context first) of this parsing error
    */
  def context: List[String] =
    this match {
      case Expectation.WithContext(ctx, inner) =>
        ctx :: inner.context
      case _ => Nil
    }
}

object Expectation {
  final case class OneOfSeq[S](offset: Int, seqs: List[S]) extends Expectation[S]
  final case class StartOfString[S](offset: Int) extends Expectation[S]
  final case class EndOfString[S](offset: Int, length: Int) extends Expectation[S]
  final case class Length[S](offset: Int, expected: Int, actual: Int) extends Expectation[S]
  final case class ExpectedFailureAt[S](offset: Int, matched: S) extends Expectation[S]
  // this is the result of oneOf0(Nil) at a given location
  final case class Fail[S](offset: Int) extends Expectation[S]
  final case class FailWith[S](offset: Int, message: String) extends Expectation[S]
  final case class WithContext[S](contextStr: String, expect: Expectation[S])
      extends Expectation[S] {
    def offset: Int = expect.offset
  }

  /** The one open branch of the hierarchy: expectation cases whose meaning only an [[Alphabet]]
    * instance can interpret (a token set cannot be a plain generic case-class field). The char
    * instance's case is `InRange`; other instances define their own. The backing cold obligations
    * on [[Alphabet]] are `expectSet`, `mergeOfAlphabet`, `orderOfAlphabet` and `showOfAlphabet`.
    */
  abstract class OfAlphabet[S] extends Expectation[S]

  implicit def catsOrderExpectation[S](implicit alpha: Alphabet[S]): Order[Expectation[S]] =
    new Order[Expectation[S]] {
      private def rank(ex: Expectation[S]): Int =
        ex match {
          case OneOfSeq(_, _) => 0
          case _: OfAlphabet[S] => 1
          case StartOfString(_) => 2
          case EndOfString(_, _) => 3
          case Length(_, _, _) => 4
          case ExpectedFailureAt(_, _) => 5
          case Fail(_) => 6
          case FailWith(_, _) => 7
          case WithContext(_, _) => 8
        }

      private def compareSeqs(s1: List[S], s2: List[S]): Int = {
        @tailrec
        def loop(l1: List[S], l2: List[S]): Int =
          (l1, l2) match {
            case (Nil, Nil) => 0
            case (Nil, _) => -1
            case (_, Nil) => 1
            case (h1 :: t1, h2 :: t2) =>
              val c = alpha.orderingS.compare(h1, h2)
              if (c != 0) c else loop(t1, t2)
          }
        loop(s1, s2)
      }

      override def compare(left: Expectation[S], right: Expectation[S]): Int = {
        val c = Integer.compare(left.offset, right.offset)
        if (c != 0) c
        else if (left == right) 0
        else {
          val rl = rank(left)
          val rr = rank(right)
          if (rl != rr) Integer.compare(rl, rr)
          else
            (left, right) match {
              case (OneOfSeq(_, s1), OneOfSeq(_, s2)) => compareSeqs(s1, s2)
              case (oa1: OfAlphabet[S], oa2: OfAlphabet[S]) =>
                alpha.orderOfAlphabet.compare(oa1, oa2)
              case (EndOfString(_, l1), EndOfString(_, l2)) =>
                Integer.compare(l1, l2)
              case (Length(_, e1, a1), Length(_, e2, a2)) =>
                val c1 = Integer.compare(e1, e2)
                if (c1 == 0) Integer.compare(a1, a2)
                else c1
              case (ExpectedFailureAt(_, m1), ExpectedFailureAt(_, m2)) =>
                alpha.orderingS.compare(m1, m2)
              case (FailWith(_, s1), FailWith(_, s2)) =>
                s1.compare(s2)
              case (WithContext(lctx, lexp), WithContext(rctx, rexp)) =>
                val c1 = compare(lexp, rexp)
                if (c1 != 0) c1
                else lctx.compareTo(rctx)
              // same rank, no fields to distinguish (e.g. StartOfString at equal offsets)
              case (_, _) => 0
            }
        }
      }
    }

  implicit def catsShowExpectation[S](implicit alpha: Alphabet[S]): Show[Expectation[S]] =
    new Show[Expectation[S]] {
      def show(expectation: Expectation[S]): String = expectation match {
        case OneOfSeq(_, seqs) =>
          if (seqs.lengthCompare(1) > 0) {
            "must match one of the strings: " + seqs.iterator
              .map(alpha.showLiteral(_))
              .mkString("{", ", ", "}")
          } else {
            if (seqs.nonEmpty) {
              "must match string: " + alpha.showLiteral(seqs.head)
            } else {
              "??? bug with Expectation.OneOfSeq"
            }
          }

        case oa: OfAlphabet[S] =>
          alpha.showOfAlphabet.show(oa)

        case StartOfString(_) =>
          "must start the string"

        case EndOfString(_, _) =>
          s"must end the string"

        case Length(_, expected, actual) =>
          s"must have a length of $expected but got a length of $actual"

        case ExpectedFailureAt(_, matched) =>
          s"must fail but matched with $matched"

        case Fail(_) =>
          "must fail"

        case FailWith(_, message) =>
          s"must fail: $message"

        case WithContext(contextStr, expect) =>
          s"context: $contextStr, ${show(expect)}"
      }
    }

  private def mergeOneOfSeq[S](
      ooss: List[OneOfSeq[S]]
  )(implicit ordS: Ordering[S]): Option[OneOfSeq[S]] =
    if (ooss.isEmpty) None
    else {
      val ssb = SortedSet.newBuilder[S]
      ooss.foreach(ssb ++= _.seqs)
      Some(OneOfSeq(ooss.head.offset, ssb.result().toList))
    }

  @tailrec
  private def stripContext[S](ex: Expectation[S]): Expectation[S] =
    ex match {
      case WithContext(_, inner) => stripContext(inner)
      case _ => ex
    }

  @tailrec
  private def addContext[S](revCtx: List[String], ex: Expectation[S]): Expectation[S] =
    revCtx match {
      case Nil => ex
      case h :: tail => addContext(tail, WithContext(h, ex))
    }

  /** Sort, dedup and merge the errors accumulated. This is called just before finally returning an
    * error in Parser.parse. The alphabet supplies the merge of its own cases (char merges
    * overlapping ranges) and the literal ordering for OneOfSeq dedup.
    */
  def unify[S](
      errors: NonEmptyList[Expectation[S]]
  )(implicit alpha: Alphabet[S]): NonEmptyList[Expectation[S]] = {
    val result = errors
      .groupBy { ex => (ex.offset, ex.context) }
      .iterator
      .flatMap { case ((_, ctx), list) =>
        val am = ListBuffer.empty[OfAlphabet[S]]
        val om = ListBuffer.empty[OneOfSeq[S]]
        val fails = ListBuffer.empty[Fail[S]]
        val others = ListBuffer.empty[Expectation[S]]

        var items = list.toList
        while (items.nonEmpty) {
          stripContext(items.head) match {
            case oa: OfAlphabet[S] => am += oa
            case os: OneOfSeq[S] => om += os
            case fail: Fail[S] => fails += fail
            case other => others += other
          }
          items = items.tail
        }

        // merge the alphabet's own cases (e.g. char ranges):
        val alphaMerge = alpha.mergeOfAlphabet(am.toList)
        // merge the OneOfSeq
        val oossMerge = mergeOneOfSeq(om.toList)(alpha.orderingS)

        val errors = others.toList reverse_::: (oossMerge ++: alphaMerge)
        val finals = if (errors.isEmpty) fails.toList else errors
        if (ctx.nonEmpty) {
          val revCtx = ctx.reverse
          finals.map(addContext(revCtx, _))
        } else finals
      }
      .toList

    NonEmptyList.fromListUnsafe(
      result.distinct.sorted(catsOrderExpectation[S].toOrdering)
    )
  }
}

/** Represents where a failure occurred and all the expectations that were broken */
final class Error[S](
    val input: Option[S],
    val failedAtOffset: Int,
    val expected: NonEmptyList[Expectation[S]]
) extends Serializable {

  def this(failedAtOffset: Int, expected: NonEmptyList[Expectation[S]]) =
    this(None, failedAtOffset, expected)

  def offsets: NonEmptyList[Int] =
    expected.map(_.offset).distinct

  def copy(
      failedAtOffset: Int = this.failedAtOffset,
      expected: NonEmptyList[Expectation[S]] = this.expected
  ): Error[S] =
    new Error(failedAtOffset, expected)

  override def hashCode(): Int = {
    import scala.runtime.Statics
    var i = -889275714
    i = Statics.mix(i, "Error".hashCode())
    i = Statics.mix(i, Statics.anyHash(input))
    i = Statics.mix(i, failedAtOffset)
    i = Statics.mix(i, Statics.anyHash(expected))
    Statics.finalizeHash(i, 2)
  }

  override def toString(): String = s"Error($failedAtOffset, $expected)"

  override def equals(other: Any): Boolean =
    other match {
      case that: Error[_] =>
        that.input == input &&
        that.failedAtOffset == failedAtOffset &&
        that.expected == expected
      case _ => false
    }
}

object ErrorWithInput {
  def unapply[S](error: Error[S]): Option[(S, Int, NonEmptyList[Expectation[S]])] =
    error.input.map(input => (input, error.failedAtOffset, error.expected))
}

object Error {
  def apply[S](failedAtOffset: Int, expected: NonEmptyList[Expectation[S]]): Error[S] =
    new Error(None, failedAtOffset, expected)

  def apply[S](
      input: S,
      failedAtOffset: Int,
      expected: NonEmptyList[Expectation[S]]
  ): Error[S] =
    new Error(Some(input), failedAtOffset, expected)

  def unapply[S](error: Error[S]): Option[(Int, NonEmptyList[Expectation[S]])] =
    Some((error.failedAtOffset, error.expected))

  implicit def catsShowError[S](implicit
      showExp: Show[Expectation[S]],
      alpha: Alphabet[S]
  ): Show[Error[S]] =
    new Show[Error[S]] {
      def show(error: Error[S]): String = {
        val nl = "\n"

        def errorMsg = {
          val expectations =
            error.expected.toList.iterator.map(e => s"* ${showExp.show(e)}").mkString(nl)

          s"""|expectation${if (error.expected.tail.nonEmpty) "s" else ""}:
              |$expectations""".stripMargin
        }

        error.input match {
          case Some(input) =>
            alpha.renderContext(input, error.failedAtOffset, errorMsg).getOrElse(errorMsg)
          case None =>
            s"""|at offset ${error.failedAtOffset}
                |$errorMsg""".stripMargin
        }
      }
    }
}
