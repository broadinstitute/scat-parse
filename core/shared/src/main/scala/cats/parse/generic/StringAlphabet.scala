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
import cats.data.{Chain, NonEmptyList}
// cats.parse.Parser is spelled out: the import would be shadowed by generic.Parser on 2.12
import cats.parse.{BitSetUtil, LocationMap, RadixNode}

import java.util.Arrays
import scala.annotation.tailrec
import scala.collection.immutable.SortedSet
import scala.collection.mutable.ListBuffer

/** The `Char`/`String` [[Alphabet]] instance: the machinery cats-parse has always used, repackaged
  * behind the typeclass. `Slice = String`, so slice captures keep their exact historical type;
  * token sets are the bitset + contiguous-ranges representation of the char parsers; multi-literal
  * dispatch wraps `RadixNode`.
  */
object StringAlphabet extends Alphabet[String] {

  /** A set of chars: a bitset (offset by `min`) for the hot membership test, plus the contiguous
    * ranges covering exactly the members (used for error reporting and cold set algebra).
    */
  final class CharSet private[parse] (
      private[parse] val min: Int,
      private[parse] val bitSet: BitSetUtil.Tpe,
      private[parse] val ranges: NonEmptyList[(Char, Char)]
  ) extends Serializable {
    override def toString(): String = s"CharSet($ranges)"

    /* `ranges` is canonical -- minimal, disjoint, ascending, from `rangesFor` on sorted input -- so
     * it decides membership, and equality on it is set equality. This is load-bearing: parser nodes
     * are case classes over their TokenSet, and char's own equality laws (charIn(a) | charIn(b) ==
     * charIn(a | b), charWhere(_ => true) == anyChar) are structural. */
    override def equals(other: Any): Boolean =
      other match {
        case that: CharSet => (this eq that) || (ranges == that.ranges)
        case _ => false
      }

    override def hashCode(): Int = ranges.hashCode()
  }

  final case class InRange(offset: Int, lower: Char, upper: Char)
      extends Expectation.OfAlphabet[String]

  type Token = Char
  type TokenSet = CharSet
  type Slice = String

  /** Build the set of the given chars (which must be non-empty). */
  def charSet(cs: Iterable[Char]): CharSet = {
    require(cs.nonEmpty, "cannot build an empty CharSet")
    val ary = cs.toArray
    Arrays.sort(ary)
    new CharSet(ary(0).toInt, BitSetUtil.bitSetFor(ary), rangesFor(ary))
  }

  /** The minimal ascending contiguous ranges covering exactly the chars of `sorted`, which must be
    * sorted. This canonical form is what makes [[CharSet]] equality set equality.
    *
    * @return
    *   one `(lower, upper)` pair per contiguous run
    */
  private[parse] def rangesFor(sorted: Array[Char]): NonEmptyList[(Char, Char)] = {
    def rangesFrom(start: Char, end: Char, idx: Int): NonEmptyList[(Char, Char)] =
      if (idx >= sorted.length || (idx < 0)) NonEmptyList((start, end), Nil)
      else {
        val end1 = sorted(idx)
        if ((end1.toInt == end.toInt + 1) || (end1 == end)) rangesFrom(start, end1, idx + 1)
        else {
          // we had a break:
          (start, end) :: rangesFrom(end1, end1, idx + 1)
        }
      }

    rangesFrom(sorted(0), sorted(0), 1)
  }

  //////////////////////////////////////////////////////////////////////
  // Hot core
  //////////////////////////////////////////////////////////////////////

  def length(s: String): Int = s.length

  def matchesAt(set: CharSet, s: String, i: Int): Boolean =
    (i < s.length) && {
      val cInt = s.charAt(i).toInt
      BitSetUtil.isSet(set.bitSet, cInt - set.min)
    }

  def scanWhile(set: CharSet, s: String, from: Int): Int = {
    val len = s.length
    val bitSet = set.bitSet
    val min = set.min
    var i = from
    while ((i < len) && BitSetUtil.isSet(bitSet, s.charAt(i).toInt - min)) {
      i += 1
    }
    i
  }

  def startsWithAt(s: String, offset: Int, lit: String): Boolean =
    s.regionMatches(offset, lit, 0, lit.length)

  def slice(s: String, from: Int, until: Int): String =
    s.substring(from, until)

  def sliceLength(sl: String): Int = sl.length

  //////////////////////////////////////////////////////////////////////
  // Cold error section
  //////////////////////////////////////////////////////////////////////

  def expectSet(offset: Int, set: CharSet): NonEmptyList[Expectation[String]] =
    set.ranges.map { case (lo, hi) => InRange(offset, lo, hi) }

  def mergeOfAlphabet(
      cases: List[Expectation.OfAlphabet[String]]
  ): List[Expectation.OfAlphabet[String]] = {
    val irs = ListBuffer.empty[InRange]
    val others = ListBuffer.empty[Expectation.OfAlphabet[String]]
    cases.foreach {
      case ir: InRange => irs += ir
      case other => others += other
    }
    mergeInRange(irs.toList) ::: others.toList
  }

  val orderingS: Ordering[String] = Ordering.String

  val orderOfAlphabet: Order[Expectation.OfAlphabet[String]] =
    new Order[Expectation.OfAlphabet[String]] {
      def compare(
          left: Expectation.OfAlphabet[String],
          right: Expectation.OfAlphabet[String]
      ): Int =
        (left, right) match {
          case (InRange(_, l1, u1), InRange(_, l2, u2)) =>
            val c1 = Character.compare(l1, l2)
            if (c1 == 0) Character.compare(u1, u2)
            else c1
          case (_: InRange, _) => -1
          case (_, _: InRange) => 1
          // foreign cases: keep the order total (see Alphabet.orderOfAlphabet)
          case (l, r) => l.toString.compareTo(r.toString)
        }
    }

  val showOfAlphabet: Show[Expectation.OfAlphabet[String]] =
    Show.show {
      case InRange(_, lower, upper) =>
        if (lower != upper) s"must be a char within the range of: ['$lower', '$upper']"
        else s"must be char: '$lower'"
      case other => other.toString
    }

  def showLiteral(s: String): String = "\"" + s + "\""

  override def renderContext(input: String, offset: Int, errorMsg: String): Option[String] = {
    val nl = "\n"
    val locationMap = new LocationMap(input)

    locationMap.toCaret(offset) match {
      case None => None
      case Some(caret) =>
        val lines = locationMap.lines

        val contextSize = 2

        val start = caret.line - contextSize
        val end = caret.line + 1 + contextSize

        val elipsis = "..."

        val beforeElipsis =
          if (start <= 0) None
          else Some(elipsis)

        val beforeContext =
          Some(lines.slice(start, caret.line).mkString(nl)).filter(_.nonEmpty)

        val line = lines(caret.line)

        val afterContext: Option[String] =
          Some(lines.slice(caret.line + 1, end).mkString(nl)).filter(_.nonEmpty)

        val afterElipsis: Option[String] =
          if (end >= lines.length - 1) None
          else Some(elipsis)

        Some(
          List(
            beforeElipsis,
            beforeContext,
            Some(line),
            Some((1 to caret.col).map(_ => " ").mkString("") + "^"),
            Some(errorMsg),
            afterContext,
            afterElipsis
          ).flatten.mkString(nl)
        )
    }
  }

  def tokenAt(s: String, i: Int): Char = s.charAt(i)

  def subInput(s: String, from: Int, until: Int): String = s.substring(from, until)

  //////////////////////////////////////////////////////////////////////
  // Cold optimizer section
  //////////////////////////////////////////////////////////////////////

  def union(a: CharSet, b: CharSet): CharSet =
    charSet(BitSetUtil.union((a.min, a.bitSet) :: (b.min, b.bitSet) :: Nil))

  val universal: CharSet =
    new CharSet(
      0,
      BitSetUtil.bitSetForRange(Char.MaxValue.toInt + 1),
      NonEmptyList.one((Char.MinValue, Char.MaxValue))
    )

  def contains(set: CharSet, t: Char): Boolean =
    BitSetUtil.isSet(set.bitSet, t.toInt - set.min)

  def pattern(lit: String): List[CharSet] =
    lit.toList.map(c => charSet(c :: Nil))

  def setWhere(p: Char => Boolean): Option[CharSet] = {
    val cs = p match {
      // Set extends Char => Boolean, and enumerating it beats sweeping the domain (as charWhere does)
      case s: Set[_] => s.asInstanceOf[Set[Char]].toSeq
      case _ => allChars.filter(p)
    }
    if (cs.isEmpty) None else Some(charSet(cs))
  }

  def subsetOf(a: CharSet, b: CharSet): Boolean =
    a.ranges.forall { case (lo, hi) =>
      (lo to hi).forall(c => BitSetUtil.isSet(b.bitSet, c.toInt - b.min))
    }

  def intersects(a: CharSet, b: CharSet): Boolean =
    a.ranges.exists { case (lo, hi) =>
      (lo to hi).exists(c => BitSetUtil.isSet(b.bitSet, c.toInt - b.min))
    }

  def literalsOf(set: CharSet): List[String] =
    set.ranges.toList.flatMap { case (lo, hi) => (lo to hi).map(_.toString) }

  override def singletonLiteralOf(set: CharSet): Option[String] =
    if (BitSetUtil.isSingleton(set.bitSet)) Some(set.min.toChar.toString) else None

  override def seqMatcher(alts: SortedSet[String]): SeqMatcher[String, String] = {
    require(alts.nonEmpty && !alts.exists(_.isEmpty), "seqMatcher requires non-empty literals")
    val radix = RadixNode.fromSortedStrings(NonEmptyList.fromListUnsafe(alts.toList))
    new SeqMatcher[String, String](StringAlphabet) {
      def matchAt(input: String, offset: Int): Int =
        // the bound here and then the loop directly, rather than radix.matchAt (which re-checks the
        // same bound one frame further in): the frames between the parser leaf and the loop are
        // what decide whether the whole match stays inside the JIT's inline budget, and it does not
        // survive the two that radix.matchAt costs. `offset >= 0` is SeqMatcher's precondition.
        if (offset > input.length) -1
        else {
          val matched = radix.matchAtOrNullLoop(input, offset)
          if (matched eq null) -1 else offset + matched.length
        }

      // the literal *is* the matched region here, so the capture costs nothing beyond the match:
      // char's `pattern` is all singleton sets, so matching is by equality and every char of the
      // winning alternative equals the input char it matched. The default would substring instead.
      // Under a non-injective alphabet the two differ, which is why this is the instance's to say.
      override def sliceAt(input: String, offset: Int): String =
        if (offset > input.length) null else radix.matchAtOrNullLoop(input, offset)
    }
  }

  /** The whole token domain, hoisted the way char's `Impl.allChars` is: `setWhere` sweeps it. */
  private val allChars: IndexedSeq[Char] = Char.MinValue to Char.MaxValue

  private def mergeInRange(irs: List[InRange]): List[InRange] = {
    @tailrec
    def merge(rs: List[InRange], aux: Chain[InRange] = Chain.empty): Chain[InRange] =
      rs match {
        case x :: y :: rest =>
          if (y.lower.toInt > x.upper.toInt + 1) merge(y :: rest, aux :+ x)
          else merge(InRange(x.offset, x.lower, x.upper.max(y.upper)) :: rest, aux)
        case _ =>
          aux ++ Chain.fromSeq(rs.reverse)
      }
    merge(irs.sortBy(_.lower)).toList
  }
}
