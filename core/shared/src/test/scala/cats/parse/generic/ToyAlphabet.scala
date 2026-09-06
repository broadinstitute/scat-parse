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

import java.util.Arrays

/** A wrapped byte array: the input type of [[ToyAlphabet]] and a deliberately non-`String` `Slice`.
  * Construction canonicalizes every byte to the 4-bit token domain (`b & 0xf`), so a `ByteSeq`
  * never holds a value token equality and set membership could disagree on.
  */
final class ByteSeq private[generic] (val bytes: Array[Byte]) {
  override def equals(other: Any): Boolean =
    other match {
      case that: ByteSeq => Arrays.equals(bytes, that.bytes)
      case _ => false
    }

  override def hashCode(): Int = Arrays.hashCode(bytes)

  override def toString(): String = bytes.mkString("ByteSeq(", ",", ")")
}

object ByteSeq {
  def apply(bs: Int*): ByteSeq = fromBytes(bs.iterator.map(_.toByte).toArray)

  def fromBytes(bytes: Array[Byte]): ByteSeq =
    new ByteSeq(bytes.map(b => (b & 0xf).toByte))

  implicit val byteSeqOrdering: Ordering[ByteSeq] =
    new Ordering[ByteSeq] {
      def compare(x: ByteSeq, y: ByteSeq): Int = {
        val xs = x.bytes
        val ys = y.bytes
        val len = java.lang.Math.min(xs.length, ys.length)
        var i = 0
        while (i < len) {
          val c = java.lang.Byte.compare(xs(i), ys(i))
          if (c != 0) return c
          i += 1
        }
        Integer.compare(xs.length, ys.length)
      }
    }
}

/** A deliberately non-char, non-injective [[Alphabet]]: tokens are 4-bit masks over 4 base tokens
  * (bits 0-3), a `TokenSet` is a 16-bit mask over the 16 possible token values, and a literal token
  * `p` accepts any input token `i` with `(i | p) == p` — one input token can satisfy many literal
  * tokens. It exists to keep the abstraction honest: anything char-shaped that leaks into the
  * generic machinery fails here.
  */
class ToyAlphabet extends Alphabet[ByteSeq] {
  import ToyAlphabet.ExpectedMask

  type Token = Byte
  type TokenSet = Int // 16-bit mask: bit i set iff token value i is a member
  type Slice = ByteSeq

  //////////////////////////////////////////////////////////////////////
  // Hot core
  //////////////////////////////////////////////////////////////////////

  def length(s: ByteSeq): Int = s.bytes.length

  def matchesAt(set: Int, s: ByteSeq, i: Int): Boolean =
    (i < s.bytes.length) && (((set >> (s.bytes(i) & 0xf)) & 1) != 0)

  def scanWhile(set: Int, s: ByteSeq, from: Int): Int = {
    val bytes = s.bytes
    var i = from
    while ((i < bytes.length) && (((set >> (bytes(i) & 0xf)) & 1) != 0)) {
      i += 1
    }
    i
  }

  def startsWithAt(s: ByteSeq, offset: Int, lit: ByteSeq): Boolean =
    (offset >= 0) && ((offset + lit.bytes.length) <= s.bytes.length) && {
      var i = 0
      while ((i < lit.bytes.length) && (s.bytes(offset + i) == lit.bytes(i))) {
        i += 1
      }
      i == lit.bytes.length
    }

  def slice(s: ByteSeq, from: Int, until: Int): ByteSeq =
    new ByteSeq(Arrays.copyOfRange(s.bytes, from, until))

  //////////////////////////////////////////////////////////////////////
  // Cold error section
  //////////////////////////////////////////////////////////////////////

  def expectSet(offset: Int, set: Int): NonEmptyList[Expectation[ByteSeq]] =
    NonEmptyList.one(ExpectedMask(offset, set))

  def mergeOfAlphabet(
      cases: List[Expectation.OfAlphabet[ByteSeq]]
  ): List[Expectation.OfAlphabet[ByteSeq]] = {
    val masks = cases.collect { case em: ExpectedMask => em }
    val others = cases.filterNot(_.isInstanceOf[ExpectedMask])
    masks match {
      case Nil => others
      case head :: tail =>
        ExpectedMask(head.offset, tail.foldLeft(head.mask)(_ | _.mask)) :: others
    }
  }

  val orderingS: Ordering[ByteSeq] = ByteSeq.byteSeqOrdering

  val orderOfAlphabet: Order[Expectation.OfAlphabet[ByteSeq]] =
    new Order[Expectation.OfAlphabet[ByteSeq]] {
      def compare(
          left: Expectation.OfAlphabet[ByteSeq],
          right: Expectation.OfAlphabet[ByteSeq]
      ): Int =
        (left, right) match {
          case (ExpectedMask(_, m1), ExpectedMask(_, m2)) => Integer.compare(m1, m2)
          case (ExpectedMask(_, _), _) => -1
          case (_, ExpectedMask(_, _)) => 1
          // foreign cases: keep the order total (see Alphabet.orderOfAlphabet)
          case (l, r) => l.toString.compareTo(r.toString)
        }
    }

  val showOfAlphabet: Show[Expectation.OfAlphabet[ByteSeq]] =
    Show.show {
      case ExpectedMask(_, mask) => s"must match a token in mask 0x${mask.toHexString}"
      case other => other.toString
    }

  def showLiteral(s: ByteSeq): String =
    s.bytes.iterator.map(b => (b & 0xf).toHexString).mkString("0x[", " ", "]")

  def tokenAt(s: ByteSeq, i: Int): Byte = s.bytes(i)

  //////////////////////////////////////////////////////////////////////
  // Cold optimizer section
  //////////////////////////////////////////////////////////////////////

  def union(a: Int, b: Int): Int = a | b

  val universal: Int = 0xffff

  def contains(set: Int, t: Byte): Boolean = ((set >> (t & 0xf)) & 1) != 0

  def pattern(lit: ByteSeq): List[Int] =
    lit.bytes.toList.map { p =>
      var mask = 0
      var i = 0
      while (i < 16) {
        if ((i | (p & 0xf)) == (p & 0xf)) mask |= (1 << i)
        i += 1
      }
      mask
    }

  def setWhere(p: Byte => Boolean): Option[Int] = {
    var mask = 0
    var i = 0
    while (i < 16) {
      if (p(i.toByte)) mask |= (1 << i)
      i += 1
    }
    if (mask == 0) None else Some(mask)
  }

  def subsetOf(a: Int, b: Int): Boolean = (a & ~b & 0xffff) == 0

  def intersects(a: Int, b: Int): Boolean = (a & b) != 0

  def literalsOf(set: Int): List[ByteSeq] =
    (0 until 16).iterator
      .filter(i => ((set >> i) & 1) != 0)
      .map(i => ByteSeq(i))
      .toList
}

object ToyAlphabet extends ToyAlphabet {
  final case class ExpectedMask(offset: Int, mask: Int) extends Expectation.OfAlphabet[ByteSeq]
}

/** [[ToyAlphabet]] with its two hot-path entry points counted, so a test can hold the bulk-scan
  * rule honest: a scan of a run must cost one `scanWhile` call and no per-token `matchesAt` calls.
  */
final class CountingToyAlphabet extends ToyAlphabet {
  var scans: Int = 0
  var probes: Int = 0

  override def scanWhile(set: Int, s: ByteSeq, from: Int): Int = {
    scans += 1
    super.scanWhile(set, s, from)
  }

  override def matchesAt(set: Int, s: ByteSeq, i: Int): Boolean = {
    probes += 1
    super.matchesAt(set, s, i)
  }
}
