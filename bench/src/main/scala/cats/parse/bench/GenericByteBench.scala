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

package cats.parse.bench

import cats.data.NonEmptyList
import cats.parse.generic.{Alphabet, Expectation, Parser, Parser0}
import cats.{Order, Show}

import java.util.Arrays
import java.util.concurrent.TimeUnit
import org.openjdk.jmh.annotations._

/** A byte sequence over a 4-bit token domain: the input type of [[ByteAlphabet]].
  *
  * Unlike the test-scope `ByteSeq` this does not canonicalize its bytes to `b & 0xf` on
  * construction -- slicing is on the measured path here, and a copy-and-mask there would be
  * measuring the wrong thing. So it is the caller's job to build only canonical tokens (0-15):
  * outside that range `startsWithAt`, which compares raw bytes, disagrees with the masking
  * `matchesAt`. The benchmark inputs below are tokens 0, 1, 2, 4 and 8.
  */
final class Bytes(val bytes: Array[Byte])

/** A non-char alphabet on the generic path, to pin the byte-at-a-time v1 numbers. Tokens are 4-bit
  * masks, a `TokenSet` is a 16-bit mask over the token values, and a literal token `p` accepts any
  * input token `i` with `(i | p) == p`.
  *
  * This duplicates ~50 lines of the test-scope `ToyAlphabet` (bench cannot see test scope). Drift
  * is harmless: the tests check semantics, this checks the performance shape.
  */
object ByteAlphabet extends Alphabet[Bytes] {
  type Token = Byte
  type TokenSet = Int
  type Slice = Bytes

  // hot core
  def length(s: Bytes): Int = s.bytes.length
  def matchesAt(set: Int, s: Bytes, i: Int): Boolean =
    (i < s.bytes.length) && (((set >> (s.bytes(i) & 0xf)) & 1) != 0)
  def scanWhile(set: Int, s: Bytes, from: Int): Int = {
    val bytes = s.bytes
    var i = from
    while ((i < bytes.length) && (((set >> (bytes(i) & 0xf)) & 1) != 0)) i += 1
    i
  }
  def startsWithAt(s: Bytes, offset: Int, lit: Bytes): Boolean =
    (offset >= 0) && ((offset + lit.bytes.length) <= s.bytes.length) && {
      var i = 0
      while ((i < lit.bytes.length) && (s.bytes(offset + i) == lit.bytes(i))) i += 1
      i == lit.bytes.length
    }
  def slice(s: Bytes, from: Int, until: Int): Bytes =
    new Bytes(Arrays.copyOfRange(s.bytes, from, until))

  // cold error section
  final case class ExpectedMask(offset: Int, mask: Int) extends Expectation.OfAlphabet[Bytes]
  def expectSet(offset: Int, set: Int): NonEmptyList[Expectation[Bytes]] =
    NonEmptyList.one(ExpectedMask(offset, set))
  def mergeOfAlphabet(
      cases: List[Expectation.OfAlphabet[Bytes]]
  ): List[Expectation.OfAlphabet[Bytes]] = cases
  val orderingS: Ordering[Bytes] = Ordering.by(_.bytes.mkString(","))
  val orderOfAlphabet: Order[Expectation.OfAlphabet[Bytes]] = Order.by(_.toString)
  val showOfAlphabet: Show[Expectation.OfAlphabet[Bytes]] = Show.fromToString
  def showLiteral(s: Bytes): String = s.bytes.mkString("[", " ", "]")
  def tokenAt(s: Bytes, i: Int): Byte = s.bytes(i)
  def subInput(s: Bytes, from: Int, until: Int): Bytes = slice(s, from, until)

  // cold optimizer section
  def union(a: Int, b: Int): Int = a | b
  val universal: Int = 0xffff
  def contains(set: Int, t: Byte): Boolean = ((set >> (t & 0xf)) & 1) != 0
  def pattern(lit: Bytes): List[Int] =
    lit.bytes.toList.map { p => maskWhere(i => (i | (p & 0xf)) == (p & 0xf)) }
  def setWhere(p: Byte => Boolean): Option[Int] =
    maskWhere(i => p(i.toByte)) match {
      case 0 => None
      case m => Some(m)
    }
  def subsetOf(a: Int, b: Int): Boolean = (a & ~b & 0xffff) == 0
  def intersects(a: Int, b: Int): Boolean = (a & b) != 0
  def literalsOf(set: Int): List[Bytes] =
    (0 until 16).iterator
      .filter(i => ((set >> i) & 1) != 0)
      .map(i => new Bytes(Array(i.toByte)))
      .toList

  private def maskWhere(p: Int => Boolean): Int = {
    var mask = 0
    var i = 0
    while (i < 16) {
      if (p(i)) mask |= (1 << i)
      i += 1
    }
    mask
  }
}

/** The v1 byte-at-a-time baseline for the generic path: the same engine the char facade runs on,
  * driven over [[ByteAlphabet]].
  */
@State(Scope.Benchmark)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MICROSECONDS)
class GenericByteBenchmarks {
  private implicit val alpha: ByteAlphabet.type = ByteAlphabet

  /** Tokens 1, 2, 4 and 8 -- the unambiguous "bases". */
  private val bases: Int = (1 << 1) | (1 << 2) | (1 << 4) | (1 << 8)

  /** Token 0, the run separator: a submask of every base, so no base set holds it. */
  private val gap: Int = 1 << 0

  /** 16k tokens of bases, with a gap every 64 (never last): the runs input. */
  var gapped: Bytes = _

  /** 16k tokens of bases, no gaps: the single-scan and per-token input. */
  var contiguous: Bytes = _

  /** One bulk scan: `scanWhile` over the whole input. */
  val scan: Parser[Bytes, Bytes] = Parser.tokensIn(ByteAlphabet)(bases)

  /** Runs of bases separated by single gap tokens, captured as slices. */
  val runs: Parser0[Bytes, List[Bytes]] = scan.repSep0(Parser.tokenIn(ByteAlphabet)(gap))

  /** The byte-at-a-time shape: one `matchesAt` per token, one boxed `Token` per token. */
  val perToken: Parser0[Bytes, List[Byte]] = Parser.tokenIn(ByteAlphabet)(bases).rep0

  @Setup(Level.Trial)
  def setup(): Unit = {
    val baseTokens = Array[Byte](1, 2, 4, 8)
    val size = 16384
    val gaps = new Array[Byte](size)
    val contig = new Array[Byte](size)
    var i = 0
    while (i < size) {
      val t = baseTokens(i % 4)
      contig(i) = t
      gaps(i) = if ((i > 0) && ((i % 64) == 0)) 0 else t
      i += 1
    }
    gapped = new Bytes(gaps)
    contiguous = new Bytes(contig)
  }

  @Benchmark
  def scanParse(): Int =
    scan.parseAll(contiguous) match {
      case Right(slice) => slice.bytes.length
      case Left(e) => sys.error(e.toString)
    }

  @Benchmark
  def runsParse(): Int =
    runs.parseAll(gapped) match {
      case Right(rs) => rs.length
      case Left(e) => sys.error(e.toString)
    }

  @Benchmark
  def perTokenParse(): Int =
    perToken.parseAll(contiguous) match {
      case Right(ts) => ts.length
      case Left(e) => sys.error(e.toString)
    }
}
