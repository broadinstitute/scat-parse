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

package cats.parse

import cats.{Align, Alternative, Defer, FlatMap, FunctorFilter, Monad, MonoidK, Order, Show}
import cats.data.NonEmptyList
import cats.parse.generic.StringAlphabet

/** The char facade over the generic parser engine.
  *
  * `Parser0[A]`/`Parser[A]` are aliases (see the `cats.parse` package object) for the generic
  * parsers at [[cats.parse.generic.StringAlphabet]]; everything here forwards to
  * [[cats.parse.generic.Parser]] with that alphabet supplied. The char-only residue — `ignoreCase`,
  * `caret`, and the character-level spellings of the generic primitives — lives here and nowhere
  * else.
  */
object Parser {

  //////////////////////////////////////////////////////////////////////
  // Errors: char aliases over the generic hierarchy, plus companion values so that existing
  // constructor calls and pattern matches read exactly as they did.
  //////////////////////////////////////////////////////////////////////

  /** An expectation reports the kind of parsing error and where it occurred. */
  type Expectation = generic.Expectation[String]

  object Expectation {
    type OneOfStr = generic.Expectation.OneOfSeq[String]
    val OneOfStr: generic.Expectation.OneOfSeq.type = generic.Expectation.OneOfSeq

    /** expected a character in a given range */
    type InRange = StringAlphabet.InRange
    val InRange: StringAlphabet.InRange.type = StringAlphabet.InRange

    type StartOfString = generic.Expectation.StartOfString[String]
    val StartOfString: generic.Expectation.StartOfString.type = generic.Expectation.StartOfString

    type EndOfString = generic.Expectation.EndOfString[String]
    val EndOfString: generic.Expectation.EndOfString.type = generic.Expectation.EndOfString

    type Length = generic.Expectation.Length[String]
    val Length: generic.Expectation.Length.type = generic.Expectation.Length

    type ExpectedFailureAt = generic.Expectation.ExpectedFailureAt[String]
    val ExpectedFailureAt: generic.Expectation.ExpectedFailureAt.type =
      generic.Expectation.ExpectedFailureAt

    /** this is the result of oneOf0(Nil) at a given location */
    type Fail = generic.Expectation.Fail[String]
    val Fail: generic.Expectation.Fail.type = generic.Expectation.Fail

    type FailWith = generic.Expectation.FailWith[String]
    val FailWith: generic.Expectation.FailWith.type = generic.Expectation.FailWith

    type WithContext = generic.Expectation.WithContext[String]
    val WithContext: generic.Expectation.WithContext.type = generic.Expectation.WithContext

    implicit val catsOrderExpectation: Order[Expectation] =
      generic.Expectation.catsOrderExpectation[String]

    implicit val catsShowExpectation: Show[Expectation] =
      generic.Expectation.catsShowExpectation[String]

    /** Sort, dedup and unify ranges for the errors accumulated. This is called just before finally
      * returning an error in Parser.parse
      */
    def unify(errors: NonEmptyList[Expectation]): NonEmptyList[Expectation] =
      generic.Expectation.unify[String](errors)
  }

  /** Represents where a failure occurred and all the expectations that were broken */
  type Error = generic.Error[String]

  object Error {
    def apply(failedAtOffset: Int, expected: NonEmptyList[Expectation]): Error =
      generic.Error(failedAtOffset, expected)

    def apply(input: String, failedAtOffset: Int, expected: NonEmptyList[Expectation]): Error =
      generic.Error(input, failedAtOffset, expected)

    def unapply(error: Error): Option[(Int, NonEmptyList[Expectation])] =
      generic.Error.unapply(error)

    implicit def catsShowErrorGivenExpectation(implicit showExp: Show[Expectation]): Show[Error] =
      generic.Error.catsShowError[String](showExp, StringAlphabet)

    val catsShowError: Show[Error] =
      catsShowErrorGivenExpectation(Expectation.catsShowExpectation)
  }

  object ErrorWithInput {
    def unapply(error: Error): Option[(String, Int, NonEmptyList[Expectation])] =
      generic.ErrorWithInput.unapply(error)
  }

  //////////////////////////////////////////////////////////////////////
  // Syntax helpers
  //////////////////////////////////////////////////////////////////////

  /** Enables syntax to access product01, product and flatMap01. This helps us build Parser
    * instances when starting from a Parser0
    */
  type With1[+A] = generic.Parser.With1[String, A]

  /** If we can parse this then that, do so; if we fail that without consuming, rewind before this
    * without consuming. If either consume 1 or more, do not rewind
    */
  type Soft0[+A] = generic.Parser.Soft0[String, A]

  /** the [[Soft0]] with the left-hand parser known to consume input */
  type Soft[+A] = generic.Parser.Soft[String, A]

  /** the [[Soft0]] with the right-hand parser known to consume input */
  type Soft01[+A] = generic.Parser.Soft01[String, A]

  /** char's `.string`/`.withString`, the only two combinators whose char spelling differs from the
    * generic one (`.slice`/`.withSlice`, which are `Slice`-typed in general and `String`-typed
    * here). Reached through implicit conversions declared in `generic.Parser0`'s companion, so no
    * import is needed at a char call site.
    */
  final class StringSyntax0[+A](private val parser: generic.Parser0[String, A]) extends AnyVal {

    /** Return the string matched by this parser.
      *
      * When parsing an input string that the underlying parser matches, this parser will return the
      * matched substring instead of any value that the underlying parser would have returned. It
      * will still match exactly the same inputs as the original parser.
      */
    def string: Parser0[String] = generic.Parser.slice0(StringAlphabet)(parser)

    /** Return the value and the input string matched */
    def withString: Parser0[(A, String)] = generic.Parser.withSlice0(StringAlphabet)(parser)
  }

  /** the [[StringSyntax0]] refined for a parser known to consume input */
  final class StringSyntax[+A](private val parser: generic.Parser[String, A]) extends AnyVal {
    def string: Parser[String] = generic.Parser.slice(StringAlphabet)(parser)

    def withString: Parser[(A, String)] = generic.Parser.withSlice(StringAlphabet)(parser)
  }

  //////////////////////////////////////////////////////////////////////
  // Char primitives
  //////////////////////////////////////////////////////////////////////

  /** Don't advance in the parsed string, just return a. This is used by the Applicative typeclass.
    */
  def pure[A](a: A): Parser0[A] =
    generic.Parser.pure(a)

  /** A parser that returns unit */
  val unit: Parser0[Unit] = generic.Parser.unit[String]

  /** A parser that always fails with an epsilon failure */
  val Fail: Parser[Nothing] = generic.Parser.fail[String, Nothing]

  /** A parser that always fails with an epsilon failure */
  def fail[A]: Parser[A] = Fail.asInstanceOf[Parser[A]]

  /** A parser that always fails with an epsilon failure and a given message. This is generally used
    * with flatMap to validate a result beyond the literal parsing.
    *
    * e.g. parsing a number then validate that it is bounded.
    */
  def failWith[A](message: String): Parser[A] =
    generic.Parser.failWith(message)

  private[this] val anyCharP: Parser[Char] = generic.Parser.anyToken(StringAlphabet)

  /** Parse 1 character from the string */
  def anyChar: Parser[Char] = anyCharP

  /** An empty iterable is the same as fail */
  def charIn(cs: Iterable[Char]): Parser[Char] =
    if (cs.isEmpty) fail
    else generic.Parser.tokenIn(StringAlphabet)(StringAlphabet.charSet(cs))

  /** parse one of a given set of characters */
  def charIn(c0: Char, cs: Char*): Parser[Char] =
    charIn(c0 +: cs)

  /** Parse any single character in a set of characters as lower or upper case */
  def ignoreCaseCharIn(cs: Iterable[Char]): Parser[Char] =
    charIn(cs.flatMap { c => c.toUpper :: c.toLower :: Nil })

  /** Parse any single character in a set of characters as lower or upper case */
  def ignoreCaseCharIn(c0: Char, cs: Char*): Parser[Char] =
    ignoreCaseCharIn(c0 +: cs)

  // Cache the common parsers to reduce allocations
  private[this] val charArray: Array[Parser[Unit]] =
    (32 to 126).map { idx => charIn(idx.toChar :: Nil).void }.toArray

  /** parse a single character */
  def char(c: Char): Parser[Unit] = {
    val cidx = c.toInt - 32
    if ((cidx >= 0) && (cidx < charArray.length)) charArray(cidx)
    else charIn(c :: Nil).void
  }

  /** parse one character that matches a given function */
  def charWhere(fn: Char => Boolean): Parser[Char] =
    generic.Parser.tokenWhere(StringAlphabet)(fn)

  /** Parse a string while the given function is true. Parses at least one character */
  def charsWhile(fn: Char => Boolean): Parser[String] =
    generic.Parser.tokensWhile(StringAlphabet)(fn)

  /** Parse a string while the given function is true */
  def charsWhile0(fn: Char => Boolean): Parser0[String] =
    generic.Parser.tokensWhile0(StringAlphabet)(fn)

  /** Parse a given string or fail. This backtracks on failure. This is an error if the string is
    * empty
    */
  def string(str: String): Parser[Unit] =
    // a one-character literal stays a char parser: `charIn` is cheaper than a literal match, and
    // its `InRange` expectation is what char's error messages have always shown for it
    if (str.length == 1) char(str.charAt(0))
    else generic.Parser.seq(str)(StringAlphabet)

  /** Parse a potentially empty string or fail. This backtracks on failure */
  def string0(str: String): Parser0[Unit] =
    if (str.isEmpty) unit
    else string(str)

  /** Parse a given string, in a case-insensitive manner, or fail. This backtracks on failure. This
    * is an error if the string is empty
    */
  def ignoreCase(str: String): Parser[Unit] =
    if (str.length == 1) ignoreCaseChar(str.charAt(0))
    else generic.Parser.Impl.IgnoreCase(str.toLowerCase)

  /** Ignore the case of a single character. If you want to know if it is upper or lower, use
    * .string to capture the string and then map to process the result.
    */
  def ignoreCaseChar(c: Char): Parser[Unit] =
    charIn(c.toLower, c.toUpper).void

  /** Parse a potentially empty string, in a case-insensitive manner, or fail. This backtracks on
    * failure
    */
  def ignoreCase0(str: String): Parser0[Unit] =
    if (str.isEmpty) unit
    else ignoreCase(str)

  /** Parse the longest matching string between alternatives. The order of the strings does not
    * matter.
    *
    * If no string matches, this parser results in an epsilon failure.
    *
    * It is an error to pass the empty string here, if you need that see stringIn0
    */
  def stringIn(strings: Iterable[String]): Parser[String] =
    strings.toList.distinct match {
      case Nil => fail
      // route the single case back through this facade's `string`, so that a one-character
      // alternative captures the way `char(c).string` does rather than as a literal
      case s :: Nil => string(s).string
      case two => generic.Parser.seqIn(two)(StringAlphabet)
    }

  /** Version of stringIn that allows the empty string */
  def stringIn0(strings: Iterable[String]): Parser0[String] =
    if (strings.exists(_.isEmpty)) stringIn(strings.filter(_.nonEmpty)).orElse(emptyStringParser0)
    else stringIn(strings)

  private[this] val emptyStringParser0: Parser0[String] = pure("")

  /** Convert a Map[Char, A] to Parser[A]: first match a character, then map it to a value A */
  def fromCharMap[A](charMap: Map[Char, A]): Parser[A] =
    charIn(charMap.keySet).map(charMap)

  /** Convert a Map[String, A] to Parser[A]: first match a string, then map it to a value A. This
    * throws if any of the keys are the empty string
    */
  def fromStringMap[A](stringMap: Map[String, A]): Parser[A] =
    stringIn(stringMap.keySet).map(stringMap)

  /** Convert a Map[String, A] to Parser0[A]: first match a string, then map it to a value A */
  def fromStringMap0[A](stringMap: Map[String, A]): Parser0[A] =
    stringIn0(stringMap.keySet).map(stringMap)

  /** if len < 1, the same as pure("") else length(len) */
  def length0(len: Int): Parser0[String] =
    if (len > 0) length(len) else emptyStringParser0

  /** Parse the next len characters where len > 0. If (len < 1) throw IllegalArgumentException */
  def length(len: Int): Parser[String] =
    generic.Parser.length(len)(StringAlphabet)

  private[this] val indexP: Parser0[Int] = generic.Parser.index[String]

  /** return the current position in the string we are parsing. This lets you record position
    * information in your ASTs you are parsing
    */
  def index: Parser0[Int] = indexP

  private[this] val caretP: Parser0[Caret] = generic.Parser.Impl.GetCaret()

  /** return the current Caret (offset, line, column). This is a bit more expensive than just the
    * index
    */
  def caret: Parser0[Caret] = caretP

  private[this] val startP: Parser0[Unit] = generic.Parser.start[String]

  /** succeeds when we are at the start */
  def start: Parser0[Unit] = startP

  private[this] val endP: Parser0[Unit] = generic.Parser.end(StringAlphabet)

  /** succeeds when we are at the end */
  def end: Parser0[Unit] = endP

  //////////////////////////////////////////////////////////////////////
  // Combinators
  //////////////////////////////////////////////////////////////////////

  /** go through the list of parsers trying each as long as they are epsilon failures (don't
    * advance). See @backtrack if you want to do backtracking.
    *
    * This is the same as parsers.foldLeft(fail)(_.orElse(_))
    *
    * recommended style: oneOf(p1 :: p2 :: p3 :: Nil) rather than oneOf(List(p1, p2, p3))
    *
    * Note: order matters here, since we don't backtrack by default.
    */
  def oneOf[A](parsers: List[Parser[A]]): Parser[A] =
    generic.Parser.oneOf(parsers)

  /** the [[oneOf]] whose alternatives may consume no input */
  def oneOf0[A](ps: List[Parser0[A]]): Parser0[A] =
    generic.Parser.oneOf0(ps)

  /** If the first parser fails to parse its input with an epsilon error, try the second parser
    * instead.
    */
  def eitherOr0[A, B](first: Parser0[B], second: Parser0[A]): Parser0[Either[A, B]] =
    generic.Parser.eitherOr0(first, second)

  /** the [[eitherOr0]] when both sides are known to consume input */
  def eitherOr[A, B](first: Parser[B], second: Parser[A]): Parser[Either[A, B]] =
    generic.Parser.eitherOr(first, second)

  /** Repeat the parser 0 or more times
    *
    * @note
    *   this can wind up parsing nothing
    */
  def repAs0[A, B](p1: Parser[A])(implicit acc: Accumulator0[A, B]): Parser0[B] =
    generic.Parser.repAs0(p1)(acc)

  /** Repeat the parser 0 or more times, but no more than `max`
    *
    * @throws java.lang.IllegalArgumentException
    *   if max < 0
    */
  def repAs0[A, B](p1: Parser[A], max: Int)(implicit acc: Accumulator0[A, B]): Parser0[B] =
    generic.Parser.repAs0(p1, max = max)(acc)

  /** Repeat the parser `min` or more times
    *
    * @throws java.lang.IllegalArgumentException
    *   if min < 1
    */
  def repAs[A, B](p1: Parser[A], min: Int)(implicit acc: Accumulator[A, B]): Parser[B] =
    generic.Parser.repAs(p1, min = min)(acc)

  /** Repeat the parser `min` or more times, but no more than `max`
    *
    * @throws java.lang.IllegalArgumentException
    *   if min < 1 or max < min
    */
  def repAs[A, B](p1: Parser[A], min: Int, max: Int)(implicit
      acc: Accumulator[A, B]
  ): Parser[B] =
    generic.Parser.repAs(p1, min = min, max = max)(acc)

  /** Repeat the parser exactly `times` times
    *
    * @throws java.lang.IllegalArgumentException
    *   if times < 1
    */
  def repExactlyAs[A, B](p: Parser[A], times: Int)(implicit acc: Accumulator[A, B]): Parser[B] =
    generic.Parser.repExactlyAs(p, times = times)(acc)

  /** Repeat 1 or more times with a separator */
  def repSep[A](p1: Parser[A], sep: Parser0[Any]): Parser[NonEmptyList[A]] =
    generic.Parser.repSep(p1, sep)

  /** Repeat `min` or more times with a separator, at least once.
    *
    * @throws java.lang.IllegalArgumentException
    *   if `min <= 0`
    */
  def repSep[A](p1: Parser[A], min: Int, sep: Parser0[Any]): Parser[NonEmptyList[A]] =
    generic.Parser.repSep(p1, min, sep)

  /** Repeat `min` or more, up to `max` times with a separator, at least once.
    *
    * @throws java.lang.IllegalArgumentException
    *   if `min <= 0` or `max < min`
    */
  def repSep[A](p1: Parser[A], min: Int, max: Int, sep: Parser0[Any]): Parser[NonEmptyList[A]] =
    generic.Parser.repSep(p1, min, max, sep)

  /** Repeat 0 or more times with a separator */
  def repSep0[A](p1: Parser[A], sep: Parser0[Any]): Parser0[List[A]] =
    generic.Parser.repSep0(p1, sep)

  /** Repeat `min` or more times with a separator.
    *
    * @throws java.lang.IllegalArgumentException
    *   if `min < 0`
    */
  def repSep0[A](p1: Parser[A], min: Int, sep: Parser0[Any]): Parser0[List[A]] =
    generic.Parser.repSep0(p1, min, sep)

  /** Repeat `min` or more, up to `max` times with a separator.
    *
    * @throws java.lang.IllegalArgumentException
    *   if `min < 0` or `max < min`
    */
  def repSep0[A](p1: Parser[A], min: Int, max: Int, sep: Parser0[Any]): Parser0[List[A]] =
    generic.Parser.repSep0(p1, min, max, sep)

  /** parse first then second */
  def product0[A, B](first: Parser0[A], second: Parser0[B]): Parser0[(A, B)] =
    generic.Parser.product0(first, second)

  /** product with the first argument being a Parser */
  def product10[A, B](first: Parser[A], second: Parser0[B]): Parser[(A, B)] =
    generic.Parser.product10(first, second)

  /** product with the second argument being a Parser */
  def product01[A, B](first: Parser0[A], second: Parser[B]): Parser[(A, B)] =
    generic.Parser.product01(first, second)

  /** softProduct, a variant of product. A soft product backtracks if the first succeeds and the
    * second is an epsilon-failure. By contrast product will be a failure in that case
    *
    * see @Parser.soft
    */
  def softProduct0[A, B](first: Parser0[A], second: Parser0[B]): Parser0[(A, B)] =
    generic.Parser.softProduct0(first, second)

  /** softProduct with the first argument being a Parser */
  def softProduct10[A, B](first: Parser[A], second: Parser0[B]): Parser[(A, B)] =
    generic.Parser.softProduct10(first, second)

  /** softProduct with the second argument being a Parser */
  def softProduct01[A, B](first: Parser0[A], second: Parser[B]): Parser[(A, B)] =
    generic.Parser.softProduct01(first, second)

  /** This implements the main method from the Align typeclass. This parses the first then maybe the
    * second, or just the second. Put another way, it parses at least one of the arguments.
    */
  def align[A, B](pa: Parser[A], pb: Parser[B]): Parser[cats.data.Ior[A, B]] =
    generic.Parser.align(pa, pb)

  /** the [[align]] whose parsers may consume no input */
  def align0[A, B](pa: Parser0[A], pb: Parser0[B]): Parser0[cats.data.Ior[A, B]] =
    generic.Parser.align0(pa, pb)

  /** transform a Parser0 result */
  def map0[A, B](p: Parser0[A])(fn: A => B): Parser0[B] =
    generic.Parser.map0(p)(fn)

  /** transform a Parser result */
  def map[A, B](p: Parser[A])(fn: A => B): Parser[B] =
    generic.Parser.map(p)(fn)

  /** Parse p and if we get the Left side, parse fn. This function name comes from selective
    * functors. This should be more efficient than flatMap since the fn Parser0 is evaluated once,
    * not on every item parsed
    */
  def select0[A, B](p: Parser0[Either[A, B]])(fn: Parser0[A => B]): Parser0[B] =
    generic.Parser.select0(p)(fn)

  /** Parser version of select */
  def select[A, B](p: Parser[Either[A, B]])(fn: Parser0[A => B]): Parser[B] =
    generic.Parser.select(p)(fn)

  /** Standard monadic flatMap. Avoid this function if possible. If you can instead use product, ~,
    * *>, or <* use that. flatMap always has to allocate a parser, and the parser is less amenable
    * to optimization
    */
  def flatMap0[A, B](pa: Parser0[A])(fn: A => Parser0[B]): Parser0[B] =
    generic.Parser.flatMap0(pa)(fn)

  /** Standard monadic flatMap where you start with a Parser */
  def flatMap10[A, B](pa: Parser[A])(fn: A => Parser0[B]): Parser[B] =
    generic.Parser.flatMap10(pa)(fn)

  /** Standard monadic flatMap where you end with a Parser */
  def flatMap01[A, B](pa: Parser0[A])(fn: A => Parser[B]): Parser[B] =
    generic.Parser.flatMap01(pa)(fn)

  /** tail recursive monadic flatMaps. This is a rarely used function, but needed to implement
    * cats.FlatMap
    */
  def tailRecM0[A, B](init: A)(fn: A => Parser0[Either[A, B]]): Parser0[B] =
    generic.Parser.tailRecM0(init)(fn)

  /** tail recursive monadic flatMaps on Parser */
  def tailRecM[A, B](init: A)(fn: A => Parser[Either[A, B]]): Parser[B] =
    generic.Parser.tailRecM(init)(fn)

  /** Lazily create a Parser. This is useful to create some recursive parsers. See Defer[Parser].fix
    */
  def defer[A](pa: => Parser[A]): Parser[A] =
    generic.Parser.defer(pa)

  /** Lazily create a Parser0 */
  def defer0[A](pa: => Parser0[A]): Parser0[A] =
    generic.Parser.defer0(pa)

  /** Build a recursive parser by assuming you have it. Useful for parsing recursive structures like
    * JSON.
    */
  def recursive[A](fn: Parser[A] => Parser[A]): Parser[A] =
    generic.Parser.recursive(fn)

  /** parse zero or more characters as long as they don't match p. This is useful for parsing
    * comment strings, for instance.
    */
  def until0(p: Parser0[Any]): Parser0[String] =
    generic.Parser.until0(StringAlphabet)(p)

  /** parse one or more characters as long as they don't match p */
  def until(p: Parser0[Any]): Parser[String] =
    generic.Parser.until(StringAlphabet)(p)

  /** parse zero or more times until Parser `end` succeeds. */
  def repUntil0[A](p: Parser[A], end: Parser0[Any]): Parser0[List[A]] =
    generic.Parser.repUntil0(p, end)(StringAlphabet)

  /** parse one or more times until Parser `end` succeeds. */
  def repUntil[A](p: Parser[A], end: Parser0[Any]): Parser[NonEmptyList[A]] =
    generic.Parser.repUntil(p, end)(StringAlphabet)

  /** parse zero or more times until Parser `end` succeeds. */
  def repUntilAs0[A, B](p: Parser[A], end: Parser0[Any])(implicit
      acc: Accumulator0[A, B]
  ): Parser0[B] =
    generic.Parser.repUntilAs0(p, end)(StringAlphabet, acc)

  /** parse one or more times until Parser `end` succeeds. */
  def repUntilAs[A, B](p: Parser[A], end: Parser0[Any])(implicit
      acc: Accumulator[A, B]
  ): Parser[B] =
    generic.Parser.repUntilAs(p, end)(StringAlphabet, acc)

  /** discard the value in a Parser. This is an optimization because we remove trailing map
    * operations and don't allocate internal data structures. This function is called internally by
    * Functor.as, Apply.*> and Apply.<*, so those are good uses.
    */
  def void0(pa: Parser0[Any]): Parser0[Unit] =
    generic.Parser.void0(pa)

  /** the [[void0]] with `pa` known to consume input */
  def void(pa: Parser[Any]): Parser[Unit] =
    generic.Parser.void(pa)

  /** Discard the result A and instead capture the matching string. This is optimized to avoid
    * internal allocations
    */
  def string0(pa: Parser0[Any]): Parser0[String] =
    generic.Parser.slice0(StringAlphabet)(pa)

  /** the [[string0]] with `pa` known to consume input */
  def string(pa: Parser[Any]): Parser[String] =
    generic.Parser.slice(StringAlphabet)(pa)

  /** Return the value and the input string matched */
  def withString0[A](pa: Parser0[A]): Parser0[(A, String)] =
    generic.Parser.withSlice0(StringAlphabet)(pa)

  /** the [[withString0]] with `pa` known to consume input */
  def withString[A](pa: Parser[A]): Parser[(A, String)] =
    generic.Parser.withSlice(StringAlphabet)(pa)

  /** returns a parser that succeeds if the current parser fails. Note, this parser backtracks
    * (never returns an arresting failure)
    */
  def not(pa: Parser0[Any]): Parser0[Unit] =
    generic.Parser.not(pa)(StringAlphabet)

  /** a parser that consumes nothing when it succeeds, basically rewind on success */
  def peek(pa: Parser0[Any]): Parser0[Unit] =
    generic.Parser.peek(pa)

  /** If we fail, rewind the offset back so that we can try other branches. This tends to harm
    * debuggability and ideally should be minimized
    */
  def backtrack0[A](pa: Parser0[A]): Parser0[A] =
    generic.Parser.backtrack0(pa)

  /** the [[backtrack0]] with `pa` known to consume input */
  def backtrack[A](pa: Parser[A]): Parser[A] =
    generic.Parser.backtrack(pa)

  /** Replaces parsed values with the given value. */
  def as0[B](pa: Parser0[Any], b: B): Parser0[B] =
    generic.Parser.as0(pa, b)

  /** the [[as0]] with `pa` known to consume input */
  def as[B](pa: Parser[Any], b: B): Parser[B] =
    generic.Parser.as(pa, b)

  /** Add a context string to Errors to aid debugging */
  def withContext0[A](p0: Parser0[A], ctx: String): Parser0[A] =
    generic.Parser.withContext0(p0, ctx)

  /** the [[withContext0]] with `p` known to consume input */
  def withContext[A](p: Parser[A], ctx: String): Parser[A] =
    generic.Parser.withContext(p, ctx)

  implicit val catsInstancesParser
      : FlatMap[Parser] with Defer[Parser] with MonoidK[Parser] with FunctorFilter[Parser] =
    generic.Parser.catsInstancesParser[String]

  implicit val catsAlignParser: Align[Parser] =
    generic.Parser.catsAlignParser[String]

  /** the contiguous ranges covering exactly the chars of `charArray`, which must be sorted */
  private[parse] def rangesFor(charArray: Array[Char]): NonEmptyList[(Char, Char)] =
    StringAlphabet.rangesFor(charArray)
}

/** holds just the typeclass instances, and brings them in implicit scope */
object Parser0 {
  implicit val catInstancesParser0
      : Monad[Parser0] with Alternative[Parser0] with Defer[Parser0] with FunctorFilter[Parser0] =
    generic.Parser0.catsInstancesParser0[String]

  implicit val catsAlignParser0: Align[Parser0] =
    generic.Parser0.catsAlignParser0[String]
}
