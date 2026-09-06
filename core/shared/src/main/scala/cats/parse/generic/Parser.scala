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

import cats.{Align, Alternative, Defer, Eval, FlatMap, Functor, FunctorFilter, Monad, MonoidK, Now}
import cats.data.{Chain, Ior, NonEmptyList}
import cats.parse.{Accumulator, Accumulator0, Appender, LocationMap}

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet

/** A parser over an input `S` — governed by an [[Alphabet]] — which may not consume any input and
  * yields an `A` on success.
  *
  * This is the generic form of `cats.parse.Parser0`: one added type parameter, the same
  * epsilon/arresting failure semantics. `Parser0[String, A]` instantiated at [[StringAlphabet]] is
  * the char parser.
  */
sealed abstract class Parser0[S, +A] {

  /** Attempt to parse an `A` out of `input`.
    *
    * @return
    *   the unconsumed remainder of the input and the parsed value, or the failure
    */
  final def parse(input: S)(implicit alpha: Alphabet[S]): Either[Error[S], (alpha.Slice, A)] = {
    val state = new Parser.State[S](input)
    val result = parseMut(state)
    val err = state.error
    val offset = state.offset
    if (err eq null) Right((alpha.slice(input, offset, alpha.length(input)), result))
    else Left(Error(input, offset, unifyErrors(err)))
  }

  /** Attempt to parse all of `input` into an `A`: fails unless every token is consumed.
    *
    * @return
    *   the parsed value, or the failure
    */
  final def parseAll(input: S)(implicit alpha: Alphabet[S]): Either[Error[S], A] = {
    val state = new Parser.State[S](input)
    val result = parseMut(state)
    val err = state.error
    val offset = state.offset
    val length = alpha.length(input)
    if (err ne null) Left(Error(input, offset, unifyErrors(err)))
    else if (offset == length) Right(result)
    else
      Left(Error(input, offset, NonEmptyList.one(Expectation.EndOfString(offset, length))))
  }

  /** @return a parser that applies `fn` to this parser's result */
  def map[B](fn: A => B): Parser0[S, B] =
    Parser.Impl.Map0(this, fn)

  /** @return a parser that runs the parser `fn` builds from this parser's result */
  def flatMap[B](fn: A => Parser0[S, B]): Parser0[S, B] =
    Parser.Impl.FlatMap0(this, fn)

  /** @return a parser running `that` after this one, pairing both results */
  def ~[B](that: Parser0[S, B]): Parser0[S, (A, B)] =
    Parser.Impl.Prod0(this, that)

  /** @return a parser running this one and discarding its result */
  def void: Parser0[S, Unit] =
    Parser.Impl.Void0(this)

  /** Capture the input this parser consumed as the alphabet's [[Alphabet.Slice]]. This is the
    * generic form of char's `.string`: the char instance fixes `Slice = String`, so char captures
    * keep their exact historical type.
    *
    * @return
    *   a parser returning the consumed input in place of this parser's result
    */
  def slice(implicit alpha: Alphabet[S]): Parser0[S, alpha.Slice] =
    Parser.Impl.SliceP0[S, A, alpha.Slice](alpha, this)

  /** @return
    *   a parser that rewinds the offset to where it started when this one fails, turning an
    *   arresting failure into an epsilon failure
    */
  def backtrack: Parser0[S, A] =
    Parser.Impl.Backtrack0(this)

  /** Convert epsilon failures into `None`, wrapping other results in `Some`. A failure that
    * consumed input still fails.
    *
    * @return
    *   a parser that never fails on an epsilon failure of this one
    */
  def ? : Parser0[S, Option[A]] =
    Parser.oneOf0(map(Some(_): Option[A]) :: Parser.optTail[S, A])

  /** This is the generic form of char's `eitherOr`: `pb` is tried only on an epsilon failure of
    * this parser.
    *
    * @return
    *   `Right` from this parser, `Left` from `pb`
    */
  def eitherOr[B](pb: Parser0[S, B]): Parser0[S, Either[B, A]] =
    Parser.eitherOr0(this, pb)

  /** Capture both this parser's result and the input it consumed, as the generic form of char's
    * `withString`.
    *
    * @return
    *   a parser returning both the result and the consumed input, as the alphabet's
    *   [[Alphabet.Slice]]
    */
  def withSlice(implicit alpha: Alphabet[S]): Parser0[S, (A, alpha.Slice)] =
    Parser.Impl.WithSliceP0[S, A, alpha.Slice](alpha, this)

  /** @return a parser running this one then `that`, keeping only `that`'s result */
  def *>[B](that: Parser0[S, B]): Parser0[S, B] =
    (void ~ that).map(_._2)

  /** @return a parser running this one then `that`, keeping only this one's result */
  def <*[B](that: Parser0[S, B]): Parser0[S, A] =
    (this ~ that.void).map(_._1)

  /** @return `that` tried on an epsilon failure of this parser */
  def orElse[A1 >: A](that: Parser0[S, A1]): Parser0[S, A1] =
    Parser.oneOf0(this :: that :: Nil)

  /** Synonym for [[orElse]]. */
  def |[A1 >: A](that: Parser0[S, A1]): Parser0[S, A1] =
    orElse(that)

  /** @return
    *   a parser transforming this one's result by `fn`, failing (with an epsilon failure) on `None`
    */
  def mapFilter[B](fn: A => Option[B]): Parser0[S, B] = {
    val leftUnit = Left(())
    val first = map { a =>
      fn(a) match {
        case Some(b) => Right(b)
        case None => leftUnit
      }
    }
    Parser.select0(first)(Parser.fail[S, Unit => B])
  }

  /** @return a parser keeping only the results `fn` is defined on */
  def collect[B](fn: PartialFunction[A, B]): Parser0[S, B] =
    mapFilter(fn.lift)

  /** @return a parser failing (with an epsilon failure) when `fn` is false of its result */
  def filter(fn: A => Boolean): Parser0[S, A] = {
    val leftUnit = Left(())
    Parser.select0(map { a =>
      if (fn(a)) Right(a) else leftUnit
    })(Parser.fail[S, Unit => A])
  }

  /** @return a parser replacing this one's result with `b` */
  def as[B](b: B): Parser0[S, B] =
    void.map(_ => b)

  /** Wrap this parser to enable composition (`~`, `*>`, `<*`) with a [[Parser]], refining the
    * result to a [[Parser]].
    *
    * @return
    *   a syntax helper over this parser
    */
  def with1: Parser.With1[S, A] =
    new Parser.With1(this)

  /** Wrap this parser to enable backtracking composition: `(x.soft ~ y)` rewinds to before `x` when
    * `y` fails without consuming input.
    *
    * @return
    *   a syntax helper over this parser
    */
  def soft: Parser.Soft0[S, A] =
    new Parser.Soft0(this)

  /** @return a parser succeeding, consuming nothing, exactly when this one would fail */
  def unary_!(implicit alpha: Alphabet[S]): Parser0[S, Unit] =
    Parser.not(this)

  /** @return a parser succeeding, consuming nothing, exactly when this one would succeed */
  def peek: Parser0[S, Unit] =
    Parser.peek(this)

  /** @return this parser's result, parsed between `b` and `c` */
  def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser0[S, A] =
    (b.void ~ (this ~ c.void)).map { case (_, (a, _)) => a }

  /** @return this parser's result, parsed surrounded by `b` on both sides */
  def surroundedBy(b: Parser0[S, Any]): Parser0[S, A] =
    between(b, b)

  /** @return a parser adding `ctx` to the context of any failure of this one */
  def withContext(ctx: String): Parser0[S, A] =
    Parser.withContext0(this, ctx)

  /** Run this parser against the mutable state, advancing `state.offset` on success and setting
    * `state.error` on failure.
    *
    * @return
    *   the parsed value, or `null` (as `A`) when the parse failed or `state.capture` is off
    */
  private[parse] def parseMut(state: Parser.State[S]): A

  private def unifyErrors(
      err: Eval[Chain[Expectation[S]]]
  )(implicit alpha: Alphabet[S]): NonEmptyList[Expectation[S]] =
    Expectation.unify(NonEmptyList.fromListUnsafe(err.value.toList))
}

/** A [[Parser0]] that always consumes at least one token when it succeeds. */
sealed abstract class Parser[S, +A] extends Parser0[S, A] {

  override def map[B](fn: A => B): Parser[S, B] =
    Parser.Impl.Map(this, fn)

  override def flatMap[B](fn: A => Parser0[S, B]): Parser[S, B] =
    Parser.Impl.FlatMap(this, fn)

  override def ~[B](that: Parser0[S, B]): Parser[S, (A, B)] =
    Parser.Impl.Prod(this, that)

  override def void: Parser[S, Unit] =
    Parser.Impl.Void(this)

  override def slice(implicit alpha: Alphabet[S]): Parser[S, alpha.Slice] =
    Parser.Impl.SliceP[S, A, alpha.Slice](alpha, this)

  override def backtrack: Parser[S, A] =
    Parser.Impl.Backtrack(this)

  /** a version of [[Parser0.eitherOr]] when both sides are known to consume input */
  def eitherOr[B](pb: Parser[S, B]): Parser[S, Either[B, A]] =
    Parser.eitherOr(this, pb)

  override def withSlice(implicit alpha: Alphabet[S]): Parser[S, (A, alpha.Slice)] =
    Parser.Impl.WithSliceP[S, A, alpha.Slice](alpha, this)

  override def *>[B](that: Parser0[S, B]): Parser[S, B] =
    (void ~ that).map(_._2)

  override def <*[B](that: Parser0[S, B]): Parser[S, A] =
    (this ~ that.void).map(_._1)

  /** a version of [[Parser0.orElse]] when both sides are known to consume input */
  def orElse[A1 >: A](that: Parser[S, A1]): Parser[S, A1] =
    Parser.oneOf(this :: that :: Nil)

  /** Synonym for [[orElse]]. */
  def |[A1 >: A](that: Parser[S, A1]): Parser[S, A1] =
    orElse(that)

  override def collect[B](fn: PartialFunction[A, B]): Parser[S, B] =
    mapFilter(fn.lift)

  override def mapFilter[B](fn: A => Option[B]): Parser[S, B] = {
    val leftUnit = Left(())
    val first = map { a =>
      fn(a) match {
        case Some(b) => Right(b)
        case None => leftUnit
      }
    }
    Parser.select(first)(Parser.fail[S, Unit => B])
  }

  override def filter(fn: A => Boolean): Parser[S, A] = {
    val leftUnit = Left(())
    Parser.select(map { a =>
      if (fn(a)) Right(a) else leftUnit
    })(Parser.fail[S, Unit => A])
  }

  override def as[B](b: B): Parser[S, B] =
    void.map(_ => b)

  override def soft: Parser.Soft[S, A] =
    new Parser.Soft(this)

  override def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser[S, A] =
    (b.void.with1 ~ (this ~ c.void)).map { case (_, (a, _)) => a }

  override def surroundedBy(b: Parser0[S, Any]): Parser[S, A] =
    between(b, b)

  override def withContext(ctx: String): Parser[S, A] =
    Parser.withContext(this, ctx)

  /** @return a parser repeating this one one or more times */
  def rep: Parser[S, NonEmptyList[A]] = repAs[NonEmptyList[A]]

  /** @return a parser repeating this one at least `min` (which must be `>= 1`) times */
  def rep(min: Int): Parser[S, NonEmptyList[A]] = repAs[NonEmptyList[A]](min)

  /** @return a parser repeating this one zero or more times */
  def rep0: Parser0[S, List[A]] = repAs0[List[A]]

  /** @return a parser repeating this one at least `min` (which must be `>= 0`) times */
  def rep0(min: Int): Parser0[S, List[A]] =
    if (min == 0) rep0 else repAs(min)

  /** @return a parser repeating this one `min` or more, up to `max`, times */
  def rep0(min: Int, max: Int): Parser0[S, List[A]] =
    if (min == 0) repAs0(max) else repAs(min, max)

  /** @return a parser repeating this one one or more times, up to `max` times */
  def rep(min: Int, max: Int): Parser[S, NonEmptyList[A]] =
    repAs[NonEmptyList[A]](min, max)

  /** @return a parser repeating this one one or more times, accumulated by `acc` */
  def repAs[B](implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repAs(this, min = 1)(acc)

  /** @return a parser repeating this one at least `min` times, accumulated by `acc` */
  def repAs[B](min: Int)(implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repAs(this, min = min)(acc)

  /** @return a parser repeating this one `min` or more, up to `max`, times, accumulated by `acc` */
  def repAs[B](min: Int, max: Int)(implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repAs(this, min = min, max = max)(acc)

  /** @return a parser repeating this one zero or more times, accumulated by `acc` */
  def repAs0[B](implicit acc: Accumulator0[A, B]): Parser0[S, B] =
    Parser.repAs0(this)(acc)

  /** @return
    *   a parser repeating this one zero or more times, up to `max` times, accumulated by `acc`
    */
  def repAs0[B](max: Int)(implicit acc: Accumulator0[A, B]): Parser0[S, B] =
    Parser.repAs0(this, max = max)(acc)

  /** @return a parser repeating this one exactly `times` (which must be `>= 1`) times */
  def repExactlyAs[B](times: Int)(implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repExactlyAs(this, times)(acc)

  /** @return a parser repeating this one one or more times, separated by `sep` */
  def repSep(sep: Parser0[S, Any]): Parser[S, NonEmptyList[A]] =
    Parser.repSep(this, sep)

  /** @return
    *   a parser repeating this one at least `min` (which must be `>= 1`) times, separated by `sep`
    */
  def repSep(min: Int, sep: Parser0[S, Any]): Parser[S, NonEmptyList[A]] =
    Parser.repSep(this, min, sep)

  /** @return
    *   a parser repeating this one at least `min` (which must be `>= 1`), up to `max`, times,
    *   separated by `sep`
    */
  def repSep(min: Int, max: Int, sep: Parser0[S, Any]): Parser[S, NonEmptyList[A]] =
    Parser.repSep(this, min, max, sep)

  /** @return a parser repeating this one zero or more times, separated by `sep` */
  def repSep0(sep: Parser0[S, Any]): Parser0[S, List[A]] =
    Parser.repSep0(this, sep)

  /** @return
    *   a parser repeating this one at least `min` (which must be `>= 0`) times, separated by `sep`
    */
  def repSep0(min: Int, sep: Parser0[S, Any]): Parser0[S, List[A]] =
    Parser.repSep0(this, min, sep)

  /** @return
    *   a parser repeating this one at least `min` (which must be `>= 0`), up to `max`, times,
    *   separated by `sep`
    */
  def repSep0(min: Int, max: Int, sep: Parser0[S, Any]): Parser0[S, List[A]] =
    Parser.repSep0(this, min, max, sep)

  /** @return
    *   a parser repeating this one zero or more times, stopping (without consuming) once `end`
    *   succeeds
    */
  def repUntil0(end: Parser0[S, Any])(implicit alpha: Alphabet[S]): Parser0[S, List[A]] =
    Parser.repUntil0(this, end)

  /** @return
    *   a parser repeating this one one or more times, stopping (without consuming) once `end`
    *   succeeds
    */
  def repUntil(end: Parser0[S, Any])(implicit alpha: Alphabet[S]): Parser[S, NonEmptyList[A]] =
    Parser.repUntil(this, end)

  /** @return the [[repUntil0]] accumulated by `acc` */
  def repUntilAs0[B](end: Parser0[S, Any])(implicit
      alpha: Alphabet[S],
      acc: Accumulator0[A, B]
  ): Parser0[S, B] =
    Parser.repUntilAs0(this, end)(alpha, acc)

  /** @return the [[repUntil]] accumulated by `acc` */
  def repUntilAs[B](end: Parser0[S, Any])(implicit
      alpha: Alphabet[S],
      acc: Accumulator[A, B]
  ): Parser[S, B] =
    Parser.repUntilAs(this, end)(alpha, acc)
}

object Parser {

  /** @return a parser consuming nothing and always succeeding with `a` */
  def pure[S, A](a: A): Parser0[S, A] =
    Impl.Pure(a)

  /** Match the literal `lit`, which must be non-empty.
    *
    * Matching goes through [[Alphabet.pattern]]: the literal is one token set per position, and the
    * input matches when every position is a member of its set. When every one of those sets is the
    * singleton of the literal's own token — the case for an equality alphabet like char — set
    * membership is exactly token equality, and the parser takes [[Alphabet.startsWithAt]] instead.
    *
    * @return
    *   a parser matching `lit` and consuming its length
    */
  def seq[S](lit: S)(implicit alpha: Alphabet[S]): Parser[S, Unit] =
    Impl.SeqLit(alpha, lit)

  /** Match one token which is a member of `set`.
    *
    * The alphabet is an explicit parameter rather than an implicit one because the type of `set` is
    * path-dependent on it; the caller needs the instance in hand to have built `set` at all.
    *
    * @return
    *   a parser consuming one token of `set` and returning it
    */
  def tokenIn[S](alpha: Alphabet[S])(set: alpha.TokenSet): Parser[S, alpha.Token] =
    Impl.TokenIn[S, alpha.Token, alpha.TokenSet](alpha, set)

  /** @return a parser consuming any one token and returning it */
  def anyToken[S](alpha: Alphabet[S]): Parser[S, alpha.Token] =
    tokenIn(alpha)(alpha.universal)

  /** Match one token satisfying `fn`. The predicate is asked once per token of the alphabet at
    * construction (via [[Alphabet.setWhere]]) and never on the parse path, so the boxing of `fn` is
    * a cold cost only.
    *
    * @return
    *   a parser consuming one token satisfying `fn`, failing if no token does
    */
  def tokenWhere[S](alpha: Alphabet[S])(fn: alpha.Token => Boolean): Parser[S, alpha.Token] =
    alpha.setWhere(fn) match {
      case Some(set) => tokenIn(alpha)(set)
      case None => fail
    }

  /** Consume the whole run of tokens of `set` starting at the current offset, in one
    * [[Alphabet.scanWhile]] call — the loop lives on the instance so it JITs monomorphically. This
    * is the set-taking primitive under [[tokensWhile]], named for [[tokenIn]] as `tokensWhile` is
    * named for [[tokenWhere]].
    *
    * @return
    *   a parser consuming one or more tokens of `set` and returning them as a slice
    */
  def tokensIn[S](alpha: Alphabet[S])(set: alpha.TokenSet): Parser[S, alpha.Slice] =
    Impl.TokensWhile[S, alpha.TokenSet, alpha.Slice](alpha, set)

  /** The [[tokensIn]] that also accepts an empty run.
    *
    * @return
    *   a parser consuming zero or more tokens of `set` and returning them as a slice
    */
  def tokensIn0[S](alpha: Alphabet[S])(set: alpha.TokenSet): Parser0[S, alpha.Slice] =
    Impl.TokensWhile0[S, alpha.TokenSet, alpha.Slice](alpha, set)

  /** The [[tokensIn]] of the tokens satisfying `fn`, which — like [[tokenWhere]] — is asked once
    * per token of the alphabet at construction and never on the parse path.
    *
    * @return
    *   a parser consuming one or more tokens satisfying `fn`, failing if no token does
    */
  def tokensWhile[S](alpha: Alphabet[S])(fn: alpha.Token => Boolean): Parser[S, alpha.Slice] =
    alpha.setWhere(fn) match {
      case Some(set) => tokensIn(alpha)(set)
      case None => fail
    }

  /** The [[tokensWhile]] that also accepts an empty run: with no token satisfying `fn` that is
    * every run, so this is the empty slice rather than a failure (char's `charsWhile0` is
    * `pure("")`).
    *
    * @return
    *   a parser consuming zero or more tokens satisfying `fn` and returning them as a slice
    */
  def tokensWhile0[S](alpha: Alphabet[S])(fn: alpha.Token => Boolean): Parser0[S, alpha.Slice] =
    alpha.setWhere(fn) match {
      case Some(set) => tokensIn0(alpha)(set)
      case None => Impl.EmptySlice[S, alpha.Slice](alpha)
    }

  /** Match the longest of `alts` that matches at the current offset, each alternative matched
    * through [[Alphabet.pattern]] as [[seq]] does.
    *
    * The result is the '''consumed input''', not the alternative that matched: under a
    * non-injective alphabet several alternatives can match the same input, and which one "won" is
    * not a question with an answer. Char is unaffected — its `Slice` is `String` and today's
    * `stringIn` already returns the matched substring.
    *
    * @return
    *   a parser consuming the longest matching alternative and returning it as a slice
    */
  def seqIn[S](alts: Iterable[S])(implicit alpha: Alphabet[S]): Parser[S, alpha.Slice] = {
    // dedup by orderingS alone: a second pass by `==` could disagree with it and leave SeqIn a set
    // smaller than the list it was chosen for
    val sorted = SortedSet(alts.toSeq: _*)(alpha.orderingS)
    sorted.toList match {
      case Nil => fail
      case one :: Nil => seq(one).slice
      case _ => Impl.SeqIn[S, alpha.Slice](alpha, sorted)
    }
  }

  /** @return a parser consuming exactly `len` (which must be `> 0`) tokens and returning them */
  def length[S](len: Int)(implicit alpha: Alphabet[S]): Parser[S, alpha.Slice] =
    Impl.Length[S, alpha.Slice](alpha, len)

  /** @return the [[length]] that also accepts `len == 0` */
  def length0[S](len: Int)(implicit alpha: Alphabet[S]): Parser0[S, alpha.Slice] =
    if (len > 0) length(len) else Impl.EmptySlice[S, alpha.Slice](alpha)

  /** @return a parser succeeding only at the start of the input, consuming nothing */
  def start[S]: Parser0[S, Unit] =
    Impl.StartParser()

  /** @return a parser succeeding only at the end of the input, consuming nothing */
  def end[S](implicit alpha: Alphabet[S]): Parser0[S, Unit] =
    Impl.EndParser(alpha)

  /** The offset-only analogue of char's `caret`: the position, with no notion of line or column.
    *
    * @return
    *   a parser returning the current offset and consuming nothing
    */
  def index[S]: Parser0[S, Int] =
    Impl.Index()

  /** @return a parser that always fails, consuming nothing */
  def fail[S, A]: Parser[S, A] =
    Impl.Fail()

  /** @return a parser that always fails with `message`, consuming nothing */
  def failWith[S, A](message: String): Parser[S, A] =
    Impl.FailWith(message)

  /** @return a parser deferring the construction of `pa` until the first parse */
  def defer[S, A](pa: => Parser[S, A]): Parser[S, A] =
    Impl.Defer(() => pa)

  /** @return a parser deferring the construction of `pa` until the first parse */
  def defer0[S, A](pa: => Parser0[S, A]): Parser0[S, A] =
    Impl.Defer0(() => pa)

  /** Run `second` after `first`, but rewind to the start when `second` fails without having
    * consumed input: the pair is attempted as one unit, so an alternation can still try something
    * else.
    *
    * @return
    *   the soft product of `first` and `second`
    */
  def softProduct0[S, A, B](first: Parser0[S, A], second: Parser0[S, B]): Parser0[S, (A, B)] =
    Impl.SoftProd0(first, second)

  /** @return the [[softProduct0]] of a `Parser` and a `Parser0`, which consumes input */
  def softProduct10[S, A, B](first: Parser[S, A], second: Parser0[S, B]): Parser[S, (A, B)] =
    Impl.SoftProd(first, second)

  /** @return the [[softProduct0]] of a `Parser0` and a `Parser`, which consumes input */
  def softProduct01[S, A, B](first: Parser0[S, A], second: Parser[S, B]): Parser[S, (A, B)] =
    Impl.SoftProd(first, second)

  /** @return a parser repeating `p1` at least `min` (which must be `>= 1`) times */
  def repAs[S, A, B](p1: Parser[S, A], min: Int)(implicit acc: Accumulator[A, B]): Parser[S, B] = {
    require(min >= 1, s"min should be >= 1, was $min")
    Impl.Rep(p1, min, Int.MaxValue, acc)
  }

  /** @return a parser repeating `p1` at least `min` (which must be `>= 1`), up to `max`, times */
  def repAs[S, A, B](p1: Parser[S, A], min: Int, max: Int)(implicit
      acc: Accumulator[A, B]
  ): Parser[S, B] = {
    require(min >= 1, s"min should be >= 1, was $min")
    if (min == max) repExactlyAs(p1, min)
    else {
      require(max > min, s"max should be >= min, but $max < $min")
      Impl.Rep(p1, min, max - 1, acc)
    }
  }

  /** @return a parser repeating `p1` zero or more times */
  def repAs0[S, A, B](p1: Parser[S, A])(implicit acc: Accumulator0[A, B]): Parser0[S, B] =
    Impl.OneOf0(
      Impl.Rep(p1, 1, Int.MaxValue, acc) ::
        pure[S, B](acc.newAppender().finish()) ::
        Nil
    )

  /** @return
    *   a parser repeating `p1` zero or more times, up to `max` (which must be `>= 0`) times
    */
  def repAs0[S, A, B](
      p1: Parser[S, A],
      max: Int
  )(implicit acc: Accumulator0[A, B]): Parser0[S, B] = {
    require(max >= 0, s"max should be >= 0, was $max")
    val empty = acc.newAppender().finish()
    if (max == 0) pure[S, B](empty)
    else Impl.OneOf0(Impl.Rep(p1, 1, max - 1, acc) :: pure[S, B](empty) :: Nil)
  }

  /** Try each parser in order, taking the first that succeeds. A parser that fails having consumed
    * input stops the search (an arresting failure); one that fails without consuming lets the next
    * alternative run.
    *
    * Adjacent literal/token alternatives are fused into a longest-match [[seqIn]] or a unioned
    * [[tokenIn]] wherever [[Optimizer]] can prove that safe (spec S5.3); anything it cannot prove
    * safe is kept as a plain, left-biased alternation instead.
    *
    * @return
    *   the left-biased alternation of `parsers`
    */
  def oneOf[S, A](parsers: List[Parser[S, A]]): Parser[S, A] =
    Optimizer.oneOfInternal(parsers)

  /** @return the left-biased alternation of `parsers`, which may consume no input */
  def oneOf0[S, A](parsers: List[Parser0[S, A]]): Parser0[S, A] =
    Optimizer.oneOf0Internal(parsers)

  /** @return
    *   `Right` from `first` on success, `Left` from `second` on an epsilon failure of `first`
    */
  def eitherOr0[S, A, B](first: Parser0[S, B], second: Parser0[S, A]): Parser0[S, Either[A, B]] =
    oneOf0(first.map(Right(_)) :: second.map(Left(_)) :: Nil)

  /** the [[eitherOr0]] when both sides are known to consume input */
  def eitherOr[S, A, B](first: Parser[S, B], second: Parser[S, A]): Parser[S, Either[A, B]] =
    oneOf(first.map(Right(_)) :: second.map(Left(_)) :: Nil)

  /** @return a parser running `first` then `second`, pairing both results */
  def product0[S, A, B](first: Parser0[S, A], second: Parser0[S, B]): Parser0[S, (A, B)] =
    first match {
      case f1: Parser[S, A] => product10(f1, second)
      case _ =>
        second match {
          case s1: Parser[S, B] => product01(first, s1)
          case _ => Impl.Prod0(first, second)
        }
    }

  /** the [[product0]] with `first` known to consume input */
  def product10[S, A, B](first: Parser[S, A], second: Parser0[S, B]): Parser[S, (A, B)] =
    Impl.Prod(first, second)

  /** the [[product0]] with `second` known to consume input */
  def product01[S, A, B](first: Parser0[S, A], second: Parser[S, B]): Parser[S, (A, B)] =
    first match {
      case p1: Parser[S, A] => product10(p1, second)
      case _ => Impl.Prod(first, second)
    }

  /** Parse `p` and, on `Left`, run the parser `fn` builds to complete the value — more efficient
    * than `flatMap` since `fn`'s parser is fixed before parsing starts.
    *
    * @return
    *   a parser resolving `p`'s `Left` case through `fn`, passing `Right` through unchanged
    */
  def select0[S, A, B](p: Parser0[S, Either[A, B]])(fn: Parser0[S, A => B]): Parser0[S, B] =
    Impl
      .Select0(p, fn)
      .map {
        case Left((a, f)) => f(a)
        case Right(b) => b
      }

  /** the [[select0]] with `p` known to consume input */
  def select[S, A, B](p: Parser[S, Either[A, B]])(fn: Parser0[S, A => B]): Parser[S, B] =
    Impl
      .Select(p, fn)
      .map {
        case Left((a, f)) => f(a)
        case Right(b) => b
      }

  /** @return a parser dynamically constructing the next parser from `pa`'s result via `fn` */
  def flatMap0[S, A, B](pa: Parser0[S, A])(fn: A => Parser0[S, B]): Parser0[S, B] =
    pa match {
      case p: Parser[S, A] => flatMap10(p)(fn)
      case _ => Impl.FlatMap0(pa, fn)
    }

  /** the [[flatMap0]] with `pa` known to consume input */
  def flatMap10[S, A, B](pa: Parser[S, A])(fn: A => Parser0[S, B]): Parser[S, B] =
    Impl.FlatMap(pa, fn)

  /** the [[flatMap0]] with `fn`'s result known to consume input */
  def flatMap01[S, A, B](pa: Parser0[S, A])(fn: A => Parser[S, B]): Parser[S, B] =
    pa match {
      case p: Parser[S, A] => flatMap10(p)(fn)
      case _ => Impl.FlatMap(pa, fn)
    }

  /** @return a parser tail-recursively applying `fn` from `init` until it returns `Right` */
  def tailRecM[S, A, B](init: A)(fn: A => Parser[S, Either[A, B]]): Parser[S, B] =
    Impl.TailRecM(init, fn)

  /** the [[tailRecM]] whose steps may consume no input */
  def tailRecM0[S, A, B](init: A)(fn: A => Parser0[S, Either[A, B]]): Parser0[S, B] =
    Impl.TailRecM0(init, fn)

  /** @return
    *   a parser built recursively by assuming its own result: `fn(defer(result)) == result`
    */
  def recursive[S, A](fn: Parser[S, A] => Parser[S, A]): Parser[S, A] = {
    lazy val result: Parser[S, A] = fn(defer(result))
    result
  }

  /** Parse at least one of `pa`/`pb`: `pa` then maybe `pb`, or just `pb`. The `Align` typeclass's
    * main method.
    *
    * @return
    *   a parser combining both results when both are present, or whichever one matched
    */
  def align[S, A, B](pa: Parser[S, A], pb: Parser[S, B]): Parser[S, Ior[A, B]] = {
    val hasA = (pa ~ pb.?).map {
      case (a, Some(b)) => Ior.Both(a, b)
      case (a, None) => Ior.Left(a)
    }
    val onlyB = pb.map(Ior.Right(_))
    hasA | onlyB
  }

  /** the [[align]] whose parsers may consume no input */
  def align0[S, A, B](pa: Parser0[S, A], pb: Parser0[S, B]): Parser0[S, Ior[A, B]] = {
    val hasA = (pa ~ pb.?).map {
      case (a, Some(b)) => Ior.Both(a, b)
      case (a, None) => Ior.Left(a)
    }
    val onlyB = pb.map(Ior.Right(_))
    hasA | onlyB
  }

  /** @return
    *   a parser succeeding, consuming nothing, exactly when `pa` would fail; on success, its
    *   [[Expectation.ExpectedFailureAt]] carries the input `pa` unexpectedly matched
    */
  def not[S, A](pa: Parser0[S, A])(implicit alpha: Alphabet[S]): Parser0[S, Unit] =
    Impl.Not(alpha, pa.void)

  /** @return a parser succeeding, consuming nothing, exactly when `pa` would succeed */
  def peek[S, A](pa: Parser0[S, A]): Parser0[S, Unit] =
    Impl.Peek(pa.void)

  /** @return a parser consuming zero or more tokens as long as they don't match `p`, as a slice */
  def until0[S, A](alpha: Alphabet[S])(p: Parser0[S, Any]): Parser0[S, alpha.Slice] =
    repUntil0(anyToken(alpha), p)(alpha).slice(alpha)

  /** @return a parser consuming one or more tokens as long as they don't match `p`, as a slice */
  def until[S, A](alpha: Alphabet[S])(p: Parser0[S, Any]): Parser[S, alpha.Slice] =
    repUntil(anyToken(alpha), p)(alpha).slice(alpha)

  /** @return `p` zero or more times, stopping (without consuming) once `end` succeeds */
  def repUntil0[S, A](p: Parser[S, A], end: Parser0[S, Any])(implicit
      alpha: Alphabet[S]
  ): Parser0[S, List[A]] =
    (not(end).with1 *> p).rep0

  /** @return `p` one or more times, stopping (without consuming) once `end` succeeds */
  def repUntil[S, A](p: Parser[S, A], end: Parser0[S, Any])(implicit
      alpha: Alphabet[S]
  ): Parser[S, NonEmptyList[A]] =
    (not(end).with1 *> p).rep

  /** @return the [[repUntil0]] accumulated by `acc` */
  def repUntilAs0[S, A, B](p: Parser[S, A], end: Parser0[S, Any])(implicit
      alpha: Alphabet[S],
      acc: Accumulator0[A, B]
  ): Parser0[S, B] =
    (not(end).with1 *> p).repAs0

  /** @return the [[repUntil]] accumulated by `acc` */
  def repUntilAs[S, A, B](p: Parser[S, A], end: Parser0[S, Any])(implicit
      alpha: Alphabet[S],
      acc: Accumulator[A, B]
  ): Parser[S, B] =
    (not(end).with1 *> p).repAs

  /** @return a parser replacing `pa`'s result with `b` */
  def as0[S, B](pa: Parser0[S, Any], b: B): Parser0[S, B] =
    pa.void.map(_ => b)

  /** the [[as0]] with `pa` known to consume input */
  def as[S, B](pa: Parser[S, Any], b: B): Parser[S, B] =
    pa.void.map(_ => b)

  /** @return a parser adding `ctx` to the context of any failure of `p0` */
  def withContext0[S, A](p0: Parser0[S, A], ctx: String): Parser0[S, A] =
    Impl.WithContextP0(ctx, p0)

  /** the [[withContext0]] with `p` known to consume input */
  def withContext[S, A](p: Parser[S, A], ctx: String): Parser[S, A] =
    Impl.WithContextP(ctx, p)

  /** @return a parser repeating `p` exactly `times` (which must be `>= 1`) times */
  def repExactlyAs[S, A, B](p: Parser[S, A], times: Int)(implicit
      acc: Accumulator[A, B]
  ): Parser[S, B] =
    if (times == 1) p.map { a => acc.newAppender(a).finish() }
    else {
      require(times > 1, s"times should be >= 1, was $times")
      Impl.Rep(p, times, times - 1, acc)
    }

  /** @return `p1` one or more times, separated by `sep` */
  def repSep[S, A](p1: Parser[S, A], sep: Parser0[S, Any]): Parser[S, NonEmptyList[A]] =
    repSep(p1, min = 1, sep)

  /** @return `p1` at least `min` (which must be `>= 1`) times, separated by `sep` */
  def repSep[S, A](p1: Parser[S, A], min: Int, sep: Parser0[S, Any]): Parser[S, NonEmptyList[A]] = {
    // validate here, against the user's own min, rather than the min - 1 rep0 sees below
    if (min <= 0) throw new IllegalArgumentException(s"require min > 0, found: $min")
    val rest = (sep.void.with1.soft *> p1).rep0(min - 1)
    (p1 ~ rest).map { case (h, t) => NonEmptyList(h, t) }
  }

  /** @return `p1` at least `min` (which must be `>= 1`), up to `max`, times, separated by `sep` */
  def repSep[S, A](
      p1: Parser[S, A],
      min: Int,
      max: Int,
      sep: Parser0[S, Any]
  ): Parser[S, NonEmptyList[A]] = {
    // validate here, against the user's own min/max, rather than the min - 1/max - 1 rep0 sees below
    if (min <= 0) throw new IllegalArgumentException(s"require min > 0, found: $min")
    if (max < min) throw new IllegalArgumentException(s"require max >= min, found: $max < $min")
    if ((min == 1) && (max == 1)) p1.map(NonEmptyList(_, Nil))
    else {
      val rest = (sep.void.with1.soft *> p1).rep0(min = min - 1, max = max - 1)
      (p1 ~ rest).map { case (h, t) => NonEmptyList(h, t) }
    }
  }

  /** @return `p1` zero or more times, separated by `sep` */
  def repSep0[S, A](p1: Parser[S, A], sep: Parser0[S, Any]): Parser0[S, List[A]] =
    repSep0(p1, 0, sep)

  /** @return `p1` at least `min` (which must be `>= 0`) times, separated by `sep` */
  def repSep0[S, A](p1: Parser[S, A], min: Int, sep: Parser0[S, Any]): Parser0[S, List[A]] =
    if (min == 0)
      repSep(p1, sep).?.map {
        case None => Nil
        case Some(nel) => nel.toList
      }
    else repSep(p1, min, sep).map(_.toList)

  /** @return `p1` at least `min` (which must be `>= 0`), up to `max`, times, separated by `sep` */
  def repSep0[S, A](
      p1: Parser[S, A],
      min: Int,
      max: Int,
      sep: Parser0[S, Any]
  ): Parser0[S, List[A]] =
    if (min == 0) {
      if (max == 0) pure(Nil)
      else
        repSep(p1, 1, max, sep).?.map {
          case None => Nil
          case Some(nel) => nel.toList
        }
    } else repSep(p1, min, max, sep).map(_.toList)

  /** Convert a `Map` keyed by token into a parser matching a key then returning its value. The
    * predicate is asked once per token of the alphabet at construction (via [[tokenWhere]]).
    *
    * @return
    *   a parser consuming one token that is a key of `tokenMap`, mapped to its value
    */
  def fromTokenMap[S, A](alpha: Alphabet[S])(tokenMap: Map[alpha.Token, A]): Parser[S, A] =
    tokenWhere(alpha)(tokenMap.contains).map(tokenMap)

  /** the cats instances for [[Parser]], for any `S` — cached once (nothing in the implementation
    * below depends on the concrete `S` or `A`) and cast per call, as is standard for a
    * type-parameterized typeclass instance.
    */
  implicit def catsInstancesParser[S]: FlatMap[Parser[S, *]]
    with Defer[Parser[S, *]]
    with MonoidK[Parser[S, *]]
    with FunctorFilter[Parser[S, *]] =
    catsInstancesParserAny
      .asInstanceOf[FlatMap[
        Parser[S, *]
      ] with Defer[Parser[S, *]] with MonoidK[Parser[S, *]] with FunctorFilter[Parser[S, *]]]

  private[this] val catsInstancesParserAny: FlatMap[Parser[Any, *]]
    with Defer[Parser[Any, *]]
    with MonoidK[Parser[Any, *]]
    with FunctorFilter[Parser[Any, *]] =
    new FlatMap[Parser[Any, *]]
      with Defer[Parser[Any, *]]
      with MonoidK[Parser[Any, *]]
      with FunctorFilter[Parser[Any, *]] {
      override def empty[A]: Parser[Any, A] = fail[Any, A]

      override def defer[A](pa: => Parser[Any, A]): Parser[Any, A] = Parser.this.defer(pa)

      override def functor: Functor[Parser[Any, *]] = this

      override def map[A, B](fa: Parser[Any, A])(fn: A => B): Parser[Any, B] = fa.map(fn)

      override def mapFilter[A, B](fa: Parser[Any, A])(f: A => Option[B]): Parser[Any, B] =
        fa.mapFilter(f)

      override def filter[A](fa: Parser[Any, A])(fn: A => Boolean): Parser[Any, A] = fa.filter(fn)

      override def flatMap[A, B](fa: Parser[Any, A])(fn: A => Parser[Any, B]): Parser[Any, B] =
        // "flatMap10" collides with cats' own FlatMapArityFunctions.flatMap10 (arity 10); qualify
        Parser.this.flatMap10(fa)(fn)

      override def product[A, B](pa: Parser[Any, A], pb: Parser[Any, B]): Parser[Any, (A, B)] =
        product10(pa, pb)

      override def map2[A, B, C](pa: Parser[Any, A], pb: Parser[Any, B])(
          fn: (A, B) => C
      ): Parser[Any, C] =
        map(product(pa, pb)) { case (a, b) => fn(a, b) }

      override def map2Eval[A, B, C](pa: Parser[Any, A], pb: Eval[Parser[Any, B]])(
          fn: (A, B) => C
      ): Eval[Parser[Any, C]] =
        Now(pb match {
          case Now(pbv) => map2(pa, pbv)(fn)
          case later => map2(pa, defer(later.value))(fn)
        })

      override def ap[A, B](pf: Parser[Any, A => B])(pa: Parser[Any, A]): Parser[Any, B] =
        map(product(pf, pa)) { case (fn, a) => fn(a) }

      override def tailRecM[A, B](init: A)(fn: A => Parser[Any, Either[A, B]]): Parser[Any, B] =
        Parser.this.tailRecM(init)(fn)

      override def combineK[A](pa: Parser[Any, A], pb: Parser[Any, A]): Parser[Any, A] =
        oneOf(pa :: pb :: Nil)

      override def void[A](pa: Parser[Any, A]): Parser[Any, Unit] = pa.void

      override def as[A, B](pa: Parser[Any, A], b: B): Parser[Any, B] = pa.as(b)

      override def productL[A, B](pa: Parser[Any, A])(pb: Parser[Any, B]): Parser[Any, A] =
        map(product(pa, pb.void)) { case (a, _) => a }

      override def productR[A, B](pa: Parser[Any, A])(pb: Parser[Any, B]): Parser[Any, B] =
        map(product(pa.void, pb)) { case (_, b) => b }

      override def productLEval[A, B](fa: Parser[Any, A])(
          fb: Eval[Parser[Any, B]]
      ): Parser[Any, A] = {
        val pb = fb match {
          case Now(pbv) => pbv
          case notNow => defer(notNow.value)
        }
        productL(fa)(pb)
      }

      override def productREval[A, B](fa: Parser[Any, A])(
          fb: Eval[Parser[Any, B]]
      ): Parser[Any, B] = {
        val pb = fb match {
          case Now(pbv) => pbv
          case notNow => defer(notNow.value)
        }
        productR(fa)(pb)
      }
    }

  implicit def catsAlignParser[S]: Align[Parser[S, *]] =
    catsAlignParserAny.asInstanceOf[Align[Parser[S, *]]]

  private[this] val catsAlignParserAny: Align[Parser[Any, *]] =
    new Align[Parser[Any, *]] {
      def functor: Functor[Parser[Any, *]] = catsInstancesParserAny
      def align[A, B](pa: Parser[Any, A], pb: Parser[Any, B]): Parser[Any, Ior[A, B]] =
        Parser.this.align(pa, pb)
    }

  /** Enables composing a [[Parser0]] with a [[Parser]] via `~`/`*>`/`<*`/`flatMap`, refining the
    * result to a [[Parser]] (which [[Parser0]] alone can't promise).
    */
  final class With1[S, +A](val parser: Parser0[S, A]) extends AnyVal {
    def ~[B](that: Parser[S, B]): Parser[S, (A, B)] = product01(parser, that)
    def flatMap[B](fn: A => Parser[S, B]): Parser[S, B] = flatMap01(parser)(fn)
    def *>[B](that: Parser[S, B]): Parser[S, B] = product01(parser.void, that).map(_._2)
    def <*[B](that: Parser[S, B]): Parser[S, A] = product01(parser, that.void).map(_._1)
    def soft: Soft01[S, A] = new Soft01(parser)
    def between(b: Parser[S, Any], c: Parser[S, Any]): Parser[S, A] =
      (b.void ~ (parser ~ c.void)).map { case (_, (a, _)) => a }
    def surroundedBy(that: Parser[S, Any]): Parser[S, A] = between(that, that)
  }

  /** If we can parse this then that, do so; if `that` fails without consuming, rewind before this
    * without consuming. If either consumes input, do not rewind.
    */
  sealed class Soft0[S, +A](parser: Parser0[S, A]) {
    def ~[B](that: Parser0[S, B]): Parser0[S, (A, B)] = softProduct0(parser, that)
    def *>[B](that: Parser0[S, B]): Parser0[S, B] = softProduct0(parser.void, that).map(_._2)
    def <*[B](that: Parser0[S, B]): Parser0[S, A] = softProduct0(parser, that.void).map(_._1)
    def with1: Soft01[S, A] = new Soft01(parser)
    def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser0[S, A] =
      (b.void.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    def surroundedBy(b: Parser0[S, Any]): Parser0[S, A] = between(b, b)
  }

  /** the [[Soft0]] with the left-hand parser known to consume input */
  final class Soft[S, +A](parser: Parser[S, A]) extends Soft0[S, A](parser) {
    override def ~[B](that: Parser0[S, B]): Parser[S, (A, B)] = softProduct10(parser, that)
    override def *>[B](that: Parser0[S, B]): Parser[S, B] =
      softProduct10(parser.void, that).map(_._2)
    override def <*[B](that: Parser0[S, B]): Parser[S, A] =
      softProduct10(parser, that.void).map(_._1)
    override def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser[S, A] =
      (b.void.with1.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    override def surroundedBy(b: Parser0[S, Any]): Parser[S, A] = between(b, b)
  }

  /** the [[Soft0]] with the right-hand parser known to consume input */
  final class Soft01[S, +A](val parser: Parser0[S, A]) extends AnyVal {
    def ~[B](that: Parser[S, B]): Parser[S, (A, B)] = softProduct01(parser, that)
    def *>[B](that: Parser[S, B]): Parser[S, B] = softProduct01(parser.void, that).map(_._2)
    def <*[B](that: Parser[S, B]): Parser[S, A] = softProduct01(parser, that.void).map(_._1)
    def between(b: Parser[S, Any], c: Parser[S, Any]): Parser[S, A] =
      (b.void.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    def surroundedBy(b: Parser[S, Any]): Parser[S, A] = between(b, b)
  }

  /** the fixed `List(pure(None))` tail of [[Parser0.?]], typed per `S`/`A` (an `Option[Nothing]`
    * singleton the way char's does isn't possible here: nothing about `Pure` depends on `A`, but a
    * covariant `Nothing` element can't be shared across every `A` and `S` without a cast).
    */
  private[generic] def optTail[S, A]: List[Parser0[S, Option[A]]] =
    pure[S, Option[A]](None) :: Nil

  /** The mutable state threaded through a parse: input, offset, error and whether values are being
    * captured. It knows nothing of the [[Alphabet]] — every leaf carries its own from construction.
    *
    * This is protected rather than private to avoid a warning on 2.12
    */
  protected[parse] final class State[S](val input: S, locationMapThunk: () => Option[LocationMap]) {

    def this(input: S) = this(input, State.noLocationMap)

    var offset: Int = 0
    var error: Eval[Chain[Expectation[S]]] = null
    var capture: Boolean = true

    /** Lazy so that a parse which never asks for a caret never builds it. Its reader will be the
      * char-only `GetCaret` leaf; generic entry points supply no thunk and leave this empty.
      */
    lazy val locationMap: Option[LocationMap] = locationMapThunk()
  }

  protected[parse] object State {
    val noLocationMap: () => Option[LocationMap] = () => None
  }

  private[parse] object Impl {

    val nilError: Eval[Chain[Nothing]] = Eval.now(Chain.nil)

    final case class Pure[S, A](result: A) extends Parser0[S, A] {
      override def parseMut(state: State[S]): A = result
    }

    final case class SeqLit[S](alpha: Alphabet[S], lit: S) extends Parser[S, Unit] {
      private[this] val len: Int = alpha.length(lit)
      require(len > 0, "we need a non-empty literal to expect a match")

      /** True when every position's set is the singleton holding the literal's own token, so that
        * membership and token equality coincide and `startsWithAt` may answer for the whole
        * literal. This is (slightly stronger than) the precondition of
        * `AlphabetLaws.singletonPatternCoherent`, which is what makes the two paths agree.
        */
      private[this] val byEquality: Boolean = {
        val pat = alpha.pattern(lit)
        matchesPattern(pat, lit, 0) && pat.forall(alpha.literalsOf(_).lengthCompare(1) == 0)
      }

      /** Empty on the equality path, which never consults it: retaining the sets would cost char a
        * `CharSet` per character of every literal, which today's `Str` does not pay.
        */
      private[this] val pattern: List[alpha.TokenSet] =
        if (byEquality) Nil else alpha.pattern(lit)

      override def parseMut(state: State[S]): Unit = {
        val offset = state.offset
        val matched =
          if (byEquality) alpha.startsWithAt(state.input, offset, lit)
          else matchesPattern(pattern, state.input, offset)

        if (matched) state.offset = offset + len
        else state.error = Eval.later(Chain.one(Expectation.OneOfSeq(offset, lit :: Nil)))
        ()
      }

      private def matchesPattern(sets0: List[alpha.TokenSet], input: S, offset: Int): Boolean = {
        var sets = sets0
        var i = offset
        var ok = true
        while (ok && sets.nonEmpty) {
          ok = alpha.matchesAt(sets.head, input, i)
          sets = sets.tail
          i += 1
        }
        ok
      }
    }

    final case class TokenIn[S, T, TS](
        alpha: Alphabet[S] { type Token = T; type TokenSet = TS },
        set: TS
    ) extends Parser[S, T] {

      override def parseMut(state: State[S]): T = {
        val offset = state.offset
        if (alpha.matchesAt(set, state.input, offset)) {
          state.offset = offset + 1
          // tokenAt may box, which is why only the capturing path calls it
          if (state.capture) alpha.tokenAt(state.input, offset)
          else null.asInstanceOf[T]
        } else {
          state.error = Eval.later(Chain.fromSeq(alpha.expectSet(offset, set).toList))
          null.asInstanceOf[T]
        }
      }
    }

    final def scanMut[S, TS, Sl](
        alpha: Alphabet[S] { type TokenSet = TS; type Slice = Sl },
        set: TS,
        min: Int,
        state: State[S]
    ): Sl = {
      val offset = state.offset
      // one virtual call for the whole run: the loop is the instance's, not ours
      val end = alpha.scanWhile(set, state.input, offset)
      if ((end - offset) >= min) {
        state.offset = end
        if (state.capture) alpha.slice(state.input, offset, end)
        else null.asInstanceOf[Sl]
      } else {
        state.error = Eval.later(Chain.fromSeq(alpha.expectSet(offset, set).toList))
        null.asInstanceOf[Sl]
      }
    }

    final case class TokensWhile[S, TS, Sl](
        alpha: Alphabet[S] { type TokenSet = TS; type Slice = Sl },
        set: TS
    ) extends Parser[S, Sl] {
      override def parseMut(state: State[S]): Sl = Impl.scanMut(alpha, set, 1, state)
    }

    final case class TokensWhile0[S, TS, Sl](
        alpha: Alphabet[S] { type TokenSet = TS; type Slice = Sl },
        set: TS
    ) extends Parser0[S, Sl] {
      // a run of zero tokens satisfies min = 0, so this leaf never takes the failure branch
      override def parseMut(state: State[S]): Sl = Impl.scanMut(alpha, set, 0, state)
    }

    final case class SeqIn[S, Sl](
        alpha: Alphabet.Aux[S, Sl],
        sorted: SortedSet[S]
    ) extends Parser[S, Sl] {
      require(sorted.size >= 2, s"expected more than two items, found: ${sorted.size}")
      require(
        !sorted.exists(alpha.length(_) == 0),
        "an empty literal is not allowed in alternatives"
      )
      private[this] val matcher: SeqMatcher[S] = alpha.seqMatcher(sorted)
      private[this] val alts: List[S] = sorted.toList

      override def parseMut(state: State[S]): Sl = {
        val offset = state.offset
        val end = matcher.matchAt(state.input, offset)
        if (end < 0) {
          state.error = Eval.later(Chain.one(Expectation.OneOfSeq(offset, alts)))
          null.asInstanceOf[Sl]
        } else {
          state.offset = end
          if (state.capture) alpha.slice(state.input, offset, end)
          else null.asInstanceOf[Sl]
        }
      }
    }

    final case class Length[S, Sl](alpha: Alphabet.Aux[S, Sl], len: Int) extends Parser[S, Sl] {
      require(len > 0, s"required length > 0, found $len")

      override def parseMut(state: State[S]): Sl = {
        val offset = state.offset
        val end = offset + len
        val inputLen = alpha.length(state.input)
        if (end <= inputLen) {
          val res =
            if (state.capture) alpha.slice(state.input, offset, end) else null.asInstanceOf[Sl]
          state.offset = end
          res
        } else {
          state.error = Eval.later(Chain.one(Expectation.Length(offset, len, inputLen - offset)))
          null.asInstanceOf[Sl]
        }
      }
    }

    /** The zero-length capture: char's `pure("")` has no generic analogue, because an empty `Slice`
      * can only come from the instance, out of the input being parsed.
      */
    final case class EmptySlice[S, Sl](alpha: Alphabet.Aux[S, Sl]) extends Parser0[S, Sl] {

      override def parseMut(state: State[S]): Sl = {
        val offset = state.offset
        if (state.capture) alpha.slice(state.input, offset, offset)
        else null.asInstanceOf[Sl]
      }
    }

    final def void[S](pa: Parser0[S, Any], state: State[S]): Unit = {
      val s0 = state.capture
      state.capture = false
      pa.parseMut(state)
      state.capture = s0
      ()
    }

    final case class Void0[S, A](parser: Parser0[S, A]) extends Parser0[S, Unit] {
      override def parseMut(state: State[S]): Unit = Impl.void(parser, state)
    }

    final case class Void[S, A](parser: Parser[S, A]) extends Parser[S, Unit] {
      override def parseMut(state: State[S]): Unit = Impl.void(parser, state)
    }

    final def slice[S, Sl](
        alpha: Alphabet.Aux[S, Sl],
        pa: Parser0[S, Any],
        state: State[S]
    ): Sl = {
      val s0 = state.capture
      state.capture = false
      val init = state.offset
      pa.parseMut(state)
      state.capture = s0
      if (s0 && (state.error eq null)) alpha.slice(state.input, init, state.offset)
      else null.asInstanceOf[Sl]
    }

    final case class SliceP0[S, A, Sl](alpha: Alphabet.Aux[S, Sl], parser: Parser0[S, A])
        extends Parser0[S, Sl] {
      override def parseMut(state: State[S]): Sl = Impl.slice(alpha, parser, state)
    }

    final case class SliceP[S, A, Sl](alpha: Alphabet.Aux[S, Sl], parser: Parser[S, A])
        extends Parser[S, Sl] {
      override def parseMut(state: State[S]): Sl = Impl.slice(alpha, parser, state)
    }

    final def backtrack[S, A](pa: Parser0[S, A], state: State[S]): A = {
      val offset = state.offset
      val a = pa.parseMut(state)
      if (state.error ne null) {
        state.offset = offset
      }
      a
    }

    final case class Backtrack0[S, A](parser: Parser0[S, A]) extends Parser0[S, A] {
      override def parseMut(state: State[S]): A = Impl.backtrack(parser, state)
    }

    final case class Backtrack[S, A](parser: Parser[S, A]) extends Parser[S, A] {
      override def parseMut(state: State[S]): A = Impl.backtrack(parser, state)
    }

    final case class StartParser[S]() extends Parser0[S, Unit] {
      override def parseMut(state: State[S]): Unit = {
        val offset = state.offset
        if (offset != 0) {
          state.error = Eval.later(Chain.one(Expectation.StartOfString(offset)))
        }
        ()
      }
    }

    final case class EndParser[S](alpha: Alphabet[S]) extends Parser0[S, Unit] {
      override def parseMut(state: State[S]): Unit = {
        val offset = state.offset
        val len = alpha.length(state.input)
        if (offset != len) {
          state.error = Eval.later(Chain.one(Expectation.EndOfString(offset, len)))
        }
        ()
      }
    }

    final case class Index[S]() extends Parser0[S, Int] {
      override def parseMut(state: State[S]): Int = state.offset
    }

    final case class Fail[S, A]() extends Parser[S, A] {
      override def parseMut(state: State[S]): A = {
        state.error = Eval.later(Chain.one(Expectation.Fail(state.offset)))
        null.asInstanceOf[A]
      }
    }

    final case class FailWith[S, A](message: String) extends Parser[S, A] {
      override def parseMut(state: State[S]): A = {
        state.error = Eval.later(Chain.one(Expectation.FailWith(state.offset, message)))
        null.asInstanceOf[A]
      }
    }

    final case class Defer[S, A](fn: () => Parser[S, A]) extends Parser[S, A] {
      private[this] var computed: Parser0[S, A] = null

      override def parseMut(state: State[S]): A = {
        val p0 = computed
        val p =
          if (p0 ne null) p0
          else {
            val res = compute(fn)
            computed = res
            res
          }

        p.parseMut(state)
      }
    }

    final case class Defer0[S, A](fn: () => Parser0[S, A]) extends Parser0[S, A] {
      private[this] var computed: Parser0[S, A] = null

      override def parseMut(state: State[S]): A = {
        val p0 = computed
        val p =
          if (p0 ne null) p0
          else {
            val res = compute0(fn)
            computed = res
            res
          }

        p.parseMut(state)
      }
    }

    @tailrec
    final def compute[S, A](fn: () => Parser[S, A]): Parser[S, A] =
      fn() match {
        case Defer(f) => compute(f)
        case notDefer => notDefer
      }

    @tailrec
    final def compute0[S, A](fn: () => Parser0[S, A]): Parser0[S, A] =
      fn() match {
        case Defer(f) => compute(f)
        case Defer0(f) => compute0(f)
        case notDefer0 => notDefer0
      }

    final def softProd[S, A, B](
        pa: Parser0[S, A],
        pb: Parser0[S, B],
        state: State[S]
    ): (A, B) = {
      val offset = state.offset
      val a = pa.parseMut(state)
      if (state.error eq null) {
        val offseta = state.offset
        val b = pb.parseMut(state)
        // pa passed, if pb fails without consuming, rewind to offset
        if (state.error ne null) {
          if (state.offset == offseta) {
            state.offset = offset
          }
          // else partial parse of b, don't rewind
          null
        } else if (state.capture) (a, b)
        else null
      } else null
    }

    // we know that at least one of first | second is a Parser
    final case class SoftProd[S, A, B](first: Parser0[S, A], second: Parser0[S, B])
        extends Parser[S, (A, B)] {
      require(first.isInstanceOf[Parser[_, _]] || second.isInstanceOf[Parser[_, _]])
      override def parseMut(state: State[S]): (A, B) = Impl.softProd(first, second, state)
    }

    final case class SoftProd0[S, A, B](first: Parser0[S, A], second: Parser0[S, B])
        extends Parser0[S, (A, B)] {
      override def parseMut(state: State[S]): (A, B) = Impl.softProd(first, second, state)
    }

    /** A parser repeating the underlying parser between `min` and `maxMinusOne + 1` times, where
      * `maxMinusOne == Int.MaxValue` is the "forever" sentinel.
      */
    final case class Rep[S, A, B](
        p1: Parser[S, A],
        min: Int,
        maxMinusOne: Int,
        acc1: Accumulator[A, B]
    ) extends Parser[S, B] {
      require(min >= 1, s"expected min >= 1, found: $min")

      private[this] val ignore: B = null.asInstanceOf[B]

      override def parseMut(state: State[S]): B = {
        // parse one first, so the appender can be initialized with that value
        val head = p1.parseMut(state)
        def maxRemainingMinusOne =
          if (maxMinusOne == Int.MaxValue) Int.MaxValue else maxMinusOne - 1
        if (state.error ne null) ignore
        else if (state.capture) {
          val app = acc1.newAppender(head)
          if (repCapture(p1, min - 1, maxRemainingMinusOne, state, app)) app.finish()
          else ignore
        } else {
          repNoCapture(p1, min - 1, maxRemainingMinusOne, state)
          ignore
        }
      }
    }

    /** capture parser p repeatedly, at least min times, at most maxMinusOne + 1 times */
    final def repCapture[S, A, B](
        p: Parser[S, A],
        min: Int,
        maxMinusOne: Int,
        state: State[S],
        append: Appender[A, B]
    ): Boolean = {
      var offset = state.offset
      var cnt = 0
      while (cnt <= maxMinusOne) {
        val a = p.parseMut(state)
        if (state.error eq null) {
          cnt += 1
          append.append(a)
          offset = state.offset
        } else {
          // there has been an error
          if ((state.offset == offset) && (cnt >= min)) {
            // we correctly read at least min items, so this is a success
            state.error = null
            return true
          } else {
            // else we did a partial read then failed, or didn't read min items
            return false
          }
        }
      }
      true
    }

    final def repNoCapture[S, A](
        p: Parser[S, A],
        min: Int,
        maxMinusOne: Int,
        state: State[S]
    ): Unit = {
      var offset = state.offset
      var cnt = 0
      while (cnt <= maxMinusOne) {
        p.parseMut(state)
        if (state.error eq null) {
          cnt += 1
          offset = state.offset
        } else {
          if ((state.offset == offset) && (cnt >= min)) {
            state.error = null
          }
          return ()
        }
      }
    }

    final def oneOf[S, A](all: Array[Parser0[S, A]], state: State[S]): A = {
      val offset = state.offset
      var errs: Eval[Chain[Expectation[S]]] = nilError
      var idx = 0
      while (idx < all.length) {
        val res = all(idx).parseMut(state)
        val err = state.error
        // we stop if there was no error or if we consumed some input
        if ((err eq null) || (state.offset != offset)) {
          return res
        } else {
          errs = for { e1 <- errs; e2 <- err } yield e1 ++ e2
          state.error = null
          idx = idx + 1
        }
      }
      // all of them failed, and none advanced the offset
      state.error = errs.map(filterFails(offset, _))
      null.asInstanceOf[A]
    }

    /* Fail is the zero of the alternation, so its message only survives when nothing else did */
    final def filterFails[S](offset: Int, fs: Chain[Expectation[S]]): Chain[Expectation[S]] = {
      val fs1 = fs.filter {
        case Expectation.Fail(o) if o == offset => false
        case _ => true
      }
      if (fs1.isEmpty) Chain.one(Expectation.Fail(offset))
      else fs1
    }

    final case class OneOf[S, A](all: List[Parser[S, A]]) extends Parser[S, A] {
      require(all.lengthCompare(2) >= 0, s"expected more than two items, found: ${all.size}")
      private[this] val ary: Array[Parser0[S, A]] = all.toArray

      override def parseMut(state: State[S]): A = Impl.oneOf(ary, state)
    }

    final case class OneOf0[S, A](all: List[Parser0[S, A]]) extends Parser0[S, A] {
      require(all.lengthCompare(2) >= 0, s"expected more than two items, found: ${all.size}")
      private[this] val ary: Array[Parser0[S, A]] = all.toArray

      override def parseMut(state: State[S]): A = Impl.oneOf(ary, state)
    }

    final def prod[S, A, B](pa: Parser0[S, A], pb: Parser0[S, B], state: State[S]): (A, B) = {
      val a = pa.parseMut(state)
      if (state.error eq null) {
        val b = pb.parseMut(state)
        if (state.capture && (state.error eq null)) (a, b)
        else null
      } else null
    }

    // we know that at least one of first | second is a Parser
    final case class Prod[S, A, B](first: Parser0[S, A], second: Parser0[S, B])
        extends Parser[S, (A, B)] {
      require(first.isInstanceOf[Parser[_, _]] || second.isInstanceOf[Parser[_, _]])
      override def parseMut(state: State[S]): (A, B) = Impl.prod(first, second, state)
    }

    final case class Prod0[S, A, B](first: Parser0[S, A], second: Parser0[S, B])
        extends Parser0[S, (A, B)] {
      override def parseMut(state: State[S]): (A, B) = Impl.prod(first, second, state)
    }

    final def map[S, A, B](parser: Parser0[S, A], fn: A => B, state: State[S]): B = {
      val a = parser.parseMut(state)
      if ((state.error eq null) && state.capture) fn(a)
      else null.asInstanceOf[B]
    }

    final case class Map0[S, A, B](parser: Parser0[S, A], fn: A => B) extends Parser0[S, B] {
      override def parseMut(state: State[S]): B = Impl.map(parser, fn, state)
    }

    final case class Map[S, A, B](parser: Parser[S, A], fn: A => B) extends Parser[S, B] {
      override def parseMut(state: State[S]): B = Impl.map(parser, fn, state)
    }

    final def flatMap[S, A, B](
        parser: Parser0[S, A],
        fn: A => Parser0[S, B],
        state: State[S]
    ): B = {
      // we can't void before flatMap: we need the value to produce the next parser
      val cap = state.capture
      state.capture = true
      val a = parser.parseMut(state)
      state.capture = cap

      if (state.error eq null) fn(a).parseMut(state)
      else null.asInstanceOf[B]
    }

    final case class FlatMap0[S, A, B](parser: Parser0[S, A], fn: A => Parser0[S, B])
        extends Parser0[S, B] {
      override def parseMut(state: State[S]): B = Impl.flatMap(parser, fn, state)
    }

    // at least one of the parsers needs to be a Parser
    final case class FlatMap[S, A, B](parser: Parser0[S, A], fn: A => Parser0[S, B])
        extends Parser[S, B] {
      override def parseMut(state: State[S]): B = Impl.flatMap(parser, fn, state)
    }

    final def select[S, A, B, C](
        pab: Parser0[S, Either[A, B]],
        pc: Parser0[S, C],
        state: State[S]
    ): Either[(A, C), B] = {
      val cap = state.capture
      state.capture = true
      val either = pab.parseMut(state)
      state.capture = cap
      if (state.error eq null)
        either match {
          case Left(a) =>
            val c = pc.parseMut(state)
            if (cap && (state.error eq null)) Left((a, c))
            else null
          case Right(b) => Right(b)
        }
      else null
    }

    final case class Select0[S, A, B, C](pab: Parser0[S, Either[A, B]], pc: Parser0[S, C])
        extends Parser0[S, Either[(A, C), B]] {
      override def parseMut(state: State[S]): Either[(A, C), B] = Impl.select(pab, pc, state)
    }

    // at least one of pab | pc needs to be a Parser
    final case class Select[S, A, B, C](pab: Parser0[S, Either[A, B]], pc: Parser0[S, C])
        extends Parser[S, Either[(A, C), B]] {
      override def parseMut(state: State[S]): Either[(A, C), B] = Impl.select(pab, pc, state)
    }

    final def tailRecM[S, A, B](
        init: Parser0[S, Either[A, B]],
        fn: A => Parser0[S, Either[A, B]],
        state: State[S]
    ): B = {
      var p: Parser0[S, Either[A, B]] = init
      val c0 = state.capture
      state.capture = true
      while (state.error eq null) {
        val res = p.parseMut(state)
        if (state.error eq null) {
          res match {
            case Right(b) =>
              state.capture = c0
              return b
            case Left(a) =>
              p = fn(a)
          }
        }
      }
      state.capture = c0
      null.asInstanceOf[B]
    }

    final case class TailRecM0[S, A, B](init: A, fn: A => Parser0[S, Either[A, B]])
        extends Parser0[S, B] {
      private[this] val p1 = fn(init)
      override def parseMut(state: State[S]): B = Impl.tailRecM(p1, fn, state)
    }

    final case class TailRecM[S, A, B](init: A, fn: A => Parser[S, Either[A, B]])
        extends Parser[S, B] {
      private[this] val p1 = fn(init)
      override def parseMut(state: State[S]): B = Impl.tailRecM(p1, fn, state)
    }

    /** Succeeds, consuming nothing, exactly when `under` (already voided) fails; on success its
      * error slot instead carries the offset-to-offset input `under` unexpectedly matched, via
      * [[Alphabet.subInput]] — the one place the generic layer needs an `S`, not a `Slice`, out of
      * an error.
      */
    final case class Not[S](alpha: Alphabet[S], under: Parser0[S, Unit]) extends Parser0[S, Unit] {
      override def parseMut(state: State[S]): Unit = {
        val offset = state.offset
        under.parseMut(state)
        if (state.error ne null) {
          state.error = null
        } else {
          val offsetErr = state.offset
          state.error = Eval.later {
            val matched = alpha.subInput(state.input, offset, offsetErr)
            Chain.one(Expectation.ExpectedFailureAt(offset, matched))
          }
        }
        state.offset = offset
        ()
      }
    }

    /** Succeeds, consuming nothing, exactly when `under` (already voided) succeeds. */
    final case class Peek[S](under: Parser0[S, Unit]) extends Parser0[S, Unit] {
      override def parseMut(state: State[S]): Unit = {
        val offset = state.offset
        under.parseMut(state)
        if (state.error eq null) state.offset = offset
        ()
      }
    }

    final case class WithContextP0[S, A](context: String, under: Parser0[S, A])
        extends Parser0[S, A] {
      override def parseMut(state: State[S]): A = {
        val a = under.parseMut(state)
        if (state.error ne null)
          state.error = state.error.map(_.map(Expectation.WithContext(context, _)))
        a
      }
    }

    final case class WithContextP[S, A](context: String, under: Parser[S, A]) extends Parser[S, A] {
      override def parseMut(state: State[S]): A = {
        val a = under.parseMut(state)
        if (state.error ne null)
          state.error = state.error.map(_.map(Expectation.WithContext(context, _)))
        a
      }
    }

    final def withSlice[S, A, Sl](
        alpha: Alphabet.Aux[S, Sl],
        pa: Parser0[S, A],
        state: State[S]
    ): (A, Sl) = {
      val init = state.offset
      val a = pa.parseMut(state)
      if (state.error eq null) (a, alpha.slice(state.input, init, state.offset))
      else null
    }

    final case class WithSliceP0[S, A, Sl](alpha: Alphabet.Aux[S, Sl], parser: Parser0[S, A])
        extends Parser0[S, (A, Sl)] {
      override def parseMut(state: State[S]): (A, Sl) = Impl.withSlice(alpha, parser, state)
    }

    final case class WithSliceP[S, A, Sl](alpha: Alphabet.Aux[S, Sl], parser: Parser[S, A])
        extends Parser[S, (A, Sl)] {
      override def parseMut(state: State[S]): (A, Sl) = Impl.withSlice(alpha, parser, state)
    }
  }
}

/** Holds the [[Parser0]] cats instances: `object Parser0` is `class Parser0`'s implicit companion,
  * so — unlike everything else in this file, kept in `object Parser` per this codebase's existing
  * convention — these must live here for ordinary implicit search (`implicitly[Monad[Parser0[S,
  * *]]]`) to find them from an arbitrary call site.
  */
object Parser0 {

  /** the cats instances for [[Parser0]], for any `S` — cached once (nothing in the implementation
    * depends on the concrete `S` or `A`) and cast per call, as [[Parser.catsInstancesParser]] is.
    */
  implicit def catsInstancesParser0[S]: Monad[Parser0[S, *]]
    with Alternative[Parser0[S, *]]
    with Defer[Parser0[S, *]]
    with FunctorFilter[Parser0[S, *]] =
    catsInstancesParser0Any
      .asInstanceOf[Monad[
        Parser0[S, *]
      ] with Alternative[Parser0[S, *]] with Defer[Parser0[S, *]] with FunctorFilter[Parser0[S, *]]]

  private[this] val catsInstancesParser0Any: Monad[Parser0[Any, *]]
    with Alternative[Parser0[Any, *]]
    with Defer[Parser0[Any, *]]
    with FunctorFilter[Parser0[Any, *]] =
    new Monad[Parser0[Any, *]]
      with Alternative[Parser0[Any, *]]
      with Defer[Parser0[Any, *]]
      with FunctorFilter[Parser0[Any, *]] {
      override def pure[A](a: A): Parser0[Any, A] = Parser.pure(a)

      override def defer[A](a: => Parser0[Any, A]): Parser0[Any, A] = Parser.defer0(a)

      override def empty[A]: Parser0[Any, A] = Parser.fail[Any, A]

      override def functor: Functor[Parser0[Any, *]] = this

      override def map[A, B](fa: Parser0[Any, A])(fn: A => B): Parser0[Any, B] = fa.map(fn)

      override def mapFilter[A, B](fa: Parser0[Any, A])(f: A => Option[B]): Parser0[Any, B] =
        fa.mapFilter(f)

      override def replicateA[A](n: Int, fa: Parser0[Any, A]): Parser0[Any, List[A]] =
        fa match {
          case p: Parser[Any, A] if n >= 1 => Parser.repExactlyAs(p, n)
          case _ => super.replicateA(n, fa)
        }

      override def filter[A](fa: Parser0[Any, A])(fn: A => Boolean): Parser0[Any, A] =
        fa.filter(fn)

      override def product[A, B](fa: Parser0[Any, A], fb: Parser0[Any, B]): Parser0[Any, (A, B)] =
        fa ~ fb

      override def map2[A, B, C](pa: Parser0[Any, A], pb: Parser0[Any, B])(
          fn: (A, B) => C
      ): Parser0[Any, C] =
        map(product(pa, pb)) { case (a, b) => fn(a, b) }

      override def map2Eval[A, B, C](pa: Parser0[Any, A], pb: Eval[Parser0[Any, B]])(
          fn: (A, B) => C
      ): Eval[Parser0[Any, C]] =
        Now(pb match {
          case Now(pbv) => map2(pa, pbv)(fn)
          case later => map2(pa, defer(later.value))(fn)
        })

      override def ap[A, B](pf: Parser0[Any, A => B])(pa: Parser0[Any, A]): Parser0[Any, B] =
        map(product(pf, pa)) { case (fn, a) => fn(a) }

      override def flatMap[A, B](fa: Parser0[Any, A])(fn: A => Parser0[Any, B]): Parser0[Any, B] =
        fa.flatMap(fn)

      override def combineK[A](pa: Parser0[Any, A], pb: Parser0[Any, A]): Parser0[Any, A] =
        Parser.oneOf0(pa :: pb :: Nil)

      override def tailRecM[A, B](init: A)(fn: A => Parser0[Any, Either[A, B]]): Parser0[Any, B] =
        Parser.tailRecM0(init)(fn)

      override def void[A](pa: Parser0[Any, A]): Parser0[Any, Unit] = pa.void

      override def as[A, B](pa: Parser0[Any, A], b: B): Parser0[Any, B] = pa.as(b)

      override def productL[A, B](pa: Parser0[Any, A])(pb: Parser0[Any, B]): Parser0[Any, A] =
        map(product(pa, pb.void)) { case (a, _) => a }

      override def productR[A, B](pa: Parser0[Any, A])(pb: Parser0[Any, B]): Parser0[Any, B] =
        map(product(pa.void, pb)) { case (_, b) => b }

      override def productLEval[A, B](fa: Parser0[Any, A])(
          fb: Eval[Parser0[Any, B]]
      ): Parser0[Any, A] = {
        val pb = fb match {
          case Now(pbv) => pbv
          case notNow => defer(notNow.value)
        }
        productL(fa)(pb)
      }

      override def productREval[A, B](fa: Parser0[Any, A])(
          fb: Eval[Parser0[Any, B]]
      ): Parser0[Any, B] = {
        val pb = fb match {
          case Now(pbv) => pbv
          case notNow => defer(notNow.value)
        }
        productR(fa)(pb)
      }
    }

  implicit def catsAlignParser0[S]: Align[Parser0[S, *]] =
    catsAlignParser0Any.asInstanceOf[Align[Parser0[S, *]]]

  private[this] val catsAlignParser0Any: Align[Parser0[Any, *]] =
    new Align[Parser0[Any, *]] {
      def functor: Functor[Parser0[Any, *]] = catsInstancesParser0Any
      def align[A, B](pa: Parser0[Any, A], pb: Parser0[Any, B]): Parser0[Any, Ior[A, B]] =
        Parser.align0(pa, pb)
    }
}
