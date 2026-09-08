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
import cats.data.{AndThen, Chain, Ior, NonEmptyList}
import cats.syntax.traverse._
import cats.parse.{Accumulator, Accumulator0, Appender, Caret, LocationMap}

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet

/** A parser over an input `S` — governed by an [[Alphabet]] — which may not consume any input and
  * yields an `A` on success.
  *
  * This is the generic form of `cats.parse.Parser0`: one added type parameter, the same
  * epsilon/arresting failure semantics. `Parser0[String, A]` instantiated at [[StringAlphabet]] is
  * the char parser, which `cats.parse.Parser0` is an alias for.
  */
sealed abstract class Parser0[S, +A] { self: Product =>

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
    Parser.map0(this)(fn)

  /** @return a parser that runs the parser `fn` builds from this parser's result */
  def flatMap[B](fn: A => Parser0[S, B]): Parser0[S, B] =
    Parser.flatMap0(this)(fn)

  /** @return a parser running `that` after this one, pairing both results */
  def ~[B](that: Parser0[S, B]): Parser0[S, (A, B)] =
    Parser.product0(this, that)

  /** @return a parser running this one and discarding its result */
  def void: Parser0[S, Unit] =
    Parser.void0(this)

  /** Capture the input this parser consumed as the alphabet's [[Alphabet.Slice]]. This is the
    * generic form of char's `.string`: the char instance fixes `Slice = String`, so char captures
    * keep their exact historical type.
    *
    * @return
    *   a parser returning the consumed input in place of this parser's result
    */
  def slice(implicit alpha: Alphabet[S]): Parser0[S, alpha.Slice] =
    Parser.slice0(alpha)(this)

  /** @return
    *   a parser that rewinds the offset to where it started when this one fails, turning an
    *   arresting failure into an epsilon failure
    */
  def backtrack: Parser0[S, A] =
    Parser.backtrack0(this)

  /** Convert epsilon failures into `None`, wrapping other results in `Some`. A failure that
    * consumed input still fails.
    *
    * @return
    *   a parser that never fails on an epsilon failure of this one
    */
  def ? : Parser0[S, Option[A]] =
    Parser.oneOf0(Parser.map0(this)(Some(_): Option[A]) :: Parser.optTail[S, A])

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
    Parser.withSlice0(alpha)(this)

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
    Parser.as0(this, b)

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

  /** This method overrides `Object#hashCode` to cache its result for performance reasons: the
    * construction-time optimizer compares and dedups whole parser trees.
    */
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)

  private def unifyErrors(
      err: Eval[Chain[Expectation[S]]]
  )(implicit alpha: Alphabet[S]): NonEmptyList[Expectation[S]] =
    Expectation.unify(NonEmptyList.fromListUnsafe(err.value.toList))
}

/** A [[Parser0]] that always consumes at least one token when it succeeds. */
sealed abstract class Parser[S, +A] extends Parser0[S, A] { self: Product =>

  override def map[B](fn: A => B): Parser[S, B] =
    Parser.map(this)(fn)

  override def flatMap[B](fn: A => Parser0[S, B]): Parser[S, B] =
    Parser.flatMap10(this)(fn)

  override def ~[B](that: Parser0[S, B]): Parser[S, (A, B)] =
    Parser.product10(this, that)

  override def void: Parser[S, Unit] =
    Parser.void(this)

  override def slice(implicit alpha: Alphabet[S]): Parser[S, alpha.Slice] =
    Parser.slice(alpha)(this)

  override def backtrack: Parser[S, A] =
    Parser.backtrack(this)

  /** a version of [[Parser0.eitherOr]] when both sides are known to consume input */
  def eitherOr[B](pb: Parser[S, B]): Parser[S, Either[B, A]] =
    Parser.eitherOr(this, pb)

  override def withSlice(implicit alpha: Alphabet[S]): Parser[S, (A, alpha.Slice)] =
    Parser.withSlice(alpha)(this)

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
    Parser.as(this, b)

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

  /** the parser that consumes nothing and succeeds with unit — one shared node per build, so the
    * normalizer can recognize it by reference (`eq`) the way char's `Parser.unit` is recognized.
    */
  def unit[S]: Parser0[S, Unit] = unitAny.asInstanceOf[Parser0[S, Unit]]

  private[this] val unitAny: Parser0[Any, Unit] = Impl.Pure(())

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

  /** @return a parser running `first` then `second`, pairing both results */
  def product0[S, A, B](first: Parser0[S, A], second: Parser0[S, B]): Parser0[S, (A, B)] =
    first match {
      case f1: Parser[S, A] => product10(f1, second)
      case Impl.Pure(a) => second.map(Impl.ToTupleWith1(a))
      case _ =>
        second match {
          case s1: Parser[S, B] => product01(first, s1)
          case Impl.Pure(b) => first.map(Impl.ToTupleWith2(b))
          case _ => Impl.Prod0(first, second)
        }
    }

  /** the [[product0]] with `first` known to consume input */
  def product10[S, A, B](first: Parser[S, A], second: Parser0[S, B]): Parser[S, (A, B)] =
    first match {
      case f @ Impl.Fail() => f.widen
      case f @ Impl.FailWith(_) => f.widen
      case _ =>
        second match {
          case Impl.Pure(b) => first.map(Impl.ToTupleWith2(b))
          case _ => Impl.Prod(first, second)
        }
    }

  /** the [[product0]] with `second` known to consume input */
  def product01[S, A, B](first: Parser0[S, A], second: Parser[S, B]): Parser[S, (A, B)] =
    first match {
      case p1: Parser[S, A] => product10(p1, second)
      case Impl.Pure(a) => second.map(Impl.ToTupleWith1(a))
      case Impl.OneOf0(items) =>
        val lst = items.last
        if (Impl.alwaysSucceeds(lst)) {
          // (a1 + a0) * b = a1 * b + a0 * b
          // A trailing always-succeeding alternative -- what `.?` builds, and common -- would
          // otherwise hide the valid expectations of the alternatives before it (issue #382).
          product01(Impl.cheapOneOf0(items.init), second) |
            product01(lst, second)
        } else Impl.Prod(first, second)
      case Impl.Map0(f0, fn) =>
        // Make sure Map doesn't hide the above optimization
        product01(f0, second).map(Impl.Map1Fn(fn))
      case prod0: Impl.Prod0[S, a, b]
          if prod0.second.isInstanceOf[Impl.OneOf0[_, _]] ||
            prod0.second.isInstanceOf[Impl.Map0[_, _, _]] ||
            prod0.second.isInstanceOf[Impl.Prod0[_, _, _]] =>
        // Make sure Prod doesn't hide the above optimization
        // ((a, b), c) == (a, (b, c)).map(Impl.RotateRight)
        product01[S, a, (b, B)](prod0.first, product01(prod0.second, second))
          .map(Impl.RotateRight[a, b, B]())
      case _ => Impl.Prod(first, second)
    }

  /** Run `second` after `first`, but rewind to the start when `second` fails without having
    * consumed input: the pair is attempted as one unit, so an alternation can still try something
    * else.
    *
    * @return
    *   the soft product of `first` and `second`
    */
  def softProduct0[S, A, B](first: Parser0[S, A], second: Parser0[S, B]): Parser0[S, (A, B)] =
    first match {
      case f1: Parser[S, A] => softProduct10(f1, second)
      case Impl.Pure(a) => second.map(Impl.ToTupleWith1(a))
      case _ =>
        second match {
          case s1: Parser[S, B] => softProduct01(first, s1)
          case Impl.Pure(b) => first.map(Impl.ToTupleWith2(b))
          case _ => Impl.SoftProd0(first, second)
        }
    }

  /** @return the [[softProduct0]] of a `Parser` and a `Parser0`, which consumes input */
  def softProduct10[S, A, B](first: Parser[S, A], second: Parser0[S, B]): Parser[S, (A, B)] =
    first match {
      case f @ Impl.Fail() => f.widen
      case f @ Impl.FailWith(_) => f.widen
      case _ =>
        second match {
          case Impl.Pure(b) => first.map(Impl.ToTupleWith2(b))
          case _ => Impl.SoftProd(first, second)
        }
    }

  /** @return the [[softProduct0]] of a `Parser0` and a `Parser`, which consumes input */
  def softProduct01[S, A, B](first: Parser0[S, A], second: Parser[S, B]): Parser[S, (A, B)] =
    first match {
      case f @ Impl.Fail() => f.widen
      case f @ Impl.FailWith(_) => f.widen
      case Impl.Pure(a) => second.map(Impl.ToTupleWith1(a))
      /* The OneOf0 lifting product01 does is not lawful for soft products:
          val p3 = length(1).?.soft ~ length(2)
          val p4 = (length(1).soft ~ length(2)) | length(2)
         p3.parse("ab") fails (the `.?` consumes one token, then length(2) cannot succeed), while
         p4.parse("ab") succeeds (the soft product rewinds, then length(2) matches). */
      case _ => Impl.SoftProd(first, second)
    }

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
  def oneOf[S, A](parsers: List[Parser[S, A]]): Parser[S, A] = {
    val res = Optimizer.oneOfInternal(parsers)
    Impl.hasKnownResult(res) match {
      case Some(a) => res.as(a)
      case None => res
    }
  }

  /** @return the left-biased alternation of `parsers`, which may consume no input */
  def oneOf0[S, A](parsers: List[Parser0[S, A]]): Parser0[S, A] = {
    val res = Optimizer.oneOf0Internal(parsers)
    Impl.hasKnownResult(res) match {
      case Some(a) => res.as(a)
      case None => res
    }
  }

  /** @return
    *   `Right` from `first` on success, `Left` from `second` on an epsilon failure of `first`
    */
  def eitherOr0[S, A, B](first: Parser0[S, B], second: Parser0[S, A]): Parser0[S, Either[A, B]] =
    oneOf0(first.map(Right(_)) :: second.map(Left(_)) :: Nil)

  /** the [[eitherOr0]] when both sides are known to consume input */
  def eitherOr[S, A, B](first: Parser[S, B], second: Parser[S, A]): Parser[S, Either[A, B]] =
    oneOf(first.map(Right(_)) :: second.map(Left(_)) :: Nil)

  /** @return a parser applying `fn` to `p`'s result */
  def map0[S, A, B](p: Parser0[S, A])(fn: A => B): Parser0[S, B] =
    p match {
      case p1: Parser[S, A] => map(p1)(fn)
      case _ =>
        Impl.hasKnownResult(p) match {
          case Some(a) => p.as(fn(a))
          case None =>
            p match {
              case Impl.Map0(p0, f0) =>
                // reassociate in the function, not the parser, so we can quickly check if we match
                Impl.Map0(p0, AndThen(f0).andThen(fn))
              case _ => Impl.Map0(p, fn)
            }
        }
    }

  /** the [[map0]] with `p` known to consume input */
  def map[S, A, B](p: Parser[S, A])(fn: A => B): Parser[S, B] =
    Impl.hasKnownResult(p) match {
      case Some(a) => p.as(fn(a))
      case None =>
        p match {
          case f @ Impl.Fail() => f.widen
          case f @ Impl.FailWith(_) => f.widen
          case Impl.Map(p0, f0) =>
            // reassociate in the function, not the parser, so we can quickly check if we match
            Impl.Map(p0, AndThen(f0).andThen(fn))
          case _ => Impl.Map(p, fn)
        }
    }

  /** Parse `p` and, on `Left`, run the parser `fn` builds to complete the value — more efficient
    * than `flatMap` since `fn`'s parser is fixed before parsing starts.
    *
    * @return
    *   a parser resolving `p`'s `Left` case through `fn`, passing `Right` through unchanged
    */
  def select0[S, A, B](p: Parser0[S, Either[A, B]])(fn: Parser0[S, A => B]): Parser0[S, B] =
    Impl.hasKnownResult(p) match {
      case Some(Right(b)) => p.as(b)
      case Some(Left(a)) => p *> fn.map(_(a))
      case None =>
        Impl
          .Select0(p, fn)
          .map {
            case Left((a, f)) => f(a)
            case Right(b) => b
          }
    }

  /** the [[select0]] with `p` known to consume input */
  def select[S, A, B](p: Parser[S, Either[A, B]])(fn: Parser0[S, A => B]): Parser[S, B] =
    Impl.hasKnownResult(p) match {
      case Some(Right(b)) => p.as(b)
      case Some(Left(a)) => p *> fn.map(_(a))
      case None =>
        Impl
          .Select(p, fn)
          .map {
            case Left((a, f)) => f(a)
            case Right(b) => b
          }
    }

  /** @return a parser dynamically constructing the next parser from `pa`'s result via `fn` */
  def flatMap0[S, A, B](pa: Parser0[S, A])(fn: A => Parser0[S, B]): Parser0[S, B] =
    pa match {
      case p: Parser[S, A] => flatMap10(p)(fn)
      case _ =>
        Impl.hasKnownResult(pa) match {
          case Some(a) => pa *> fn(a)
          case None => Impl.FlatMap0(pa, fn)
        }
    }

  /** the [[flatMap0]] with `pa` known to consume input */
  def flatMap10[S, A, B](pa: Parser[S, A])(fn: A => Parser0[S, B]): Parser[S, B] =
    pa match {
      case f @ Impl.Fail() => f.widen
      case f @ Impl.FailWith(_) => f.widen
      case _ =>
        Impl.hasKnownResult(pa) match {
          case Some(a) => pa *> fn(a)
          case None => Impl.FlatMap(pa, fn)
        }
    }

  /** the [[flatMap0]] with `fn`'s result known to consume input */
  def flatMap01[S, A, B](pa: Parser0[S, A])(fn: A => Parser[S, B]): Parser[S, B] =
    pa match {
      case p: Parser[S, A] => flatMap10(p)(fn)
      case _ =>
        Impl.hasKnownResult(pa) match {
          case Some(a) => pa.with1 *> fn(a)
          case None => Impl.FlatMap(pa, fn)
        }
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

  /** @return a parser running `pa` and discarding its result */
  def void0[S](pa: Parser0[S, Any]): Parser0[S, Unit] =
    pa match {
      case p1: Parser[S, Any] => void(p1)
      case s if Impl.alwaysSucceeds(s) => unit
      case v @ Impl.Void0(_) => v
      case _ =>
        val unmapped = Impl.unmap0(pa)
        // normalization can expose that a parser always succeeds consuming nothing even when the
        // pre-normalization shape didn't say so (`Backtrack0(Prod0(index, index))`, say). Answering
        // `unit` for those keeps `void0` idempotent: without it `p.void` would be a wrapper whose
        // own `.void` collapses further, and `p.void.void != p.void`.
        if (Impl.alwaysSucceeds(unmapped)) unit
        else if (Impl.isVoided(unmapped)) unmapped.asInstanceOf[Parser0[S, Unit]]
        else Impl.Void0(unmapped)
    }

  /** the [[void0]] with `pa` known to consume input */
  def void[S](pa: Parser[S, Any]): Parser[S, Unit] =
    pa match {
      case v @ Impl.Void(_) => v
      case _ =>
        Impl.unmap(pa) match {
          case f @ Impl.Fail() => f.widen
          case f @ Impl.FailWith(_) => f.widen
          case notVoid =>
            if (Impl.isVoided(notVoid)) notVoid.asInstanceOf[Parser[S, Unit]]
            else Impl.Void(notVoid)
        }
    }

  /** @return a parser discarding `pa`'s result and capturing the input it consumed instead */
  def slice0[S](alpha: Alphabet[S])(pa: Parser0[S, Any]): Parser0[S, alpha.Slice] =
    pa match {
      case s1: Parser[S, Any] => slice(alpha)(s1)
      case sl if Impl.matchesSlice(alpha)(sl) => sl.asInstanceOf[Parser0[S, alpha.Slice]]
      case _ =>
        Impl.unmap0(pa) match {
          case Impl.Pure(_) => Impl.EmptySlice[S, alpha.Slice](alpha)
          case notEmpty => Impl.SliceP0[S, Any, alpha.Slice](alpha, notEmpty)
        }
    }

  /** the [[slice0]] with `pa` known to consume input */
  def slice[S](alpha: Alphabet[S])(pa: Parser[S, Any]): Parser[S, alpha.Slice] =
    pa match {
      case sl if Impl.matchesSlice(alpha)(sl) => sl.asInstanceOf[Parser[S, alpha.Slice]]
      case _ =>
        Impl.unmap(pa) match {
          case si @ Impl.SeqIn(_, _) => si.asInstanceOf[Parser[S, alpha.Slice]]
          case len @ Impl.Length(_, _) => len.asInstanceOf[Parser[S, alpha.Slice]]
          case tw @ Impl.TokensWhile(_, _) => tw.asInstanceOf[Parser[S, alpha.Slice]]
          case f @ Impl.Fail() => f.widen
          case f @ Impl.FailWith(_) => f.widen
          case notSlice =>
            // a literal whose match is exactly itself captures a value we can allocate once, here
            Impl.constantSliceOf(alpha)(notSlice) match {
              case Some(known) => Impl.Map(notSlice, Impl.ConstFn(known))
              case None => Impl.SliceP[S, Any, alpha.Slice](alpha, notSlice)
            }
        }
    }

  /** @return a parser returning both `pa`'s result and the input it consumed */
  def withSlice0[S, A](alpha: Alphabet[S])(pa: Parser0[S, A]): Parser0[S, (A, alpha.Slice)] =
    pa match {
      case p1: Parser[S, A] => withSlice(alpha)(p1)
      case sl if Impl.matchesSlice(alpha)(sl) =>
        sl.map(Impl.FanOut[A]()).asInstanceOf[Parser0[S, (A, alpha.Slice)]]
      case notSlice => Impl.WithSliceP0[S, A, alpha.Slice](alpha, notSlice)
    }

  /** the [[withSlice0]] with `pa` known to consume input */
  def withSlice[S, A](alpha: Alphabet[S])(pa: Parser[S, A]): Parser[S, (A, alpha.Slice)] =
    pa match {
      case f @ Impl.Fail() => f.widen
      case f @ Impl.FailWith(_) => f.widen
      case sl if Impl.matchesSlice(alpha)(sl) =>
        sl.map(Impl.FanOut[A]()).asInstanceOf[Parser[S, (A, alpha.Slice)]]
      case notSlice => Impl.WithSliceP[S, A, alpha.Slice](alpha, notSlice)
    }

  /** @return
    *   a parser succeeding, consuming nothing, exactly when `pa` would fail; on success, its
    *   [[Expectation.ExpectedFailureAt]] carries the input `pa` unexpectedly matched
    */
  def not[S, A](pa: Parser0[S, A])(implicit alpha: Alphabet[S]): Parser0[S, Unit] =
    void0(pa) match {
      case Impl.Fail() | Impl.FailWith(_) => unit
      case u if Impl.alwaysSucceeds(u) => Impl.Fail()
      case notFail => Impl.Not(alpha, notFail)
    }

  /** @return a parser succeeding, consuming nothing, exactly when `pa` would succeed */
  def peek[S, A](pa: Parser0[S, A]): Parser0[S, Unit] =
    pa match {
      case p @ Impl.Peek(_) => p
      case s if Impl.alwaysSucceeds(s) => unit
      case notPeek => Impl.Peek(void0(notPeek))
    }

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

  /** @return a parser rewinding the offset when `pa` fails, so an alternation can try elsewhere */
  def backtrack0[S, A](pa: Parser0[S, A]): Parser0[S, A] =
    pa match {
      case p1: Parser[S, A] => backtrack(p1)
      case bt if Impl.doesBacktrack(bt) => bt
      case Impl.Void0(b) => Impl.Void0(Impl.Backtrack0(b)).asInstanceOf[Parser0[S, A]]
      case nbt => Impl.Backtrack0(nbt)
    }

  /** the [[backtrack0]] with `pa` known to consume input */
  def backtrack[S, A](pa: Parser[S, A]): Parser[S, A] =
    pa match {
      case bt if Impl.doesBacktrack(bt) => bt
      case Impl.Void(b) => Impl.Void(Impl.Backtrack(b)).asInstanceOf[Parser[S, A]]
      case nbt => Impl.Backtrack(nbt)
    }

  /** @return a parser replacing `pa`'s result with `b` */
  def as0[S, B](pa: Parser0[S, Any], b: B): Parser0[S, B] =
    pa match {
      case p: Parser[S, Any] => as(p, b)
      case _ =>
        val voided = void0(pa)
        // void cannot make a Parser0 a Parser; if b is (), as in foo.as(()), voided is the answer
        if (Impl.isUnit(b)) voided.asInstanceOf[Parser0[S, B]]
        else if (Impl.alwaysSucceeds(voided)) pure(b)
        else Impl.Map0(voided, Impl.ConstFn(b))
    }

  /** the [[as0]] with `pa` known to consume input */
  def as[S, B](pa: Parser[S, Any], b: B): Parser[S, B] = {
    val v = void(pa)
    // if b is (), such as foo.as(()), we can just return v
    if (Impl.isUnit(b)) v.asInstanceOf[Parser[S, B]]
    else
      v match {
        case Impl.Void(ti @ Impl.TokenIn(alpha, set)) =>
          // a single-token set is cheap and always returns its own token even when voided, so
          // there is no need to keep the Void wrapper around it
          alpha.singletonLiteralOf(set.asInstanceOf[alpha.TokenSet]) match {
            case Some(lit) if Impl.sameValueAndType(b, alpha.tokenAt(lit, 0)) =>
              ti.asInstanceOf[Parser[S, B]]
            case Some(_) => Impl.Map(ti, Impl.ConstFn(b))
            case None => Impl.Map(v, Impl.ConstFn(b))
          }
        case f @ Impl.Fail() => f.widen
        case f @ Impl.FailWith(_) => f.widen
        case voided => Impl.Map(voided, Impl.ConstFn(b))
      }
  }

  /** @return a parser adding `ctx` to the context of any failure of `p0` */
  def withContext0[S, A](p0: Parser0[S, A], ctx: String): Parser0[S, A] =
    p0 match {
      case Impl.Void0(p) => Impl.Void0(withContext0(p, ctx)).asInstanceOf[Parser0[S, A]]
      case _ if Impl.alwaysSucceeds(p0) => p0
      case _ => Impl.WithContextP0(ctx, p0)
    }

  /** the [[withContext0]] with `p` known to consume input */
  def withContext[S, A](p: Parser[S, A], ctx: String): Parser[S, A] =
    p match {
      case Impl.Void(under) => Impl.Void(withContext(under, ctx)).asInstanceOf[Parser[S, A]]
      case _ => Impl.WithContextP(ctx, p)
    }

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
    def *>[B](that: Parser[S, B]): Parser[S, B] = product01(void0(parser), that).map(_._2)
    def <*[B](that: Parser[S, B]): Parser[S, A] = product01(parser, void(that)).map(_._1)
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
    def *>[B](that: Parser0[S, B]): Parser0[S, B] = softProduct0(void0(parser), that).map(_._2)
    def <*[B](that: Parser0[S, B]): Parser0[S, A] = softProduct0(parser, void0(that)).map(_._1)
    def with1: Soft01[S, A] = new Soft01(parser)
    def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser0[S, A] =
      (b.void.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    def surroundedBy(b: Parser0[S, Any]): Parser0[S, A] = between(b, b)
  }

  /** the [[Soft0]] with the left-hand parser known to consume input */
  final class Soft[S, +A](parser: Parser[S, A]) extends Soft0[S, A](parser) {
    override def ~[B](that: Parser0[S, B]): Parser[S, (A, B)] = softProduct10(parser, that)
    override def *>[B](that: Parser0[S, B]): Parser[S, B] =
      softProduct10(void(parser), that).map(_._2)
    override def <*[B](that: Parser0[S, B]): Parser[S, A] =
      softProduct10(parser, void0(that)).map(_._1)
    override def between(b: Parser0[S, Any], c: Parser0[S, Any]): Parser[S, A] =
      (b.void.with1.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    override def surroundedBy(b: Parser0[S, Any]): Parser[S, A] = between(b, b)
  }

  /** the [[Soft0]] with the right-hand parser known to consume input */
  final class Soft01[S, +A](val parser: Parser0[S, A]) extends AnyVal {
    def ~[B](that: Parser[S, B]): Parser[S, (A, B)] = softProduct01(parser, that)
    def *>[B](that: Parser[S, B]): Parser[S, B] = softProduct01(void0(parser), that).map(_._2)
    def <*[B](that: Parser[S, B]): Parser[S, A] = softProduct01(parser, void(that)).map(_._1)
    def between(b: Parser[S, Any], c: Parser[S, Any]): Parser[S, A] =
      (b.void.soft ~ (parser.soft ~ c.void)).map { case (_, (a, _)) => a }
    def surroundedBy(b: Parser[S, Any]): Parser[S, A] = between(b, b)
  }

  /** the fixed `List(pure(None))` tail of [[Parser0.?]] — one shared node, cast per use as [[unit]]
    * is.
    */
  private[parse] def optTail[S, A]: List[Parser0[S, Option[A]]] =
    optTailAny.asInstanceOf[List[Parser0[S, Option[A]]]]

  private[this] val optTailAny: List[Parser0[Any, Option[Any]]] =
    Impl.Pure[Any, Option[Any]](None) :: Nil

  /** The mutable state threaded through a parse: input, offset, error and whether values are being
    * captured. It knows nothing of the [[Alphabet]] — every leaf carries its own from construction.
    *
    * This is protected rather than private to avoid a warning on 2.12
    */
  protected[parse] final class State[S](val input: S) {

    var offset: Int = 0
    var error: Eval[Chain[Expectation[S]]] = null
    var capture: Boolean = true

    /** The per-parse memo slot for the char-only `GetCaret` leaf, which is this field's only reader
      * and its only writer. Null until a caret is actually asked for, so a parse that never asks
      * never builds one; holding the slot here rather than in the leaf is what makes the
      * memoization per-parse rather than per-parser.
      */
    var locationMap: LocationMap = null
  }

  private[parse] object Impl {

    val nilError: Eval[Chain[Nothing]] = Eval.now(Chain.nil)

    def isUnit(a: Any): Boolean = a.equals(())

    /** Equality that does not cooperate across boxed primitives. Scala's `==` says `58 == ':'`,
      * which would let the optimizer hand back a `Parser[S, Char]` where a `Parser[S, Int]` was
      * asked for; char's optimizer avoids this by type-testing the constant it is given, which
      * generically is not possible over an abstract `Token`.
      */
    def sameValueAndType(a: Any, b: Any): Boolean = {
      val ra = a.asInstanceOf[AnyRef]
      val rb = b.asInstanceOf[AnyRef]
      (ra ne null) && (rb ne null) && (ra.getClass == rb.getClass) && (ra == rb)
    }

    val someUnit: Some[Unit] = Some(())

    def sameAlphabet[S](a1: Alphabet[S], a2: Alphabet[S]): Boolean =
      (a1.asInstanceOf[AnyRef] eq a2.asInstanceOf[AnyRef]) || (a1 == a2)

    /** True when `lit`'s pattern is exactly its own tokens — every position a singleton set holding
      * the token `lit` itself has there. Membership and token equality then coincide over `lit`, so
      * matching it consumes `lit` and nothing else, which is what lets `SeqLit` take the
      * `startsWithAt` fast path and lets the optimizer treat the literal's capture as a constant
      * and rewrite a token set into literal alternatives. It is false for an alphabet whose literal
      * patterns accept more than themselves (spec S3.2).
      */
    def exactLiteral[S](alpha: Alphabet[S])(lit: S): Boolean =
      alpha.pattern(lit).iterator.zipWithIndex.forall { case (set, i) =>
        alpha.singletonLiteralOf(set).isDefined && alpha.matchesAt(set, lit, i)
      }

    //////////////////////////////////////////////////////////////////////
    // Function nodes: case classes so that the parser trees they sit in stay comparable by value.
    //////////////////////////////////////////////////////////////////////

    final case class ConstFn[A](result: A) extends Function1[Any, A] {
      def apply(any: Any): A = result

      override def andThen[B](that: A => B): ConstFn[B] = ConstFn(that(result))

      override def toString(): String = s"ConstFn($result)"
    }

    final case class ToTupleWith1[A, C](item1: A) extends Function1[C, (A, C)] {
      def apply(c: C): (A, C) = (item1, c)

      override def andThen[E](fn: ((A, C)) => E): C => E =
        fn match {
          case Map1Fn(fn1) =>
            // we know that E =:= (B, C) for some B
            type B = Any
            ToTupleWith1(fn1.asInstanceOf[A => B](item1)).asInstanceOf[C => E]
          case _ => super.andThen(fn)
        }
    }

    final case class ToTupleWith2[B, C](item2: B) extends Function1[C, (C, B)] {
      def apply(c: C): (C, B) = (c, item2)
    }

    final case class FanOut[A]() extends Function1[A, (A, A)] {
      def apply(a: A): (A, A) = (a, a)
    }

    final case class Map1Fn[A, B, C](fn: A => B) extends Function1[(A, C), (B, C)] {
      def apply(ac: (A, C)): (B, C) = (fn(ac._1), ac._2)
    }

    /** rewrites ((a, b), c) to (a, (b, c)) */
    final case class RotateRight[A, B, C]() extends Function1[(A, (B, C)), ((A, B), C)] {
      def apply(abc: (A, (B, C))): ((A, B), C) = ((abc._1, abc._2._1), abc._2._2)
    }

    /** makes [[unmap0]] a pure function with respect to `equals` */
    final case class UnmapDefer0[S](fn: () => Parser0[S, Any]) extends Function0[Parser0[S, Any]] {
      def apply(): Parser0[S, Any] = unmap0(compute0(fn))
    }

    /** makes [[unmap]] a pure function with respect to `equals` */
    final case class UnmapDefer[S](fn: () => Parser[S, Any]) extends Function0[Parser[S, Any]] {
      def apply(): Parser[S, Any] = unmap(compute(fn))
    }

    //////////////////////////////////////////////////////////////////////
    // Structural analysis. Every function here is construction-time only.
    //////////////////////////////////////////////////////////////////////

    /** only call this when removing items from the head or tail of the list: removing from the
      * middle may unlock a merge that wasn't possible before
      */
    def cheapOneOf0[S, A](items: List[Parser0[S, A]]): Parser0[S, A] =
      items match {
        case Nil => Fail()
        case pa :: Nil => pa
        case many =>
          def to1(p: Parser0[S, A]): Option[Parser[S, A]] =
            p match {
              case p1: Parser[S, A] => Some(p1)
              case _ => None
            }

          many.traverse(to1) match {
            case Some(p1s) => OneOf(p1s)
            case None => OneOf0(many)
          }
      }

    final def doesBacktrackCheat[S](p: Parser0[S, Any]): Boolean =
      doesBacktrack(p)

    @tailrec
    final def doesBacktrack[S](p: Parser0[S, Any]): Boolean =
      p match {
        case Backtrack0(_) | Backtrack(_) | TokenIn(_, _) | TokensWhile(_, _) | TokensWhile0(_, _) |
            EmptySlice(_) | SeqLit(_, _) | IgnoreCase(_) | Length(_, _) | StartParser() | EndParser(
              _
            ) | Index() | GetCaret() | Pure(_) | Fail() | FailWith(_) | Not(_, _) | SeqIn(_, _) =>
          true
        case Map0(p1, _) => doesBacktrack(p1)
        case Map(p1, _) => doesBacktrack(p1)
        case SoftProd0(a, b) => doesBacktrackCheat(a) && doesBacktrack(b)
        case SoftProd(a, b) => doesBacktrackCheat(a) && doesBacktrack(b)
        case WithContextP0(_, p1) => doesBacktrack(p1)
        case WithContextP(_, p1) => doesBacktrack(p1)
        case OneOf0(ps) => ps.forall(doesBacktrackCheat(_))
        case OneOf(ps) => ps.forall(doesBacktrackCheat(_))
        case Void0(p1) => doesBacktrack(p1)
        case Void(p1) => doesBacktrack(p1)
        case _ => false
      }

    /** A parser that matches exactly the literal it was built from — its pattern is the literal's
      * own tokens, so the input it consumes is the literal and nothing else. This is what lets the
      * optimizer treat a literal's capture as a known constant, and is false for an alphabet whose
      * literal patterns accept more than themselves.
      */
    def constantSliceOf[S](alpha: Alphabet[S])(p: Parser0[S, Any]): Option[alpha.Slice] =
      p match {
        case sl @ SeqLit(a, lit) if sameAlphabet(alpha, a) && sl.byEquality =>
          Some(alpha.slice(lit.asInstanceOf[S], 0, alpha.length(lit.asInstanceOf[S])))
        case TokenIn(a, set) if sameAlphabet(alpha, a) =>
          // a one-token set matches that token and no other, so the capture is that token's slice
          a.singletonLiteralOf(set.asInstanceOf[a.TokenSet]).map(lit => alpha.slice(lit, 0, 1))
        case _ => None
      }

    /** the literal a parser both matches and returns the capture of, if it is one */
    def definiteSlice[S](p: Parser0[S, Any]): Option[(Alphabet[S], S)] =
      p match {
        case Map(under, ConstFn(res)) =>
          under match {
            case sl @ SeqLit(alpha, lit) if sl.byEquality =>
              val l = lit.asInstanceOf[S]
              if (sameValueAndType(alpha.slice(l, 0, alpha.length(l)), res)) Some((alpha, l))
              else None
            case TokenIn(alpha, set) =>
              alpha.singletonLiteralOf(set.asInstanceOf[alpha.TokenSet]) match {
                case Some(lit) if sameValueAndType(alpha.slice(lit, 0, 1), res) =>
                  Some((alpha, lit))
                case _ => None
              }
            case _ => None
          }
        case _ => None
      }

    /** does this parser return the slice it matched? */
    def matchesSlice[S](alpha: Alphabet[S])(p: Parser0[S, Any]): Boolean =
      p match {
        case SliceP0(a, _) => sameAlphabet(alpha, a)
        case SliceP(a, _) => sameAlphabet(alpha, a)
        case SeqIn(a, _) => sameAlphabet(alpha, a)
        case Length(a, _) => sameAlphabet(alpha, a)
        case TokensWhile(a, _) => sameAlphabet(alpha, a)
        case TokensWhile0(a, _) => sameAlphabet(alpha, a)
        case EmptySlice(a) => sameAlphabet(alpha, a)
        case Fail() | FailWith(_) => true
        case OneOf(ss) => ss.forall(matchesSlice(alpha))
        case OneOf0(ss) => ss.forall(matchesSlice(alpha))
        case WithContextP(_, p1) => matchesSlice(alpha)(p1)
        case WithContextP0(_, p1) => matchesSlice(alpha)(p1)
        case _ => definiteSlice(p).exists { case (a, _) => sameAlphabet(alpha, a) }
      }

    /** does this parser always succeed without consuming input? (a `Parser` never does, and by
      * construction a `oneOf0` never does either)
      */
    final def alwaysSucceeds[S](p: Parser0[S, Any]): Boolean =
      p match {
        case Index() | GetCaret() | Pure(_) | EmptySlice(_) => true
        case Map0(p1, _) => alwaysSucceeds(p1)
        case SoftProd0(a, b) => alwaysSucceeds(a) && alwaysSucceeds(b)
        case Prod0(a, b) => alwaysSucceeds(a) && alwaysSucceeds(b)
        case WithContextP0(_, p1) => alwaysSucceeds(p1)
        case WithSliceP0(_, parser) => alwaysSucceeds(parser)
        // by construction we never build a Not(Fail()), since that is just unit
        case _ => false
      }

    /** does this parser always eventually succeed, maybe consuming input? (a `Parser` has to
      * consume, but may consume an empty run, so it can't always succeed)
      */
    final def eventuallySucceeds[S](p: Parser0[S, Any]): Boolean =
      p match {
        case Index() | GetCaret() | Pure(_) | EmptySlice(_) | TokensWhile0(_, _) => true
        case Map0(p1, _) => eventuallySucceeds(p1)
        case SoftProd0(a, b) => eventuallySucceeds(a) && eventuallySucceeds(b)
        case Prod0(a, b) => eventuallySucceeds(a) && eventuallySucceeds(b)
        case WithContextP0(_, p1) => eventuallySucceeds(p1)
        case OneOf0(ps) => eventuallySucceeds(ps.last)
        case _ => false
      }

    /** '''if''' the parser succeeds, do we already know the result? (it may not always succeed) */
    final def hasKnownResult[S, A](p: Parser0[S, A]): Option[A] =
      p match {
        case Pure(a) => Some(a)
        case TokenIn(alpha, set) =>
          alpha
            .singletonLiteralOf(set.asInstanceOf[alpha.TokenSet])
            .map(lit => alpha.tokenAt(lit, 0).asInstanceOf[A])
        case Map0(_, fn) =>
          // scala 3.0.2 seems to fail if we inline this match above
          fn match {
            case ConstFn(a) => Some(a.asInstanceOf[A])
            // by construction, if the left hasKnownResult, the right is a ConstFn
            case _ => None
          }
        case Map(_, fn) =>
          fn match {
            case ConstFn(a) => Some(a.asInstanceOf[A])
            case _ => None
          }
        case SoftProd0(a, b) =>
          for {
            ra <- hasKnownResult(a)
            rb <- hasKnownResult(b)
          } yield (ra, rb).asInstanceOf[A]
        case Prod0(a, b) =>
          for {
            ra <- hasKnownResult(a)
            rb <- hasKnownResult(b)
          } yield (ra, rb).asInstanceOf[A]
        case SoftProd(a, b) =>
          for {
            ra <- hasKnownResult(a)
            rb <- hasKnownResult(b)
          } yield (ra, rb).asInstanceOf[A]
        case Prod(a, b) =>
          for {
            ra <- hasKnownResult(a)
            rb <- hasKnownResult(b)
          } yield (ra, rb).asInstanceOf[A]
        case OneOf(h :: t) =>
          val ra = hasKnownResult(h)
          if (ra.isDefined && t.forall { p1 => hasKnownResult(p1) == ra }) ra else None
        case OneOf0(h :: t) =>
          val ra = hasKnownResult(h)
          if (ra.isDefined && t.forall { p1 => hasKnownResult(p1) == ra }) ra else None
        case WithContextP(_, p1) => hasKnownResult(p1)
        case WithContextP0(_, p1) => hasKnownResult(p1)
        case Backtrack(p1) => hasKnownResult(p1)
        case Backtrack0(p1) => hasKnownResult(p1)
        case Not(_, _) | Peek(_) | Void(_) | Void0(_) | StartParser() | EndParser(_) |
            SeqLit(_, _) | IgnoreCase(_) =>
          // these are always unit
          someUnit.asInstanceOf[Option[A]]
        case Rep(_, _, _, _) | FlatMap0(_, _) | FlatMap(_, _) | TailRecM(_, _) | TailRecM0(_, _) |
            Defer(_) | Defer0(_) | GetCaret() | Index() | Length(_, _) | Fail() | FailWith(_) |
            TokensWhile(_, _) | TokensWhile0(_, _) | EmptySlice(_) | SliceP(_, _) | OneOf(Nil) |
            OneOf0(Nil) | SliceP0(_, _) | Select(_, _) | Select0(_, _) | SeqIn(_, _) |
            WithSliceP(_, _) | WithSliceP0(_, _) =>
          // these we don't know the value of, fundamentally or by construction
          None
      }

    /** @return true if this parser does not capture, so it is already the same as its void */
    def isVoided[S](p: Parser0[S, Any]): Boolean =
      p match {
        case Pure(a) => isUnit(a)
        case StartParser() | EndParser(_) | Void(_) | Void0(_) | IgnoreCase(_) | SeqLit(_, _) |
            Fail() | FailWith(_) | Not(_, _) | Peek(_) =>
          true
        case OneOf(ps) => ps.forall(isVoided(_))
        case OneOf0(ps) => ps.forall(isVoided(_))
        case WithContextP(_, p1) => isVoided(p1)
        case WithContextP0(_, p1) => isVoided(p1)
        case Backtrack(p1) => isVoided(p1)
        case Backtrack0(p1) => isVoided(p1)
        case Length(_, _) | SliceP(_, _) | SeqIn(_, _) | Prod(_, _) | SoftProd(_, _) | Map(_, _) |
            Select(_, _) | FlatMap(_, _) | TailRecM(_, _) | Defer(_) | Rep(_, _, _, _) |
            TokenIn(_, _) | TokensWhile(_, _) | TokensWhile0(_, _) | EmptySlice(_) | SliceP0(_, _) |
            Index() | GetCaret() | Prod0(_, _) | SoftProd0(_, _) | Map0(_, _) | Select0(_, _) |
            FlatMap0(_, _) | TailRecM0(_, _) | Defer0(_) | WithSliceP(_, _) | WithSliceP0(_, _) =>
          false
      }

    def expect1[S, A](p: Parser0[S, A]): Parser[S, A] =
      p match {
        case p1: Parser[S, A] => p1
        case notP1 =>
          // $COVERAGE-OFF$
          sys.error(s"violated invariant: $notP1 should be a Parser")
        // $COVERAGE-ON$
      }

    /** Remove trailing map functions, which would otherwise allocate results we are about to throw
      * away by voiding or slicing. This stops at a `SliceP` or a `Void`, which are markers that
      * everything below them has already been transformed.
      */
    def unmap0[S](pa: Parser0[S, Any]): Parser0[S, Any] =
      pa match {
        case p1: Parser[S, Any] => unmap(p1)
        case s if alwaysSucceeds(s) => Parser.unit
        case Map0(p, _) =>
          // we discard any allocations done by fn
          unmap0(p)
        case Select0(p, fn) => Select0(p, unmap0(fn))
        case SliceP0(_, s) =>
          // SliceP is added privately, and only after unmap0
          s
        case WithSliceP0(_, s) => unmap0(s)
        case Void0(v) =>
          // Void is added privately, and only after unmap0
          v
        case n @ Not(_, _) =>
          // not is already voided
          n
        case p @ Peek(_) =>
          // peek is already voided
          p
        case Backtrack0(p) =>
          // unmap0 may simplify enough to remove the backtrack wrapper
          Parser.backtrack0(unmap0(p))
        case OneOf0(ps) =>
          // Find the fixed point here
          val next = Optimizer.oneOf0Internal(ps.map(unmap0[S]))
          if (next == pa) pa
          else unmap0(next)
        case Prod0(p1, p2) =>
          unmap0(p1) match {
            case Prod0(p11, p12) =>
              // right associate so we can check matches a bit faster; p12 is already unmapped, so
              // we wrap with Void to prevent n^2 cost
              Prod0(p11, unmap0(Prod0(Void0(p12), p2)))
            case u1 if u1 eq Parser.unit =>
              unmap0(p2)
            case u1 =>
              val u2 = unmap0(p2)
              if (u2 eq Parser.unit) u1
              else Prod0(u1, u2)
          }
        case SoftProd0(p1, p2) =>
          unmap0(p1) match {
            case SoftProd0(p11, p12) =>
              SoftProd0(p11, unmap0(SoftProd0(Void0(p12), p2)))
            case u1 if u1 eq Parser.unit =>
              unmap0(p2)
            case u1 =>
              val u2 = unmap0(p2)
              if (u2 eq Parser.unit) u1
              else SoftProd0(u1, u2)
          }
        case Defer0(fn) =>
          fn match {
            case UnmapDefer0(_) => pa // already unmapped
            case _ => Defer0(UnmapDefer0(fn))
          }
        case WithContextP0(ctx, p0) => WithContextP0(ctx, unmap0(p0))
        case StartParser() | EndParser(_) | TokensWhile0(_, _) | TailRecM0(_, _) | FlatMap0(_, _) =>
          // we can't transform these significantly
          pa
        case Pure(_) | Index() | GetCaret() | EmptySlice(_) =>
          // unreachable: alwaysSucceeds above already answered for these
          Parser.unit
      }

    /** the [[unmap0]] of a parser known to consume input */
    def unmap[S](pa: Parser[S, Any]): Parser[S, Any] =
      pa match {
        case Map(p, _) =>
          // we discard any allocations done by fn
          unmap(p)
        case Select(p, fn) => Select(p, unmap0(fn))
        case SliceP(_, s) =>
          // SliceP is added privately, and only after unmap
          s
        case WithSliceP(_, s) => unmap(s)
        case Void(v) =>
          // Void is added privately, and only after unmap
          v
        case Backtrack(p) =>
          // unmap may simplify enough to remove the backtrack wrapper
          Parser.backtrack(unmap(p))
        case OneOf(ps) =>
          val next = Optimizer.oneOfInternal(ps.map(unmap[S]))
          if (next == pa) pa
          else unmap(next)
        case Prod(p1, p2) =>
          unmap0(p1) match {
            case Prod0(p11, p12) =>
              // right associate so we can check matches a bit faster; we wrap with Void to prevent
              // n^2 cost
              Prod(p11, unmap0(Parser.product0(p12.void, p2)))
            case Prod(p11, p12) =>
              Prod(p11, unmap0(Parser.product0(p12.void, p2)))
            case u1 if u1 eq Parser.unit =>
              // if unmap0(p1) is unit, p2 must be a Parser
              unmap(expect1(p2))
            case u1 =>
              val u2 = unmap0(p2)
              if (u2 eq Parser.unit) expect1(u1)
              else Prod(u1, u2)
          }
        case SoftProd(p1, p2) =>
          unmap0(p1) match {
            case SoftProd0(p11, p12) =>
              SoftProd(p11, unmap0(Parser.softProduct0(p12.void, p2)))
            case SoftProd(p11, p12) =>
              SoftProd(p11, unmap0(Parser.softProduct0(p12.void, p2)))
            case u1 if u1 eq Parser.unit =>
              unmap(expect1(p2))
            case u1 =>
              val u2 = unmap0(p2)
              if (u2 eq Parser.unit) expect1(u1)
              else SoftProd(u1, u2)
          }
        case Defer(fn) =>
          fn match {
            case UnmapDefer(_) => pa // already unmapped
            case _ => Defer(UnmapDefer(fn))
          }
        case Rep(p, min, max, _) => Rep(unmap(p), min, max, Accumulator0.unitAccumulator0)
        case WithContextP(ctx, p) => WithContextP(ctx, unmap(p))
        case TokenIn(_, _) | TokensWhile(_, _) | SeqLit(_, _) | SeqIn(_, _) | IgnoreCase(_) |
            Fail() | FailWith(_) | Length(_, _) | TailRecM(_, _) | FlatMap(_, _) =>
          // we can't transform these significantly
          pa
      }

    //////////////////////////////////////////////////////////////////////
    // Leaves
    //////////////////////////////////////////////////////////////////////

    final case class Pure[S, A](result: A) extends Parser0[S, A] {
      override def parseMut(state: State[S]): A = result
    }

    final case class SeqLit[S](alpha: Alphabet[S], lit: S) extends Parser[S, Unit] {
      private[this] val len: Int = alpha.length(lit)
      require(len > 0, "we need a non-empty literal to expect a match")

      /** See [[Impl.exactLiteral]]: when true, `startsWithAt` may answer for the whole literal.
        * This is (slightly stronger than) the precondition of
        * `AlphabetLaws.singletonPatternCoherent`, which is what makes the two paths agree; the
        * optimizer also reads it to decide whether this literal's capture is a known constant.
        */
      val byEquality: Boolean = Impl.exactLiteral(alpha)(lit)

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

    /** Char-only residue, typed at the char instantiation and only ever built by the `cats.parse`
      * facade's `ignoreCase`: `String.regionMatches`' case-insensitive comparison is not a
      * [[Alphabet.pattern]] (it folds pairs the per-position sets can't name), so it stays its own
      * leaf. It lives here rather than in `cats.parse` only because [[Parser0]] is sealed.
      */
    final case class IgnoreCase(message: String) extends Parser[String, Unit] {
      require(message.nonEmpty, "we need a non-empty string to expect a message")

      override def parseMut(state: State[String]): Unit = {
        val offset = state.offset
        if (state.input.regionMatches(true, offset, message, 0, message.length)) {
          state.offset += message.length
        } else {
          state.error = Eval.later(Chain.one(Expectation.OneOfSeq(offset, message :: Nil)))
        }
        ()
      }
    }

    /** Char-only residue, as [[IgnoreCase]] is, and typed at the char instantiation for the same
      * reason: line and column are not a generic notion. It builds the [[LocationMap]] on first use
      * and parks it in `State`'s slot, so repeated carets within one parse share one map.
      */
    final case class GetCaret() extends Parser0[String, Caret] {
      override def parseMut(state: State[String]): Caret = {
        var lm = state.locationMap
        if (lm eq null) {
          lm = LocationMap(state.input)
          state.locationMap = lm
        }
        // this unsafe call is safe because the offset can never go too far
        lm.toCaretUnsafe(state.offset)
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
      private[this] val matcher: SeqMatcher[S, Sl] = alpha.seqMatcher(sorted)
      private[this] val alts: List[S] = sorted.toList

      /* Capture decides first, so each mode makes exactly one matcher call: the capturing branch
       * takes the matched region from the matcher (which for an equality alphabet already holds it
       * -- see SeqMatcher.sliceAt) and recovers the end offset from its length, rather than
       * matching for an end offset and then slicing the input again. The voided branch keeps the
       * offset-only instructions it has always had. */
      override def parseMut(state: State[S]): Sl =
        if (state.capture) {
          val offset = state.offset
          val sl = matcher.sliceAt(state.input, offset)
          if (sl == null) failAt(state, offset)
          else {
            state.offset = offset + alpha.sliceLength(sl)
            sl
          }
        } else {
          val offset = state.offset
          val end = matcher.matchAt(state.input, offset)
          if (end < 0) failAt(state, offset)
          else {
            state.offset = end
            null.asInstanceOf[Sl]
          }
        }

      private[this] def failAt(state: State[S], offset: Int): Sl = {
        state.error = Eval.later(Chain.one(Expectation.OneOfSeq(offset, alts)))
        null.asInstanceOf[Sl]
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
      if (state.error eq null) alpha.slice(state.input, init, state.offset)
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
        // read the offset now, into the closure: state.offset is mutable, and a soft product that
        // rewinds before this error is forced would otherwise report the rewound position
        val offset = state.offset
        state.error = Eval.later(Chain.one(Expectation.Fail(offset)))
        null.asInstanceOf[A]
      }

      def widen[B]: Parser[S, B] = this.asInstanceOf[Parser[S, B]]
    }

    final case class FailWith[S, A](message: String) extends Parser[S, A] {
      override def parseMut(state: State[S]): A = {
        val offset = state.offset
        state.error = Eval.later(Chain.one(Expectation.FailWith(offset, message)))
        null.asInstanceOf[A]
      }

      def widen[B]: Parser[S, B] = this.asInstanceOf[Parser[S, B]]
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

  /** char's `.string`/`.withString` syntax. It lives in this companion — rather than with the rest
    * of the char facade in `cats.parse` — because the companion of the receiver's type is the only
    * implicit scope every char call site sees, which is what keeps the generalization invisible to
    * char users who never import anything new (spec S3.1).
    */
  implicit def catsParseStringSyntax0[A](
      parser: Parser0[String, A]
  ): cats.parse.Parser.StringSyntax0[A] =
    new cats.parse.Parser.StringSyntax0(parser)

  /** the [[catsParseStringSyntax0]] refined for a parser known to consume input */
  implicit def catsParseStringSyntax[A](
      parser: Parser[String, A]
  ): cats.parse.Parser.StringSyntax[A] =
    new cats.parse.Parser.StringSyntax(parser)
}
