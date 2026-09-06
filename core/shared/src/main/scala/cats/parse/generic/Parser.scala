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

import cats.Eval
import cats.data.{Chain, NonEmptyList}
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

  /** @return a parser repeating this one one or more times */
  def rep: Parser[S, NonEmptyList[A]] = repAs[NonEmptyList[A]]

  /** @return a parser repeating this one at least `min` (which must be `>= 1`) times */
  def rep(min: Int): Parser[S, NonEmptyList[A]] = repAs[NonEmptyList[A]](min)

  /** @return a parser repeating this one zero or more times */
  def rep0: Parser0[S, List[A]] = repAs0[List[A]]

  /** @return a parser repeating this one at least `min` (which must be `>= 0`) times */
  def rep0(min: Int): Parser0[S, List[A]] =
    if (min == 0) rep0 else repAs(min)

  /** @return a parser repeating this one one or more times, accumulated by `acc` */
  def repAs[B](implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repAs(this, min = 1)(acc)

  /** @return a parser repeating this one at least `min` times, accumulated by `acc` */
  def repAs[B](min: Int)(implicit acc: Accumulator[A, B]): Parser[S, B] =
    Parser.repAs(this, min = min)(acc)

  /** @return a parser repeating this one zero or more times, accumulated by `acc` */
  def repAs0[B](implicit acc: Accumulator0[A, B]): Parser0[S, B] =
    Parser.repAs0(this)(acc)
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

  /** @return a parser repeating `p1` zero or more times */
  def repAs0[S, A, B](p1: Parser[S, A])(implicit acc: Accumulator0[A, B]): Parser0[S, B] =
    Impl.OneOf0(
      Impl.Rep(p1, 1, Int.MaxValue, acc) ::
        pure[S, B](acc.newAppender().finish()) ::
        Nil
    )

  /** Try each parser in order, taking the first that succeeds. A parser that fails having consumed
    * input stops the search (an arresting failure); one that fails without consuming lets the next
    * alternative run.
    *
    * The alternatives are kept as-is: no fusion into set unions or multi-literal dispatch happens
    * yet, so this is sound but unoptimized.
    *
    * @return
    *   the left-biased alternation of `parsers`
    */
  def oneOf[S, A](parsers: List[Parser[S, A]]): Parser[S, A] =
    parsers match {
      case Nil => fail
      case single :: Nil => single
      case many => Impl.OneOf(many)
    }

  /** @return the left-biased alternation of `parsers`, which may consume no input */
  def oneOf0[S, A](parsers: List[Parser0[S, A]]): Parser0[S, A] =
    parsers match {
      case Nil => fail
      case single :: Nil => single
      case many => Impl.OneOf0(many)
    }

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
  }
}
