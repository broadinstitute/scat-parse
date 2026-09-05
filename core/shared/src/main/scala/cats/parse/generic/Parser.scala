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
import cats.parse.LocationMap

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
  def oneOf[S, A](parsers: List[Parser[S, A]]): Parser[S, A] = {
    // char's oneOf(Nil) is Fail, which has no leaf until the full surface lands
    require(parsers.nonEmpty, "oneOf requires a non-empty list of parsers")
    parsers match {
      case single :: Nil => single
      case many => Impl.OneOf(many)
    }
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
      state.error = errs
      null.asInstanceOf[A]
    }

    final case class OneOf[S, A](all: List[Parser[S, A]]) extends Parser[S, A] {
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
