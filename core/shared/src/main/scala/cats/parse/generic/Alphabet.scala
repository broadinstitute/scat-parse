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

import scala.collection.immutable.SortedSet

/** The typeclass the generic parser machinery is written against: everything the library needs to
  * know about an input type `S` in order to parse it.
  *
  * `Char`/`String` is one instance ([[StringAlphabet]]); instances over other token types (for
  * example byte-encoded alphabets with non-injective matching) plug in here.
  *
  * ==Instance-authoring contract==
  *
  * This scaladoc is the normative source for instance authors; run [[AlphabetLaws]] against any new
  * instance as the acceptance suite. The members are grouped in three sections:
  *
  *   - '''Hot core''': called on every parse step. These methods take and return primitives or
  *     `S`/`Slice` values; the one exception is [[tokenAt]], which is the capture-one-token
  *     operation and so is reached only where a token parser actually keeps its token. ''Matching''
  *     never sees a `Token`, which is what lets `Token` box. Bulk operations live on the instance
  *     so their loops JIT monomorphically.
  *   - '''Cold error section''': called only when building or rendering parse errors.
  *   - '''Cold optimizer section''': called only at parser construction time.
  *
  * ==Instance identity==
  *
  * Fusion (the `oneOf`/`seqIn` optimizer) recovers the owning instance from the leaves it merges
  * and checks both sides share one alphabet before applying a cold-set rule (falling back from `eq`
  * to `equals`). Instances should be a singleton `object` (as [[StringAlphabet]] is) or otherwise
  * have a lawful `equals`, or fusion across two "equal" instances built independently will silently
  * not apply.
  *
  * ==Matching is membership==
  *
  * A parser matches input one position at a time by asking whether the token at that position is a
  * member of a [[TokenSet]]. Any richer "satisfies" relation (for example bitmask containment) is
  * expressed entirely by how an instance builds its sets — in particular by [[pattern]], which
  * converts a literal into the per-position sets it accepts.
  */
abstract class Alphabet[S] extends Serializable {

  /** The individual token type (e.g. `Char`). Values of this type may box; see [[tokenAt]]. */
  type Token

  /** An opaque set of tokens: only this instance interprets it. Instances choose a compact
    * representation (bitset and ranges for char, a small bitmask for small alphabets).
    */
  type TokenSet

  /** The type of captured input windows, returned by [[slice]] and by slice-capturing parsers.
    * Instances should give `Slice` a lawful `equals`. The char instance fixes `Slice = String`.
    */
  type Slice

  //////////////////////////////////////////////////////////////////////
  // Hot core: called on every parse step. Primitives in, primitives out -- except tokenAt.
  //////////////////////////////////////////////////////////////////////

  /** @return the number of tokens in `s` */
  def length(s: S): Int

  /** Membership of the token at position `i` of `s` in `set`.
    *
    * Must return `false` when `i >= length(s)`; behavior for negative `i` is unspecified (callers
    * pass `i >= 0`).
    *
    * @return
    *   true if the token at `s(i)` is a member of `set`
    */
  def matchesAt(set: TokenSet, s: S, i: Int): Boolean

  /** Bulk scan: the first index `i >= from` such that `matchesAt(set, s, i)` is false (which is
    * `length(s)` if the set matches to the end). The loop lives on the instance so it JITs
    * monomorphically.
    *
    * @return
    *   the end offset (exclusive) of the run of members of `set` starting at `from`
    */
  def scanWhile(set: TokenSet, s: S, from: Int): Int

  /** Literal prefix test: whether the tokens of `lit` occur verbatim (token equality) in `s`
    * starting at `offset`. This is the `regionMatches` fast path used when a literal's [[pattern]]
    * is all singleton sets; it is not the place to implement a non-injective satisfies relation
    * (that belongs in [[pattern]]).
    *
    * Must return `false` when `offset + length(lit) > length(s)` or `offset < 0`.
    *
    * @return
    *   true if `s` contains `lit` verbatim at `offset`
    */
  def startsWithAt(s: S, offset: Int, lit: S): Boolean

  /** Capture the window `[from, until)` of `s`. Instances choose their capture policy: char copies
    * (`substring`), a view-shaped `S` can be zero-copy.
    *
    * @return
    *   the captured window as a [[Slice]]
    */
  def slice(s: S, from: Int, until: Int): Slice

  /** The token at position `i` of `s` — the single-token analogue of [[slice]], and the only member
    * of this section that returns a [[Token]].
    *
    * On the parse path, but only where a token parser keeps its token: `tokenIn`/`tokenWhere` reach
    * it when they capture, and a voided or non-capturing one never does. That narrow reach is what
    * lets `Token` box, and why ''matching'' goes through [[matchesAt]]/[[scanWhile]] instead. The
    * optimizer and [[AlphabetLaws]] also call it, cold.
    *
    * @return
    *   the token at `s(i)` (requires `0 <= i < length(s)`)
    */
  def tokenAt(s: S, i: Int): Token

  //////////////////////////////////////////////////////////////////////
  // Cold error section: called only when building or rendering errors.
  //////////////////////////////////////////////////////////////////////

  /** Decompose a failed set-membership test into this instance's expectation cases (subclasses of
    * [[Expectation.OfAlphabet]]). The char instance emits one `InRange` per contiguous range.
    *
    * @return
    *   the expectations describing `set`, all at `offset`
    */
  def expectSet(offset: Int, set: TokenSet): NonEmptyList[Expectation[S]]

  /** Merge this instance's own expectation cases collected at one (offset, context) during
    * [[Expectation.unify]] — the analogue of char's range merging (adjacent/overlapping `InRange`s
    * collapse). Cases the instance does not recognize must be passed through unchanged.
    *
    * @return
    *   the merged cases
    */
  def mergeOfAlphabet(
      cases: List[Expectation.OfAlphabet[S]]
  ): List[Expectation.OfAlphabet[S]]

  /** Ordering of literals, used to sort and dedup the alternatives of [[Expectation.OneOfSeq]].
    */
  def orderingS: Ordering[S]

  /** Order over this instance's own expectation cases, used by the generic `Order[Expectation[S]]`.
    * The instance owns totality for the whole `OfAlphabet` branch: two distinct values must never
    * compare equal, including cases the instance did not define (falling back to a `toString`
    * comparison is acceptable there).
    */
  def orderOfAlphabet: Order[Expectation.OfAlphabet[S]]

  /** Show for this instance's own expectation cases, used by the generic `Show[Expectation[S]]`.
    */
  def showOfAlphabet: Show[Expectation.OfAlphabet[S]]

  /** Render a literal for error messages (e.g. char wraps in double quotes). */
  def showLiteral(s: S): String

  /** Render the input context around a failure offset for error display, with `errorMsg` (the
    * already-rendered expectation summary) placed inside the context block where the instance wants
    * it. The char instance renders the line/caret block via `LocationMap`; the default is `None`,
    * which makes error display offset-only.
    *
    * @return
    *   the full rendered error display, or None to fall back to `errorMsg` alone
    */
  def renderContext(input: S, offset: Int, errorMsg: String): Option[String] = {
    // discard the arguments: the default renders no context (offset-only errors)
    val _ = (input, offset, errorMsg)
    None
  }

  /** Capture the window `[from, until)` of `s` as an `S`, for the rare error case that must carry a
    * matched sub-input rather than a [[Slice]] (`unary_!`'s [[Expectation.ExpectedFailureAt]]).
    * Cold-path only. Instances typically implement this exactly as [[slice]], modulo the result
    * type (char: `substring` either way).
    *
    * @return
    *   the window `[from, until)` of `s`, as an `S`
    */
  def subInput(s: S, from: Int, until: Int): S

  //////////////////////////////////////////////////////////////////////
  // Cold optimizer section: called only at parser construction time.
  //////////////////////////////////////////////////////////////////////

  /** @return the set containing the members of both `a` and `b` */
  def union(a: TokenSet, b: TokenSet): TokenSet

  /** @return the set containing every token */
  def universal: TokenSet

  /** Cold membership test by token (may box; the hot path uses [[matchesAt]]).
    *
    * @return
    *   true if `t` is a member of `set`
    */
  def contains(set: TokenSet, t: Token): Boolean

  /** Convert a literal into its pattern: one [[TokenSet]] per position, such that the literal
    * matches input at an offset exactly when every position's set matches (see [[matchesAt]]). For
    * an equality alphabet like char every set is a singleton; a non-injective instance returns the
    * set of all input tokens satisfying each literal token.
    *
    * @return
    *   the per-position token sets of `lit` (empty when `length(lit) == 0`)
    */
  def pattern(lit: S): List[TokenSet]

  /** The set of the tokens satisfying `p` — the instance enumerates its own token domain, so that
    * neither the size of that domain nor the type of a token leaks into the generic layer. Backs
    * `tokenWhere`/`tokensWhile`; called once per parser construction.
    *
    * @return
    *   the set of tokens `t` with `p(t)`, or None if no token satisfies `p` (instances need not
    *   represent an empty set)
    */
  def setWhere(p: Token => Boolean): Option[TokenSet]

  /** @return true if every member of `a` is a member of `b` */
  def subsetOf(a: TokenSet, b: TokenSet): Boolean

  /** @return true if `a` and `b` share at least one member */
  def intersects(a: TokenSet, b: TokenSet): Boolean

  /** Enumerate the members of `set` as single-token literals — the expansion used by the optimizer
    * to rewrite set alternations into literal alternations.
    *
    * @return
    *   one length-1 literal per member of `set`
    */
  def literalsOf(set: TokenSet): List[S]

  /** The sole member of `set`, as a length-1 literal. A one-token set matches that token and no
    * other, which is what lets the optimizer treat such a parser's result and capture as known
    * constants — so this is asked of every `tokenIn` the optimizer touches, and instances whose
    * [[literalsOf]] is expensive (char's `universal` enumerates 65536 literals) should override it
    * with a cheap size test.
    *
    * @return
    *   the single member of `set`, or None when `set` has more than one
    */
  def singletonLiteralOf(set: TokenSet): Option[S] =
    literalsOf(set) match {
      case lit :: Nil => Some(lit)
      case _ => None
    }

  /** Build the matcher used by multi-literal alternation (`seqIn`). Built cold at parser
    * construction; the hot side is one [[SeqMatcher.matchAt]] call per attempt. The default is the
    * naive linear reference ([[SeqMatcher.naive]]); instances override for speed but must agree
    * with the reference ([[AlphabetLaws]] checks this).
    *
    * @return
    *   a longest-match matcher over `alts`
    */
  def seqMatcher(alts: SortedSet[S]): SeqMatcher[S] =
    SeqMatcher.naive(this, alts)
}

object Alphabet {

  /** Refinement alias fixing the `Slice` member — load-bearing for char-invisibility: the char
    * instance is published at `Aux[String, String]` so `parse` results still infer as `(String, A)`
    * for char users.
    */
  type Aux[S0, Slice0] = Alphabet[S0] { type Slice = Slice0 }

  def apply[S](implicit alpha: Alphabet[S]): alpha.type = alpha

  implicit val stringInstance: Aux[String, String] = StringAlphabet
}
