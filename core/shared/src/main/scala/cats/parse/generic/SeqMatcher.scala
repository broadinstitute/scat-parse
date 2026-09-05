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

import scala.collection.immutable.SortedSet

/** A matcher for a fixed set of literal alternatives, built cold at parser construction time.
  *
  * The contract is '''longest match''' under the owning alphabet's literal-to-pattern semantics
  * (see [[Alphabet.pattern]]): of all alternatives whose pattern matches at `offset`, the one
  * consuming the most input wins.
  *
  * Preconditions (guaranteed by callers in this library): the alternatives are non-empty, no
  * alternative is an empty literal, and `matchAt` is called with `offset >= 0`.
  */
abstract class SeqMatcher[S] extends Serializable {

  /** @return
    *   the end offset (exclusive) of the longest alternative matching in `input` at `offset` (which
    *   must be `>= 0`), or -1 if none matches
    */
  def matchAt(input: S, offset: Int): Int
}

object SeqMatcher {

  /** The naive linear longest-match reference implementation: correct for any lawful alphabet,
    * O(alternatives x alternative-length) per attempt. Instances override [[Alphabet.seqMatcher]]
    * only for speed; [[AlphabetLaws]] checks agreement with this reference.
    */
  def naive[S](alpha: Alphabet[S], alts: SortedSet[S]): SeqMatcher[S] =
    new SeqMatcher[S] {
      private[this] val patterns: List[List[alpha.TokenSet]] =
        alts.toList.map(alpha.pattern(_))

      def matchAt(input: S, offset: Int): Int = {
        var best = -1
        var rest = patterns
        while (rest.nonEmpty) {
          var sets = rest.head
          var i = 0
          var ok = true
          while (ok && sets.nonEmpty) {
            ok = alpha.matchesAt(sets.head, input, offset + i)
            sets = sets.tail
            i += 1
          }
          if (ok && (offset + i) > best) best = offset + i
          rest = rest.tail
        }
        best
      }
    }
}
