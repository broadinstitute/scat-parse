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

package cats

/** The char parsers are the generic engine at one alphabet.
  *
  * `Parser0`/`Parser` are aliases for [[cats.parse.generic.Parser0]]/[[cats.parse.generic.Parser]]
  * instantiated at [[cats.parse.generic.StringAlphabet]], whose `Slice` is `String` — so a char
  * parser's `parse` still infers `(String, A)`, and every method a char user calls still returns
  * the type it always did. `object Parser` (in `Parser.scala`) is the char facade over the generic
  * combinators; `.string`/`.withString` come from implicit conversions in
  * [[cats.parse.generic.Parser0]]'s companion, which is the one implicit scope every char call site
  * sees.
  */
package object parse {

  /** A char parser that may consume no input. */
  type Parser0[+A] = generic.Parser0[String, A]

  /** A char parser that always consumes at least one character when it succeeds. */
  type Parser[+A] = generic.Parser[String, A]
}
