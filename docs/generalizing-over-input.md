# Generalizing over input

cats-parse parses `String`, but the engine underneath does not care what a token is. Every parser is
written against an `Alphabet[S]` — the typeclass holding everything the machinery needs to know about
an input type `S` — and `Char`/`String` is simply one instance of it. Supply another instance and the
whole combinator surface (`~`, `oneOf`, `rep`, `soft`, `slice`, backtracking, error reporting) works
over your own token type, unchanged.

Nothing about char parsing moves. `cats.parse.Parser0[A]` and `cats.parse.Parser[A]` are aliases for
`cats.parse.generic.Parser0[String, A]` and `cats.parse.generic.Parser[String, A]` at the built-in
`StringAlphabet`, so existing code compiles as it did. Code that is generic over the input names the
type explicitly: `generic.Parser[S, A]`.

# Alphabet at a glance

An instance fixes three type members:

| Member | Meaning |
| --- | --- |
| `Token` | one token (`Char` for the string instance). May box: matching never sees one, and only `tokenAt` returns one. |
| `TokenSet` | an opaque set of tokens, interpreted only by the instance. Choose a compact representation. |
| `Slice` | a captured window of input, returned by `slice` and by slice-capturing parsers. |

and three groups of methods, split by how often they are called:

- **Hot core** — `length`, `matchesAt`, `scanWhile`, `startsWithAt`, `slice`, `tokenAt`. Called on
  every parse step, so they take and return primitives, `S`, or `Slice`. The exception is `tokenAt`,
  which captures one token and is the only member that returns a `Token`; a parser reaches it only
  when it keeps that token, which is why `Token` is allowed to box. Bulk operations such as
  `scanWhile` live on the instance so their loops compile monomorphically.
- **Cold error section** — `expectSet`, `mergeOfAlphabet`, `orderingS`, `orderOfAlphabet`,
  `showOfAlphabet`, `showLiteral`, `renderContext`, `subInput`. Reached only when a parse error is
  built or rendered.
- **Cold optimizer section** — `union`, `universal`, `contains`, `pattern`, `setWhere`, `subsetOf`,
  `intersects`, `literalsOf`, `singletonLiteralOf`, `seqMatcher`. Reached only at parser
  construction time.

Matching is always *membership*: a parser asks whether the token at a position belongs to a
`TokenSet`. A richer "satisfies" relation — a bitmask containment, a wildcard, a case-insensitive
token — is expressed by how the instance builds its sets, chiefly in `pattern`, which turns a
literal into the per-position sets that literal accepts.

The `Alphabet` scaladoc is the normative contract: it carries the per-member obligations this page
only sketches. Read it before writing an instance.

# A worked example

Suppose the input is not text but a vector of small integer tokens — the output of a lexer, say,
where each token is a code in `0` to `9`. Here is a complete `Alphabet` for it.

```scala mdoc:silent
import cats.parse.generic.{Alphabet, Expectation}
import cats.{Order, Show}
import cats.data.NonEmptyList

/** The one expectation case this alphabet reports: "expected one of these codes here". */
final class ExpectedCodes(val offset: Int, val set: Set[Int])
    extends Expectation.OfAlphabet[Vector[Int]] {
  // canonical, so that two equal expectations render (and therefore order) identically
  override def toString: String =
    s"ExpectedCodes($offset, ${set.toList.sorted.mkString("{", ",", "}")})"
}

object CodeAlphabet extends Alphabet[Vector[Int]] {
  type Token = Int
  type TokenSet = Set[Int]
  type Slice = Vector[Int]

  /** The whole token domain: valid input holds only these. `universal` is it, and `setWhere`
    * enumerates it, so it has to be finite.
    */
  private val domain: Set[Int] = (0 to 9).toSet

  // --- hot core ---

  def length(s: Vector[Int]): Int = s.length

  def matchesAt(set: Set[Int], s: Vector[Int], i: Int): Boolean =
    (i < s.length) && set(s(i))

  def scanWhile(set: Set[Int], s: Vector[Int], from: Int): Int = {
    var i = from
    while ((i < s.length) && set(s(i))) {
      i += 1
    }
    i
  }

  def startsWithAt(s: Vector[Int], offset: Int, lit: Vector[Int]): Boolean =
    (offset >= 0) && ((offset + lit.length) <= s.length) && s.startsWith(lit, offset)

  def slice(s: Vector[Int], from: Int, until: Int): Vector[Int] = s.slice(from, until)

  // --- cold error section ---

  def expectSet(offset: Int, set: Set[Int]): NonEmptyList[Expectation[Vector[Int]]] =
    NonEmptyList.one(new ExpectedCodes(offset, set))

  // merging is optional; this instance keeps its cases as they come
  def mergeOfAlphabet(
      cases: List[Expectation.OfAlphabet[Vector[Int]]]
  ): List[Expectation.OfAlphabet[Vector[Int]]] = cases

  val orderingS: Ordering[Vector[Int]] = Ordering.Implicits.seqOrdering[Vector, Int]

  val orderOfAlphabet: Order[Expectation.OfAlphabet[Vector[Int]]] = Order.by(_.toString)

  val showOfAlphabet: Show[Expectation.OfAlphabet[Vector[Int]]] = Show.fromToString

  def showLiteral(s: Vector[Int]): String = s.mkString("[", " ", "]")

  def tokenAt(s: Vector[Int], i: Int): Int = s(i)

  def subInput(s: Vector[Int], from: Int, until: Int): Vector[Int] = s.slice(from, until)

  // --- cold optimizer section ---

  def union(a: Set[Int], b: Set[Int]): Set[Int] = a.union(b)

  val universal: Set[Int] = domain

  def contains(set: Set[Int], t: Int): Boolean = set(t)

  def pattern(lit: Vector[Int]): List[Set[Int]] = lit.toList.map(Set(_))

  def setWhere(p: Int => Boolean): Option[Set[Int]] = {
    val set = domain.filter(p)
    if (set.isEmpty) None else Some(set)
  }

  def subsetOf(a: Set[Int], b: Set[Int]): Boolean = a.subsetOf(b)

  def intersects(a: Set[Int], b: Set[Int]): Boolean = a.exists(b.contains)

  def literalsOf(set: Set[Int]): List[Vector[Int]] = set.toList.sorted.map(Vector(_))
}
```

A few details are worth pointing at.

**The token domain is declared, and finite.** `Token` is `Int`, but this alphabet's tokens are the
codes `0` to `9`: that is what `universal` returns and what `setWhere` enumerates. Input holding
anything else is not input for this alphabet, and `AlphabetLaws.universalMatches` would say so. An
alphabet over an unbounded token type has to bound its domain somewhere, because `setWhere` has to
answer "which tokens satisfy this predicate" without the generic layer knowing what a token is; here
is where.

**`slice` and `subInput` are the same method twice.** They are both "capture the window
`[from, until)`", differing only in result type — `Slice` and `S`. They coincide here because this
instance sets `Slice = S`; the char instance is `substring` either way. `subInput` exists for the
one error case that has to carry a matched sub-input rather than a capture.

**Three members are not implemented, because they have usable defaults.** `renderContext` returns
`None`, which makes errors offset-only rather than showing a line and a caret; `singletonLiteralOf`
falls back to `literalsOf`, which an instance with an expensive enumeration should override with a
size test; and `seqMatcher` returns the naive longest-match reference, which is correct but linear
in the alternatives. An instance can ship without any of them and add them when the shape or the
profile asks for it.

`mergeOfAlphabet` returns its argument. Merging is an optimization — the char instance collapses
adjacent `InRange` cases into one — and an instance is free to skip it. The one hard rule is that
cases the instance does not recognize must pass through unchanged.

`pattern` returns one singleton set per position, which is what makes this an *equality* alphabet:
a literal matches only itself. An alphabet where one input token satisfies several literal tokens
returns wider sets here, and gets that behaviour everywhere — `seq`, `seqIn`, and the optimizer all
go through `pattern`.

The instance is a singleton `object`. The optimizer recovers the owning alphabet from the leaves it
fuses and checks both sides share one, so an instance built twice at two call sites would silently
stop fusing. A singleton (or a lawful `equals`) avoids that.

Last, an artifact of this page rather than of the design: `ExpectedCodes` would be a top-level
`final case class` in real code. It is a plain class here only because every snippet
below is compiled inside a method, where the `equals` a case class generates cannot check its outer
reference.

Publish it implicitly, using the `Aux` alias so that `Slice` stays visible in inferred types:

```scala mdoc:silent
implicit val codeAlphabet: Alphabet.Aux[Vector[Int], Vector[Int]] = CodeAlphabet
```

Now the ordinary combinators work over `Vector[Int]`:

```scala mdoc:silent
import cats.parse.generic.Parser

val code: Parser[Vector[Int], Int] = Parser.tokenIn(CodeAlphabet)(Set(1, 2, 3))

val lowCodes: Parser[Vector[Int], Vector[Int]] = Parser.tokensWhile(CodeAlphabet)(_ < 5)

val opcode: Parser[Vector[Int], Vector[Int]] =
  Parser.seqIn(List(Vector(1, 2), Vector(1, 2, 3)))
```

```scala mdoc
code.parse(Vector(2, 9))

code.parse(Vector(9))

lowCodes.parse(Vector(1, 2, 3, 7, 0))

opcode.parse(Vector(1, 2, 3, 9))

(Parser.seq(Vector(1, 2)) ~ lowCodes).parse(Vector(1, 2, 0, 4, 8))
```

The error from the failing `code.parse` above carries `ExpectedCodes` — the case the instance
defined — which is how a domain-specific alphabet gets domain-specific error messages out of the
generic machinery.

# Checking your instance

`AlphabetLaws` is the acceptance suite: a set of pure functions, each returning `Right(())` when the
law holds and `Left(description)` when it does not, with no test-framework dependency. Run them from
whatever harness you use, over well-distributed samples.

```scala mdoc
import cats.parse.generic.AlphabetLaws

AlphabetLaws.scanWhileConsistent(CodeAlphabet)(Set(1, 2), Vector(1, 2, 3), 0)

AlphabetLaws.patternSelfMatch(CodeAlphabet)(Vector(4, 2))

AlphabetLaws.startsWithAtConsistent(CodeAlphabet)(Vector(1, 2, 3), 1, Vector(2, 3))

AlphabetLaws.universalMatches(CodeAlphabet)(Vector(0, 9, 4))

val alts =
  scala.collection.immutable.SortedSet(Vector(1, 2), Vector(1, 2, 3))(CodeAlphabet.orderingS)

AlphabetLaws.seqMatcherAgreesWithNaive(CodeAlphabet)(alts, Vector(1, 2, 3), 0)
```

An instance that passes every law honors the contract the parser machinery relies on.
