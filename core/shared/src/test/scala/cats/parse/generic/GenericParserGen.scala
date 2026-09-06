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

import cats.{Defer, Eval, FlatMap, Monad, MonoidK}
import cats.parse.GenT
import cats.parse.ParserGen.{biasSmall, functorGen}
import org.scalacheck.{Arbitrary, Cogen, Gen}

/** The generic form of `cats.parse.ParserGen` (spec S8): the gen0/gen tables ported node for node
  * so every generic `Parser.Impl` node is constructible, with the alphabet-specific pieces --
  * `Gen[Token]`, `Gen[TokenSet]`, `Gen[S]` -- left to the instance.
  *
  * `GenT` itself is reused from `cats.parse` rather than copied: it is already generic in `F[_]`,
  * so the char suite's 12 pinned files stay byte-for-byte unchanged (this only reads them).
  *
  * The two char-only leaves (`Impl.IgnoreCase`, `Impl.GetCaret`) are out of reach here by
  * construction -- they are built by the char facade, not the generic companion -- and stay covered
  * by `cats.parse.ParserTest`.
  */
abstract class GenericParserGen[S] {
  val alpha: Alphabet[S]

  type P0[A] = Parser0[S, A]
  type P1[A] = Parser[S, A]
  type Tok = alpha.Token
  type Sl = alpha.Slice

  //////////////////////////////////////////////////////////////////////
  // What an instance supplies
  //////////////////////////////////////////////////////////////////////

  /** Inputs and literals: a small token space, so a random parser has a real chance of matching. */
  def genInput: Gen[S]

  /** Non-empty token sets, biased toward the ambiguity the alphabet allows. */
  def genTokenSet: Gen[alpha.TokenSet]

  /** Predicates for `tokenWhere`/`tokensWhile`, which reach `Alphabet.setWhere`. */
  def genTokenPred: Gen[Tok => Boolean]

  implicit def cogenToken: Cogen[Tok]

  implicit def cogenSlice: Cogen[Sl]

  //////////////////////////////////////////////////////////////////////
  // Leaves
  //////////////////////////////////////////////////////////////////////

  private def arbGen[A: Arbitrary: Cogen]: GenT[Gen] =
    GenT(Arbitrary.arbitrary[A])

  /** Result values, all alphabet-independent. */
  lazy val pures: Gen[GenT[Gen]] =
    Gen.oneOf(arbGen[Int], arbGen[Boolean], arbGen[(Int, Int)])

  private def widen(g: GenT[P1]): GenT[P0] =
    GenT[P0, g.A](g.fa)(g.cogen)

  lazy val seqLit: Gen[GenT[P1]] =
    genInput.map { lit =>
      // a literal must consume, so an empty one is `fail` -- the same guard char's `expect1` makes
      if (alpha.length(lit) == 0) GenT[P1, Unit](Parser.fail[S, Unit])
      else GenT[P1, Unit](Parser.seq(lit)(alpha))
    }

  lazy val seqLit0: Gen[GenT[P0]] =
    genInput.map { lit =>
      if (alpha.length(lit) == 0) GenT[P0, Unit](Parser.unit[S])
      else GenT[P0, Unit](Parser.seq(lit)(alpha))
    }

  lazy val tokenIn: Gen[GenT[P1]] =
    Gen.oneOf(
      genTokenSet.map { set => GenT[P1, Tok](Parser.tokenIn(alpha)(set)) },
      Gen.const(GenT[P1, Tok](Parser.anyToken(alpha))),
      genTokenPred.map { fn => GenT[P1, Tok](Parser.tokenWhere(alpha)(fn)) }
    )

  lazy val tokensIn: Gen[GenT[P1]] =
    Gen.oneOf(
      genTokenSet.map { set => GenT[P1, Sl](Parser.tokensIn(alpha)(set)) },
      genTokenPred.map { fn => GenT[P1, Sl](Parser.tokensWhile(alpha)(fn)) }
    )

  lazy val tokensIn0: Gen[GenT[P0]] =
    Gen.oneOf(
      genTokenSet.map { set => GenT[P0, Sl](Parser.tokensIn0(alpha)(set)) },
      genTokenPred.map { fn => GenT[P0, Sl](Parser.tokensWhile0(alpha)(fn)) }
    )

  lazy val seqIn: Gen[GenT[P1]] =
    Gen.listOf(genInput).map { alts =>
      val lits = alts.filter(alpha.length(_) > 0)
      if (lits.isEmpty) GenT[P1, Sl](Parser.fail[S, Sl])
      else GenT[P1, Sl](Parser.seqIn(lits)(alpha))
    }

  lazy val lengthP: Gen[GenT[P1]] =
    Gen.choose(1, 10).map { l => GenT[P1, Sl](Parser.length(l)(alpha)) }

  lazy val lengthP0: Gen[GenT[P0]] =
    Gen.choose(0, 10).map { l => GenT[P0, Sl](Parser.length0(l)(alpha)) }

  lazy val positional: Gen[GenT[P0]] =
    Gen.oneOf(
      GenT[P0, Unit](Parser.start[S]),
      GenT[P0, Unit](Parser.end[S](alpha)),
      GenT[P0, Int](Parser.index[S])
    )

  lazy val failP: Gen[GenT[P0]] =
    Gen.const(GenT[P0, Unit](Parser.fail[S, Unit]))

  lazy val failWithP: Gen[GenT[P0]] =
    Gen.asciiPrintableStr.map { msg => GenT[P0, Unit](Parser.failWith[S, Unit](msg)) }

  //////////////////////////////////////////////////////////////////////
  // Wrappers
  //////////////////////////////////////////////////////////////////////

  def void0(g: GenT[P0]): GenT[P0] = GenT[P0, Unit](Parser.void0(g.fa))

  def void(g: GenT[P1]): GenT[P1] = GenT[P1, Unit](Parser.void(g.fa))

  def slice0(g: GenT[P0]): GenT[P0] = GenT[P0, Sl](Parser.slice0(alpha)(g.fa))

  def slice(g: GenT[P1]): GenT[P1] = GenT[P1, Sl](Parser.slice(alpha)(g.fa))

  def withSlice0(g: GenT[P0]): GenT[P0] = {
    implicit val cga: Cogen[g.A] = g.cogen
    GenT[P0, (g.A, Sl)](Parser.withSlice0(alpha)(g.fa))
  }

  def withSlice(g: GenT[P1]): GenT[P1] = {
    implicit val cga: Cogen[g.A] = g.cogen
    GenT[P1, (g.A, Sl)](Parser.withSlice(alpha)(g.fa))
  }

  def backtrack0(g: GenT[P0]): GenT[P0] = GenT[P0, g.A](g.fa.backtrack)(g.cogen)

  def backtrack(g: GenT[P1]): GenT[P1] = GenT[P1, g.A](g.fa.backtrack)(g.cogen)

  def defer0(g: GenT[P0]): GenT[P0] = GenT[P0, g.A](Defer[P0].defer(g.fa))(g.cogen)

  def defer(g: GenT[P1]): GenT[P1] = GenT[P1, g.A](Defer[P1].defer(g.fa))(g.cogen)

  def notP(g: GenT[P0]): GenT[P0] = GenT[P0, Unit](Parser.not(g.fa)(alpha))

  def peekP(g: GenT[P0]): GenT[P0] = GenT[P0, Unit](Parser.peek(g.fa))

  def rep0(min: Int, max: Int, g: GenT[P1]): GenT[P0] = {
    implicit val cga: Cogen[g.A] = g.cogen
    GenT[P0, List[g.A]](g.fa.rep0(min = min, max = max))
  }

  def genRep0(g: GenT[P1]): Gen[GenT[P0]] =
    for {
      min <- biasSmall(0)
      max <- biasSmall(min)
    } yield rep0(min, max, g)

  def rep(min: Int, max: Int, g: GenT[P1]): GenT[P1] = {
    implicit val cga: Cogen[g.A] = g.cogen
    GenT[P1, List[g.A]](g.fa.rep(min, max).map(_.toList))
  }

  def genRep(g: GenT[P1]): Gen[GenT[P1]] =
    for {
      min <- biasSmall(1)
      max <- biasSmall(min)
    } yield rep(min, max, g)

  def withContext0(g: GenT[P0]): Gen[GenT[P0]] =
    Gen.asciiPrintableStr.map { ctx => GenT[P0, g.A](Parser.withContext0(g.fa, ctx))(g.cogen) }

  def withContext(g: GenT[P1]): Gen[GenT[P1]] =
    Gen.asciiPrintableStr.map { ctx => GenT[P1, g.A](Parser.withContext(g.fa, ctx))(g.cogen) }

  def product0(ga: GenT[P0], gb: GenT[P0]): Gen[GenT[P0]] = {
    implicit val ca: Cogen[ga.A] = ga.cogen
    implicit val cb: Cogen[gb.A] = gb.cogen
    Gen.oneOf(
      GenT[P0, (ga.A, gb.A)](Monad[P0].product(ga.fa, gb.fa)),
      GenT[P0, (ga.A, gb.A)](Monad[P0].map2(ga.fa, gb.fa)((_, _))),
      GenT[P0, (ga.A, gb.A)](Monad[P0].map2Eval(ga.fa, Eval.later(gb.fa))((_, _)).value),
      GenT[P0, (ga.A, gb.A)](Monad[P0].map2Eval(ga.fa, Eval.now(gb.fa))((_, _)).value)
    )
  }

  def softProduct0(ga: GenT[P0], gb: GenT[P0]): Gen[GenT[P0]] = {
    implicit val ca: Cogen[ga.A] = ga.cogen
    implicit val cb: Cogen[gb.A] = gb.cogen
    Gen.const(GenT[P0, (ga.A, gb.A)](ga.fa.soft ~ gb.fa))
  }

  def product(ga: GenT[P1], gb: GenT[P1]): Gen[GenT[P1]] = {
    implicit val ca: Cogen[ga.A] = ga.cogen
    implicit val cb: Cogen[gb.A] = gb.cogen
    Gen.oneOf(
      GenT[P1, (ga.A, gb.A)](FlatMap[P1].product(ga.fa, gb.fa)),
      GenT[P1, (ga.A, gb.A)](FlatMap[P1].map2(ga.fa, gb.fa)((_, _))),
      GenT[P1, (ga.A, gb.A)](FlatMap[P1].map2Eval(ga.fa, Eval.later(gb.fa))((_, _)).value),
      GenT[P1, (ga.A, gb.A)](FlatMap[P1].map2Eval(ga.fa, Eval.now(gb.fa))((_, _)).value)
    )
  }

  def product10(ga: GenT[P1], gb: GenT[P0]): Gen[GenT[P1]] = {
    implicit val ca: Cogen[ga.A] = ga.cogen
    implicit val cb: Cogen[gb.A] = gb.cogen
    Gen.oneOf(
      GenT[P1, (ga.A, gb.A)](Parser.product10(ga.fa, gb.fa)),
      GenT[P1, ga.A](ga.fa <* gb.fa),
      GenT[P1, gb.A](ga.fa *> gb.fa),
      GenT[P1, (ga.A, ga.A)](Parser.product10(ga.fa, ga.fa))
    )
  }

  def softProduct10(ga: GenT[P1], gb: GenT[P0]): Gen[GenT[P1]] = {
    implicit val ca: Cogen[ga.A] = ga.cogen
    implicit val cb: Cogen[gb.A] = gb.cogen
    Gen.oneOf(
      // left is Parser
      GenT[P1, (ga.A, gb.A)](ga.fa.soft ~ gb.fa),
      // right is Parser
      GenT[P1, (gb.A, ga.A)](gb.fa.with1.soft ~ ga.fa),
      // both are Parser
      GenT[P1, (ga.A, ga.A)](ga.fa.soft ~ ga.fa)
    )
  }

  def orElse0(ga: GenT[P0], gb: GenT[P0], res: GenT[Gen]): Gen[GenT[P0]] = {
    val genFn1: Gen[ga.A => res.A] = Gen.function1(res.fa)(ga.cogen)
    val genFn2: Gen[gb.A => res.A] = Gen.function1(res.fa)(gb.cogen)
    implicit val cogenResA: Cogen[res.A] = res.cogen

    Gen.zip(genFn1, genFn2).flatMap { case (f1, f2) =>
      Gen.oneOf(
        GenT[P0, res.A](ga.fa.map(f1).orElse(gb.fa.map(f2))),
        GenT[P0, res.A](MonoidK[P0].combineK(ga.fa.map(f1), gb.fa.map(f2)))
      )
    }
  }

  def orElse(ga: GenT[P1], gb: GenT[P1], res: GenT[Gen]): Gen[GenT[P1]] = {
    val genFn1: Gen[ga.A => res.A] = Gen.function1(res.fa)(ga.cogen)
    val genFn2: Gen[gb.A => res.A] = Gen.function1(res.fa)(gb.cogen)
    implicit val cogenResA: Cogen[res.A] = res.cogen

    Gen.zip(genFn1, genFn2).flatMap { case (f1, f2) =>
      Gen.oneOf(
        GenT[P1, res.A](ga.fa.map(f1).orElse(gb.fa.map(f2))),
        GenT[P1, res.A](MonoidK[P1].combineK(ga.fa.map(f1), gb.fa.map(f2)))
      )
    }
  }

  def mapped0(ga: GenT[P0]): Gen[GenT[P0]] =
    pures.flatMap { genRes =>
      implicit val ca: Cogen[ga.A] = ga.cogen
      implicit val cb: Cogen[genRes.A] = genRes.cogen
      Gen.function1(genRes.fa)(ca).flatMap { fn =>
        Gen.oneOf(
          GenT[P0, genRes.A](ga.fa.map(fn)),
          GenT[P0, genRes.A](Monad[P0].map(ga.fa)(fn))
        )
      }
    }

  def mapped(ga: GenT[P1]): Gen[GenT[P1]] =
    pures.flatMap { genRes =>
      implicit val ca: Cogen[ga.A] = ga.cogen
      implicit val cb: Cogen[genRes.A] = genRes.cogen
      Gen.function1(genRes.fa)(ca).flatMap { fn =>
        Gen.oneOf(
          GenT[P1, genRes.A](ga.fa.map(fn)),
          GenT[P1, genRes.A](FlatMap[P1].map(ga.fa)(fn))
        )
      }
    }

  def selected0(ga: Gen[GenT[P0]]): Gen[GenT[P0]] =
    Gen.zip(pures, pures).flatMap { case (genRes1, genRes2) =>
      val genPR: Gen[P0[Either[genRes1.A, genRes2.A]]] =
        ga.flatMap { init =>
          Gen
            .function1(Gen.either(genRes1.fa, genRes2.fa))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      val gfn: Gen[P0[genRes1.A => genRes2.A]] =
        ga.flatMap { init =>
          Gen
            .function1(Gen.function1(genRes2.fa)(genRes1.cogen))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      Gen.zip(genPR, gfn).map { case (pab, fn) =>
        GenT[P0, genRes2.A](Parser.select0(pab)(fn))(genRes2.cogen)
      }
    }

  def selected(ga1: Gen[GenT[P1]], ga0: Gen[GenT[P0]]): Gen[GenT[P1]] =
    Gen.zip(pures, pures).flatMap { case (genRes1, genRes2) =>
      val genPR: Gen[P1[Either[genRes1.A, genRes2.A]]] =
        ga1.flatMap { init =>
          Gen
            .function1(Gen.either(genRes1.fa, genRes2.fa))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      val gfn: Gen[P0[genRes1.A => genRes2.A]] =
        ga0.flatMap { init =>
          Gen
            .function1(Gen.function1(genRes2.fa)(genRes1.cogen))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      Gen.zip(genPR, gfn).map { case (pab, fn) =>
        GenT[P1, genRes2.A](Parser.select(pab)(fn))(genRes2.cogen)
      }
    }

  def flatMapped0(ga: Gen[GenT[P0]]): Gen[GenT[P0]] =
    Gen.zip(ga, pures).flatMap { case (parser, genRes) =>
      val genPR: Gen[P0[genRes.A]] =
        ga.flatMap { init =>
          Gen.function1(genRes.fa)(init.cogen).map { fn => init.fa.map(fn) }
        }

      Gen.function1(genPR)(parser.cogen).flatMap { fn =>
        Gen.oneOf(
          GenT[P0, genRes.A](parser.fa.flatMap(fn))(genRes.cogen),
          GenT[P0, genRes.A](Monad[P0].flatMap(parser.fa)(fn))(genRes.cogen)
        )
      }
    }

  def flatMapped(ga0: Gen[GenT[P0]], ga1: Gen[GenT[P1]]): Gen[GenT[P1]] =
    Gen.zip(ga0, ga1, pures).flatMap { case (parser0, parser1, genRes) =>
      val genPR: Gen[P1[genRes.A]] =
        ga1.flatMap { init =>
          Gen.function1(genRes.fa)(init.cogen).map { fn => init.fa.map(fn) }
        }

      val gfn1: Gen[parser1.A => P1[genRes.A]] = Gen.function1(genPR)(parser1.cogen)
      val gfn0: Gen[parser0.A => P1[genRes.A]] = Gen.function1(genPR)(parser0.cogen)

      Gen.frequency(
        (
          2,
          gfn1.flatMap { fn =>
            Gen.oneOf(
              GenT[P1, genRes.A](parser1.fa.flatMap(fn))(genRes.cogen), // 1 -> 0
              GenT[P1, genRes.A](FlatMap[P1].flatMap(parser1.fa)(fn))(genRes.cogen) // 1 -> 1
            )
          }
        ),
        (
          1,
          gfn0.map { fn =>
            GenT[P1, genRes.A](parser0.fa.with1.flatMap(fn))(genRes.cogen) // 0 -> 1
          }
        )
      )
    }

  // a Parser0 here could loop forever parsing nothing, so the step is always a Parser
  def tailRecM0(ga: Gen[GenT[P1]]): Gen[GenT[P0]] =
    Gen.zip(pures, pures).flatMap { case (genRes1, genRes2) =>
      val genPR: Gen[P0[Either[genRes1.A, genRes2.A]]] =
        ga.flatMap { init =>
          Gen
            .function1(Gen.either(genRes1.fa, genRes2.fa))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      Gen.zip(genRes1.fa, Gen.function1(genPR)(genRes1.cogen)).map { case (init, fn) =>
        GenT[P0, genRes2.A](Monad[P0].tailRecM(init)(fn))(genRes2.cogen)
      }
    }

  def tailRecM(ga: Gen[GenT[P1]]): Gen[GenT[P1]] =
    Gen.zip(pures, pures).flatMap { case (genRes1, genRes2) =>
      val genPR: Gen[P1[Either[genRes1.A, genRes2.A]]] =
        ga.flatMap { init =>
          Gen
            .function1(Gen.either(genRes1.fa, genRes2.fa))(init.cogen)
            .map { fn => init.fa.map(fn) }
        }

      Gen.zip(genRes1.fa, Gen.function1(genPR)(genRes1.cogen)).map { case (init, fn) =>
        GenT[P1, genRes2.A](FlatMap[P1].tailRecM(init)(fn))(genRes2.cogen)
      }
    }

  //////////////////////////////////////////////////////////////////////
  // The tables (cats.parse.ParserGen's gen0/gen, node for node)
  //////////////////////////////////////////////////////////////////////

  lazy val gen0: Gen[GenT[P0]] = {
    val rec = Gen.lzy(gen0)

    Gen.frequency(
      (3, pures.flatMap(_.toId).map { g => GenT[P0, g.A](Parser.pure[S, g.A](g.fa))(g.cogen) }),
      (5, seqLit0),
      (5, tokenIn.map(widen)),
      (3, tokensIn0),
      (1, positional),
      (1, failP),
      (1, failWithP),
      (1, rec.map(void0(_))),
      (1, rec.map(slice0(_))),
      (1, rec.map(withSlice0(_))),
      (1, seqIn.map(widen)),
      (1, rec.map(backtrack0(_))),
      (1, rec.map(defer0(_))),
      (1, rec.map(notP(_))),
      (1, rec.map(peekP(_))),
      (1, Gen.lzy(gen.flatMap(genRep0(_)))),
      (1, rec.flatMap(mapped0(_))),
      (1, selected0(rec)),
      (1, tailRecM0(Gen.lzy(gen))),
      (1, lengthP0),
      (1, flatMapped0(rec)),
      (1, Gen.zip(rec, rec).flatMap { case (g1, g2) => product0(g1, g2) }),
      (1, Gen.zip(rec, rec).flatMap { case (g1, g2) => softProduct0(g1, g2) }),
      (1, Gen.zip(rec, rec, pures).flatMap { case (g1, g2, p) => orElse0(g1, g2, p) }),
      (1, rec.flatMap(withContext0(_)))
    )
  }

  lazy val gen: Gen[GenT[P1]] = {
    val rec = Gen.lzy(gen)

    Gen.frequency(
      (8, seqLit),
      (8, tokenIn),
      (4, tokensIn),
      (8, seqIn),
      (2, rec.map(void(_))),
      (2, rec.map(slice(_))),
      (1, rec.map(withSlice(_))),
      (2, rec.map(backtrack(_))),
      (1, rec.map(defer(_))),
      (1, rec.flatMap(genRep(_))),
      (1, selected(rec, gen0)),
      (1, rec.flatMap(mapped(_))),
      (1, flatMapped(gen0, rec)),
      (1, tailRecM(rec)),
      (1, lengthP),
      (1, rec.flatMap(withContext(_))),
      (
        2,
        Gen.frequency(
          (1, Gen.zip(rec, rec).flatMap { case (g1, g2) => product(g1, g2) }),
          (1, Gen.zip(rec, gen0).flatMap { case (g1, g2) => product10(g1, g2) }),
          (1, Gen.zip(rec, gen0).flatMap { case (g1, g2) => softProduct10(g1, g2) }),
          (1, Gen.zip(rec, rec, pures).flatMap { case (g1, g2, p) => orElse(g1, g2, p) })
        )
      )
    )
  }

  /** The leaves fusion can actually rewrite (spec S5.3): literals, token sets and multi-literals.
    */
  lazy val genFusableLeaf: Gen[P1[Unit]] =
    Gen.oneOf(seqLit, tokenIn, seqIn).map(g => Parser.void(g.fa))

  def genParser0[A](genA: Gen[A]): Gen[P0[A]] =
    for {
      genT <- gen0
      fn <- Gen.function1(genA)(genT.cogen)
    } yield genT.fa.map(fn)

  def genParser[A](genA: Gen[A]): Gen[P1[A]] =
    for {
      genT <- gen
      fn <- Gen.function1(genA)(genT.cogen)
    } yield genT.fa.map(fn)

  implicit def arbParser0[A: Arbitrary]: Arbitrary[P0[A]] =
    Arbitrary(genParser0(Arbitrary.arbitrary[A]))

  implicit def arbParser[A: Arbitrary]: Arbitrary[P1[A]] =
    Arbitrary(genParser(Arbitrary.arbitrary[A]))
}

/** The char instantiation: proves the alias facade and the generic engine agree. */
object CharParserGen extends GenericParserGen[String] {
  val alpha: StringAlphabet.type = StringAlphabet

  // the same 5-token space `cats.parse.ParserGen.genSmallChar` uses, for the same reason:
  // collisions between independently generated parsers and inputs have to be common
  private lazy val genSmallChar: Gen[Char] = Gen.oneOf('A', 'a', 'B', 'b', ' ')

  def genInput: Gen[String] =
    Gen.frequency(
      (5, Gen.geometric(5.0).flatMap(Gen.stringOfN(_, genSmallChar))),
      (1, Gen.asciiPrintableStr)
    )

  def genTokenSet: Gen[StringAlphabet.CharSet] =
    Gen.frequency(
      (5, Gen.nonEmptyListOf(genSmallChar).map(StringAlphabet.charSet(_))),
      (1, Gen.nonEmptyListOf(Arbitrary.arbitrary[Char]).map(StringAlphabet.charSet(_))),
      (1, Gen.const(StringAlphabet.universal))
    )

  def genTokenPred: Gen[Char => Boolean] =
    Gen.nonEmptyListOf(genSmallChar).map { cs =>
      val set = cs.toSet; set.contains(_)
    }

  implicit def cogenToken: Cogen[Char] = Cogen.cogenChar

  implicit def cogenSlice: Cogen[String] = Cogen.cogenString
}

/** The toy instantiation: the non-injective, non-`String`-slice path. Anything char-shaped that
  * survived the cutover because char was the only caller fails here.
  */
object ToyParserGen extends GenericParserGen[ByteSeq] {
  val alpha: ToyAlphabet.type = ToyAlphabet

  // same bias as GenericOptimizerTest: unambiguous, ambiguous, then anything
  private lazy val genToken: Gen[Byte] =
    Gen.frequency(
      (3, Gen.oneOf(1, 2, 4, 8).map(_.toByte)),
      (3, Gen.oneOf(3, 5, 10, 12, 15).map(_.toByte)),
      (1, Gen.choose(0, 15).map(_.toByte))
    )

  def genInput: Gen[ByteSeq] =
    Gen.choose(0, 5).flatMap(Gen.listOfN(_, genToken)).map(l => ByteSeq.fromBytes(l.toArray))

  def genTokenSet: Gen[Int] =
    Gen.frequency(
      (3, genToken.map(t => 1 << (t & 0xf))),
      (3, Gen.nonEmptyListOf(genToken).map(_.foldLeft(0)((m, t) => m | (1 << (t & 0xf))))),
      (1, Gen.const(ToyAlphabet.universal))
    )

  def genTokenPred: Gen[Byte => Boolean] =
    genTokenSet.map { mask => (b: Byte) => ToyAlphabet.contains(mask, b) }

  implicit def cogenToken: Cogen[Byte] = Cogen.cogenByte

  implicit def cogenSlice: Cogen[ByteSeq] =
    Cogen.cogenList(Cogen.cogenByte).contramap(_.bytes.toList)
}
