# Roadmap and handbook coverage

calyx follows the structure of the Magma handbook. This page summarises
what is implemented and what is deliberately different. Open work (bugs,
missing features, known differences from Magma) is tracked as
[GitHub issues](https://github.com/aygerix/calyx-math/issues); see "Open
work" at the end.

## Part I: The Magma Language

| Chapter | Status |
| --- | --- |
| Statements and expressions | Done: assignment (multiple, indexed, generator, mutation), `delete`, booleans, `eq`/`cmpeq`, coercion `!`, `where ... is`, `select`, `case` statement and expression, `for`/`while`/`repeat`, `for random`, dual iteration `i -> x`, `break x`/`continue x`, `eval`, comments and `\` continuation, `time`/`vtime`, types and extended types, `ISA`, `MakeType`, `CoveringStructure`, random seeds, `IsIntrinsic`. |
| Functions, procedures and packages | Done: `function`/`procedure` (both forms), `func<>`/`proc<>`, parameters, variadic functions, `$$`, `forward`, `local`, reference arguments (including `~A[x]` and `` ~r`f ``), closures capturing values at creation, packages with `intrinsic`, `Attach`/`Detach`/`AttachSpec`, automatic reloading of changed packages, `import`, `require`/`requirege`/`requirerange`, `Nresults`, attributes (`AddAttribute`, `declare attributes`), user-defined types (`declare type`, `New`, `Clone`, user `Print`, `Parent`, `IsCoercible`, `in`, operators), verbose flags. |
| Input and output | Mostly done: strings and their intrinsics (including `Split` and `Regexp`), `print` with print levels, `printf`/`fprintf`/`Sprintf` (widths, `%o %O %m %h`), `Sprint`, previous values `$1`..., indentation, `PrintFile`, `SetOutputFile`, `SetLogFile`, file objects (`Open`, `Gets`, `Puts`, ...), `Pipe`, `System`, `load`/`iload`, `read`/`readi`. **Missing:** binary strings, sockets, `POpen`, asynchronous I/O, `ReadObject`/`WriteObject`, `save`/`restore` ([#27](https://github.com/aygerix/calyx-math/issues/27)). |
| Environment and options | Partly done: `-b -e -h -n -s -S -V` and `name:=value` arguments, set/get intrinsics (`SetColumns`, `SetAssertions`, `SetVerbose`, ...), `ShowIdentifiers`, `ShowValues`, `ListSignatures`, `ListCategories`, `?Name` help. **Missing:** `%p`-style history commands, most environment variables, vi mode ([#28](https://github.com/aygerix/calyx-math/issues/28)). |
| Parallelism | Not started ([#29](https://github.com/aygerix/calyx-math/issues/29)). |
| Magma semantics | Done (see "Differences" below). |
| Profiler | Intrinsics accepted; no profile data is collected yet ([#30](https://github.com/aygerix/calyx-math/issues/30)). |
| Debugger | `SetDebugOnError` accepted; no debugger yet ([#31](https://github.com/aygerix/calyx-math/issues/31)). |

## Part II: Sets, Sequences, and Mappings

| Chapter | Status |
| --- | --- |
| Introduction to aggregates | Done: universes, automatic coercion to a common overstructure, power structures, nested aggregates, multi-indexing, sequences used as universes. |
| Sets | Done: enumerated sets (with lazy arithmetic progressions), indexed sets, multisets, formal sets, all constructors, power sets, `Include`/`Exclude`/`ChangeUniverse`/..., set operators, `Subsets`, `Multisets`, `Permutations`, quantifiers `exists`/`forall`/`rep`/`random`, reductions, iteration. |
| Sequences | Done, including indexing by ranges (`s[i..j]`, `s[i..j by k]`). `Sort` gives its sorting permutation as an element of `Sym(n)`; the symmetric groups and their elements have what Part II needs (products, powers, inverses, the action `i^p`, conjugation, `Order`, `Eltseq`, `Sign`, `CycleStructure`, `Cycle`, generators, coercion from image sequences), and the rest of permutation groups comes in Part IX. |
| Tuples and Cartesian products | Done. |
| Lists | Done. |
| Associative arrays | Done, including `Default` values and widening of the index universe. |
| Coproducts | Done. |
| Records | Done. |
| Mappings | Done for maps given by rules, graphs and coercions, composition, inverses and preimages. Homomorphisms given by generator images need the algebraic structures of later parts ([#33](https://github.com/aygerix/calyx-math/issues/33)). |

## Checking against Magma

Output is checked against real Magma (V2.29-10, the version behind the
public Magma calculator). The scripts in `crates/calyx-cli/tests/compat`
have Magma's own output as their expected output, and cover print lists,
line wrapping, aggregate layout, records, error reports (source windows,
carets, call frames, `eval` errors, syntax error recovery), coercion
errors, `Sort`'s permutations, and the generic ring functions of Part III
(ring properties, element predicates and orders, ring printing and naming,
ideals of the integers, `Infinity`). Where the handbook's examples
disagree with current Magma (they were produced by many different
versions), calyx follows current Magma:
for example records print one field per line, reals print with all their
digits, and a literal such as `1/0` is rejected when it is read.

## Differences from Magma

- **Hash order.** Magma stores sets and associative arrays in hash tables.
  It prints sets of integers, rationals and residues sorted (as calyx does),
  but iterates over them, and prints sets of strings, tuples, sets and
  sequences, in its internal hash order. calyx iterates in sorted order
  (or insertion order), so loops over sets and some printed sets can list
  elements in a different order. For example `Subsets({1..8}, 1)` prints
  as `{3}, {6}, {1}, ...` in Magma. `PartialFactorization` does reproduce
  Magma's iteration order of `Subsets({1..n}, 1)`, which it depends on
  ([#32](https://github.com/aygerix/calyx-math/issues/32)).
- **Iterator order.** In `[ e : x in X, y in Y ]` the first iterator is
  the inner loop, while in `[ e : x, y in S ]` the first variable is the
  outer one; both match Magma.
- **Extensions.** calyx also supports formal sequences `[! ... !]`, `@@`,
  `IsInjective`, `IsSurjective`, `IsBijective` and `Graph` for maps given
  by a graph, which Magma rejects.
- **Intrinsic descriptions** (`?Name`, or printing an intrinsic) use calyx's
  own documentation.
- **Random numbers** come from a different generator, so values differ from
  Magma's for the same seed. `SetSeed`/`GetSeed` behave the same way.
- **Extended reals.** Numbers mixed with `Infinity()` get the universe
  `Extended Reals` as in Magma, but keep their own types there (`Type`
  gives `RngIntElt` where Magma gives `ExtReElt`).
- **Magma's own packages.** Errors raised inside Magma's package code show
  a traceback into Magma's files (for example `ResidueClassField` of a
  non-maximal ideal); calyx reports just the error. Intrinsics Magma has
  only for other types (such as `IsMaximal`) are not declared in calyx, so
  calling them gives an undeclared-identifier error rather than "Bad
  argument types".

## Part III: Basic Rings (in progress)

The ring layer is in place: FLINT's generic rings (`gr`) provide residue
class rings, finite fields (Conway polynomials, Zech logarithms for fields
of up to 2^20 elements), univariate and multivariate polynomial rings and
the complex field; real and complex numbers are computed with MPFR. Rings
are values with Magma's printing, automatic and forced coercion, and
caching (one `Integers(n)` per modulus, one default `GF(q)`, one global
`PolynomialRing(R)` per coefficient ring).

| Chapter | Status |
| --- | --- |
| Introduction to rings | Done: `Characteristic`, `#R` (`Infinity` for infinite rings), `IsFinite` and all the ring predicates (`IsField`, `IsEuclideanDomain`, `IsPID`, `IsUFD`, `HasGCD`, ..., with Magma's answers for every kind of ring), `PrimeRing`, `PrimeField`, `Centre`, ring equality and membership (with Magma's errors between unrelated rings), element predicates (`IsUnit`, `IsIdempotent`, `IsNilpotent`, `IsZeroDivisor`, `IsIrreducible`, `IsPrime`), Magma's order on residues, finite field elements and polynomials (`lt`, `Sort`), `Maximum`/`Minimum`, ideals of the integers (`ideal< >`, `quo< >`, ideal arithmetic, `ResidueClassField`), `ext< R \| >`, and naming of structures and aggregates by assignment (generators print as `F.1`, maps show `RngInt: Z`). **Pending:** `Localization` and `Completion` ([#36](https://github.com/aygerix/calyx-math/issues/36)). |
| Ring of integers | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation (`Integers`, `IntegerRing`, `RingOfIntegers`, hexadecimal literals, `elt< >`, `sub< >`, the natural `hom< >`), coercion into Z, hexadecimal printing (`:Hex`), arithmetic and bit operations (`div`/`mod`, `Quotrem`, `ExactQuotient`, `ShiftLeft`, `Bitwise*`, `ModByPowerOf2`), predicates, `Isqrt`/`Iroot`/`IsPower`/`IsSquare`, `Ilog`, `Valuation`, digit sequences (`Intseq`/`Seqint`), gcds (`Xgcd` of sequences with small multipliers), random integers and primes, primality (proven with FLINT, certificates by ECPP with `PrimalityCertificate`, `CheckCertificate` and `OldCertificate`, `IsProbablePrime` with `Bases`, `Proof := false` in the prime finders), `NextPrime`/`PreviousPrime`/`NthPrime`/`PrimesUpTo`, `Factorization` as a pipeline of methods that honours its limit parameters, with stored factors, the individual factoring methods (`TrialDivision`, `PollardRho`, `pMinus1`, `pPlus1`, `SQUFOF`, `ECM` with Suyama curves, `ECMOrder`, `MPQS` as a self-initialising quadratic sieve; p - 1, p + 1 and ECM with Magma's default stage 2 bounds), `Divisors`, `CoprimeBasis`, `PartialFactorization`, `Cunningham`, factorization sequences (`RngIntEltFact`: arithmetic, divisor functions, predicates), arithmetic functions (`EulerPhi` and its inverse, `CarmichaelLambda`, `DivisorSigma`, `MoebiusMu`, `DickmanRho`), combinatorial functions, modular arithmetic (`Modexp`, `Modinv`, `Modsqrt` with Magma's choice of root, `Modorder`, `PrimitiveRoot`, `Solution`, `CRT`), quadratic residue symbols, `NormEquation`, and `AdditiveGroup`, `MultiplicativeGroup` and `ClassGroup` of Z. **Pending:** see the [`area: integers` issues](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3A%22area%3A+integers%22). |
| Residue class rings | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation (`Integers(m)`, `IntegerRing(m)` and `ResidueClassRing(m)` of an integer or a factorization, `quo< >`), `Modulus`/`FactoredModulus`, square roots (`IsSquare`, `Sqrt`, `AllSquareRoots`, with Magma's choice of root), `Solution`, gcds and lcms of elements, `Normalize`, ideals (`ideal< >`, `sub< >`, sums, products, intersections, membership, `Generator`), the unit group (`UnitGroup`/`MultiplicativeGroup` with Magma's generators, discrete logarithms by Pohlig–Hellman with baby-step giant-step or Pollard's rho, `IsPrimitive`, `PrimitiveElement`, `Order`), `AdditiveGroup`, the natural `hom< >` between residue class rings, and the abelian groups these return (`GrpAb`: elements and their arithmetic, `Invariants`, `Order`, `Exponent`, `IsCyclic`, `Generators`, maps and preimages), and Dirichlet characters (text/199: `DirichletGroup`, characters, their values as `chi(n)` and `n @ chi`, arithmetic, Kronecker characters). **Pending:** the Dirichlet functions that need cyclotomic or number fields (`FullDirichletGroup`, groups over number fields, `^ phi`; [#48](https://github.com/aygerix/calyx-math/issues/48)). |
| Rational field | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): Q as a number field (`MaximalOrder`, the bases, `MinimalField`, `UnitGroup`, `ClassGroup`, `AutomorphismGroup`, `Decomposition`, the invariants, `DefiningPolynomial`, `Signature`), creation (`RootOfUnity`, `Random`, `Q.1`, `Q![n, d]`, `elt< >`, the natural `hom< >`), and elements: `Height`, `Qround`, regular (with `Bound`) and Hirzebruch-Jung continued fractions, `RationalReconstruction` of residues and prime field elements, `Valuation` at primes and prime ideals, `Eltseq`, `MinimalPolynomial`. Also Z as a number field order (`Decomposition`, `RamificationIndex`, `TwoElementNormal`, `ChineseRemainderTheorem` and `Valuation` at ideals). **Pending:** `Algebra`, `VectorSpace` and matrix `RationalReconstruction` ([#53](https://github.com/aygerix/calyx-math/issues/53)). |
| Finite fields | In progress ([#39](https://github.com/aygerix/calyx-math/issues/39)): the lattice of finite fields, elements, structure operations, arithmetic, polynomials over finite fields, discrete logarithms, permutation polynomials, `hom< >` from a finite field by generator images or as the natural map from a prime field, and `ExtensionField< F, x \| P >`. |
| Nearfields | In progress ([#43](https://github.com/aygerix/calyx-math/issues/43)): Dickson and Zassenhaus nearfields and their elements, and `IsIsomorphic` for Dickson nearfields. **Pending:** the unit, affine and automorphism groups (they need the groups of Part IX, [#44](https://github.com/aygerix/calyx-math/issues/44)), and the projective planes. |
| Univariate polynomial rings | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation and print options, structure operations, coefficients and terms, roots (`Roots`, `HasRoot` and `Roots(f : Max := m)` with Magma's choice of roots), derivatives, evaluation and interpolation, division, `Modexp` and `CRT`, gcds, content, resultants and discriminants, integer polynomial norms and `DedekindTest`, polynomials over finite fields (`PrimePolynomials` in Magma's order, `JacobiSymbol`), factorization (irreducible, squarefree, distinct- and equal-degree, Hensel lifting, `IsIrreducible`, `IsPrime`), ideals and quotient rings (`ideal< >`, `quo< >`), the special families (Chebyshev, Legendre, Laguerre, Hermite, Bernoulli, Gegenbauer, Dickson, Swinnerton-Dyer), Magma-level printing, gcds, factorization, roots, content and discriminants over polynomial coefficient rings, `Xgcd` over the real and complex fields, `SmallRoots` (Coppersmith's method), roots over the real and complex fields, `Decomposition` (the order of its decompositions awaits 2.29 output), and the matrix functions (`CompanionMatrix`, `SylvesterMatrix`, `QMatrix`). **Pending:** rational functions ([#57](https://github.com/aygerix/calyx-math/issues/57)). Polynomial rings over quotient rings such as Q[x]/(f) wait for the number fields of Part VI, whose factorization they need. |
| Multivariate polynomial rings | In progress ([#41](https://github.com/aygerix/calyx-math/issues/41)): creation and coercion, every monomial order in the handbook and graded rings, elements and their arithmetic, `ChangeRing`, `hom< >` by generator images, gcds and factorization, `IsIrreducible` and `IsPrime`, gcds, factorization, resultants and discriminants over polynomial coefficient rings, content, resultants and discriminants over Z/nZ, and resultants and discriminants over the real and complex fields (computed exactly and rounded once). Magma has no gcds over composite residue rings or the reals, and calyx gives its errors. `JacobianMatrix`, `SymmetricBilinearForm`, `DiagonalForm` and `IsAlgebraicallyDependent` in characteristic 0 are done too. **Pending:** `IsAlgebraicallyDependent` in positive characteristic (it needs Gröbner bases) and division by non-constant polynomials (rational functions). |
| Real and complex fields | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation (including real literals with a precision, `1.2345p10`, and `elt< >`), structure, element operations, printing, the transcendental functions, the elliptic and modular functions (handbook sections 254 to 259), the Gamma, Bessel and hypergeometric U functions (sections 261 and 262), and the other special functions, infinite sums and numerical integration (sections 263 to 265), roots of polynomials (`Roots`, `HasRoot`, `HenselLift`, `RootsNonExact` with Magma's error bounds), continued fractions (`ContinuedFraction`, `BestApproximation`), and the integer relations (`IntegerRelation`, `LinearRelation`, `PowerRelation`, `MinimalPolynomial`), and complex numbers that are real in the real functions that accept them. **Pending:** general polynomial products, which round differently from Magma in the last bits (a known difference, [#73](https://github.com/aygerix/calyx-math/issues/73)), and `Round` of complex numbers, which gives Gaussian integers ([#92](https://github.com/aygerix/calyx-math/issues/92), Part VI). |

Ideals of multivariate polynomial rings and Gröbner bases are not
Part III: the multivariate chapter covers only the rings and their
elements, and leaves ideals and Gröbner bases to the Gröbner Bases
chapter, in Commutative Algebra. Part of that chapter was done early and
is merged: Gröbner bases of sets and sequences of polynomials over finite
fields and Q (`GroebnerBasis`, `NormalForm`, `Reduce`, `SPolynomial`,
`IsGroebner`; F4 over GF(p) for p < 2^31 in the graded orders and for
truncated bases, then FGLM for zero-dimensional ideals in the lex,
elimination, univariate and weight orders over any field, Buchberger
elsewhere; over Q, bases lifted from word primes by multi-CRT and rational
reconstruction, Monte Carlo as in Magma unless `GlobalModular := false`),
and ideals (`ideal< >`, `Ideal`, bases and generators, their Gröbner bases
(`GroebnerBasis`, `NormalForm`, `Coordinates`, `HasGroebnerBasis`,
`MarkGroebner`, `EasyIdeal`, `EasyBasis`, `SmallBasis`, `ChangeOrder`),
sums, products and powers, membership, equality, inclusion and
intersection, `Dimension`, `IsProper`, `IsZeroDimensional`,
`QuotientDimension`, `IsPrincipal`, `IsHomogeneous`,
`LeadingMonomialIdeal`, `IsInRadical`, `JacobianIdeal`, colon ideals and
saturation, elimination (`EliminationIdeal`,
`UnivariateEliminationIdealGenerator(s)`, `RelationIdeal`),
`VariableExtension` and `Homogenization`, printed with what is known of
them as Magma does). The rest of
[#35](https://github.com/aygerix/calyx-math/issues/35) waits for that
part.

## Part IV: Matrices and Linear Algebra (started)

| Chapter | Status |
| --- | --- |
| Matrices | In progress ([#76](https://github.com/aygerix/calyx-math/issues/76)): matrices and vectors on FLINT's native matrix types over the entry ring, with matrix algebras, matrix spaces and R-spaces as parents; creation (text/270), elementary properties (text/271), access and modification of entries (text/272), printing with Magma's column alignment, elementary arithmetic (text/275), block matrices (text/273), changing rings (text/274), nullspaces and solutions of systems (text/276), predicates (text/277), determinants, ranks, minors, Pfaffians and the other properties of text/278 (`Rank` also over multivariate polynomial rings), characteristic and minimal polynomials, their factored forms, eigenvalues and eigenspaces (text/279), and part of the canonical forms (text/280: `EchelonForm`, `HermiteForm`, `Adjoint`). The rest of the canonical forms are next. |
| Sparse matrices | Not started ([#77](https://github.com/aygerix/calyx-math/issues/77)). |
| Vector spaces | Not started ([#78](https://github.com/aygerix/calyx-math/issues/78)). |
| Polar spaces | Not started ([#79](https://github.com/aygerix/calyx-math/issues/79)). The sections on isometry groups, classical groups and Lie algebras wait for Parts IX and XIII. |

## Open work

Everything still to do is a GitHub issue, labelled by area (`area:
integers`, `area: rings`, ...), kind (`bug`, `missing`,
`known-difference`, `perf`, `testing`) and priority (`P1` to `P3`), with
one milestone per handbook Part:

- [Open issues](https://github.com/aygerix/calyx-math/issues)
- [Known differences from Magma](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3Aknown-difference)
- [Waiting on Magma 2.29](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3Aneeds-2.29),
  including the pending compat scripts ([#24](https://github.com/aygerix/calyx-math/issues/24))

Alongside the rest of Part III come Part IV and the generator-based
constructors ([#33](https://github.com/aygerix/calyx-math/issues/33)); the groups of Part IX are planned in [#44](https://github.com/aygerix/calyx-math/issues/44).
