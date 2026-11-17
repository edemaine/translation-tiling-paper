# Lean formalization

The complete computable Wang-to-tile reduction and co-RE-completeness in
dimension three are proved unconditionally. Its output is a nonempty,
face-connected tile, tileable exactly when the input Wang tiles tile the plane.

Start with [Abstract.lean](TranslationTiling/Abstract.lean) for the
human-readable definitions and main theorem statements used in the paper.
Its prototiles are lists of points `Fin 3 → ℤ`; connectivity is defined by paths
of adjacent points, lattice tiling by unique covering translates, and real tiling
by almost-everywhere unique coverage by translates of the solid body. The
statements give co-RE-completeness for connected prototiles in both `ℤ³`
and `ℝ³`, and undecidability in both. They also give co-RE-completeness and
undecidability for arbitrary Euclidean motions, with or without reflections,
and total computable Wang reductions for translations and for Euclidean
motions. For the same rotation-resistant output, lattice translations, real
translations, and Euclidean motions are equivalent, with or without reflections.
Each reduction theorem includes the quasipolynomial cube bound for the same
total computable function, with a factor of 64,000 for rotations.
`RealTiles P motions` takes an explicit set of allowed Euclidean motions.
The named choices are `allMotions`, `translations`, `translationsAndRotations`,
and `translationsAndReflections`. Hardness, undecidability, and
the rigid reduction equivalence hold for any motion set containing all translations.
All real-space statements use Mathlib's `EuclideanSpace`; motions use its
`AffineIsometryEquiv`. The comments explain the motion and set-image notation.

[AbstractBridge.lean](TranslationTiling/AbstractBridge.lean) proves these
statements from the rest of the development, which uses the same model
`Fin 3 → ℤ` of `ℤ³`. It proves equivalence of the connectivity and lattice/real
tiling predicates with the project's definitions, and derives co-RE-completeness
and undecidability. The definitions and theorem statements in `Abstract.lean`
make the claims inspectable; Lean checks the bridge and the underlying proofs.
The motion bridge also reconciles the abstract's cubes `p + [0,1]³` with the
rotation construction's centered cubes. Build this interface with
`lake build TranslationTiling.Abstract` from this directory.

Read [Statements.lean](TranslationTiling/Statements.lean) for the broader public
interface, including the compiler and dimension-optimality results.
`compiler_effectivity` and `compiler_correct`
prove uniform computability and connected correctness. Every public theorem,
including `reduction`, `connected_completeness`, `real_completeness`, and
`dimension_optimality`, has no imported mathematical hypothesis. The former
inputs appear as proved theorems: `sudoku_soundness`, `mss_rigidity`,
`kim_coset_rigidity`, and `planar_periodicity`. There is no assumed compiler
certificate or outstanding `Claims` namespace.

## Rotation-Resistant Replacement

The six-key construction is formalized in
[Rotations/Main.lean](TranslationTiling/Rotations/Main.lean) for grid rotations
and [Rotations/Euclidean/Main.lean](TranslationTiling/Rotations/Euclidean/Main.lean)
for arbitrary Euclidean rotations and translations. Both give a computable
Wang reduction, a face-connected output, co-RE-hardness, and undecidability.
The Euclidean results cover all proper rotations and also the larger class
allowing reflections. [EuclideanMembership/EffectiveSystem.lean](TranslationTiling/EuclideanMembership/EffectiveSystem.lean)
proves co-RE membership for all four motion choices, including arbitrary
mirror-plane reflections without rotations. It encodes tilings as a computable
compact system of closed polynomial constraints and semidecides failure using
finite rational grids with explicit error bounds. Combined with hardness,
this proves co-RE-completeness for every fixed dimension at least three.

The fixed gadget has 64,000 voxels. Replacing each voxel of an input tile by
one scaled, translated copy preserves tilability and face-connectivity, with
exactly a factor of 64,000 in the number of distinct voxels.
[Rotations/Volume.lean](TranslationTiling/Rotations/Volume.lean) proves these
cardinalities. The arbitrary-angle proof uses square-neck width to force a
signed coordinate permutation, a chamber separation argument, and contact
with the chamber's end wall to force the remaining translation phase.
[Rotations/Euclidean/GlobalRigidity.lean](TranslationTiling/Rotations/Euclidean/GlobalRigidity.lean)
proves that every tiling has one common Euclidean frame and origins on its
40ℤ³ grid. The tiling model permits arbitrary orthogonal linear isometries,
real offsets, and shared boundaries through almost-everywhere unique coverage;
face-to-face contacts and a common initial grid are not assumed.

The geometric proof and reduction are described in the grid-rotation and
arbitrary-Euclidean-rotation sections of [slop.texlish](../slop.texlish).
All these main results are included in the axiom audit.

## Build

The project uses Lean 4.35.0 and the GitHub dependency
[`edemaine/lean-wang`](https://github.com/edemaine/lean-wang/tree/64268a3aaaef3eac65559352ef94f62ab9c00482),
pinned to `64268a3aaaef3eac65559352ef94f62ab9c00482`. There is no local-path
dependency. `lake-manifest.json` also pins mathlib v4.35.0 and its transitive dependencies.

From the paper repository's root:

```sh
cd lean
lake update
lake exe cache get
lake build
```

The first build includes the Wang repository's completed Kari–Hooper development.
Build artifacts from the same dependency commit and toolchain may be reused.
The full `lake build` passes, including the examples and axiom audit.
`TranslationTiling/AxiomAudit.lean` rejects every axiom beyond `propext`,
`Classical.choice`, and `Quot.sound` in the public theorems and selected main lemmas.
Generic auxiliary lemmas use explicit theorem parameters; the public results
have no unproved mathematical input. No unfinished proof is accepted.

## Cube Bound by Wang Tile Count

[Compiler/CleanQuasipolynomialBound.lean](TranslationTiling/Compiler/CleanQuasipolynomialBound.lean)
gives `(n+4)^(1.75*10^4*log₂(log₂(n+4))) = n^O(log log n)` with ordinary real
logarithms. The theorem `Size.exists_connected_tile_clean_quasipolynomial_bound`
includes nonemptiness, face connectedness, and both tilability directions.
Here `n` counts distinct input tiles. The one-tile specialization in
[Compiler/QuasipolynomialBound.lean](TranslationTiling/Compiler/QuasipolynomialBound.lean)
gives at most `2^49162` cubes.

[FixedCycleTests.lean](TranslationTiling/FiniteCompiler/FixedCycleTests.lean)
uses one fixed test per forbidden word or seed-label pair. Each digit subgroup
is cyclic, so activity has a witness separated by its fixed generator
`r_i/r_ij`. The response is zero at zero and this generator at every nonzero
input; the witnesses give a collision whenever all selected labels are active.
[Effective/FixedPrimitives.lean](TranslationTiling/FiniteCompiler/Effective/FixedPrimitives.lean)
implements these response tables and proves primitive recursiveness;
[Effective/FixedCorrect.lean](TranslationTiling/FiniteCompiler/Effective/FixedCorrect.lean)
proves that the numerical gadget is exactly the fixed semantic test.

[Effective/PackedWords.lean](TranslationTiling/FiniteCompiler/Effective/PackedWords.lean)
counts and enumerates three disjoint classes of ternary words: words containing
0 but no 1, words containing 1 but no 0, and words containing both.
Their capacities are `2^k-1`, `2^k-1`, and `3^k-2^(k+1)+1`.
[Effective/MixedCode.lean](TranslationTiling/FiniteCompiler/Effective/MixedCode.lean)
assigns seed-class tile indices and other decorated indices to these words,
without dedicated prefix positions. The code length is the maximum of the
binary length of `n` and the ternary length of `2pqn`.
For one Wang tile, six positions per column suffice.
[TaggedSystem.lean](TranslationTiling/FiniteCompiler/TaggedSystem.lean)
proves the tiling equivalence for any injective code with the exact seed predicates.
[Effective/MixedInput.lean](TranslationTiling/FiniteCompiler/Effective/MixedInput.lean)
implements the code and proves primitive recursiveness and correctness.
All positions share their column's original slope. The board has `2q+2 = 28`
columns; coefficient residues use `p²q²`, and seed residues use `5pq = 715`.
The fixed primes are `p = 11` and `q = 13`.
[FivePointPattern.lean](TranslationTiling/SudokuArithmetic/FivePointPattern.lean)
and [FivePointRecovery.lean](TranslationTiling/SudokuArithmetic/FivePointRecovery.lean)
replace the clean 4×4 patch with five points and two diagonal triples.
Ten incidences recover two affine rows and one point for every prime
`r > 10`. Seven affine root exclusions at eight columns then recover the
third row, using the two step sizes in
[FivePointRows.lean](TranslationTiling/SudokuArithmetic/FivePointRows.lean).
The intervening-row lemma in
[SixPointRecovery.lean](TranslationTiling/SudokuArithmetic/SixPointRecovery.lean)
gives four consecutive good rows, after which four-line closure propagates the
approximation.
The shorter-board proof also uses three prime-spaced columns in rescaling
and two prime-multiple samples to identify the higher-digit coefficients.

[Compiler/SmallBudgetCounting.lean](TranslationTiling/Compiler/SmallBudgetCounting.lean)
extends the useful-prime pools down to budget 256 using seventeen monotone
interval certificates. Their primality and increasing-order certificates are in
[Compiler/SmallBudgetPrimeList.lean](TranslationTiling/Compiler/SmallBudgetPrimeList.lean);
the largest listed prime is 29,791. Above budget 962, the existing Chebyshev
estimate supplies the same bounds.
[SmallBudgetParameters.lean](TranslationTiling/FiniteCompiler/SmallBudgetParameters.lean)
allocates ordinary useful primes asymmetrically: `a_i ≤ 15U/32`, `b_i ≤ U`,
where `U = P*isqrt(P)` and `P = max(w+2,256)` for `w` ordinary channels.
The auxiliary seed primes can be `511237` and `511243`,
above the seed threshold `(5pq)² = 511225`; their common representation
threshold is `4*511243+3`.
[Compiler/SmallBudgetInterval.lean](TranslationTiling/Compiler/SmallBudgetInterval.lean)
bounds ordinary digit primes by `P³` using Chebyshev theta bounds, with
`ln P ≤ P/40` and `sqrt(P³) ≤ P²/16`.
The two seed digit primes remain at most `P⁴`.
Ordinary useful-prime pairs satisfy `a_i*b_i ≤ P³`;
seed pairs satisfy `a_i*b_i ≤ P⁴`.
The effective certificate checks these bounds, giving the common parameter
budget `P^9`.
[BudgetParameters.lean](TranslationTiling/FiniteCompiler/BudgetParameters.lean)
separates this prime budget from the actual channel count. For fewer than
254 ordinary channels it restricts a larger prime allocation; it adds no
channels to the actual compiler.
[Proofs/LogDifferenceBound.lean](TranslationTiling/Proofs/LogDifferenceBound.lean)
keeps the exponential probability estimate, giving a partition modulus
quadratic times a logarithm in the equation count.
[Effective/FreshStack.lean](TranslationTiling/FiniteCompiler/Effective/FreshStack.lean)
implements this bounded partition search and proves coprimality from a bound
on the prime divisors of the finite factor.
[BudgetBounds.lean](TranslationTiling/FiniteCompiler/BudgetBounds.lean)
keeps powers integral and retains the actual ordinary-channel count `w = 28k`:
the cyclic order satisfies `|V|^10 ≤ P^(210*w+280)`.
[FixedBounds.lean](TranslationTiling/FiniteCompiler/FixedBounds.lean)
counts the dependence indices directly, giving at most `(w+2)^2+w+4` tests.
Thus `s ≤ 3^w+w^2+12*w+11 ≤ 3^(w+1)` for `w ≥ 4`.
For the actual minimum `w = 168`, it also proves `P² ≤ 3^(w+1)`.
Stacking uses `X = max(s,P²) ≤ 3^(w+1)`, giving stacked modulus
`R^30 ≤ P^(630*w+930)*3^(60*w+60)`.
[Compiler/SparseGeometryBound.lean](TranslationTiling/Compiler/SparseGeometryBound.lean)
counts each MSS component by `2^24`, independently of its displacement.
[MassBounds.lean](TranslationTiling/FiniteCompiler/MassBounds.lean)
bounds every test tile by `J = D*∏ᵢ(r_i*a_i*b_i) ≤ P^(12*w+20)`, including
the ordinary and seed activation tiles. Their batch counts compensate for
the fixed coordinates within each batch.
[Effective/MassGeometry.lean](TranslationTiling/FiniteCompiler/Effective/MassGeometry.lean)
carries this count through stacking and geometry: the stacked tile has at
most `ℓ*J` points, and the MSS output has at most `2^24*ℓ*J` cubes.
[Rails/](TranslationTiling/Rails/) separates the short planar slots from the
long vertical rail in an eight-layer color partition. Every rail color touches
every planar color, and opposite-face contacts connect the slot set. The
partition, inflated pieces, modified shell, and arbitrary-complement rigidity
are proved for all parameters. The shell expands an `A×A×B` input box by a
volume factor `O(A⁴+A²B)`, using at most `549072*A²*B` cubes after padding `B`
to at least `A²`. The earlier four-layer variant uses `O(A²B²)` cubes.
[Rails/Compiler.lean](TranslationTiling/Rails/Compiler.lean) proves total
computability, correctness, connectivity, and the volume bound for the concrete
compiler output.
[SupportBounds.lean](TranslationTiling/FiniteCompiler/SupportBounds.lean)
uses the exact identity `H(b) = b^6*(b+1)^16+b` to give `H ≤ P^200`.
The connectedness box uses `max(H²,R)`. Counting the actual points gives
volume at most `K₀*H²*max(H²,R)*ℓ*J`, where
`K₀ = 2^24*549072*8003^4 ≤ P^12`.
[Rails/SizeBound.lean](TranslationTiling/Rails/SizeBound.lean) gives
`|F| ≤ P^(33*w+466)*3^(4*w+4) ≤ P^(34*w+467)`.
Earlier estimates remain in `EconomicalBounds.lean`, `CompactParameters.lean`, `CompactBounds.lean`,
`TightParameters.lean`, `TightBounds.lean`, and `FourLayer/SizeBound.lean`.
[Effective/SharpCompiler.lean](TranslationTiling/FiniteCompiler/Effective/SharpCompiler.lean)
combines these bounds with correctness and computability.
[Compiler/MixedLogBound.lean](TranslationTiling/Compiler/MixedLogBound.lean)
converts this estimate directly to the clean logarithmic bound, using code
length at most `(11/4)*log₂(n+4)`.

[Effective/MixedCompiler.lean](TranslationTiling/FiniteCompiler/Effective/MixedCompiler.lean)
proves the same bound for one total computable compiler, with input list length
in place of distinct tile count. For empty input it uses a fixed connected
nontile with at most `2^250` cubes, constructed and verified in
[Compiler/EmptyInputBound.lean](TranslationTiling/Compiler/EmptyInputBound.lean).
The public abstract and motion wrappers use this compiler. All dependencies
are included in the axiom audit.

The earlier binary-payload ternary encoding remains in
[TernarySystem.lean](TranslationTiling/FiniteCompiler/TernarySystem.lean),
[TernaryBounds.lean](TranslationTiling/FiniteCompiler/TernaryBounds.lean), and
[TernaryConstruction.lean](TranslationTiling/FiniteCompiler/TernaryConstruction.lean).
Its bound `C^(3510*C)` and integer-logarithm estimates remain available in
[Compiler/QuasipolynomialBound.lean](TranslationTiling/Compiler/QuasipolynomialBound.lean).

### Explicit numerical bounds

[Compiler/SingleExponentialBound.lean](TranslationTiling/Compiler/SingleExponentialBound.lean)
proves a singly exponential size bound: there is a fixed natural constant `K`
such that `n` distinct Wang tiles have an equivalent nonempty, face-connected
polycube with at most

```text
(n+2)^(K*(n+1)) = 2^O(n log n)
```

distinct unit cubes. `Size.exists_connected_tile_power_bound` gives the complete
geometric conclusion; `Size.singleCubeBound_le_power` bounds its arithmetic
formula `singleCubeBound`. `Size.exists_connected_tile_exp_log_bound` uses the explicit exponent
`K*(n+1)*(Nat.log 2 (n+2)+1)`. The constant is uniform, including for empty
input, and duplicate input entries are ignored.

[Compiler/ExplicitGeneralBound.lean](TranslationTiling/Compiler/ExplicitGeneralBound.lean)
makes the constant explicit: `K = 10^101` suffices in the power bound
(`Size.exists_connected_tile_explicit_power_bound`), and `10^100` suffices as
the coefficient in the binary exponent
(`Size.exists_connected_tile_explicit_exp_log_bound`). It uses useful primes
at most `10^40`, digit primes at most `10^164*(n+2)^2`, and parameter budget
`(n+2)^(10^8*(n+1))`.

[Compiler/PolynomialPrimes.lean](TranslationTiling/Compiler/PolynomialPrimes.lean)
uses Mathlib's elementary Chebyshev estimate to prove the coarse quadratic
bound `Nat.nth Nat.Prime k ≤ (8*(k+1))^2`, then supplies admissible encoding
parameters with polynomially bounded digit primes.
[Compiler/DirectTestCount.lean](TranslationTiling/Compiler/DirectTestCount.lean)
counts the actual cycle-test maps, retaining the fixed useful-output domain
sizes. Stacking and the geometric steps have polynomial cost in the resulting
parameter budget. These are size bounds for bounded admissible choices, not
bounds on the original compiler's least-encoded-certificate search. The new
statements and their supporting lemmas are included in the axiom audit.

[Compiler/ExplicitOneBound.lean](TranslationTiling/Compiler/ExplicitOneBound.lean)
proves the earlier one-tile bound `2^(10^100)` cubes, including connectedness,
nonemptiness, and both tilability directions
(`Size.exists_connected_tile_one_explicit_bound`).
[Compiler/SmallOneParameters.lean](TranslationTiling/Compiler/SmallOneParameters.lean)
bounds the useful primes by `10^40` and digit primes by `10^164`.
The resulting parameter budget is `2^(10^8)` and the equation count is at most
`2^(10^98)`. This specializes the full reduction without deciding the
one-tile Wang problem separately, and ignores duplicate input entries.

### Bit-channel proof structure

The construction uses `O(log n)` channels
with fixed alphabets and cycle maps supported at a single useful-output value.
Its supporting lemmas are checked and included in the axiom audit:

- [Compiler/SparseCycleTests.lean](TranslationTiling/Compiler/SparseCycleTests.lean)
  proves that these maps give the same activity exclusion as arbitrary maps,
  using at most `∏ j, card(P_prev(j))*card(U_j)` tests. It also proves that
  the restricted tiles are nonempty members of the original cycle family.
- [Compiler/BitChannels.lean](TranslationTiling/Compiler/BitChannels.lean)
  constructs finite bit codes and proves that an encoded line-rule array
  decodes coherently along the original column line maps. Copied arithmetic
  digits and distinct bit channels may share a line map.
- [Compiler/BitChannelSize.lean](TranslationTiling/Compiler/BitChannelSize.lean)
  converts `(N*l+2)^(d*(N*l+2))` to a bound with binary exponent
  `K*l*(Nat.log 2 (l+1)+1)`, then substitutes logarithmic bit length.

[FiniteCompiler/](TranslationTiling/FiniteCompiler) generalizes the finite
line-rule backend to variable channel counts, slopes, alphabets, allowed words,
and seed predicates. It retains the original compiler's interface in
`Compiler/`. The generalized activation and common-solution proofs allow
repeated slopes. [BitSystem.lean](TranslationTiling/FiniteCompiler/BitSystem.lean)
encodes the Wang labels in bit channels and proves the full finite-system
equivalence, including the two seed conditions. [GeometryBound.lean](TranslationTiling/FiniteCompiler/GeometryBound.lean)
proves a uniform `C^(d*C)` cube bound for fixed alphabet and slope bounds.
Substituting `C = Sudoku.Width*l+2` and logarithmic bit length gives the public
quasipolynomial bound above.

### Earlier numerical bounds

[Compiler/SimpleSizeBound.lean](TranslationTiling/Compiler/SimpleSizeBound.lean)
proves an earlier fully numerical corollary: for `n` distinct Wang tiles, an equivalent
nonempty, face-connected polycube has at most

```text
2^(2^(10^40 * (n+1)^2))
```

distinct unit cubes. `Size.explicitCubeBound_le_simple` proves that this
dominates the detailed arithmetic bound, and
`Size.exists_connected_tile_simple_bound` includes connectedness, nonemptiness,
and both tilability directions. The proof uses bounded admissible construction
choices, leaving the original compiler unchanged. These results are included
in the axiom audit.

The earlier one-tile bound `2^(2^(10^29))` remains available as
`Size.exists_connected_tile_one_bound` in the same file.

<details>
<summary>Detailed arithmetic bound used in the proof</summary>

[Compiler/ClosedFormBound.lean](TranslationTiling/Compiler/ClosedFormBound.lean)
proves `Size.exists_connected_tile_closed_bound`: for `n` distinct Wang tiles,
there is a nonempty, face-connected polycube with the same tileability and at
most `closedCubeBound n` distinct cubes. All constants in the bound are explicit.
Set `N = 715` (the seed modulus), `C = 30` (the channel count), and define:

```text
U = 4^(2C+1) * (N²+28)
L = 120n+1
Q = 4^(CL+1) * (U²+2U+28)
b = Q^L+U+N+2
c(x) = x²+2x;  J = c(c(c(c(b))))
H = b*(b^5*(J+1)+1)
V = b^(4C+2);  W = (2H+1)²*V
M = 2V*(8*(2^W)^5+V+3)
S = 2000*(2H+M+1)+3
closedCubeBound n = S³*(3S³+6)³
```

The bound is double exponential in `n` and is proved primitive recursive.
The proof uses Bertrand's postulate for bounded prime choices, bounds all
equation tiles inside one finite support, bounds their number by its powerset,
and chooses a bounded stacking prime. The final geometric steps have polynomial
cost in the resulting dimensions. It uses bounded admissible choices instead
of the original compiler's least-encoded-certificate search; it does not claim
that `cubeBound n` below satisfies this formula. The corollary and its supporting
lemmas are included in the axiom audit.

</details>

[Compiler/SizeBound.lean](TranslationTiling/Compiler/SizeBound.lean) proves a
computable bound depending only on the number of **distinct** input Wang tiles.
`Size.boundedCompile_spec` states that `boundedCompile T` is nonempty,
face connected, tileable exactly when `T` is, and has at most
`cubeBound T.toFinset.card` distinct unit cubes. Both the compiler and the bound
are proved computable and included in the axiom audit.

This is a finite-enumeration bound, not a closed-form exponential estimate.
First [ColorNormalization.lean](TranslationTiling/Compiler/ColorNormalization.lean)
renames the at most `4n` colors without changing tileability. Define `C(n)` to be
all length-`n` tile lists with colors below `4n`, and set
`cubeBound n = max { (connectedCompile U).length : U ∈ C(n) }` (with default zero).
The proof establishes `|C(n)| = (4n)^(4n)` and uniform computability of this finite
maximum. No tileability test is used. The original compiler is unchanged;
`boundedCompile` first removes duplicate tiles and normalizes their colors.
This normalization matters because the original compiler's prime choices depend
on the numeric color labels.

[GeometricSizeBound.lean](TranslationTiling/Compiler/GeometricSizeBound.lean)
also proves the separate arithmetic bound
`cubeCount (connectedTile E) ≤ cubeCount E * (3 * cubeSize E ^ 3 + 6) ^ 3`,
where `cubeSize E = 2 * coordinateBound E + 3`. It first bounds the assembly by
the input cube count times Kim's exact shell volume. These results do not
certify the earlier informal numerical estimates or the proposed rotation gadget.

## Definitions and proved inputs

`Tile d` is a list of points of `Fin d → ℤ`, with the canonical primitive-recursive
encoding. List membership interprets it as a finite set: order and duplicate
entries have no effect on tilability. `ExactTiling A F` says that addition from
`A × F` to the entire ambient group is bijective. Translation sets are arbitrary
sets, with no periodicity or finite-support assumption.

`RealTiles F` allows arbitrary real translations of the closed unit-cube union
associated with `F`. Coverage and uniqueness hold almost everywhere for Lebesgue
measure, so shared cube boundaries do not count as overlapping interiors.
`FaceConnected` uses paths of signed coordinate unit steps within the tile.

[ExternalInputs.lean](TranslationTiling/ExternalInputs.lean) imports the proved
inputs used by the compiler. The former `ReductionInputs` hypothesis is removed.

| Proved input | Formal meaning |
| --- | --- |
| Greenfeld–Tao | Decorated Sudoku soundness (`Sudoku.soundness`). |
| Meyerovitch–Sanadhya–Solomon | Arbitrary mixed-tiling rigidity of the two scale-201 component shapes (`MSS.rigidity`). |
| Kim | Arbitrary-tiling coset rigidity and all geometric shell properties (`Kim.cosetRigidity`, `Kim.rigidity`). |
| Bhattacharya | Existence of a fully periodic planar tiling complement (`planarPeriodicity_proved`). |

Meyerovitch–Sanadhya–Solomon rigidity is proved in
`MSS/GridAssembly.lean`. The proof uses singleton isolation to force a forward
ray of centers, coverage to close that ray backwards, and packing to separate
the transverse rows. The main cubes cover the transverse plane. Whole-frame
matching then forces the other coordinate steps and the full cubic grid.
The special frames force both color periods. Reassembly of the marked cells
proves the converse mixed tiling.

Kim's arbitrary-tiling coset rigidity is proved in `Proofs/KimRigidity.lean`.
The shell before its unit modifications consists of aligned 3-blocks. Two
distinct missing points cannot be in one such block. The occupied transverse
rim of a dent therefore excludes coverage by an ordinary block of another
copy. A bump must fill the dent, and the occupied corner block forces its
orientation. This forces all three positive grid steps. Coverage and the
shell's fundamental-domain property then force a complete grid coset.

Bhattacharya's planar periodicity theorem is now proved in
`Proofs/PlanarPeriodicity.lean` using the ported proof chain in `Planar/`.
The theorem supplies a complement with a finite-index subgroup of periods.
It is included in the axiom audit.

Greenfeld–Tao's decorated Sudoku soundness is proved in
`SudokuArithmetic/Soundness.lean`. The proof projects the decorated rule to
each arithmetic component, establishes affine structure on the whole board,
proves compatibility under prime rescaling, and iterates to arbitrary finite
valuation depth. A simultaneous CRT shear makes both components canonical
at the required depths. Constant rows and the tested columns `1`, `p`, and `q`
then provide Wang adjacencies on every finite rectangle; the pinned Wang
dependency supplies compactness. This discharges the Sudoku input without
p-adic compactness or additional hypotheses.

The input statements are defined in `TranslationTiling/External/` and proved
by the modules above. Berger's undecidability and completeness theorems are
proved by the pinned Wang dependency, using its independent Kari–Hooper certificate.

## Checked proofs

| Part | Proof files |
| --- | --- |
| Exact coverage, duplicate/order invariance, additive transport | `Proofs/Basic.lean` |
| Compactness and finite obstruction characterization | `Proofs/Compactness.lean` |
| Primitive-recursive finite satisfiability test; co-RE membership in every fixed dimension | `Proofs/FiniteSearch.lean` |
| Primitive-recursive finite cut test, computable face-connectivity, and connected co-RE membership in every fixed dimension | `Proofs/FiniteConnectivity.lean` |
| Total computable witness search, computable prime search, and decidability from positive certificates | `Proofs/ComputableSearch.lean`, `Proofs/Decidability.lean` |
| Quadrant/plane Wang equivalence; extraction of Wang tilings from an activated label system and Sudoku soundness | `Proofs/Wang.lean`, `Proofs/SudokuSoundness.lean` |
| Last-nonzero-digit arithmetic, two-prime CRT, canonical Sudoku solutions, and unconditional Sudoku–Wang equivalence | `Proofs/Arithmetic.lean`, `Proofs/Canonical.lean`, `Proofs/WordResidues.lean`, `Proofs/CanonicalLineRule.lean` |
| Initial and finite-depth arithmetic structure, rescaling compatibility, decorated rectangle extraction, and Sudoku soundness | `SudokuArithmetic/*.lean` |
| Bounded coefficient equivalence, executable finite word-rule search, and exact enumeration of allowed words | `Proofs/FiniteWordRule.lean` |
| Graph equation and arbitrary-tiling stacking equivalence | `Proofs/Graph.lean`, `Proofs/Stacking*.lean` |
| Existence of fresh prime full-difference partitions and cyclic consolidation | `Proofs/FullDifferencePartition.lean` and its counting lemmas, `Proofs/CyclicStacking.lean` |
| Histogram separability and mass divisibility obstruction | `Proofs/Histogram.lean` |
| Computable dimensional embedding and tiling equivalence | `Proofs/Dimension.lean` |
| Translating a tile preserves tilability | `Proofs/Translation.lean` |
| Integer/real tiling equivalence, including countability of arbitrary real translation sets and a good sampling grid | `Proofs/Euclidean.lean` |
| Unconditional planar periodicity, using finite periodic decomposition and periodic region replacement | `Planar/*.lean`, `Proofs/PlanarPeriodicity.lean` |
| Rectangular periods from a finite-index period subgroup | `Proofs/PeriodicGrid.lean` |
| Primitive-recursive torus certificates, their equivalence with periodic tilings, and planar decidability from periodicity | `Proofs/IntegerResidues.lean`, `Proofs/PeriodicCertificates.lean` |
| Kim's finite color bounds, nonempty pieces, exact block partition, disjoint colors, internal and external piece contacts, and nonempty shells | `Proofs/KimGeometry.lean` |
| Kim's residue representatives, shell fundamental-domain coverage, volume `s³`, disjoint grid translates, and contacts between whole shells | `Proofs/KimResidues.lean`, `Proofs/KimShellGeometry.lean` |
| Kim's coarse color classes, dented pieces, cube boundary, and shell are face connected | `Proofs/FacePaths.lean`, `Proofs/Kim*Connectivity.lean` |
| Unconditional arbitrary-tiling Kim shell coset rigidity | `Proofs/KimBlocks.lean`, `Proofs/KimDefectGeometry.lean`, `Proofs/KimDentForcing.lean`, `Proofs/KimRigidity.lean` |
| Generic shell-assembly equivalence from fundamental-domain coverage and coset rigidity | `Proofs/ShellAssembly.lean` |
| MSS frame geometry and a counterexample to the one-point local forcing argument (not to global rigidity) | `MSS/FrameGeometry.lean`, `MSS/LocalForcingCheck.lean` |
| MSS frame connectivity and separation, neighbors in frames, and uniqueness of the singleton in the punctured body | `MSS/FrameConnectivity.lean`, `MSS/FrameSeparation.lean`, `MSS/FrameIsolation.lean`, `MSS/BodyIsolation.lean` |
| Unconditional arbitrary mixed-tiling MSS rigidity, including both directions | `MSS/FirstBump.lean`, `MSS/FirstPeriod.lean`, `MSS/RayPacking.lean`, `MSS/TransverseCoverage.lean`, `MSS/FrameMatching.lean`, `MSS/CommonForcing.lean`, `MSS/GridCenters.lean`, `MSS/ColorPeriods.lean`, `MSS/GridAssembly.lean` |
| Completeness, undecidability, higher dimensions, connected completeness, and dimension optimality | `Proofs/Complexity.lean`, `Compiler/Main.lean` |

`Examples.lean` checks small finite searches, repeated tile entries,
face-connectivity, and torus certificates, including rejection of folded
overlaps and modulus zero. It also derives real tilability of a single cube.
It uses kernel evaluation.

## Main compiler

`Compiler/Completeness.lean` proves equivalence of the graph, dependence, cycle,
ordinary activation, and paired-seed constraints with Wang tilability. It uses
one common auxiliary solution for completeness and the proved decorated Sudoku
soundness theorem. `Consolidation.lean` stacks the finite family into a cyclic tile.
`LatticeCompiler.lean` proves arbitrary-tiling descent and completeness using the
explicit MSS components. `ConnectedCompiler.lean` applies Kim's shells and proves
face-connectivity. These semantic constructions have corresponding uniform
numerical algorithms, assembled in `Compiler/Main.lean`.

The numerical alphabet and decorated word-rule enumeration are primitive
recursive (`EffectiveWordRule*.lean`, `EffectiveAlphabet.lean`). Prime and block
coefficient searches are total computable (`EffectiveChoices.lean`,
`EffectiveParameters.lean`). Full-difference colorings are found by a total
computable certificate search (`EffectivePartition.lean`). Numerical cyclic
stacking, its tiling equivalence, positivity, and nonemptiness are checked in
`EffectiveStacking.lean`. Lattice assembly and
connected-shell conversion are primitive recursive (`EffectiveLattice.lean`,
`EffectiveConnected.lean`). Activation fibre orderings and batch indices now use
explicit numerical ranks instead of input-dependent arbitrary enumerations.

`EffectiveDependence.lean`, `EffectiveConstraintFamilies.lean`, and
`EffectiveActivationFamily.lean` serialize every dependence, bad-word,
seed-constraint, and activation gadget. `EffectiveCycleCorrect.lean` proves that
the numerical cycle tables represent **every** required finite function and
produce exactly the semantic cycle family. `EffectiveSystem.lean` proves that
the complete serialized family equals the checked finite system, and transports
its common complement through the cyclic CRT equivalence.

`Main.lean` composes this family with the searched full-difference partition,
cyclic stacking, MSS lattice assembly, and Kim shell conversion. It constructs
`wangReduction` and `connectedWangReduction`, proving effectivity, nonemptiness,
arbitrary-tiling soundness and completeness, and face-connectivity. The algorithm
does not depend on proofs of the mathematical inputs.

The optimized compiler is in `FiniteCompiler/Effective/Compiler.lean`.
It computes the ternary-channel input and bounded prime parameters, emits one
fixed cycle test per forbidden tuple, removes duplicate canonical tile descriptions, and searches
for a full-difference partition with the polynomial modulus bound.
`FiniteCompiler/Effective/Correctness.lean` proves answer preservation;
`FiniteCompiler/Effective/SizeBound.lean` proves the closed quasipolynomial bound
for this same computable function. The public reduction theorems combine these
properties, including the six-key replacement for arbitrary Euclidean motions.

The `Computable` proofs establish total recursion on the canonical encodings.
Some definitions use `noncomputable` to express fixed finite tables or searched
witnesses; their uniform effectivity is separately proved. The exhaustive
enumerations are enormous and are intended for the reduction proof.

All mathematical inputs are proved. The public compiler correctness, connected
completeness, Euclidean completeness, and dimension-optimality theorems are
unconditional. No periodicity assumption is imposed on a tiling complement.

The local forcing sentence in MSS Lemma 2.1 does not by itself establish
rigidity. `MSS.unintended_neighbor` gives two disjoint copies of `baseShape`:
one at zero and one translated by `(-214, -1, 200)`. The latter covers
`201 e₂` through its first detached frame, although its translation is not
`201 e₂`. These two copies are not claimed to extend to a tiling. The full rigidity
proof in `MSS/GridAssembly.lean` uses further coverage constraints.

## Online formalizations inspected (October 7, 2026)

The most relevant source is
[`openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling),
already cited by the paper.

- [PlanarPeriodicity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/PlanarPeriodicity.lean)
  contains `plane_tile_has_fullyPeriodic_complement`, the required form of planar
  periodicity. Its 28-module proof closure has been ported, built, and audited
  against this project's pinned dependencies. The lattice bridge discharges
  the Bhattacharya hypothesis.
- [Stacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Stacking.lean)
  and [Activation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Activation.lean)
  provide generic stacking and histogram arguments. Selected parts have been
  ported and checked in this project; see the license/provenance record below.
- [WordRule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/WordRule.lean)
  treats the one-prime arithmetic rule. Its initial affine structure and
  vertical-period obstruction proof closure have been ported. The additional
  finite-depth, two-prime, and decoration arguments in this project prove
  the required decorated soundness theorem.
- [MarkedTileDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/MarkedTileDescent.lean)
  descends fully periodic tilings. That restriction does not provide the
  arbitrary-tiling MSS equivalence required by this reduction.

Targeted web and GitHub searches by authors, paper IDs, and Lean terminology
found no preexisting exact formalization of the decorated two-prime soundness,
the stated MSS rigid-component input, or Kim's coset rigidity input. This is a search result,
not a proof of their absence.

See [third_party/README.md](third_party/README.md) for copied-source provenance.
