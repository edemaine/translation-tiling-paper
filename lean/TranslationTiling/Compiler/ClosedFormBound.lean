import TranslationTiling.Compiler.ClosedGeometryBound

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# A closed-form upper bound

`exists_connected_tile_closed_bound` bounds an equivalent connected monotile
using only the number of distinct Wang tiles. The bound is a composition of
addition, multiplication, and natural-number powers, with fixed constants from
the construction. There is no input-dependent finite maximum or search in it.
It uses bounded admissible prime and stacking choices; it is not a bound on
the original compiler's least-encoded-certificate search.

Writing `N = residueModulus`, `C = N + 2`, `A = arithmeticAlphabet`,
`U = 4^(2C+1)*(N²+p+q+4)`, and `B = U² + 2U + p + q + 3`, the formula is:

* `L = A*n + 1`, `Q = 4^(C*L + 1) * (B + 1)`;
* `b = Q^L + U + N + 2`;
* `c(x) = x² + 2x`, `J = c(c(c(c(b))))`;
* `H = b*(b^5*(J+1)+1)`, `V = b^(4C+2)`, `W = (2H+1)²*V`;
* `M = 2V*(8*(2^W)^5 + V + 3)`;
* `S = 2000*(2H+M+1)+3`;
* `closedCubeBound n = S³*(3S³+6)³`.

In particular, its growth in `n` is double exponential. All constants are
explicit arithmetic expressions in the fixed primes `p = 211`, `q = 223`.
The proof retains
nonemptiness, face connectedness, and both tilability directions. It applies
also to the empty input and ignores duplicate input tiles and output cubes.
-/

namespace TranslationTiling.Compiler.Size

open LeanWang
noncomputable section

def closedCubeBound (n : ℕ) : ℕ :=
  geometryCap (horizontalCap (parameterCap n)) (modulusCap (parameterCap n))

/-- A purely arithmetic formula. Parameters keep Lean from trying to materialize
the enormous fixed powers while elaborating or compiling the definition. -/
noncomputable def arithmeticCubeBound (N C A n : ℕ) : ℕ :=
  let U := 4 ^ (2 * C + 1) * (N ^ 2 + 438)
  let L := A * n + 1
  let Q := 4 ^ (C * L + 1) * (U ^ 2 + 2 * U + 438)
  let b := Q ^ L + U + N + 2
  let c := fun x : ℕ => x * x + 2 * x
  let J := c (c (c (c b)))
  let H := b * (b ^ 5 * (J + 1) + 1)
  let V := b ^ (4 * C + 2)
  let W := (2 * H + 1) ^ 2 * V
  let M := V * (2 * (8 * (2 ^ W) ^ 5 + V + 3))
  let S := 2 * (1000 * (2 * H + M + 1)) + 3
  S ^ 3 * (3 * S ^ 3 + 6) ^ 3

/-- The bound with all constants specified by numerals. -/
noncomputable def explicitCubeBound (n : ℕ) : ℕ :=
  arithmeticCubeBound 2213984809 2213984811 46620 n

theorem closedCubeBound_eq_arithmetic (n : ℕ) :
    closedCubeBound n = arithmeticCubeBound residueModulus channelCount arithmeticAlphabet n := by
  have hsum : Sudoku.p + Sudoku.q = 434 := by norm_num [Sudoku.p, Sudoku.q]
  have hstart : usefulStart + 1 = residueModulus ^ 2 + 438 := by unfold usefulStart; omega
  have hU : usefulCap = 4 ^ (2 * channelCount + 1) * (residueModulus ^ 2 + 438) := by
    unfold usefulCap
    rw [hstart]
  have hB : digitStart + 1 = usefulCap ^ 2 + 2 * usefulCap + 438 := by
    unfold digitStart
    omega
  unfold closedCubeBound arithmeticCubeBound geometryCap latticeSide latticeRadius modulusCap stackCap
    supportVolume finiteCap horizontalCap indexCap pairCap parameterCap lowCap
    digitPrimeBound labelsBound
  simp only [hB, hU]

theorem closedCubeBound_eq_explicit (n : ℕ) : closedCubeBound n = explicitCubeBound n := by
  have hN : residueModulus = 2213984809 := by
    rw [residueModulus_eq]
    norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
  have hC : channelCount = 2213984811 := by rw [channelCount_eq, hN]
  have hA : arithmeticAlphabet = 46620 := by norm_num [arithmeticAlphabet, Sudoku.p, Sudoku.q]
  calc
    closedCubeBound n = arithmeticCubeBound residueModulus channelCount arithmeticAlphabet n :=
      closedCubeBound_eq_arithmetic n
    _ = arithmeticCubeBound 2213984809 2213984811 46620 n := by rw [hN, hC, hA]
    _ = explicitCubeBound n := rfl

@[local fun_prop] theorem natPowerRule {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a ^ g a) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg

/-- Even primitive recursion suffices to evaluate the closed-form bound. -/
theorem closedCubeBound_primrec : Primrec closedCubeBound := by
  unfold closedCubeBound geometryCap latticeSide latticeRadius modulusCap stackCap
    supportVolume finiteCap horizontalCap indexCap pairCap parameterCap lowCap
    digitPrimeBound labelsBound
  fun_prop

theorem explicitCubeBound_primrec : Primrec explicitCubeBound :=
  closedCubeBound_primrec.of_eq closedCubeBound_eq_explicit

/-- Closed-form corollary of the bounded parameter, support, consolidation,
and geometry lemmas. This is an existence bound for bounded admissible choices,
not a claim about the earlier compiler's numerical certificate enumeration. -/
theorem exists_connected_tile_closed_bound (T : TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ closedCubeBound T.toFinset.card := by
  obtain ⟨E, hE⟩ := exists_parameterBudget T.dedup
  obtain ⟨m, hm, hcap, F, hF, hcorrect, hcoord⟩ := exists_bounded_cyclic_tile hE
  obtain ⟨P, hP, hconn, hiff, hcount⟩ :=
    exists_bounded_connected_tile hm hcap F hF hcorrect hcoord
  have hd : TilesPlane T ↔ TilesPlane T.dedup := tilesPlane_congr (by intro t; simp)
  refine ⟨P, hP, hconn, hd.trans hiff, ?_⟩
  change cubeCount P ≤ closedCubeBound T.dedup.length at hcount
  simpa only [List.card_toFinset] using hcount

/-- A numerals-only version of the closed-form corollary. -/
theorem exists_connected_tile_explicit_bound (T : TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ explicitCubeBound T.toFinset.card := by
  simpa only [closedCubeBound_eq_explicit] using exists_connected_tile_closed_bound T

end
end TranslationTiling.Compiler.Size
