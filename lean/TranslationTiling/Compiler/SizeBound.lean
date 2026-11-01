import TranslationTiling.Compiler.Main
import TranslationTiling.Compiler.ColorNormalization
import TranslationTiling.Compiler.EffectiveLists

/-!
# A computable cube bound depending only on the number of Wang tiles

This is a finite-enumeration bound, not an elementary or numerical estimate.
Normalize the at most `4 * n` colors, enumerate all length-`n` inputs over
that palette, and maximize the lengths of their connected compiled tiles.
There are exactly `(4 * n) ^ (4 * n)` candidates. The maximum is computable
because the existing connected compiler is total computable; no tilability
test, undecidable oracle, or search for a smaller equivalent tile is used.

`boundedCompile` applies this normalization to the distinct input tiles.
The original compiler is unchanged. `boundedCompile_spec` gives the
tilability equivalence, connectedness, nonemptiness, and cube bound together.
The bound counts distinct cubes, not merely entries of their encoding list.
-/

namespace TranslationTiling.Compiler.Size

open LeanWang
open TranslationTiling.Compiler.Effective

/-- All tiles whose four colors are less than `c`. -/
def palette (c : ℕ) : TileSet :=
  (List.range c).flatMap fun n => (List.range c).flatMap fun s =>
    (List.range c).flatMap fun e => (List.range c).map fun w => WangTile.ofTuple (n, s, e, w)

theorem mem_palette (c : ℕ) (t : WangTile) :
    t ∈ palette c ↔ t.n < c ∧ t.s < c ∧ t.e < c ∧ t.w < c := by
  cases t
  simp [palette, WangTile.ofTuple, List.mem_flatMap, List.mem_map, WangTile.mk.injEq]

@[simp] theorem palette_length (c : ℕ) : (palette c).length = c ^ 4 := by
  simp [palette, List.length_flatMap, List.map_const', List.sum_replicate, Nat.pow_succ,
    Nat.mul_assoc]

/-- A finite list containing every normalized input with `n` tile entries. -/
def inputs (n : ℕ) : List TileSet := strings (palette (4 * n)) n

theorem strings_length {α : Type*} (xs : List α) (n : ℕ) :
    (strings xs n).length = xs.length ^ n := by
  induction n with
  | zero => simp [strings]
  | succ n ih => simp [strings, List.length_flatMap, ih, List.map_const', List.sum_replicate,
      Nat.pow_succ, Nat.mul_comm]

/-- The enumeration size is explicit, including `n = 0`. -/
theorem inputs_length (n : ℕ) : (inputs n).length = (4 * n) ^ (4 * n) := by
  rw [inputs, strings_length, palette_length, ← pow_mul]

theorem normalize_mem_inputs (T : TileSet) : normalize T ∈ inputs T.length := by
  apply (mem_strings _ _ _).mpr
  exact ⟨normalize_length T, fun t ht => (mem_palette _ _).mpr (normalize_colors_lt ht)⟩

def maximum (xs : List ℕ) : ℕ := xs.foldr max 0

theorem le_maximum {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maximum xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- A concrete total computable bound, obtained by a specified finite maximum.
It is independent of color labels, input order, and tilability. -/
noncomputable def cubeBound (n : ℕ) : ℕ :=
  maximum ((inputs n).map fun T => (connectedCompile T).length)

attribute [local fun_prop] WangTile.ofTuple_primrec

@[fun_prop] theorem palette_primrec : Primrec palette := by
  unfold palette
  fun_prop

@[fun_prop] theorem inputs_primrec : Primrec inputs := by
  unfold inputs
  exact strings_primrec.comp ((palette_primrec.comp (by fun_prop)).pair Primrec.id)

@[fun_prop] theorem maximum_primrec : Primrec maximum := by
  unfold maximum
  apply foldList (h := fun (_ : List ℕ) (p : ℕ × ℕ) => max p.1 p.2)
    Primrec.id (Primrec.const 0)
  fun_prop

theorem cubeBound_computable : Computable cubeBound := by
  have hm : Computable (fun n =>
      (inputs n).map fun T => (connectedCompile T).length) :=
    computableListMap inputs_primrec.to_comp
      ((Computable.list_length.comp connectedCompile_computable).comp Computable.snd)
  exact maximum_primrec.to_comp.comp hm

theorem normalized_length_le (T : TileSet) :
    (connectedCompile (normalize T)).length ≤ cubeBound T.length :=
  le_maximum (List.mem_map.mpr ⟨normalize T, normalize_mem_inputs T, rfl⟩)

/-- Number of distinct lattice cubes; repeated list entries do not count twice. -/
def cubeCount (F : Tile 3) : ℕ := F.toFinset.card

theorem cubeCount_le_length (F : Tile 3) : cubeCount F ≤ F.length :=
  List.toFinset_card_le F

/-- The connected compiler with harmless duplicate removal and color normalization. -/
noncomputable def boundedCompile (T : TileSet) : Tile 3 :=
  connectedCompile (normalize T.dedup)

theorem boundedCompile_computable : Computable boundedCompile :=
  connectedCompile_computable.comp (normalize_primrec.to_comp.comp dedup_primrec.to_comp)

theorem boundedCompile_correct (T : TileSet) :
    TilesPlane T ↔ TranslationTiling.Tiles (boundedCompile T) := by
  have hd : TilesPlane T ↔ TilesPlane T.dedup :=
    tilesPlane_congr (by intro t; simp)
  exact (hd.trans (normalize_tilesPlane T.dedup).symm).trans
    (connectedCompile_correct _)

theorem boundedCompile_cubeCount_le (T : TileSet) :
    cubeCount (boundedCompile T) ≤ cubeBound T.toFinset.card := by
  have hlen : T.dedup.length = T.toFinset.card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup T)]
    simp
  exact (cubeCount_le_length _).trans (hlen ▸ normalized_length_le T.dedup)

/-- A count-bounded, connected, nonempty monotile with the same tilability.
All conclusions hold also for the empty input set. -/
theorem boundedCompile_spec (T : TileSet) :
    boundedCompile T ≠ [] ∧ FaceConnected (boundedCompile T) ∧
      (TilesPlane T ↔ TranslationTiling.Tiles (boundedCompile T)) ∧
      cubeCount (boundedCompile T) ≤ cubeBound T.toFinset.card :=
  ⟨connectedCompile_nonempty _, connectedCompile_connected _,
    boundedCompile_correct T, boundedCompile_cubeCount_le T⟩

end TranslationTiling.Compiler.Size
