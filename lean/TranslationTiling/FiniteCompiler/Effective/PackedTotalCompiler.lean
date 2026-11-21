import TranslationTiling.FiniteCompiler.PackedCompiler
import TranslationTiling.Compiler.PackedLogBound

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler
open scoped Classical
noncomputable section
set_option exponentiation.threshold 10000

private def profile (n : ℕ) : Packed.CheckedProfile :=
  if n ≤ 1 then Packed.checked1 else if n ≤ 12 then Packed.checked12
  else if n ≤ 36 then Packed.checked36 else Packed.checked243

private def GuardedResult (T : LeanWang.TileSet) (U : Tile 3) : Prop :=
  U ≠ [] ∧ FaceConnected U ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
    U.length ≤ 2^(profile T.length).exponent

private theorem guarded_witness (T : LeanWang.TileSet) (hlo : 0 < T.length) (hhi : T.length ≤ 242) :
    ∃ U, GuardedResult T U := by
  apply Packed.tile_exists _ T hlo
  unfold profile
  split_ifs with h₁ h₁₂ h₃₆
  · exact h₁
  · exact h₁₂
  · exact h₃₆
  · exact hhi.trans (by decide : 242 ≤ 243)

private def count (k : Fin 242) : ℕ := 1+k.val

private theorem count_pos (k : Fin 242) : 0 < count k := by unfold count; omega

private def finiteTile (k : Fin 242) (i : Fin (Size.inputs (count k)).length) : Tile 3 :=
  (guarded_witness (Size.decodeInput (count k) i)
    (by rw [Size.decodeInput_length]; unfold count; omega)
    (by rw [Size.decodeInput_length]; unfold count; omega)).choose

private def guardedCompile (k : Fin 242) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Size.inputIndex (count k) (count_pos k) T)

private theorem guardedCompile_primrec (k : Fin 242) : Primrec (guardedCompile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).comp (Size.inputIndex_primrec (count k) (count_pos k))

private theorem guardedCompile_facts (k : Fin 242) (T : LeanWang.TileSet) (hlen : T.length = count k) :
    GuardedResult T (guardedCompile k T) := by
  have h : GuardedResult (Size.decodeInput (count k) (Size.inputIndex (count k) (count_pos k) T))
      (guardedCompile k T) :=
    (guarded_witness (Size.decodeInput (count k) (Size.inputIndex (count k) (count_pos k) T))
      (by rw [Size.decodeInput_length]; unfold count; omega)
      (by rw [Size.decodeInput_length]; unfold count; omega)).choose_spec
  rw [Size.decodeInput_index _ _ _ hlen] at h
  obtain ⟨hne,hc,ht,hsize⟩ := h
  exact ⟨hne,hc,(Size.normalize_tilesPlane T).symm.trans ht,by simpa using hsize⟩

private def index (T : LeanWang.TileSet) : Fin 242 :=
  ⟨(T.length-1)%242,Nat.mod_lt _ (by decide)⟩

/-- The guarded encoder needs a nonempty alphabet. A tile with unequal opposite edge colors
represents the empty alphabet, so the geometric construction is the same. -/
private def nonemptyInput (T : LeanWang.TileSet) : LeanWang.TileSet :=
  if T.length = 0 then [⟨0,1,0,0⟩] else T

private theorem nonemptyInput_primrec : Primrec nonemptyInput := by
  have h : Primrec (fun T : LeanWang.TileSet => decide (T.length=0)) := by fun_prop
  exact (h.cond (Primrec.const [⟨0,1,0,0⟩]) Primrec.id).of_eq
    (fun T => by simp only [nonemptyInput, Bool.cond_decide, id_eq])

private theorem nonemptyInput_length (T : LeanWang.TileSet) :
    (nonemptyInput T).length = max 1 T.length := by
  unfold nonemptyInput
  split
  · simp_all
  · exact (max_eq_right (by omega)).symm

private theorem nonemptyInput_tiles (T : LeanWang.TileSet) :
    LeanWang.TilesPlane (nonemptyInput T) ↔ LeanWang.TilesPlane T := by
  cases T with
  | nil =>
    simp only [nonemptyInput, List.length_nil, ite_true]
    apply iff_of_false
    · rintro ⟨w,hw⟩
      have h (x : ℤ × ℤ) : (w x).val = ⟨0,1,0,0⟩ := List.mem_singleton.mp (w x).property
      have hh := hw.2 (0,0)
      simp [LeanWang.WangTile.VMatches,h] at hh
    · rintro ⟨w,_⟩
      exact List.not_mem_nil (w (0,0)).property
  | cons t T => simp [nonemptyInput]

private theorem index_count (T : LeanWang.TileSet) (hlo : 0 < T.length) (hhi : T.length ≤ 242) :
    T.length = count (index T) := by
  simp only [count,index,Nat.mod_eq_of_lt (show T.length-1<242 by omega)]
  omega

private theorem profile_bound (n : ℕ) (hn : n ≤ 242) :
    ((2^(profile (max 1 n)).exponent : ℕ) : ℝ) ≤ Size.packedBound n := by
  have hbudget (d : ℕ) (hd : d ≤ 2392) : ((2^d : ℕ) : ℝ) ≤ Size.packedBound n := by
    apply le_trans _ (le_max_right _ _)
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hd
  unfold profile
  split_ifs with h₁ h₁₂ h₃₆
  · exact hbudget 2112 (by decide)
  · exact hbudget 2392 (by decide)
  · apply le_trans _ (le_max_left _ _)
    apply Size.packed_dyadic_real_bound (le_refl _)
    exact Size.packed_exponent (m:=13) (a:=49) (b:=12) (c:=69) (d:=34) (by omega)
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by change (2573 : ℝ) ≤ _; norm_num)
  · apply le_trans _ (le_max_left _ _)
    apply Size.packed_dyadic_real_bound (le_refl _)
    exact Size.packed_exponent (m:=37) (a:=5) (b:=1) (c:=2) (d:=1) (by omega)
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by change (2876 : ℝ) ≤ _; norm_num)

def packedCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length ≤ 242 then guardedCompile (index (nonemptyInput T)) (nonemptyInput T)
  else sparseStripCore T

theorem packedCompile_computable : Computable packedCompile := by
  have hix : Primrec index := by
    apply Primrec.fin_val_iff.mp
    unfold index
    fun_prop
  have hguard := (Primrec.fin_curry₁.mpr guardedCompile_primrec).comp hix Primrec.id
  have hm : Primrec (fun T : LeanWang.TileSet => decide (T.length≤242)) := by fun_prop
  exact (hm.to_comp.cond (hguard.comp nonemptyInput_primrec).to_comp
    sparseStripCore_computable).of_eq
    (fun T => by simp only [packedCompile,Bool.cond_decide,id_eq])

theorem packedCompile_facts (T : LeanWang.TileSet) :
    packedCompile T ≠ [] ∧ FaceConnected (packedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (packedCompile T)) ∧
    ((packedCompile T).length : ℝ) ≤ Size.packedBound T.length := by
  by_cases hm : T.length ≤ 242
  · rw [packedCompile, if_pos hm]
    have hlen := nonemptyInput_length T
    have h := index_count (nonemptyInput T) (by omega) (by omega)
    obtain ⟨hne,hc,ht,hsize⟩ := guardedCompile_facts (index (nonemptyInput T)) (nonemptyInput T) h
    rw [hlen] at hsize
    exact ⟨hne,hc,(nonemptyInput_tiles T).symm.trans ht,
      (show (_ : ℝ) ≤ ((2^(profile (max 1 T.length)).exponent : ℕ) : ℝ) by exact_mod_cast hsize).trans
        (profile_bound T.length hm)⟩
  · rw [packedCompile, if_neg hm]
    obtain ⟨hne,hc,ht,_⟩ := sparseStripCore_facts T (by omega)
    exact ⟨hne,hc,ht,(Size.sparseStripCore_packed_bound T (by omega)).trans (le_max_left _ _)⟩

theorem packedCompile_real_bound (T : LeanWang.TileSet) :
    ((packedCompile T).length : ℝ) ≤ Size.packedBound T.length :=
  (packedCompile_facts T).2.2.2

/-- The one-symbol instance of the same guarded compiler uses the capacity-one prime table. -/
theorem packedCompile_one_bound (T : LeanWang.TileSet) (h : T.length = 1) :
    (packedCompile T).length ≤ 2^2112 := by
  have hin := nonemptyInput_length T
  rw [h] at hin
  norm_num at hin
  rw [packedCompile, if_pos (by omega)]
  have hidx := index_count (nonemptyInput T) (by omega) (by omega)
  have hb := (guardedCompile_facts (index (nonemptyInput T)) (nonemptyInput T) hidx).2.2.2
  simpa only [hin,profile,le_refl,if_true,Packed.checked1] using hb

end
end TranslationTiling.FiniteCompiler.Effective

namespace TranslationTiling.Compiler.Size

/-- Mixed-radix compiler bound for the number of distinct Wang tiles. -/
theorem exists_connected_tile_packed_quasipolynomial_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      (cubeCount P : ℝ) ≤ packedBound T.toFinset.card := by
  let P := FiniteCompiler.Effective.packedCompile T.dedup
  obtain ⟨hne,hc,hi,hsize⟩ := FiniteCompiler.Effective.packedCompile_facts T.dedup
  have he : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨P,hne,hc,he.trans hi,?_⟩
  have hcount : (cubeCount P : ℝ) ≤ (P.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le P
  exact hcount.trans (by simpa only [List.card_toFinset] using hsize)

end TranslationTiling.Compiler.Size
