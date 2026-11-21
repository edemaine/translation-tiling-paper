import TranslationTiling.FiniteCompiler.PackedCompiler
import TranslationTiling.Compiler.PackedLogBound
import TranslationTiling.Compiler.FiniteSmallLookup
import TranslationTiling.FiniteCompiler.Effective.SevenCompiler

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler
open scoped Classical
noncomputable section
set_option exponentiation.threshold 10000

private def Good (T : LeanWang.TileSet) (U : Tile 3) : Prop :=
  U ≠ [] ∧ FaceConnected U ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
    (U.length : ℝ) ≤ ((T.length : ℝ)+4)^(312*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))

private theorem small_exponent (n : ℕ) :
    (250 : ℝ) ≤ 312*Real.logb 2 ((n : ℝ)+4)*Real.logb 2 (Real.logb 2 ((n : ℝ)+4)) :=
  Size.packed_exponent (m:=0) (a:=2) (b:=1) (c:=1) (d:=1) (by omega)
    (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem middle_witness (T : LeanWang.TileSet) (hlo : 6 ≤ T.length) (hhi : T.length ≤ 242) :
    ∃ U, Good T U := by
  by_cases hsmall : T.length ≤ 10
  · let U := Size.smallLookup T.length (by omega) T
    obtain ⟨hne,hc,ht,hb⟩ := Size.smallLookup_facts T.length (by omega) T rfl
    exact ⟨U,hne,hc,ht,Size.packed_dyadic_real_bound hb (small_exponent _)⟩
  by_cases h12 : T.length ≤ 12
  · obtain ⟨U,hne,hc,ht,hb⟩ := Packed.tile_exists Packed.checked12 T (by omega)
      (show T.length ≤ 12 from h12)
    refine ⟨U,hne,hc,ht,Size.packed_dyadic_real_bound hb ?_⟩
    exact Size.packed_exponent (m:=11) (a:=82) (b:=21) (c:=55) (d:=28) (by omega)
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by change (2392 : ℝ) ≤ _; norm_num)
  by_cases h36 : T.length ≤ 36
  · obtain ⟨U,hne,hc,ht,hb⟩ := Packed.tile_exists Packed.checked36 T (by omega)
      (show T.length ≤ 36 from h36)
    refine ⟨U,hne,hc,ht,Size.packed_dyadic_real_bound hb ?_⟩
    exact Size.packed_exponent (m:=13) (a:=49) (b:=12) (c:=69) (d:=34) (by omega)
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by change (2573 : ℝ) ≤ _; norm_num)
  · obtain ⟨U,hne,hc,ht,hb⟩ := Packed.tile_exists Packed.checked243 T (by omega)
      (show T.length ≤ 243 from by omega)
    refine ⟨U,hne,hc,ht,Size.packed_dyadic_real_bound hb ?_⟩
    exact Size.packed_exponent (m:=37) (a:=5) (b:=1) (c:=2) (d:=1) (by omega)
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by change (2876 : ℝ) ≤ _; norm_num)

private def count (k : Fin 237) : ℕ := 6+k.val

private theorem count_pos (k : Fin 237) : 0 < count k := by unfold count; omega

private def finiteTile (k : Fin 237) (i : Fin (Size.inputs (count k)).length) : Tile 3 :=
  (middle_witness (Size.decodeInput (count k) i)
    (by rw [Size.decodeInput_length]; unfold count; omega)
    (by rw [Size.decodeInput_length]; unfold count; omega)).choose

private def midCompile (k : Fin 237) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Size.inputIndex (count k) (count_pos k) T)

private theorem midCompile_primrec (k : Fin 237) : Primrec (midCompile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).comp (Size.inputIndex_primrec (count k) (count_pos k))

private theorem midCompile_good (k : Fin 237) (T : LeanWang.TileSet) (hlen : T.length = count k) :
    Good T (midCompile k T) := by
  have h : Good (Size.decodeInput (count k) (Size.inputIndex (count k) (count_pos k) T))
      (midCompile k T) :=
    (middle_witness (Size.decodeInput (count k) (Size.inputIndex (count k) (count_pos k) T))
      (by rw [Size.decodeInput_length]; unfold count; omega)
      (by rw [Size.decodeInput_length]; unfold count; omega)).choose_spec
  rw [Size.decodeInput_index _ _ _ hlen] at h
  obtain ⟨hne,hc,ht,hsize⟩ := h
  exact ⟨hne,hc,(Size.normalize_tilesPlane T).symm.trans ht,by simpa using hsize⟩


private def index (T : LeanWang.TileSet) : Fin 237 :=
  ⟨(T.length-6)%237,Nat.mod_lt _ (by decide)⟩

def packedCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length ≤ 5 then sevenCompile T
  else if T.length ≤ 242 then midCompile (index T) T else sparseStripCore T

theorem packedCompile_computable : Computable packedCompile := by
  have hix : Primrec index := by
    apply Primrec.fin_val_iff.mp
    unfold index
    fun_prop
  have hmid := (Primrec.fin_curry₁.mpr midCompile_primrec).comp hix Primrec.id
  have hs : Primrec (fun T : LeanWang.TileSet => decide (T.length≤5)) := by fun_prop
  have hm : Primrec (fun T : LeanWang.TileSet => decide (T.length≤242)) := by fun_prop
  exact (hs.to_comp.cond sevenCompile_computable
    (hm.to_comp.cond hmid.to_comp sparseStripCore_computable)).of_eq
    (fun T => by simp only [packedCompile,Bool.cond_decide,id_eq])

theorem packedCompile_facts (T : LeanWang.TileSet) :
    packedCompile T ≠ [] ∧ FaceConnected (packedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (packedCompile T)) ∧
    ((packedCompile T).length : ℝ) ≤ ((T.length : ℝ)+4)^
      (312*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  by_cases hs : T.length ≤ 5
  · rw [show packedCompile T=sevenCompile T by simp [packedCompile,hs]]
    obtain ⟨hne,hc,ht,_⟩ := sevenCompile_checked_facts T
    exact ⟨hne,hc,ht,Size.packed_dyadic_real_bound
      (sevenCompile_checked_small_bound T hs) (small_exponent _)⟩
  by_cases hm : T.length ≤ 242
  · rw [show packedCompile T=midCompile (index T) T by simp [packedCompile,hs,hm]]
    have hlen : T.length = count (index T) := by
      simp only [count,index,Nat.mod_eq_of_lt (show T.length-6<237 by omega)]
      omega
    exact midCompile_good _ _ hlen
  · rw [show packedCompile T=sparseStripCore T by simp [packedCompile,hs,hm]]
    obtain ⟨hne,hc,ht,_⟩ := sparseStripCore_facts T (by omega)
    exact ⟨hne,hc,ht,Size.sparseStripCore_packed_bound T (by omega)⟩

theorem packedCompile_real_bound (T : LeanWang.TileSet) :
    ((packedCompile T).length : ℝ) ≤ ((T.length : ℝ)+4)^
      (312*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) :=
  (packedCompile_facts T).2.2.2


end
end TranslationTiling.FiniteCompiler.Effective

namespace TranslationTiling.Compiler.Size

/-- The mixed-radix compiler gives a coefficient of 312 for the real iterated-log bound. -/
theorem exists_connected_tile_packed_quasipolynomial_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      (cubeCount P : ℝ) ≤ ((T.toFinset.card : ℝ)+4)^
        (312*Real.logb 2 (Real.logb 2 ((T.toFinset.card : ℝ)+4))) := by
  let P := FiniteCompiler.Effective.packedCompile T.dedup
  obtain ⟨hne,hc,hi,hsize⟩ := FiniteCompiler.Effective.packedCompile_facts T.dedup
  have he : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨P,hne,hc,he.trans hi,?_⟩
  have hcount : (cubeCount P : ℝ) ≤ (P.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le P
  exact hcount.trans (by simpa only [List.card_toFinset] using hsize)

end TranslationTiling.Compiler.Size
