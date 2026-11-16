import TranslationTiling.Rails.Assembly
import TranslationTiling.Compiler.EffectiveLists
import TranslationTiling.FourLayer.Compiler

namespace TranslationTiling.Rails
open FourLayer (Rect gridMap radius side shift shifted shifted_primrec side_primrec)
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] FourLayer.side FourLayer.radius

def connectedTile (E : Tile 3) (H M : ℕ) : Tile 3 :=
  (assembly (shifted E H M) (side H) (max ((side H)^2) (side M))).dedup

private theorem assembly_aux_primrec : Primrec (fun z : Tile 3×Tile 3×(Fin 3→ℕ) =>
    z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v) := by
  fun_prop

set_option maxHeartbeats 50000 in
theorem connectedTile_computable : Computable (fun z : Tile 3×ℕ×ℕ => connectedTile z.1 z.2.1 z.2.2) := by
  unfold connectedTile assembly
  have hp : Primrec (fun z : Tile 3×ℕ×ℕ => (side z.2.1,max ((side z.2.1)^2) (side z.2.2))) := by simp only [pow_two]; unfold side radius; fun_prop
  have hs := Computable.comp (f:=fun z : ℕ×ℕ => shell z.1 z.2)
    (g:=fun z : Tile 3×ℕ×ℕ => (side z.2.1,max ((side z.2.1)^2) (side z.2.2))) shell_computable hp.to_comp
  have hscale := Primrec.comp (f:=fun z : ℕ×ℕ => shellScales z.1 z.2)
    (g:=fun z : Tile 3×ℕ×ℕ => (side z.2.1,max ((side z.2.1)^2) (side z.2.2))) shellScales_primrec hp
  have htuple := shifted_primrec.to_comp.pair (hs.pair hscale.to_comp)
  have hout := Computable.comp (f:=fun z : Tile 3×Tile 3×(Fin 3→ℕ) =>
    z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v)
    (g:=fun z : Tile 3×ℕ×ℕ => (shifted z.1 z.2.1 z.2.2,
      shell (side z.2.1) (max ((side z.2.1)^2) (side z.2.2)),
      shellScales (side z.2.1) (max ((side z.2.1)^2) (side z.2.2)))) assembly_aux_primrec.to_comp htuple
  have hd := (dedup_primrec (α:=Lattice 3)).to_comp.comp hout
  dsimp only at hd
  exact hd

theorem connectedTile_correct (E : Tile 3) (H M : ℕ) :
    TranslationTiling.Tiles (connectedTile E H M) ↔ TranslationTiling.Tiles E := by
  have ht := (assembly_correct (shifted E H M) (side H) (max ((side H)^2) (side M))).trans
    (tiles_translate_iff E.dedup (shift H M))
  simpa only [connectedTile,shifted,TranslationTiling.Tiles,List.mem_dedup] using ht

private theorem rect_mono {s t : Fin 3→ℕ} (h : ∀ i, s i≤t i) {v : Lattice 3}
    (hv : Rect s v) : Rect t v := by
  intro i
  exact ⟨(hv i).1,(hv i).2.trans_le (Int.ofNat_le.mpr (h i))⟩

private theorem padded_widths (A B : ℕ) (hA : A≤A^2) : ∀ i : Fin 3,
    (![A,A,max A B] : Fin 3→ℕ) i≤(![A,A,max (A^2) B] : Fin 3→ℕ) i := by
  intro i
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact max_le_max hA le_rfl

set_option maxHeartbeats 50000 in
theorem shifted_in_box (E : Tile 3) (H M : ℕ)
    (hE : ∀ u∈E, (u 0).natAbs≤radius H ∧ (u 1).natAbs≤radius H ∧ (u 2).natAbs≤radius M) :
    ∀ u∈shifted E H M, Rect ![side H,side H,max ((side H)^2) (side M)] u := by
  have hside : side H≤(side H)^2 := by
    have hh : 1≤side H := by unfold side; omega
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  intro u hu
  exact rect_mono (padded_widths (side H) (side M) hside) (FourLayer.shifted_in_box E H M hE u hu)

theorem connectedTile_connected (E : Tile 3) (H M : ℕ)
    (hE : ∀ u∈E, (u 0).natAbs≤radius H ∧ (u 1).natAbs≤radius H ∧ (u 2).natAbs≤radius M) :
    FaceConnected (connectedTile E H M) := by
  simpa only [connectedTile,FaceConnected,List.mem_dedup] using
    assembly_connected (shifted E H M) (side H) (max ((side H)^2) (side M))
      (by unfold side; omega) (le_max_left _ _) (shifted_in_box E H M hE)

theorem connectedTile_nonempty (E : Tile 3) (H M : ℕ) (hE : E≠[]) : connectedTile E H M≠[] := by
  apply (List.dedup_eq_nil _).not.mpr
  apply assembly_nonempty
  intro he
  exact hE ((List.dedup_eq_nil _).mp (List.map_eq_nil_iff.mp he))

theorem connectedTile_length_mass (E : Tile 3) (H M : ℕ) (hH : 1≤H) (hHM : H^2≤M) :
    (connectedTile E H M).length≤Compiler.Size.cubeCount E*(549072*8003^4)*H^2*M := by
  have hA : side H≤8003*H := by unfold side radius; omega
  have hH2 : H≤H^2 := by nlinarith
  have hB : max ((side H)^2) (side M)≤8003^2*M := by
    apply max_le
    · calc
        (side H)^2 ≤ (8003*H)^2 := Nat.pow_le_pow_left hA 2
        _ = 8003^2*H^2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hHM
    · have hs : side M≤8003*M := by unfold side radius; omega
      exact hs.trans (Nat.mul_le_mul_right _ (by norm_num : 8003≤8003^2))
  have hs := shell_length_le (side H) (max ((side H)^2) (side M))
    (by unfold side; omega) (le_max_left _ _)
  have hlen : (assembly (shifted E H M) (side H) (max ((side H)^2) (side M))).length=
      E.dedup.length*(shell (side H) (max ((side H)^2) (side M))).length := by
    simp [assembly,shifted,List.length_flatMap,List.length_map,Function.comp_def,List.map_const,List.sum_replicate]
  have hraw : E.dedup.length=Compiler.Size.cubeCount E := by rw [←List.card_toFinset]; rfl
  calc
    _ ≤ (assembly (shifted E H M) (side H) (max ((side H)^2) (side M))).length := by
      simpa only [connectedTile,List.card_toFinset] using List.toFinset_card_le
        (assembly (shifted E H M) (side H) (max ((side H)^2) (side M)))
    _ ≤ Compiler.Size.cubeCount E*(549072*(8003*H)^2*(8003^2*M)) := by
      rw [hlen,hraw]
      exact Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 2)) hB))
    _ = _ := by ring

end
end TranslationTiling.Rails
