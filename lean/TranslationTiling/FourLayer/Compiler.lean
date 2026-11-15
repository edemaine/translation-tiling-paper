import TranslationTiling.FourLayer.Assembly
import TranslationTiling.Compiler.EffectiveLists

namespace TranslationTiling.FourLayer
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 100000

def radius (H : ℕ) := 1000*(2*H+1)
def side (H : ℕ) := 2*radius H+3
def shift (H M : ℕ) : Lattice 3 := ![(radius H:ℤ),(radius H:ℤ),(radius M:ℤ)]
def shifted (E : Tile 3) (H M : ℕ) : Tile 3 := E.dedup.map fun u => u+shift H M

def connectedTile (E : Tile 3) (H M : ℕ) : Tile 3 :=
  (assembly (shifted E H M) (side H) (max (side H) (side M))).dedup

@[fun_prop] theorem shifted_primrec : Primrec (fun z : Tile 3×ℕ×ℕ => shifted z.1 z.2.1 z.2.2) := by
  have hs : Primrec (fun z : ℕ×ℕ => shift z.1 z.2) := by
    apply piValue
    intro i
    fin_cases i <;> change Primrec (fun z : ℕ×ℕ => (radius _:ℤ)) <;> unfold radius <;> fun_prop
  unfold shifted
  apply mapList (dedup_primrec.comp Primrec.fst)
  apply Compiler.latticePlus Primrec.snd
  exact hs.comp (by fun_prop)

@[fun_prop] theorem side_primrec : Primrec side := by unfold side radius; fun_prop

private theorem assembly_aux_primrec : Primrec (fun z : Tile 3×Tile 3×(Fin 3→ℕ) =>
    z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v) := by
  fun_prop

theorem connectedTile_computable : Computable (fun z : Tile 3×ℕ×ℕ => connectedTile z.1 z.2.1 z.2.2) := by
  unfold connectedTile assembly
  have hp : Primrec (fun z : Tile 3×ℕ×ℕ => (side z.2.1,max (side z.2.1) (side z.2.2))) := by fun_prop
  have hs := Computable.comp (f:=fun z : ℕ×ℕ => shell z.1 z.2)
    (g:=fun z : Tile 3×ℕ×ℕ => (side z.2.1,max (side z.2.1) (side z.2.2))) shell_computable hp.to_comp
  have hscale := Primrec.comp (f:=fun z : ℕ×ℕ => shellScales z.1 z.2)
    (g:=fun z : Tile 3×ℕ×ℕ => (side z.2.1,max (side z.2.1) (side z.2.2))) shellScales_primrec hp
  have htuple := shifted_primrec.to_comp.pair (hs.pair hscale.to_comp)
  have hout := Computable.comp (f:=fun z : Tile 3×Tile 3×(Fin 3→ℕ) =>
    z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v)
    (g:=fun z : Tile 3×ℕ×ℕ => (shifted z.1 z.2.1 z.2.2,
      shell (side z.2.1) (max (side z.2.1) (side z.2.2)),
      shellScales (side z.2.1) (max (side z.2.1) (side z.2.2)))) assembly_aux_primrec.to_comp htuple
  have hd := (dedup_primrec (α:=Lattice 3)).to_comp.comp hout
  dsimp only at hd
  exact hd

theorem connectedTile_correct (E : Tile 3) (H M : ℕ) :
    TranslationTiling.Tiles (connectedTile E H M) ↔ TranslationTiling.Tiles E := by
  have ht := (assembly_correct (shifted E H M) (side H) (max (side H) (side M))).trans
    (tiles_translate_iff E.dedup (shift H M))
  simpa only [connectedTile,shifted,TranslationTiling.Tiles,List.mem_dedup] using ht

theorem shifted_in_box (E : Tile 3) (H M : ℕ)
    (hE : ∀ u∈E, (u 0).natAbs≤radius H ∧ (u 1).natAbs≤radius H ∧ (u 2).natAbs≤radius M) :
    ∀ u∈shifted E H M, Rect ![side H,side H,max (side H) (side M)] u := by
  intro u hu
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  have h := hE v (List.mem_dedup.mp hv)
  have h0 := Int.le_natAbs (a:=v 0); have h0' := Int.le_natAbs (a:=-v 0)
  have h1 := Int.le_natAbs (a:=v 1); have h1' := Int.le_natAbs (a:=-v 1)
  have h2 := Int.le_natAbs (a:=v 2); have h2' := Int.le_natAbs (a:=-v 2)
  simp only [Int.natAbs_neg] at h0' h1' h2'
  intro i
  have hm : side M≤max (side H) (side M) := le_max_right _ _
  fin_cases i <;> simp [Rect,shift,side] <;> omega

theorem connectedTile_connected (E : Tile 3) (H M : ℕ)
    (hE : ∀ u∈E, (u 0).natAbs≤radius H ∧ (u 1).natAbs≤radius H ∧ (u 2).natAbs≤radius M) :
    FaceConnected (connectedTile E H M) := by
  simpa only [connectedTile,FaceConnected,List.mem_dedup] using
    assembly_connected (shifted E H M) (side H) (max (side H) (side M))
      (by unfold side; omega) (le_max_left _ _) (shifted_in_box E H M hE)

theorem connectedTile_nonempty (E : Tile 3) (H M : ℕ) (hE : E≠[]) : connectedTile E H M≠[] := by
  apply (List.dedup_eq_nil _).not.mpr
  apply assembly_nonempty
  intro he
  exact hE ((List.dedup_eq_nil _).mp (List.map_eq_nil_iff.mp he))

theorem connectedTile_length_le (E : Tile 3) (H M : ℕ) (hH : 1≤H) (hHM : H≤M)
    (hvol : Compiler.Size.cubeCount E≤9*2^24*H^2*M) :
    (connectedTile E H M).length≤(9*2^24*972*36*8003^4)*H^4*M^3
    := by
  have hA : side H≤8003*H := by unfold side radius; omega
  have hB : max (side H) (side M)≤8003*M := by
    unfold side radius at *; omega
  have hs := shell_length_le (side H) (max (side H) (side M))
    (by unfold side; omega) (le_max_left _ _)
  have hlen : (assembly (shifted E H M) (side H) (max (side H) (side M))).length=
      E.dedup.length*(shell (side H) (max (side H) (side M))).length := by
    simp [assembly,shifted,List.length_flatMap,List.length_map,Function.comp_def,List.map_const,List.sum_replicate]
  have hraw : E.dedup.length=Compiler.Size.cubeCount E := by
    rw [← List.card_toFinset]
    rfl
  have hpre : (connectedTile E H M).length≤Compiler.Size.cubeCount E*(972*(6*(8003*H)*(8003*M))^2) := by
    apply (show (assembly (shifted E H M) (side H) (max (side H) (side M))).dedup.length≤
      (assembly (shifted E H M) (side H) (max (side H) (side M))).length from by
        simpa only [List.card_toFinset] using List.toFinset_card_le
          (assembly (shifted E H M) (side H) (max (side H) (side M)))).trans
    rw [hlen,hraw]
    exact Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hA) hB) 2)))
  apply hpre.trans
  calc
    _ ≤ (9*2^24*H^2*M)*(972*(6*(8003*H)*(8003*M))^2) := Nat.mul_le_mul_right _ hvol
    _ = _ := by ring

end
end TranslationTiling.FourLayer
