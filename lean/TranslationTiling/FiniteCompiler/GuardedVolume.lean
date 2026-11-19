import TranslationTiling.FiniteCompiler.GuardedCap
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyCompiler
import TranslationTiling.Proofs.TightDifferenceBound

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open Compiler Compiler.Effective TranslationTiling.FiniteCompiler.Effective
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000

private theorem railCap_mono (H Q Q' : ℕ) (h : Q≤Q') : railCap H Q≤railCap H Q' := by
  dsimp [railCap]
  gcongr

private theorem shell_by_plane (A B : ℕ) :
    (Rails.shell A B).length≤216*(4*(2*A+1)^2+7*(B+2)+1)*(4*(2*A+1)^2+1) := by
  have he : (Rails.planeEnum A).length=(2*A+1)^2 := by
    simp [Rails.planeEnum,List.length_flatMap,Function.comp_def,List.map_const,List.sum_replicate,pow_two]
  have hn : (Rails.planeList A).toFinset=(Rails.planeEnum A).toFinset := by
    ext x
    simp only [List.mem_toFinset,Rails.planeList_mem,Rails.planeEnum_mem]
  have hh : (Rails.planeList A).length≤(2*A+1)^2 := by
    rw [←List.toFinset_card_of_nodup (Rails.planeList_nodup A),hn,←he]
    exact List.toFinset_card_le _
  unfold Rails.shell
  have hm := FourLayer.matching_spec (Rails.planeList A) (Rails.planeList_required A)
  apply (Rails.shapeList_length_le _ _ _ _ hm.1 hm.2.1).trans
  unfold Rails.lengthX Rails.lengthY
  gcongr

theorem connected_length (U : Tile 3) (H Q : ℕ) :
    (Rails.connectedTile U H (max (H^2) Q)).length≤Size.cubeCount U*railCap H Q := by
  let A := FourLayer.side H
  let B := max (A^2) (FourLayer.side (max (H^2) Q))
  have hs : (Rails.shell A B).length≤railCap H Q := by
    simpa [railCap,A,B,FourLayer.side,FourLayer.radius,show ∀ v : ℕ, 2*(1000*(2*v+1))+3=4000*v+2003 by intro; ring]
      using shell_by_plane A B
  have hl : (Rails.assembly (FourLayer.shifted U H (max (H^2) Q)) A B).length=
      Size.cubeCount U*(Rails.shell A B).length := by
    have he : U.dedup.length=Size.cubeCount U := by rw [←List.card_toFinset]; rfl
    simp [Rails.assembly,FourLayer.shifted,List.length_flatMap,Function.comp_def,List.map_const,List.sum_replicate,he]
  calc
    _ ≤ (Rails.assembly (FourLayer.shifted U H (max (H^2) Q)) A B).length := by
      simpa only [Rails.connectedTile,List.card_toFinset,A,B] using List.toFinset_card_le
        (Rails.assembly (FourLayer.shifted U H (max (H^2) Q)) A B)
    _ ≤ _ := by rw [hl]; exact Nat.mul_le_mul_left _ hs

theorem exists_connected_from_family (N H J X : ℕ) (Fs : List CyclicTile)
    (hN : 0<N) (hpr : PrimeBound N 65536) (hs : 0<Fs.length) (hX : Fs.length≤X)
    (hP : 65536+3≤2*X^2)
    (hn : ∀ F∈Fs, F≠[]) (hJ : ∀ F∈Fs, (cyclicTileSet N F).card≤J)
    (hH : ∀ F∈Fs, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      ((∃ C : Set (Plane × ZMod N), ∀ i : Fin Fs.length, Tiles (cyclicTileSet N (Fs.getD i.val [])) C)
        ↔ TranslationTiling.Tiles U) ∧ U.length≤cubeCap H N J (stackCap X) := by
  let R := Stacking.tightThreshold X 65536
  obtain ⟨q,hq,hlo,hhi⟩ := Nat.bertrand R (by dsimp [R,Stacking.tightThreshold]; omega)
  have hc := coprime_of_primeBound hN hpr hq (by dsimp [R,Stacking.tightThreshold] at hlo; omega)
  have hs' : Fs.length-1+1=Fs.length := by omega
  obtain ⟨P,hP',hfull⟩ := Stacking.partition_tight (Fs.length-1+1) X 65536 q
    (by omega) (by rwa [hs']) hP hq hlo hhi
  obtain ⟨cs,hcs⟩ := partition_certificate (Fs.length-1) 65536 q hq
    (by dsimp [R,Stacking.tightThreshold] at hlo; omega) P hP' hfull
  let d : CyclicTileData := (N*q,stackCodes (N,(q,cs),Fs))
  let U : Tile 3 := Rails.connectedTile (integerTile d) H (max (H^2) d.1)
  have hpos : 0<d.1 := Nat.mul_pos hN hq.pos
  have hnon : d.2≠[] := stackCodes_nonempty N _ Fs hs hcs hn
  have hrect := Size.integerTile_rectangle_bound d H (max (H^2) d.1) hpos
    (le_max_right _ _) hnon (stackCodes_horizontal N (q,cs) Fs H hH)
  refine ⟨U,Rails.connectedTile_nonempty _ _ _ (integerTile_nonempty _ hnon),
    Rails.connectedTile_connected _ _ _ hrect,?_,?_⟩
  · exact (stackCodes_correct_coprime N 65536 hN Fs hs (q,cs) hcs hc).trans
      ((integerTile_correct MSS.rigidity _ hpos hnon).trans
        (Rails.connectedTile_correct _ _ _).symm)
  · have hm := stack_mass N 65536 hN Fs hs (q,cs) hcs hc J hJ
    have hv := (Size.integerTile_cubeCount_sharp d hpos).trans (Nat.mul_le_mul_left _ hm)
    calc
      U.length ≤ Size.cubeCount (integerTile d)*railCap H (N*q) := connected_length _ _ _
      _ ≤ (Size.mssPieceCap*(J*q))*railCap H (N*q) := Nat.mul_le_mul_right _ hv
      _ ≤ (Size.mssPieceCap*(J*stackCap X))*railCap H (N*stackCap X) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hhi))
          (railCap_mono _ _ _ (Nat.mul_le_mul_left _ hhi))
      _ = _ := by unfold cubeCap Size.mssPieceCap; ring

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
