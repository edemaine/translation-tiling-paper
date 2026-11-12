import TranslationTiling.Rotations.Euclidean.LocalIntegrality
import TranslationTiling.Rotations.Euclidean.GridSampling

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

theorem localChamber_card (i : Face) : (localChamber i).card=364 := by
  rw [localChamber,Finset.card_image_of_injective _ (frameMotion i).inverse.injective,chamber_card]

theorem local_chamber_low (i : Face) {p : Lattice 3}
    (hp : p ∈ localChamber i) (hlo : p 0≤2) : p=![1,0,0] ∨ p=![2,0,0] := by
  rcases (mem_localChamber i p).mp hp with hs | hb
  · have hp0 : p 0=1 ∨ p 0=2 := by omega
    rcases hp0 with hp0 | hp0
    · left; ext k; fin_cases k <;> simp_all
    · right; ext k; fin_cases k <;> simp_all
  · omega

theorem local_chamber_no_shortcut (i : Face) {p : Lattice 3}
    (hp : p ∈ localChamber i) (hne : p≠![1,0,0]) : ¬ FaceAdjacent p 0 := by
  intro hadj
  have hd := adjacent_delta hadj 0
  have hp0 : 1≤p 0 := by rcases (mem_localChamber i p).mp hp with h | h <;> omega
  have hlo : p 0≤2 := by
    have h1 : p 0≤1 := by simpa using hd.1
    omega
  rcases local_chamber_low i hp hlo with h | h
  · exact hne h
  · subst p; norm_num at hd

theorem integral_fills_chamber {ι : Type*} (M : ι → RigidMotion)
    (cover : AECover (fun j => Placed gadget (M j))) (host : ι) (i : Face)
    (hhost : Placed gadget (M host)=solid (localGadget i)) :
    ∃ (j : ι) (a : Motion), j≠host ∧ M j=embedMotion a ∧
      (localChamber i : Set (Lattice 3)) ⊆ a.apply '' (gadget : Set (Lattice 3)) ∧
      Disjoint (a.apply '' (gadget : Set (Lattice 3))) (localBody i : Set (Lattice 3)) := by
  obtain ⟨j,a,h,jne,ha,hh,filled,neck⟩ := integral_chamber_blocker M cover host i hhost
  let S := a.apply '' (gadget : Set (Lattice 3))
  have packing : Disjoint (Placed gadget (embedMotion a)) (interior (solid (localBody i))) := by
    rw [← ha]
    have hd := (cover.interior_solid_disjoint (Ne.symm jne)).symm
    rw [hhost] at hd
    apply hd.mono_right
    apply interior_mono
    rintro y ⟨q,hq,hy⟩
    exact ⟨q,localBody_subset_localGadget i hq,hy⟩
  have avoids : Disjoint S (localBody i : Set (Lattice 3)) := grid_footprint_avoids_body a _ _ packing
  let K : Set (Lattice 3) := (localChamber i : Set (Lattice 3)) \ {![1,0,0]}
  have filledSuffix : K ⊆ S := by
    intro p hp
    by_cases hlo : p 0≤2
    · rcases local_chamber_low i hp.1 hlo with he | he
      · exact (hp.2 he).elim
      · exact he.symm ▸ neck
    · apply (castPoint_mem_placed a gadget p).mp
      rw [← ha]
      apply filled
      exact chamber_center_above i h (by linarith) p hp.1 (by omega)
  have escape : ∃ y ∈ S, y ∉ K := by
    have hlarge : (localChamber i : Set (Lattice 3)).ncard<S.ncard := by
      rw [Set.ncard_coe_finset,localChamber_card,Set.InjOn.ncard_image a.injective.injOn]
      simpa only [Finset.setOfPred_mem] using gadget_large
    obtain ⟨y,hy,hn⟩ := escape_of_card (localChamber i).finite_toSet hlarge
    exact ⟨y,hy,fun hk => hn hk.1⟩
  have neckK : (![2,0,0] : Lattice 3) ∈ K := by
    refine ⟨?_,by decide⟩
    change (![2,0,0] : Lattice 3) ∈ localChamber i
    rw [mem_localChamber]
    left; norm_num [NeckBox]
  have gate1 : (![1,0,0] : Lattice 3) ∈ S := uses_gate neckK neck
    (a.connected gadget_connected) escape (by
      intro p hp q hq hpq
      rcases local_chamber_boundary i hp.1 hpq with hqK | hq0 | hqH
      · by_cases he : q=![1,0,0]
        · exact Or.inr he
        · exact Or.inl ⟨hqK,he⟩
      · exact (local_chamber_no_shortcut i hp.1 hp.2 (hq0 ▸ hpq)).elim
      · exact (Set.disjoint_left.mp avoids hq hqH).elim)
  refine ⟨j,a,jne,ha,?_,avoids⟩
  intro p hp
  by_cases he : p=![1,0,0]
  · exact he.symm ▸ gate1
  · exact filledSuffix ⟨hp,he⟩

end
end TranslationTiling.Rotations.Euclidean
