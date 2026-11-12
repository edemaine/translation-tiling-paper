import TranslationTiling.Rotations.General.Real.GridSampling
import TranslationTiling.Rotations.General.LocalForcing
import TranslationTiling.Rotations.General.Faithfulness

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

theorem filled_chamber_parameters (hd : 3 ≤ d) (m : Motion d) (f : Face d)
    (filled : chamber f ⊆ Footprint m)
    (avoids : Disjoint (Footprint m) (body : Finset (Lattice d))) :
    m.orientation=Orientation.ident ∧ m.offset= -shift f := by
  have hc : CutComponent (Footprint m) (gate f) (chamber f) := by
    refine ⟨⟨(frameMotion f).apply keyLo,?_⟩,filled,gate_not_chamber f,chamber_connected f,?_⟩
    · exact ⟨keyLo,Or.inl (fun j => ⟨le_rfl,key_bounds f j⟩),rfl⟩
    · intro x hx y hy hyG hxy
      rcases chamber_boundary f hx hxy with h | h | h
      · exact h
      · exact (hyG h).elim
      · exact (Set.disjoint_left.mp avoids hy h).elim
  have hc' := m.pullback_component hc
  have hk : (m.apply ⁻¹' chamber f).Finite := by
    rw [m.preimage_eq]
    exact (chamber_finite f).image _
  have hkcard : (m.apply ⁻¹' chamber f).ncard=boxVolume d+neckLength d-1 := by
    rw [m.preimage_eq,Set.ncard_image_of_injective _ m.inverse.injective,chamber_card (by omega : 2 ≤ d)]
  obtain ⟨k,_,hcore⟩ := (keyedBody hd).recognize hc' hk hkcard
  have he : m.apply '' placedKey keyMotion k = chamber f := by
    rw [← protrusion_core,← hcore]
    exact Set.image_preimage_eq _ m.equiv.surjective
  obtain ⟨hkf,hmap⟩ := framed_key_rigid (by omega : 2 ≤ d) keyMotion frameMotion k f m he
  subst k
  have hRigid (x : Lattice d) : m.apply x= -shift f+x := by
    let u := (frameMotion f).inverse.apply (x-shift f)
    have hfu : (frameMotion f).apply u=x-shift f := (frameMotion f).apply_inverse_apply _
    have hku : (keyMotion f).apply u=x := by
      have hh : (keyMotion f).apply u=shift f+(frameMotion f).apply u := by
        simp only [keyMotion,keyGate,frameMotion,Motion.apply]
        abel
      rw [hh,hfu]
      abel
    have hh := hmap u
    rw [hku,hfu] at hh
    simpa only [sub_eq_add_neg,add_comm] using hh
  have heq : m=(⟨Orientation.ident,-shift f⟩ : Motion d) := Motion.apply_faithful (by
    intro x
    simpa only [Motion.apply,Orientation.ident_apply] using hRigid x)
  exact ⟨congrArg Motion.orientation heq,congrArg Motion.offset heq⟩

end
end TranslationTiling.Rotations.General.Real
