import TranslationTiling.Rotations.Euclidean.GridSampling
import TranslationTiling.Rotations.LocalForcing

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

theorem filled_chamber_parameters (m : Motion) (i : Face)
    (filled : (chamber i : Set Point) ⊆ Footprint m)
    (avoids : Disjoint (Footprint m) (body : Set Point)) :
    m.orientation=Orientation.ident ∧ m.offset= -shift i := by
  have hc : CutComponent (Footprint m) (gate i) (chamber i : Set Point) := by
    refine ⟨⟨chamberVoxel i 0,chamberVoxel_mem i 0⟩,filled,by simp [chamber],
      chamber_connected i,?_⟩
    intro x hx y hy hyG hxy
    rcases chamber_boundary i hx hxy with h | h | h
    · exact h
    · exact (hyG h).elim
    · exact (Set.disjoint_left.mp avoids hy h).elim
  have hc' := m.pullback_component hc
  have hkFinite : (m.apply ⁻¹' (chamber i : Set Point)).Finite := by
    rw [m.preimage_eq]
    exact (chamber i).finite_toSet.image _
  have hkCard : (m.apply ⁻¹' (chamber i : Set Point)).ncard=364 := by
    rw [m.preimage_eq,Set.InjOn.ncard_image m.inverse.injective.injOn]
    simp only [Set.ncard_coe_finset,chamber_card]
  obtain ⟨k,_,hcore⟩ := recognize_component hc' hkFinite hkCard
  simp only [Finset.setOfPred_mem] at hcore
  have hset : m.apply '' ((chamber k).image (shift k+·) : Set Point)=(chamber i : Set Point) := by
    rw [← hcore]
    exact Set.image_preimage_eq _ m.equiv.surjective
  have hfin : ((chamber k).image (shift k+·)).image m.apply=chamber i := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using hset
  let n : Motion := ⟨m.orientation,m.offset+m.orientation.linear (shift k)⟩
  have hn : n.apply=m.apply ∘ (shift k+·) := by
    funext x
    simp [n,Motion.apply,map_add,add_assoc]
  rw [Finset.image_image,← hn] at hfin
  obtain ⟨hki,hr,ht⟩ := chamber_rigid k i n hfin
  subst k
  have hr' : m.orientation=Orientation.ident := hr
  have ht' : m.offset+shift i=0 := by
    change m.offset+m.orientation.linear (shift i)=0 at ht
    simpa [hr'] using ht
  have hoff : m.offset= -shift i := eq_neg_of_add_eq_zero_left ht'
  exact ⟨hr',hoff⟩

theorem filled_chamber_rigid (m : Motion) (i : Face)
    (filled : (chamber i : Set Point) ⊆ Footprint m)
    (avoids : Disjoint (Footprint m) (body : Set Point)) :
    ∀ x, m.apply x = -shift i+x := by
  obtain ⟨hr,ht⟩ := filled_chamber_parameters m i filled avoids
  intro x
  simp [Motion.apply,hr,ht]

end
end TranslationTiling.Rotations.Euclidean
