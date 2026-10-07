import TranslationTiling.External.Geometry
import TranslationTiling.Planar.PlanarPeriodicity

namespace TranslationTiling

/-- Period subgroups transport along additive equivalences. -/
theorem fullyPeriodic_transport {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {A : Set G} (h : FullyPeriodic A) : FullyPeriodic (e '' A) := by
  obtain ⟨P, hP, hp⟩ := h
  refine ⟨P.map e.toAddMonoidHom, ?_, ?_⟩
  · constructor
    change (P.map (e : G →+ H)).index ≠ 0
    rw [P.index_map_equiv e]
    exact hP.index_ne_zero
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hv
    change Period (e '' A) (e w)
    intro x
    have hm (y : G) : e y ∈ e '' A ↔ y ∈ A := by
      simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right]
    rw [← e.apply_symm_apply x, ← map_add, hm, hm]
    exact hp w hw (e.symm x)

private theorem planar_tiles_iff_exact {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) :
    Planar.Tiles F A ↔ ExactTiling A {x | x ∈ F} := by
  rw [Planar.tiles_iff_unique_tile, exactTiling_iff]
  rfl

/-- Bhattacharya's planar periodicity theorem, with no mathematical hypotheses. -/
theorem planarPeriodicity_proved : PlanarPeriodicity := by
  classical
  intro F hF
  obtain ⟨A, hA⟩ := hF
  let e := Planar.planeEquiv
  let P : Finset Planar.Plane := F.toFinset.image e.symm
  have hPset : {x | x ∈ P} = e.symm '' {x | x ∈ F} := by
    ext x
    simp [P]
  have hP : Planar.Tiles P (e.symm '' A) := by
    apply (planar_tiles_iff_exact P _).mpr
    rw [hPset]
    exact exactTiling_transport e.symm hA
  obtain ⟨B, hB, hp⟩ := Planar.plane_tile_has_fullyPeriodic_complement P
    hP.tile_nonempty ⟨e.symm '' A, hP⟩
  have hback : e '' {x | x ∈ P} = {x | x ∈ F} := by
    rw [hPset]
    ext x
    simp
  refine ⟨e '' B, ?_, fullyPeriodic_transport e hp⟩
  rw [← hback]
  exact exactTiling_transport e ((planar_tiles_iff_exact P B).mp hB)

end TranslationTiling
