import TranslationTiling.Rotations.General.ChamberGeometry
import TranslationTiling.Rotations.General.FrameComparison

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def Footprint (m : Motion d) : Set (Lattice d) := m.apply '' (gadget : Finset (Lattice d))

theorem protrusion_core (f : Face d) : (protrusion f : Set (Lattice d)) \ {keyGate f} = placedKey keyMotion f := by
  have hs : (Key f ∪ {0}) \ {0} = Key f := by
    ext x
    by_cases hx : x = 0
    · subst x; simp [zero_not_key f]
    · simp [hx]
  rw [protrusion_image,← keyMotion_zero f,← Set.image_singleton,
    ← Set.image_sdiff (keyMotion f).injective,fullKeyFinset_set,hs]
  rfl

/-- The complete dimension-generic grid gadget forces every exactly positioned
neighbor. The covering copies may use arbitrary grid rotations and reflections. -/
theorem chamber_forces_neighbor (hd : 3 ≤ d) {ι : Type*} (M : ι → Motion d)
    (cover : ExactCover (fun j => Footprint (M j)))
    (host : ι) (hhost : Footprint (M host) = (gadget : Finset (Lattice d))) (i : Face d) :
    ∃ j, ∀ x, (M j).apply x = -shift i+x := by
  have escape (j : ι) : ∃ y ∈ Footprint (M j), y ∉ chamber i := by
    apply escape_of_card (chamber_finite i)
    rw [Footprint,Set.ncard_image_of_injective _ (M j).injective,
      Set.ncard_coe_finset,chamber_card (by omega : 2 ≤ d)]
    have hb := body_large hd
    have hg := Finset.card_le_card (body_subset_gadget (d := d))
    omega
  have hne : (chamber i).Nonempty :=
    ⟨(frameMotion i).apply keyLo,Set.mem_image_of_mem _ (Or.inl (fun j => ⟨le_rfl,key_bounds i j⟩))⟩
  obtain ⟨j,_,_,hc⟩ := chamber_component cover
    (fun j => (M j).connected (gadget_connected hd)) host (chamber i) (gate i)
    hne (chamber_connected i) (gate_not_chamber i)
    (by intro x hx; rw [hhost]; exact recess_free i (chamber_subset_recess i hx))
    (by rw [hhost]; exact recess_free i (gate_mem_recess i))
    (by
      intro x hx y hxy
      rcases chamber_boundary i hx hxy with hy | hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (by rw [hhost]; exact body_subset_gadget hy))) escape
  have hc' := (M j).pullback_component hc
  have hk : ((M j).apply ⁻¹' chamber i).Finite := by
    rw [(M j).preimage_eq]
    exact (chamber_finite i).image _
  have hkcard : ((M j).apply ⁻¹' chamber i).ncard = boxVolume d+neckLength d-1 := by
    rw [(M j).preimage_eq,Set.ncard_image_of_injective _ (M j).inverse.injective,
      chamber_card (by omega : 2 ≤ d)]
  obtain ⟨f,_,hcore⟩ := (keyedBody hd).recognize hc' hk hkcard
  have he : (M j).apply '' placedKey keyMotion f = chamber i := by
    rw [← protrusion_core,← hcore]
    exact Set.image_preimage_eq _ (M j).equiv.surjective
  obtain ⟨hfi,hmap⟩ := framed_key_rigid (by omega : 2 ≤ d) keyMotion frameMotion f i (M j) he
  subst f
  refine ⟨j,fun x => ?_⟩
  let u := (frameMotion i).inverse.apply (x-shift i)
  have hfu : (frameMotion i).apply u = x-shift i := (frameMotion i).apply_inverse_apply _
  have hku : (keyMotion i).apply u = x := by
    have hh : (keyMotion i).apply u = shift i+(frameMotion i).apply u := by
      simp only [keyMotion,keyGate,frameMotion,Motion.apply]
      abel
    rw [hh,hfu]
    abel
  have hh := hmap u
  rw [hku,hfu] at hh
  simpa only [sub_eq_add_neg,add_comm] using hh

/-- Undoing a placement preserves exact coverage. -/
theorem normalize_cover {ι : Type*} (M : ι → Motion d)
    (cover : ExactCover (fun j => Footprint (M j))) (r : Motion d) :
    ExactCover (fun j => Footprint (r.inverse.comp (M j))) := by
  intro x
  obtain ⟨j,⟨u,hu,he⟩,unique⟩ := cover (r.apply x)
  refine ⟨j,⟨u,hu,?_⟩,?_⟩
  · simp [Motion.comp_apply,he]
  · rintro k ⟨v,hv,he⟩
    apply unique k
    refine ⟨v,hv,?_⟩
    have hh := congrArg r.apply he
    simpa only [Motion.comp_apply,Motion.apply_inverse_apply] using hh

end TranslationTiling.Rotations.General
