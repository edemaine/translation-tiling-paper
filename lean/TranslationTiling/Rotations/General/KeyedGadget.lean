import TranslationTiling.Rotations.General.BodySize
import TranslationTiling.Rotations.General.Attachments
import TranslationTiling.Rotations.KeyRecognition

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def keyMotion (f : Face d) : Motion d := ⟨frameOrientation f,keyGate f⟩

@[simp] theorem keyMotion_zero (f : Face d) : (keyMotion f).apply 0 = keyGate f := by
  simp [keyMotion,Motion.apply]

theorem protrusion_image (f : Face d) :
    (protrusion f : Set (Lattice d)) = (keyMotion f).apply '' (fullKeyFinset f : Set (Lattice d)) := by
  simp only [protrusion,recess,Finset.coe_image,Set.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply,keyMotion,frameMotion,Motion.apply,keyGate,shift]
  abel

theorem protrusion_card (hd : 2 ≤ d) (f : Face d) :
    (protrusion f).card = boxVolume d + neckLength d := by
  have h := Set.ncard_image_of_injective (fullKeyFinset f : Set (Lattice d)) (keyMotion f).injective
  rw [← protrusion_image,Set.ncard_coe_finset,Set.ncard_coe_finset,fullKey_card hd f] at h
  exact h

theorem protrusion_connected (f : Face d) : Connected (protrusion f : Set (Lattice d)) := by
  rw [protrusion_image]
  exact (keyMotion f).connected (fullKey_connected f)

theorem keyGate_mem (f : Face d) : keyGate f ∈ protrusion f := by
  rw [← Finset.mem_coe,protrusion_image]
  exact ⟨0,by simp [fullKeyFinset],keyMotion_zero f⟩

theorem body_subset_gadget : (body : Finset (Lattice d)) ⊆ gadget := by
  rw [gadget_decomposition]
  exact Finset.subset_union_left

theorem protrusion_subset_gadget (f : Face d) : protrusion f ⊆ gadget := by
  intro x hx
  rw [gadget_decomposition]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f,Finset.mem_univ _,hx⟩)

theorem gadget_parts {x : Lattice d} (hx : x ∈ gadget) : x ∈ body ∨ ∃ f : Face d, x ∈ protrusion f := by
  rw [gadget_decomposition] at hx
  rcases Finset.mem_union.mp hx with hb | hp
  · exact Or.inl hb
  · obtain ⟨f,_,hf⟩ := Finset.mem_biUnion.mp hp
    exact Or.inr ⟨f,hf⟩

/-- The finite component-recognition hypotheses hold for the explicit gadget
in every dimension at least three. -/
theorem keyedBody (hd : 3 ≤ d) :
    KeyedBody (Face d) (↑(gadget : Finset (Lattice d))) (↑(body : Finset (Lattice d)))
      (fun f => ↑(protrusion f)) keyGate attachment (boxVolume d+neckLength d-1) := by
  have hn : 0 < neckLength d := by unfold neckLength; omega
  refine ⟨Finset.finite_toSet _,?_,body_subset_gadget,body_punctured hd,?_,
    protrusion_subset_gadget,fun _ => Finset.finite_toSet _,?_,protrusion_connected,
    keyGate_mem,?_,?_,?_⟩
  · have h := body_large hd
    simp only [Set.ncard_coe_finset]
    omega
  · exact fun _ hx => gadget_parts hx
  · intro f
    simp only [Set.ncard_coe_finset,protrusion_card (by omega : 2 ≤ d)]
    omega
  · intro f
    exact_mod_cast protrusion_disjoint_body f
  · intro f x hx y hy hxy
    rcases gadget_parts hy with hb | ⟨g,hg⟩
    · exact Or.inr hb
    · by_cases hfg : f = g
      · subst g; exact Or.inl hg
      · exact (protrusions_separated hfg hx hg hxy).elim
  · intro f
    exact ⟨attachment_body (by omega : 2 ≤ d) f,gate_attachment_adjacent f⟩

/-- The full replacement is connected, including all its protruding keys. -/
theorem gadget_connected (hd : 3 ≤ d) : Connected (↑(gadget : Finset (Lattice d)) : Set (Lattice d)) := by
  have zeroB := zero_body (by omega : 2 ≤ d)
  have path (x : Lattice d) (hx : x ∈ gadget) : FacePath (· ∈ gadget) x 0 := by
    rcases gadget_parts hx with hb | ⟨f,hf⟩
    · exact (body_connected hd x hb 0 zeroB).mono (fun _ hz => body_subset_gadget hz)
    · have p1 := (protrusion_connected f x hf (keyGate f) (keyGate_mem f)).mono
        (fun _ hz => protrusion_subset_gadget f hz)
      have p2 := FacePath.step (protrusion_subset_gadget f (keyGate_mem f))
        (body_subset_gadget (attachment_body (by omega : 2 ≤ d) f)) (gate_attachment_adjacent f)
      have p3 := (body_connected hd (attachment f) (attachment_body (by omega : 2 ≤ d) f) 0 zeroB).mono
        (fun _ hz => body_subset_gadget hz)
      exact (p1.trans p2).trans p3
  intro x hx y hy
  exact (path x hx).trans (path y hy).reverse

end TranslationTiling.Rotations.General
