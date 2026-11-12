import TranslationTiling.Rotations.BodyConnectivity
import TranslationTiling.Rotations.KeyConnectivity
import TranslationTiling.Rotations.KeyRecognition
import Mathlib.Data.Fintype.BigOperators

namespace TranslationTiling.Rotations.SixKeys

private def bodyWitness : Finset Point :=
  Fintype.piFinset fun i : Fin 3 => if i = 0 then {10} else Finset.Icc (0 : ℤ) 19

private theorem bodyWitness_card : bodyWitness.card = 400 := by
  simp [bodyWitness, Fintype.card_piFinset, Fin.prod_univ_succ, Int.card_Icc]

private theorem bodyWitness_subset : bodyWitness ⊆ body := by
  intro x hx
  have hp := Fintype.mem_piFinset.mp hx
  have hx0 : x 0 = 10 := by simpa [bodyWitness] using hp 0
  apply (mem_body_iff _).mpr
  apply skeleton_body
  refine ⟨?_, 0, Or.inl hx0⟩
  intro i
  have hi := hp i
  change x i ∈ (if i = 0 then {10} else Finset.Icc (0 : ℤ) 19) at hi
  split_ifs at hi
  · simp only [Finset.mem_singleton] at hi; omega
  · simp only [Finset.mem_Icc] at hi; omega

theorem body_large : 365 < ({x : Point | x ∈ body}).ncard := by
  have hle := Finset.card_le_card bodyWitness_subset
  rw [bodyWitness_card] at hle
  simp only [Finset.setOfPred_mem, Set.ncard_coe_finset]
  omega

theorem body_subset_gadget : body ⊆ gadget := Finset.subset_union_left

theorem protrusion_subset_gadget (i : Face) : protrusion i ⊆ gadget := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)

theorem key_structure : KeyedBody Face {x | x ∈ gadget} {x | x ∈ body}
    (fun i => {x | x ∈ protrusion i}) (fun i => shift i + gate i) attachment 364 := by
  refine ⟨body.finite_toSet, body_large, body_subset_gadget, body_punctured,
    ?_, protrusion_subset_gadget, ?_, ?_, protrusion_connected, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change x ∈ gadget at hx
    rw [gadget] at hx
    rcases Finset.mem_union.mp hx with hb | hp
    · exact Or.inl hb
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      exact Or.inr ⟨i, hi⟩
  · intro i; exact (protrusion i).finite_toSet
  · intro i
    simp only [Finset.setOfPred_mem, Set.ncard_coe_finset]
    rw [protrusion, Finset.card_image_of_injective _ (fun _ _ he => add_left_cancel he), recess_card]
  · intro i
    exact Finset.mem_image.mpr ⟨gate i, gate_mem_recess i, rfl⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro x hx hb
    change x ∈ body at hb
    exact Finset.disjoint_left.mp (protrusion_disjoint_cube i) hx (Finset.mem_sdiff.mp hb).1
  · intro i x hx y hy hxy
    exact protrusion_boundary i hx hy hxy
  · intro i
    exact ⟨attachment_body i, attachment_adjacent i⟩

/-- The concrete cut-component characterization required by chamber forcing. -/
theorem recognize_component {v : Point} {K : Set Point}
    (h : CutComponent {x | x ∈ gadget} v K) (hK : K.Finite) (hcard : K.ncard = 364) :
    ∃ i, v = shift i + gate i ∧ K = {x | x ∈ (chamber i).image (shift i + ·)} := by
  obtain ⟨i, hv, he⟩ := key_structure.recognize h hK hcard
  exact ⟨i, hv, he.trans (key_core_eq i)⟩

theorem zero_body : (0 : Point) ∈ body := by
  rw [mem_body_iff]
  simp [BodyPred, InCube]

theorem body_connected : Connected {x | x ∈ body} := by
  let v : Point := fun _ => 100
  have avoid (x : Point) (hx : x ∈ body) : x ≠ v := by
    intro he
    have hh := Fintype.mem_piFinset.mp (Finset.mem_sdiff.mp hx).1 0
    have hh' := congrFun he 0
    simp only [Finset.mem_Icc] at hh
    change x 0 = 100 at hh'
    omega
  intro x hx y hy
  exact FacePath.mono (body_punctured v x ⟨hx, avoid x hx⟩ y ⟨hy, avoid y hy⟩)
    (fun _ hz => hz.1)

theorem gadget_connected : Connected {x | x ∈ gadget} := by
  have path (x : Point) (hx : x ∈ gadget) : FacePath (fun z => z ∈ gadget) x 0 := by
    rcases Finset.mem_union.mp hx with hb | hp
    · exact FacePath.mono (body_connected x hb 0 zero_body) body_subset_gadget
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hg := key_structure.gate_mem i
    have p₁ := FacePath.mono (protrusion_connected i x hi _ hg) (protrusion_subset_gadget i)
    have p₂ := FacePath.step (protrusion_subset_gadget i hg)
      (body_subset_gadget (attachment_body i)) (attachment_adjacent i)
    have p₃ := FacePath.mono (body_connected _ (attachment_body i) 0 zero_body) body_subset_gadget
    exact (p₁.trans p₂).trans p₃
  intro x hx y hy
  exact (path x hx).trans (path y hy).reverse

theorem gadget_large : 364 < ({x : Point | x ∈ gadget}).ncard := by
  have hb := body_large
  have hsub : ({x : Point | x ∈ body} : Set Point) ⊆ {x | x ∈ gadget} := body_subset_gadget
  have hle := Set.ncard_le_ncard hsub gadget.finite_toSet
  omega

theorem recess_free (i : Face) {x : Point} (hx : x ∈ recess i) : x ∉ gadget := by
  intro hg
  rcases Finset.mem_union.mp hg with hb | hp
  · exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact Finset.disjoint_left.mp (protrusion_disjoint_cube j) hj (recess_subset_cube i hx)

end TranslationTiling.Rotations.SixKeys
