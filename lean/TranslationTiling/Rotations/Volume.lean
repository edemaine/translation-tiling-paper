import TranslationTiling.Rotations.Assembly
import Mathlib.Data.Fintype.BigOperators

namespace TranslationTiling.Rotations.SixKeys

set_option maxHeartbeats 200000

theorem cube_card : cube.card = 64000 := by
  rw [cube, Fintype.card_piFinset]
  norm_num [Fin.prod_univ_succ, Int.card_Icc]

theorem removed_card : removed.card = 2190 := by
  unfold removed
  rw [Finset.card_biUnion (fun i _ j _ h => recesses_disjoint h)]
  simp [recess_card]

theorem body_card : body.card = 61810 := by
  have hsub : removed ⊆ cube := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact recess_subset_cube i hi
  rw [body, Finset.card_sdiff_of_subset hsub, cube_card, removed_card]

theorem protrusion_card (i : Face) : (protrusion i).card = 365 := by
  rw [protrusion, Finset.card_image_of_injective _ (fun _ _ he => add_left_cancel he), recess_card]

theorem protrusions_disjoint {i j : Face} (hne : i ≠ j) :
    Disjoint (protrusion i) (protrusion j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨k, hk⟩ := protrusions_apart hne hx hy
  omega

theorem gadget_card : gadget.card = 64000 := by
  have hcard : (Finset.univ.biUnion protrusion).card = 2190 := by
    rw [Finset.card_biUnion (fun i _ j _ h => protrusions_disjoint h)]
    simp [protrusion_card]
  have hd : Disjoint body (Finset.univ.biUnion protrusion) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact Finset.disjoint_left.mp (protrusion_disjoint_cube i) hi (Finset.mem_sdiff.mp hx).1
  rw [gadget, Finset.card_union_of_disjoint hd, body_card, hcard]

/-- The replacement's exact volume overhead is 40³, even for disconnected inputs. -/
theorem assembly_card (E : Finset Point) : (assembly E).card = 64000 * E.card := by
  have hd : (E : Set Point).PairwiseDisjoint (fun e => gadget.image (grid e + ·)) := by
    intro e _ f _ hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hf⟩ := Finset.mem_image.mp hy
    exact hne (grid_unique hu hv (he.trans hf.symm)).1
  unfold assembly
  rw [Finset.card_biUnion hd]
  have each (e : Point) : (gadget.image (grid e + ·)).card = 64000 := by
    rw [Finset.card_image_of_injective _ (fun _ _ he => add_left_cancel he), gadget_card]
  simp_rw [each]
  simp [Nat.mul_comm]

end TranslationTiling.Rotations.SixKeys
