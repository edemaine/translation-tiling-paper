import TranslationTiling.Rotations.General.Protect
import TranslationTiling.Rotations.General.SizeBound

namespace TranslationTiling.Rotations.General
noncomputable section
variable {d : ℕ} [NeZero d]

/-- Distinct macrovoxels have disjoint replacement cells, even for disconnected inputs. -/
theorem assembly_card (E : Finset (Lattice d)) :
    (assembly E).card=(cubeSide d)^d*E.card := by
  have hd : (E : Set (Lattice d)).PairwiseDisjoint (fun e => gadget.image (grid e+·)) := by
    intro e _ f _ hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,hf⟩ := Finset.mem_image.mp hy
    exact hne (grid_unique hu hv (he.trans hf.symm)).1
  unfold assembly
  rw [Finset.card_biUnion hd]
  have each (e : Lattice d) : (gadget.image (grid e+·)).card=(cubeSide d)^d := by
    rw [Finset.card_image_of_injective _ (fun _ _ he => add_left_cancel he),gadget_card]
  simp_rw [each]
  simp [Nat.mul_comm]

theorem protect_card (E : Tile d) :
    (protect E).toFinset.card=(cubeSide d)^d*E.toFinset.card := by
  rw [protect_toFinset,assembly_card]

theorem protect_length (E : Tile d) : (protect E).length=(cubeSide d)^d*E.length := by
  simp [protect,List.length_flatMap,gadget_card,Nat.mul_comm]

theorem protect_card_bound (E : Tile d) :
    (protect E).toFinset.card ≤ 2^(10*(d+1)^2)*E.toFinset.card := by
  rw [protect_card]
  have hb : (cubeSide d)^d ≤ 2^(10*(d+1)^2) := by
    simpa only [gadget_card] using gadget_card_bound (d := d)
  exact Nat.mul_le_mul_right _ hb

theorem protect_length_bound (E : Tile d) :
    (protect E).length ≤ 2^(10*(d+1)^2)*E.length := by
  rw [protect_length]
  have hb : (cubeSide d)^d ≤ 2^(10*(d+1)^2) := by
    simpa only [gadget_card] using gadget_card_bound (d := d)
  exact Nat.mul_le_mul_right _ hb

end
end TranslationTiling.Rotations.General
