import TranslationTiling.Compiler.SizeBound
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Arithmetic bounds for the connectedness step. These bounds count distinct
cubes even when the input or output encoding lists have duplicate entries. -/

namespace TranslationTiling.Compiler.Size

open scoped Classical

theorem kim_cube_length (l : ℕ) : (Kim.cube l).length = l ^ 3 := by
  simp [Kim.cube, List.length_flatMap, List.map_const', List.sum_replicate,
    Nat.pow_succ, Nat.mul_assoc]

theorem kim_boundary_length_le (l : ℕ) : (Kim.boundary l).length ≤ l ^ 3 := by
  rw [← kim_cube_length]
  exact List.length_filter_le _ _

/-- Replacing each input cube by a shell multiplies the number of distinct
cubes by at most the shell volume. No injectivity assumption on the input
encoding is needed. -/
theorem connectedAssembly_cubeCount_le (E : Tile 3) (l : ℕ) (hl : 0 < l) :
    cubeCount (connectedAssembly E l) ≤
      cubeCount E * (Kim.scale (Kim.boundary l).length) ^ 3 := by
  let f (p : Lattice 3 × Lattice 3) :=
    (Kim.scale (Kim.boundary l).length : ℤ) • p.1 + p.2
  have he : (connectedAssembly E l).toFinset =
      (E.toFinset.product (Kim.shell l).toFinset).image f := by
    ext x
    simp only [Finset.product_eq_sprod, List.mem_toFinset, mem_connectedAssembly, Finset.mem_image,
      Finset.mem_product, List.mem_toFinset, Prod.exists]
    constructor
    · rintro ⟨u, hu, v, hv, he⟩
      exact ⟨u, v, ⟨hu, hv⟩, he.symm⟩
    · rintro ⟨u, v, ⟨hu, hv⟩, he⟩
      exact ⟨u, hu, v, hv, he.symm⟩
  unfold cubeCount
  rw [he]
  calc
    _ ≤ (E.toFinset.product (Kim.shell l).toFinset).card := Finset.card_image_le
    _ = E.toFinset.card * (Kim.scale (Kim.boundary l).length) ^ 3 := by
      rw [Finset.product_eq_sprod, Finset.card_product, Kim.shell_card l hl]

theorem positiveTile_cubeCount (E : Tile 3) : cubeCount (positiveTile E) = cubeCount E := by
  have he : (positiveTile E).toFinset =
      E.toFinset.image (fun x => x + fun _ => (coordinateBound E : ℤ)) := by
    ext x
    simp only [positiveTile, List.mem_toFinset, List.mem_map, Finset.mem_image]
  unfold cubeCount
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]

/-- A purely arithmetic upper bound for the connected geometric compiler in
terms of the input volume and the bounding-cube side chosen by the compiler. -/
theorem connectedTile_cubeCount_le (E : Tile 3) :
    cubeCount (connectedTile E) ≤
      cubeCount E * (3 * cubeSize E ^ 3 + 6) ^ 3 := by
  have h := connectedAssembly_cubeCount_le (positiveTile E) (cubeSize E)
    (by unfold cubeSize; omega)
  rw [positiveTile_cubeCount] at h
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (kim_boundary_length_le _)) 6

end TranslationTiling.Compiler.Size
