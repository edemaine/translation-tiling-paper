import TranslationTiling.FiniteCompiler.ActivationOffsets
import Mathlib.Data.ZMod.QuotientRing

namespace TranslationTiling.FiniteCompiler

open scoped Classical BigOperators

noncomputable section

/-- Batch indices can be separated on a single slope while satisfying
all low and block-rotation congruences at once. -/
theorem exists_slot_activation_offsets {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (hp : ∀ i, 0 < p i) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (desired : J → ∀ i, ZMod (p i)) (slope : ℤ) :
    ∃ h : J → Plane, Function.Injective h ∧
      ∀ j, (h j).2 = -slope * (h j).1 ∧
        (∀ i, ((h j).1 : ZMod (p i)) = desired j i) ∧
        0 ≤ (h j).1 ∧ (h j).1 < ((∏ i, p i) * Fintype.card J : ℕ) := by
  let M := ∏ i, p i
  have : NeZero M := ⟨(Finset.prod_pos fun i _ => hp i).ne'⟩
  let e := ZMod.prodEquivPi p hc
  let v (j : J) := e.symm (desired j)
  let code (j : J) := (Fintype.equivFin J j).val
  let a := separatedResidueLift M v code
  refine ⟨fun j => (a j,-slope*a j),fun i j he => ?_,fun j => ⟨rfl,?_,?_,?_⟩⟩
  · apply separatedResidueLift_injective M v code
      (fun _ _ he => (Fintype.equivFin J).injective (Fin.ext he))
    exact congrArg Prod.fst he
  · have hv : e (a j : ZMod M) = desired j := by
      rw [separatedResidueLift_cast]
      exact e.apply_symm_apply _
    intro i
    have he := congrFun hv i
    rwa [map_intCast] at he
  · unfold a separatedResidueLift
    positivity
  · have hv := ZMod.val_lt (v j)
    have hc' : code j + 1 ≤ Fintype.card J := (Fintype.equivFin J j).isLt
    have hb : (v j).val + M * code j < M * Fintype.card J := by
      calc
        _ < M + M * code j := Nat.add_lt_add_right hv _
        _ = M * (code j+1) := by rw [Nat.mul_succ,Nat.add_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ hc'
    change ((v j).val : ℤ) + (M : ℤ) * (code j : ℤ) < _
    exact_mod_cast hb

end

end TranslationTiling.FiniteCompiler
