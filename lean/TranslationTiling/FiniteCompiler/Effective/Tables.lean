import TranslationTiling.Compiler.EffectiveChoices
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

namespace TranslationTiling.FiniteCompiler.Effective

/-- Every finite table can be stored at prescribed distinct natural addresses.
This lemma supplies existence for a computable certificate search; it does not
claim that an arbitrary varying table is computable. -/
theorem exists_finite_table {α β : Type*} [Fintype α]
    (code : α → ℕ) (hc : Function.Injective code) (f : α → β) (d : β) :
    ∃ xs : List β, ∀ a, xs.getD (code a) d = f a := by
  classical
  let n := Finset.univ.sup code + 1
  let g := Function.extend code f (fun _ => d)
  refine ⟨List.ofFn (fun i : Fin n => g i.val), fun a => ?_⟩
  have ha : code a < n := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using ha), List.getElem_ofFn]
  exact hc.extend_apply f (fun _ => d) a

end TranslationTiling.FiniteCompiler.Effective
