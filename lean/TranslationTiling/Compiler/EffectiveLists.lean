import TranslationTiling.Compiler.EffectiveArithmetic
import Mathlib.Data.List.Dedup

namespace TranslationTiling.Compiler.Effective

theorem dedup_primrec {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (List.dedup : List α → List α) := by
  have hp : Primrec (fun xs : List α => xs.foldr
      (fun x ys => if x ∈ ys then ys else x :: ys) []) := by
    apply foldList (h := fun _ p => if p.1 ∈ p.2 then p.2 else p.1 :: p.2)
      Primrec.id (Primrec.const [])
    fun_prop
  apply hp.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, ih, List.dedup_cons']

theorem product_primrec : Primrec (List.prod : List ℕ → ℕ) := by
  change Primrec (fun xs : List ℕ => xs.foldr (· * ·) 1)
  apply foldList (h := fun _ p => p.1 * p.2) Primrec.id (Primrec.const 1)
  fun_prop

/-- Map a uniformly computable function over a variable finite list. -/
theorem computableListMap {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Inhabited β] {f : α → List β} {g : α → β → γ}
    (hf : Computable f) (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).map (g a)) := by
  let step (a : α) (p : ℕ × List γ) := p.2 ++ [g a ((f a).getD p.1 default)]
  have hget : Computable (fun p : α × (ℕ × List γ) =>
      (f p.1).getD p.2.1 default) :=
    (Primrec.list_getD default).to_comp.comp
      (hf.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ step :=
    Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp
        (hg.comp (Computable.fst.pair hget)) (Computable.const []))
  have hp := Computable.nat_rec (Computable.list_length.comp hf) (Computable.const []) hstep
  apply hp.of_eq
  intro a
  have hprefix (n : ℕ) (hn : n ≤ (f a).length) :
      Nat.rec ([] : List γ) (fun i xs => step a (i, xs)) n =
        ((f a).take n).map (g a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hi : n < (f a).length := by omega
      change step a (n, Nat.rec ([] : List γ) (fun i xs => step a (i, xs)) n) = _
      rw [ih (by omega)]
      simp only [step, List.take_succ, List.map_append, List.map_singleton,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, Option.toList_some]
  simpa only [List.take_length] using hprefix (f a).length le_rfl

end TranslationTiling.Compiler.Effective
