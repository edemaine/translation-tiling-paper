import TranslationTiling.FiniteCompiler.Effective.BitInput
import TranslationTiling.FiniteCompiler.Effective.Arithmetic
import Mathlib.Data.List.OfFn

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Numerical words use the standard increasing column order. -/
def wordList {T : System} (w : Word T) : List ℕ := List.ofFn (fun i => (w i).val)

def numericalWords (w B : ℕ) : List (List ℕ) := strings (List.range B) w

theorem numericalWords_primrec : Primrec (fun d : ℕ × ℕ => numericalWords d.1 d.2) :=
  strings_primrec.comp ((Primrec.list_range.comp Primrec.snd).pair Primrec.fst)

theorem wordList_injective (T : System) : Function.Injective (wordList (T := T)) := by
  intro v w h
  have he := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun he i)

theorem mem_numericalWords (T : System) (xs : List ℕ) :
    xs ∈ numericalWords T.width T.alphabet ↔ ∃ w : Word T, wordList w = xs := by
  rw [numericalWords, mem_strings]
  constructor
  · rintro ⟨hlen,hvals⟩
    have hi (i : Column T) : i.val < xs.length := by rw [hlen]; exact i.isLt
    let w : Word T := fun i =>
      ⟨xs[i.val]'(hi i), List.mem_range.mp (hvals _ (List.getElem_mem (hi i)))⟩
    refine ⟨w,?_⟩
    apply List.ext_getElem
    · simp [wordList,hlen]
    · intro i hi' hi''
      simp only [wordList,List.getElem_ofFn,w]
  · rintro ⟨w,rfl⟩
    refine ⟨by simp [wordList],?_⟩
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact List.mem_range.mpr (w i).isLt

/-- A raw payload gives exactly the slopes, line rule, and seed predicates of `T`. -/
def PayloadCorrect (T : System) (p : Payload) : Prop :=
  (∀ n : Column T, p.1.getD n.val 0 = T.slope n) ∧
  (∀ w : Word T, wordList w ∈ p.2.1 ↔ Allowed T w) ∧
  ∀ (t : Fin 2) (j : Symbol T),
    j.val ∈ (if t.val = 0 then p.2.2.1 else p.2.2.2) ↔ SeedSet T t j

def numericalBadWords (d : ParameterData) (p : Payload) : List (List ℕ) :=
  (numericalWords d.1 d.2.1).filter fun w => decide (w ∉ p.2.1)

theorem numericalBadWords_primrec : Primrec (fun d : ParameterData × Payload =>
    numericalBadWords d.1 d.2) := by
  unfold numericalBadWords
  have hp : Primrec (fun z : ParameterData × Payload => (z.1.1,z.1.2.1)) := by fun_prop
  apply filterList (numericalWords_primrec.comp hp)
  fun_prop

theorem mem_numericalBadWords (T : System) (p : Payload) (hp : PayloadCorrect T p) (xs : List ℕ) :
    xs ∈ numericalBadWords (parameterData T) p ↔
      ∃ w : Word T, wordList w = xs ∧ ¬ Allowed T w := by
  simp only [numericalBadWords,List.mem_filter,decide_eq_true_eq]
  rw [show (parameterData T).1 = T.width from rfl,
    show (parameterData T).2.1 = T.alphabet from rfl,mem_numericalWords]
  constructor
  · rintro ⟨⟨w,rfl⟩,hw⟩
    exact ⟨w,rfl,fun h => hw ((hp.2.1 w).mpr h)⟩
  · rintro ⟨w,rfl,hw⟩
    exact ⟨⟨w,rfl⟩,fun h => hw ((hp.2.1 w).mp h)⟩

end TranslationTiling.FiniteCompiler.Effective
