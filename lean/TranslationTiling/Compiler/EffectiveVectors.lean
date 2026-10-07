import TranslationTiling.Compiler.EffectiveCycleTables
import Mathlib.Data.List.Forall2

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

theorem ofFn_primrec {α : Type*} [Primcodable α] {n : ℕ} :
    Primrec (List.ofFn : (Fin n → α) → List α) := by
  have hp : Primrec (fun p : (Fin n → α) × Fin n => p.1 p.2) :=
    applyFin Primrec.fst Primrec.snd
  have h := mapList (f := fun _ : Fin n → α => List.ofFn (id : Fin n → Fin n))
    (g := fun f i => f i) (Primrec.const _) hp
  exact h.of_eq (fun _ => by simp only [List.map_ofFn, Function.comp_def, id_eq])

def vectorOfList {α : Type*} [Inhabited α] {n : ℕ} (xs : List α) : Fin n → α :=
  fun i => xs.getD i.val default

theorem vectorOfList_primrec {α : Type*} [Primcodable α] [Inhabited α] {n : ℕ} :
    Primrec (vectorOfList (α := α) (n := n)) := by
  apply piValue
  intro i
  exact (Primrec.list_getD default).comp Primrec.id (Primrec.const i.val)

def vectors {α : Type*} [Inhabited α] {n : ℕ}
    (alphabets : Fin n → List α) : List (Fin n → α) :=
  (mixedProducts (List.ofFn alphabets)).map vectorOfList

theorem vectors_primrec {α : Type*} [Primcodable α] [Inhabited α] {n : ℕ} :
    Primrec (vectors (α := α) (n := n)) := by
  unfold vectors
  exact mapList (mixedProducts_primrec.comp ofFn_primrec)
    (vectorOfList_primrec.comp Primrec.snd)

theorem mem_vectors {α : Type*} [Inhabited α] {n : ℕ}
    (alphabets : Fin n → List α) (f : Fin n → α) :
    f ∈ vectors alphabets ↔ ∀ i, f i ∈ alphabets i := by
  constructor
  · intro hf
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hf
    have h := (mem_mixedProducts _ _).mp hxs
    have hlen : xs.length = n := h.length_eq.trans List.length_ofFn
    intro i
    have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
    have hn : i.val < (List.ofFn alphabets).length := by
      rw [List.length_ofFn]; exact i.isLt
    have he := h.get hi hn
    simpa only [vectorOfList, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, List.get_eq_getElem,
      List.getElem_ofFn] using he
  · intro hf
    apply List.mem_map.mpr
    refine ⟨List.ofFn f, (mem_mixedProducts _ _).mpr ?_, ?_⟩
    · apply List.forall₂_of_length_eq_of_get
      · simp only [List.length_ofFn]
      · intro k hk hk'
        simpa only [List.get_eq_getElem, List.getElem_ofFn] using
          hf ⟨k, by simpa only [List.length_ofFn] using hk⟩
    · funext i
      simp only [vectorOfList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        dif_pos i.isLt, Option.getD_some]

theorem computablePi {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {n : ℕ} {f : α → Fin n → β}
    (hf : ∀ i, Computable (fun a => f a i)) : Computable f := by
  have hl := Computable.list_ofFn hf
  have h := (vectorOfList_primrec (α := β) (n := n)).to_comp.comp hl
  exact h.of_eq (fun _ => by
    funext i
    simp only [vectorOfList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dif_pos i.isLt, Option.getD_some])

end TranslationTiling.Compiler.Effective
