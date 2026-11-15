import TranslationTiling.FiniteCompiler.Effective.TernaryInput
import Mathlib.Algebra.BigOperators.Fin

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The seed class of a ternary word; class three is the unused constant-two word. -/
def packedClass (m a : ℕ) : ℕ :=
  if ∃ k ∈ List.range m, a / 3^k % 3 = 0 then
    if ∃ k ∈ List.range m, a / 3^k % 3 = 1 then 2 else 0
  else if ∃ k ∈ List.range m, a / 3^k % 3 = 1 then 1 else 3

def packedCandidates (m c : ℕ) : List ℕ :=
  (List.range (3^m)).filter (fun a => packedClass m a == c)

def packedSelect (m c j : ℕ) : ℕ := (packedCandidates m c).getD j 0

def packedDigit (m c j k : ℕ) : ℕ := packedSelect m c j / 3^k % 3

@[fun_prop] theorem packedClass_primrec : Primrec (fun z : ℕ×ℕ => packedClass z.1 z.2) := by
  unfold packedClass
  fun_prop
@[fun_prop] theorem packedCandidates_primrec : Primrec (fun z : ℕ×ℕ => packedCandidates z.1 z.2) := by
  unfold packedCandidates
  fun_prop
@[fun_prop] theorem packedSelect_primrec : Primrec (fun z : ℕ×ℕ×ℕ => packedSelect z.1 z.2.1 z.2.2) := by
  unfold packedSelect
  fun_prop
@[fun_prop] theorem packedDigit_primrec : Primrec (fun z : ℕ×ℕ×ℕ×ℕ => packedDigit z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold packedDigit
  fun_prop

def wordClass {m : ℕ} (f : Fin m → Fin 3) : ℕ :=
  if ∃ k, f k = 0 then if ∃ k, f k = 1 then 2 else 0
  else if ∃ k, f k = 1 then 1 else 3

def avoided (m : ℕ) (d : Fin 3) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter (fun f => ∀ k, f k ≠ d)

def wordClassSet (m c : ℕ) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter (fun f => wordClass f = c)

theorem avoided_card (m : ℕ) (d : Fin 3) : (avoided m d).card = 2^m := by
  let e : {f : Fin m → Fin 3 // ∀ k, f k ≠ d} ≃ (Fin m → {j : Fin 3 // j ≠ d}) :=
    ⟨fun f k => ⟨f.val k,f.property k⟩,
      fun f => ⟨fun k => (f k).val,fun k => (f k).property⟩,
      by intro f; rfl,by intro f; rfl⟩
  have hd : Fintype.card {j : Fin 3 // j ≠ d} = 2 := by
    fin_cases d <;> decide
  calc
    (avoided m d).card = Fintype.card {f : Fin m → Fin 3 // ∀ k, f k ≠ d} := by
      simp [avoided,Fintype.card_subtype]
    _ = Fintype.card (Fin m → {j : Fin 3 // j ≠ d}) := Fintype.card_congr e
    _ = 2^m := by simp [hd]

theorem avoided_inter (m : ℕ) : avoided m 0 ∩ avoided m 1 = {fun _ => 2} := by
  ext f
  simp only [avoided,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨h0,h1⟩
    funext k
    have h0 := h0 k
    have h1 := h1 k
    generalize he : f k = z at *; fin_cases z <;> simp_all
  · rintro rfl
    simp

theorem wordClassSet_zero (m : ℕ) : wordClassSet m 0 = avoided m 1 \ avoided m 0 := by
  ext f
  simp only [wordClassSet,avoided,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [wordClass]
  by_cases h0 : ∃ k, f k = 0 <;> by_cases h1 : ∃ k, f k = 1 <;> simp_all

theorem wordClassSet_one (m : ℕ) : wordClassSet m 1 = avoided m 0 \ avoided m 1 := by
  ext f
  simp only [wordClassSet,avoided,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [wordClass]
  by_cases h0 : ∃ k, f k = 0 <;> by_cases h1 : ∃ k, f k = 1 <;> simp_all

theorem wordClassSet_two (m : ℕ) : wordClassSet m 2 = Finset.univ \ (avoided m 0 ∪ avoided m 1) := by
  ext f
  simp only [wordClassSet,avoided,Finset.mem_sdiff,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [wordClass]
  by_cases h0 : ∃ k, f k = 0 <;> by_cases h1 : ∃ k, f k = 1 <;> simp_all

theorem wordClassSet_card (m : ℕ) :
    (wordClassSet m 0).card+1=2^m ∧ (wordClassSet m 1).card+1=2^m ∧
    (wordClassSet m 2).card+2*2^m=3^m+1 := by
  have h0 := Finset.card_sdiff_add_card_inter (avoided m 1) (avoided m 0)
  have h1 := Finset.card_sdiff_add_card_inter (avoided m 0) (avoided m 1)
  have h2 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m → Fin 3))
    (avoided m 0 ∪ avoided m 1)
  have hu := Finset.card_union_add_card_inter (avoided m 0) (avoided m 1)
  rw [Finset.inter_comm] at h0
  simp only [avoided_inter,Finset.card_singleton,avoided_card,Finset.univ_inter,
    Finset.card_univ,Fintype.card_fun,Fintype.card_fin,← wordClassSet_zero,
    ← wordClassSet_one,← wordClassSet_two] at h0 h1 h2 hu
  omega

theorem packedClass_equiv (m : ℕ) (f : Fin m → Fin 3) :
    packedClass m (finFunctionFinEquiv f).val = wordClass f := by
  have hd (k : Fin m) : (finFunctionFinEquiv f).val / 3^k.val % 3 = (f k).val :=
    congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply f) k)
  have hh (d : Fin 3) :
      (∃ k ∈ List.range m, (finFunctionFinEquiv f).val / 3^k % 3 = d.val) ↔
        ∃ k, f k = d := by
    simp only [List.mem_range]
    constructor
    · rintro ⟨k,hk,he⟩
      exact ⟨⟨k,hk⟩,Fin.ext ((hd ⟨k,hk⟩).symm.trans he)⟩
    · rintro ⟨k,hk⟩
      exact ⟨k.val,k.isLt,(hd k).trans (congrArg Fin.val hk)⟩
  simp only [packedClass,wordClass,← hh 0,← hh 1,Fin.val_zero,Fin.val_one]

theorem packedCandidates_length (m c : ℕ) :
    (packedCandidates m c).length = (wordClassSet m c).card := by
  have hmap : (packedCandidates m c).toFinset = (wordClassSet m c).image
      (fun f => (finFunctionFinEquiv f).val) := by
    ext a
    simp only [packedCandidates,List.mem_toFinset,List.mem_filter,List.mem_range,beq_iff_eq,
      Finset.mem_image,wordClassSet,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ha,hc⟩
      refine ⟨finFunctionFinEquiv.symm ⟨a,ha⟩,?_,?_⟩
      · simpa only [← packedClass_equiv,Equiv.apply_symm_apply] using hc
      · simp
    · rintro ⟨f,hc,rfl⟩
      exact ⟨(finFunctionFinEquiv f).isLt,(packedClass_equiv m f).trans hc⟩
  have hn : (packedCandidates m c).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hn,hmap,
    Finset.card_image_of_injective]
  intro f g h
  exact finFunctionFinEquiv.injective (Fin.ext h)

theorem packedSelect_mem {m c j : ℕ} (hj : j < (packedCandidates m c).length) :
    packedSelect m c j < 3^m ∧ packedClass m (packedSelect m c j) = c := by
  have h : packedSelect m c j ∈ packedCandidates m c := by
    unfold packedSelect
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  simpa [packedCandidates] using h

theorem packedSelect_injective {m c i j : ℕ} (hi : i < (packedCandidates m c).length)
    (hj : j < (packedCandidates m c).length) (he : packedSelect m c i = packedSelect m c j) : i=j := by
  unfold packedSelect at he
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at he
  exact (List.nodup_range.filter _).getElem_inj_iff.mp he

theorem wordClass_seed {m : ℕ} (f : Fin m → Fin 3) (hc : wordClass f < 3) (t : Fin 2) :
    (∀ k, f k = TernarySystem.seedTag t ∨ f k = 2) ↔ wordClass f = t.val := by
  have h0 : (∀ k, f k = 0 ∨ f k = 2) ↔ ¬ ∃ k, f k = 1 := by
    simp only [not_exists]
    constructor
    · intro h k he; simpa [he] using h k
    · intro h k; have h := h k; generalize he : f k = z at *; fin_cases z <;> simp_all
  have h1 : (∀ k, f k = 1 ∨ f k = 2) ↔ ¬ ∃ k, f k = 0 := by
    simp only [not_exists]
    constructor
    · intro h k he; simpa [he] using h k
    · intro h k; have h := h k; generalize he : f k = z at *; fin_cases z <;> simp_all
  fin_cases t
  · change (∀ k, f k = 0 ∨ f k = 2) ↔ wordClass f = 0
    rw [h0]
    unfold wordClass at *
    split_ifs at * <;> simp_all
  · change (∀ k, f k = 1 ∨ f k = 2) ↔ wordClass f = 1
    rw [h1]
    unfold wordClass at *
    split_ifs at * <;> simp_all

end
end TranslationTiling.FiniteCompiler.Effective
