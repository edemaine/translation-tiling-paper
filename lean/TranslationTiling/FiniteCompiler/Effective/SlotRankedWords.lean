import TranslationTiling.Compiler.EffectiveArithmetic
import TranslationTiling.FiniteCompiler.Effective.BitCode
import TranslationTiling.FiniteCompiler.SlotWords
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange

namespace TranslationTiling.FiniteCompiler.SlotWords

private def support {m : ℕ} (f : Fin m → Option (Fin 3)) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).isSome = true

private abbrev Flat (m w : ℕ) := {f : Fin m → Option (Fin 3) // (support f).card = w}

private def flatten {m w : ℕ} (word : Word m w 3) (i : Fin m) : Option (Fin 3) :=
  if h : i ∈ word.1.val then some (word.2 ⟨i,h⟩) else none

private theorem support_flatten {m w : ℕ} (word : Word m w 3) :
    support (flatten word) = word.1.val := by
  ext i
  by_cases h : i ∈ word.1.val <;> simp [support,flatten,h]

private def unflatten {m w : ℕ} (f : Flat m w) : Word m w 3 :=
  ⟨⟨support f.val,f.property⟩,fun i => (f.val i).get (by simpa [support] using i.property)⟩

private def flattenEquiv (m w : ℕ) : Word m w 3 ≃ Flat m w where
  toFun v := ⟨flatten v,by rw [support_flatten]; exact v.1.property⟩
  invFun := unflatten
  left_inv v := by
    symm
    apply (reads_uses_iff v (unflatten ⟨flatten v, _⟩)).mp
    intro i
    have hi : (i : Fin m) ∈ v.1.val := by
      have h : (i : Fin m) ∈ support (flatten v) := i.property
      exact Eq.mp (congrArg (fun S : Finset (Fin m) => i.val ∈ S) (support_flatten v)) h
    exact ⟨hi,by simp [unflatten,flatten,hi]⟩
  right_inv f := by
    apply Subtype.ext
    funext i
    have hiff : i ∈ support f.val ↔ (f.val i).isSome = true := by simp [support]
    change flatten (unflatten f) i = f.val i
    unfold flatten
    change (if h : i ∈ support f.val then _ else _) = _
    split
    · rename_i hi
      have hs := hiff.mp hi
      cases h : f.val i with
      | none => simp [h] at hs
      | some a => simp [unflatten,h]
    · rename_i hi
      cases h : f.val i with
      | none => rfl
      | some a => exact (hi (hiff.mpr (by simp [h]))).elim

private def flatCode (m : ℕ) : (Fin m → Option (Fin 3)) ≃ Fin (4^m) :=
  (Equiv.piCongrRight fun _ => (finSuccEquiv 3).symm).trans finFunctionFinEquiv

private def codes (m w : ℕ) : List (Fin (4^m)) :=
  (List.finRange (4^m)).filter fun a => decide ((support ((flatCode m).symm a)).card = w)

private theorem mem_codes {m w : ℕ} {a : Fin (4^m)} :
    a ∈ codes m w ↔ (support ((flatCode m).symm a)).card = w := by
  simp [codes]

private def flatNumber (m w : ℕ) : Flat m w ≃ {a : Fin (4^m) // a ∈ codes m w} where
  toFun f := ⟨flatCode m f.val,mem_codes.mpr (by simpa using f.property)⟩
  invFun a := ⟨(flatCode m).symm a,mem_codes.mp a.property⟩
  left_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (Equiv.apply_symm_apply _ _)

private def listNumber {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (h : xs.Nodup) :
    {a : α // a ∈ xs} ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a.val,List.idxOf_lt_length_of_mem a.property⟩
  invFun i := ⟨xs[i.val],List.getElem_mem i.isLt⟩
  left_inv a := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem a.property))
  right_inv i := Fin.ext (h.idxOf_getElem i.val i.isLt)

private def wordNumber (m w : ℕ) : Word m w 3 ≃ Fin (codes m w).length :=
  (flattenEquiv m w).trans ((flatNumber m w).trans
    (listNumber _ (List.Nodup.filter _ (List.nodup_finRange _))))

private theorem codes_length (m w : ℕ) : (codes m w).length = m.choose w * 3^w := by
  simpa only [Fintype.card_fin,card_word] using (Fintype.card_congr (wordNumber m w)).symm

/-- Number fixed-weight words by sorting their base-four representations. -/
def rankedWord (m w : ℕ) : Word m w 3 ≃ Fin (m.choose w * 3^w) :=
  (wordNumber m w).trans (finCongr (codes_length m w))

/-- Pack several fixed-weight digits using the numbered word alphabet. -/
def rankedWordTuple (k m w : ℕ) :
    Fin ((m.choose w * 3^w)^k) ≃ (Fin k → Word m w 3) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => (rankedWord m w).symm)

open TranslationTiling.Compiler.Effective TranslationTiling.FiniteCompiler.Effective

private def baseFourDigit (a i : ℕ) : ℕ := a / 4^i % 4

@[fun_prop] private theorem baseFourDigit_primrec :
    Primrec (fun p : ℕ × ℕ => baseFourDigit p.1 p.2) := by
  unfold baseFourDigit
  fun_prop

private def baseFourWeight (m a : ℕ) : ℕ :=
  ((List.range m).filter fun i => decide (0 < baseFourDigit a i)).length

@[fun_prop] private theorem baseFourWeight_primrec :
    Primrec (fun p : ℕ × ℕ => baseFourWeight p.1 p.2) := by
  unfold baseFourWeight
  apply Primrec.list_length.comp
  exact filterList (f := fun p : ℕ × ℕ => List.range p.1)
    (p := fun p i => 0 < baseFourDigit p.2 i) (by fun_prop) (by fun_prop)

private def numericalWordCodes (m w : ℕ) : List ℕ :=
  (List.range (4^m)).filter fun a => decide (baseFourWeight m a = w)

@[fun_prop] private theorem numericalWordCodes_primrec :
    Primrec (fun p : ℕ × ℕ => numericalWordCodes p.1 p.2) := by
  unfold numericalWordCodes
  exact filterList (f := fun p : ℕ × ℕ => List.range (4^p.1))
    (p := fun p a => baseFourWeight p.1 a = p.2) (by fun_prop) (by fun_prop)

/-- Zero records an unused slot. Values one through three record marker labels. -/
def numericalWordDigit (m w index i : ℕ) : ℕ :=
  baseFourDigit ((numericalWordCodes m w).getD index 0) i

@[fun_prop] theorem numericalWordDigit_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => numericalWordDigit p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold numericalWordDigit
  fun_prop

theorem numericalWordDigit_lt (m w index i : ℕ) : numericalWordDigit m w index i < 4 :=
  Nat.mod_lt _ (by decide)

private theorem flatCode_digit {m : ℕ} (a : Fin (4^m)) (i : Fin m) :
    ((finSuccEquiv 3).symm ((flatCode m).symm a i)).val = baseFourDigit a.val i.val := by
  change ((finSuccEquiv 3).symm (finSuccEquiv 3 (finFunctionFinEquiv.symm a i))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    rfl

private theorem baseFourWeight_eq (m : ℕ) (a : Fin (4^m)) :
    baseFourWeight m a.val = (support ((flatCode m).symm a)).card := by
  let q := fun i : Fin m => decide (0 < baseFourDigit a.val i.val)
  have hq (i : Fin m) : q i = ((flatCode m).symm a i).isSome := by
    unfold q
    rw [← flatCode_digit a i]
    cases h : (flatCode m).symm a i <;> simp [finSuccEquiv_symm_none,finSuccEquiv_symm_some]
  have hn : ((List.finRange m).filter q).Nodup := (List.nodup_finRange _).filter _
  have hs : ((List.finRange m).filter q).toFinset = support ((flatCode m).symm a) := by
    ext i
    simp only [List.mem_toFinset,List.mem_filter,List.mem_finRange,true_and,hq i,
      support,Finset.mem_filter,Finset.mem_univ]
  unfold baseFourWeight
  rw [← finRange_values m,List.filter_map,List.length_map]
  change ((List.finRange m).filter q).length = _
  rw [← List.toFinset_card_of_nodup hn,hs]

private theorem numericalWordCodes_eq (m w : ℕ) :
    numericalWordCodes m w = (codes m w).map Fin.val := by
  unfold numericalWordCodes codes
  rw [← finRange_values (4^m),List.filter_map]
  simp only [Function.comp_def,baseFourWeight_eq]

theorem numericalWordDigit_correct {m w : ℕ} (a : Fin (m.choose w * 3^w)) (i : Fin m) :
    numericalWordDigit m w a.val i.val =
      ((finSuccEquiv 3).symm (flatten ((rankedWord m w).symm a) i)).val := by
  let j : Fin (codes m w).length := (finCongr (codes_length m w)).symm a
  let b := (codes m w)[j.val]
  have ha : a.val < (codes m w).length := j.isLt
  unfold numericalWordDigit
  rw [numericalWordCodes_eq,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ha),
    List.getElem_map]
  change baseFourDigit b.val i.val =
    ((finSuccEquiv 3).symm (flatten (unflatten ⟨(flatCode m).symm b, _⟩) i)).val
  have hf := (flattenEquiv m w).apply_symm_apply ⟨(flatCode m).symm b, mem_codes.mp (List.getElem_mem j.isLt)⟩
  have he := congrArg Subtype.val hf
  change flatten (unflatten ⟨(flatCode m).symm b, _⟩) = _ at he
  rw [he,flatCode_digit]

theorem numericalWordDigit_uses {m w : ℕ} (a : Fin (m.choose w * 3^w))
    (i : Fin m) (j : Fin 3) :
    numericalWordDigit m w a.val i.val = j.val+1 ↔ Uses ((rankedWord m w).symm a) i j := by
  rw [numericalWordDigit_correct]
  rw [← show ((finSuccEquiv 3).symm (some j)).val = j.val+1 from rfl]
  rw [← Fin.ext_iff, (finSuccEquiv 3).symm.injective.eq_iff]
  unfold flatten Uses
  split
  · rename_i h
    exact ⟨fun he => ⟨h,Option.some.inj he⟩,fun ⟨_,he⟩ => congrArg some he⟩
  · simp_all

/-- The code of a packed digit is its base-radix numerical coordinate. -/
theorem rankedWordTuple_coordinate {k m w : ℕ} (a : Fin ((m.choose w * 3^w)^k)) (d : Fin k) :
    rankedWordTuple k m w a d =
      (rankedWord m w).symm ⟨a.val / (m.choose w * 3^w)^d.val % (m.choose w * 3^w),
        (finFunctionFinEquiv.symm a d).isLt⟩ := rfl

end TranslationTiling.FiniteCompiler.SlotWords
