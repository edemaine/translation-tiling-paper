import TranslationTiling.FiniteCompiler.Effective.CompactActivation

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler.Effective TranslationTiling.FiniteCompiler.Effective
open scoped Classical

noncomputable section

variable {r a b : ℕ} [NeZero r] [NeZero a] [NeZero b]

abbrev OrdinaryIndex (r a b : ℕ) := ZMod r × ShiftIndex a b

def ordinaryIndexCode (j : OrdinaryIndex r a b) : ActivationCode :=
  (j.1.val,j.2.1.1.val,j.2.1.2.val,j.2.2.val)

theorem activationIndices_iff (ha : 2 ≤ a) (hb : 2 ≤ b) (c : ActivationCode) :
    c ∈ activationIndices a b r ↔ ∃ j : OrdinaryIndex r a b, ordinaryIndexCode j = c := by
  constructor
  · intro hc
    obtain ⟨hr,ha',hb',hm⟩ := (mem_activationIndices _ _ _ _).mp hc
    let e : ZMod a × ZMod b := ((c.2.1 : ℕ),(c.2.2.1 : ℕ))
    have h₁ : e.1.val = c.2.1 := by simp [e,ZMod.val_natCast,Nat.mod_eq_of_lt ha']
    have h₂ : e.2.val = c.2.2.1 := by simp [e,ZMod.val_natCast,Nat.mod_eq_of_lt hb']
    have h : c.2.2.2 < shiftMultiplicity a b e := by
      rw [shiftMultiplicity_numerical ha hb,h₁,h₂]
      exact hm
    refine ⟨((c.1 : ℕ),⟨e,⟨c.2.2.2,h⟩⟩),?_⟩
    change ((c.1 : ZMod r).val,e.1.val,e.2.val,c.2.2.2) = c
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hr,h₁,h₂]
  · rintro ⟨j,rfl⟩
    apply (mem_activationIndices _ _ _ _).mpr
    refine ⟨ZMod.val_lt j.1,ZMod.val_lt j.2.1.1,ZMod.val_lt j.2.1.2,?_⟩
    simpa only [ordinaryIndexCode,shiftMultiplicity_numerical ha hb,
      show FiniteCompiler.numericalMultiplicity = Compiler.numericalMultiplicity from rfl] using j.2.2.isLt

private def offsetCRT (h₁ : Nat.Coprime r a) (h₂ : Nat.Coprime (r*a) b) :
    ZMod (r*a*b) ≃+* (ZMod r × ZMod a) × ZMod b :=
  (ZMod.chineseRemainder h₂).trans ((ZMod.chineseRemainder h₁).prodCongr (RingEquiv.refl _))

private def compactResidue (h₁ : Nat.Coprime r a) (h₂ : Nat.Coprime (r*a) b)
    (j : OrdinaryIndex r a b) : ZMod (r*a*b) :=
  (offsetCRT h₁ h₂).symm ((j.1,compactRhoA j.2),compactRhoB j.2)

private def compactLayer (j : OrdinaryIndex r a b) : ℕ := if extraShift j.2 then 1 else 0

private theorem compactFirst_eq_lift (h₁ : Nat.Coprime r a) (h₂ : Nat.Coprime (r*a) b)
    (j : OrdinaryIndex r a b) :
    compactFirst ((a,b,r),ordinaryIndexCode j) =
      separatedResidueLift (r*a*b) (compactResidue h₁ h₂) compactLayer j := by
  let e := offsetCRT h₁ h₂
  let u := compactRhoA j.2
  let v := compactRhoB j.2
  have ha : differenceResidue a
      (2*Compiler.numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val) j.2.1.1.val = u.val := by
    rw [differenceResidue_eq,ZMod.natCast_zmod_val,Nat.cast_mul,Nat.cast_ofNat]
    rfl
  have hb : differenceResidue b
      (2*Compiler.numericalRank j.2.1.2.val j.2.1.1.val j.2.2.val) j.2.1.2.val = v.val := by
    rw [differenceResidue_eq,ZMod.natCast_zmod_val,Nat.cast_mul,Nat.cast_ofNat]
    rfl
  have hc (n : ℕ) : Congruences [(r,j.1.val),(a,u.val),(b,v.val)] n ↔
      e (n : ZMod (r*a*b)) = ((j.1,u),v) := by
    have h : e (n : ZMod (r*a*b)) = (((n : ZMod r),(n : ZMod a)),(n : ZMod b)) := by
      rw [map_natCast]
      rfl
    rw [h]
    simp only [Congruences,List.forall_mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,
      Prod.mk.injEq,← (ZMod.val_injective r).eq_iff,← (ZMod.val_injective a).eq_iff,
      ← (ZMod.val_injective b).eq_iff,ZMod.val_natCast,Nat.mod_eq_of_lt (ZMod.val_lt j.1),
      Nat.mod_eq_of_lt (ZMod.val_lt u),Nat.mod_eq_of_lt (ZMod.val_lt v)]
    exact and_assoc.symm
  have h := residueSearch_of_equiv e.toEquiv ((j.1,u),v)
    [(r,j.1.val),(a,u.val),(b,v.val)] hc
  unfold compactFirst ordinaryIndexCode separatedResidueLift compactResidue compactLayer
  dsimp only
  rw [ha,hb,h]
  unfold extraShift
  by_cases hh : Compiler.numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val = j.2.1.1.val
  · simp [hh,show FiniteCompiler.numericalRank = Compiler.numericalRank from rfl,e,u,v]
  · simp [hh,show FiniteCompiler.numericalRank = Compiler.numericalRank from rfl,e,u,v]

theorem compactFirst_residues (h₁ : Nat.Coprime r a) (h₂ : Nat.Coprime (r*a) b)
    (j : OrdinaryIndex r a b) :
    let h := compactFirst ((a,b,r),ordinaryIndexCode j)
    (((h : ZMod r),(h : ZMod a)),(h : ZMod b)) = ((j.1,compactRhoA j.2),compactRhoB j.2) := by
  dsimp only
  rw [compactFirst_eq_lift h₁ h₂]
  have he := congrArg (offsetCRT h₁ h₂)
    (separatedResidueLift_cast (r*a*b) (compactResidue h₁ h₂) compactLayer j)
  rw [map_intCast,compactResidue,RingEquiv.apply_symm_apply] at he
  exact he

theorem compactFirst_injective (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h₁ : Nat.Coprime r a) (h₂ : Nat.Coprime (r*a) b)
    (hne : ((2 : ZMod a),(2 : ZMod b)) ≠ (-1,-1)) :
    Function.Injective (fun j : OrdinaryIndex r a b => compactFirst ((a,b,r),ordinaryIndexCode j)) := by
  intro i j he
  have hr := (compactFirst_residues h₁ h₂ i).symm.trans
    ((congrArg (fun x : ℤ => (((x : ZMod r),(x : ZMod a)),(x : ZMod b))) he).trans
      (compactFirst_residues h₁ h₂ j))
  have hl := congrArg (fun v : (ZMod r × ZMod a) × ZMod b => v.1.1) hr
  have hu := congrArg (fun v : (ZMod r × ZMod a) × ZMod b => v.1.2) hr
  have hv := congrArg (fun v : (ZMod r × ZMod a) × ZMod b => v.2) hr
  simp only [compactFirst_eq_lift h₁ h₂] at he
  have hc := separatedResidueLift_code_eq _ _ _ he
  have hd : extraShift i.2 = extraShift j.2 := by
    unfold compactLayer at hc
    cases hi : extraShift i.2 <;> cases hj : extraShift j.2 <;> simp_all
  exact Prod.ext hl (compactShift_injective ha hb hne (Prod.ext hd (Prod.ext hu hv)))

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
