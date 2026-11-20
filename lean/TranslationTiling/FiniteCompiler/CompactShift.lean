import TranslationTiling.FiniteCompiler.BlockActivationInverse
import Mathlib.Algebra.Group.Units.Equiv

namespace TranslationTiling.FiniteCompiler
open scoped Classical
noncomputable section

variable {a b : ℕ} [NeZero a] [NeZero b]

def extraShift (δ : ShiftIndex a b) : Bool :=
  decide (numericalRank δ.1.1.val δ.1.2.val δ.2.val ≠ δ.1.1.val)

theorem rank_pair_cases (ha : 2≤a) (hb : 2≤b) (δ : ShiftIndex a b) :
    (extraShift δ=false ∧ rankA δ=δ.1.1.val ∧ rankB δ=δ.1.2.val) ∨
    (extraShift δ=true ∧ δ.1=(0,0) ∧ rankA δ=1 ∧ rankB δ=1) ∨
    (extraShift δ=true ∧ δ.1=(1,1) ∧ rankA δ=0 ∧ rankB δ=0) := by
  rcases δ with ⟨⟨x,y⟩,j⟩
  have hm : j.val<numericalMultiplicity x.val y.val :=
    j.isLt.trans_le (shiftMultiplicity_numerical ha hb (x,y)).le
  have ha1 := ZMod.val_eq_one (by omega : 1<a) x
  have hb1 := ZMod.val_eq_one (by omega : 1<b) y
  simp only [Sigma.fst,Sigma.snd,Prod.fst,Prod.snd]
  simp only [extraShift,rankA,rankB,decide_eq_true_eq,decide_eq_false_iff_not,not_not,
    Prod.mk.injEq, ← ZMod.val_eq_zero, ← ha1, ← hb1]
  unfold numericalMultiplicity at hm
  unfold numericalRank
  split_ifs at hm ⊢ <;> omega

def compactRhoA (δ : ShiftIndex a b) : ZMod a := 2*(rankA δ : ZMod a)-δ.1.1

def compactRhoB (δ : ShiftIndex a b) : ZMod b := 2*(rankB δ : ZMod b)-δ.1.2

theorem compactRho_cases (ha : 2≤a) (hb : 2≤b) (δ : ShiftIndex a b) :
    (extraShift δ=false ∧ (compactRhoA δ,compactRhoB δ)=δ.1) ∨
    (extraShift δ=true ∧ δ.1=(0,0) ∧ (compactRhoA δ,compactRhoB δ)=(2,2)) ∨
    (extraShift δ=true ∧ δ.1=(1,1) ∧ (compactRhoA δ,compactRhoB δ)=(-1,-1)) := by
  rcases rank_pair_cases ha hb δ with ⟨h,ha',hb'⟩|⟨h,hzero,ha',hb'⟩|⟨h,hone,ha',hb'⟩
  · refine Or.inl ⟨h,?_⟩
    simp [compactRhoA,compactRhoB,ha',hb',two_mul]
  · exact Or.inr (Or.inl ⟨h,hzero,by simp [compactRhoA,compactRhoB,hzero,ha',hb']⟩)
  · exact Or.inr (Or.inr ⟨h,hone,by simp [compactRhoA,compactRhoB,hone,ha',hb']⟩)

theorem compactShift_injective (ha : 2≤a) (hb : 2≤b)
    (hne : ((2 : ZMod a),(2 : ZMod b)) ≠ (-1,-1)) :
    Function.Injective (fun δ : ShiftIndex a b => (extraShift δ,compactRhoA δ,compactRhoB δ)) := by
  intro i j h
  have hm := congrArg (fun z : Bool × ZMod a × ZMod b => z.1) h
  have hr := congrArg (fun z : Bool × ZMod a × ZMod b => z.2) h
  change extraShift i=extraShift j at hm
  change (compactRhoA i,compactRhoB i)=(compactRhoA j,compactRhoB j) at hr
  have sameIndex (hij : i.1=j.1) : i=j := by
    have ha01 : (0 : ZMod a)≠1 := by letI : Fact (1<a) := ⟨by omega⟩; exact zero_ne_one
    have hk : rankA i=rankA j := by
      rcases rank_pair_cases ha hb i with ⟨h,hi,_⟩|⟨h,hh,hi,_⟩|⟨h,hh,hi,_⟩ <;>
        rcases rank_pair_cases ha hb j with ⟨h',hj,_⟩|⟨h',hh',hj,_⟩|⟨h',hh',hj,_⟩ <;>
        simp_all
    apply (shiftOrderA ha hb).injective
    rw [shiftOrderA_apply,shiftOrderA_apply]
    have he (δ : ShiftIndex a b) :
        (shift a b δ).1+rhoA ha hb δ=(rankA δ : ZMod a) := by
      simp [rhoA,fibreOrderA]
    rw [he,he,hk]
    exact Prod.ext (congrArg Prod.snd hij) rfl
  apply sameIndex
  rcases compactRho_cases ha hb i with ⟨h,hi⟩|⟨h,he,hi⟩|⟨h,he,hi⟩ <;>
    rcases compactRho_cases ha hb j with ⟨h',hj⟩|⟨h',he',hj⟩|⟨h',he',hj⟩ <;>
    rw [h,h'] at hm <;> try contradiction
  · exact hi.symm.trans (hr.trans hj)
  · exact he.trans he'.symm
  · exact (hne (hi.symm.trans (hr.trans hj))).elim
  · exact (hne (hj.symm.trans (hr.symm.trans hi))).elim
  · exact he.trans he'.symm

def BlockShiftData.compact (ha : 2≤a) (hb : 2≤b)
    (ua : IsUnit (2 : ZMod a)) (ub : IsUnit (2 : ZMod b)) :
    BlockShiftData (ShiftIndex a b) a b where
  e := shift a b
  rhoA := compactRhoA
  rhoB := compactRhoB
  orderA := (shiftOrderA ha hb).trans (Equiv.prodCongr (Equiv.refl _) (Units.mulLeft ua.unit))
  orderB := (shiftOrderB ha hb).trans (Equiv.prodCongr (Equiv.refl _) (Units.mulLeft ub.unit))
  orderA_apply := by
    intro δ
    have he := shiftOrderA_apply ha hb δ
    simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,he,Units.mulLeft_apply,
      IsUnit.unit_spec]
    have h : (shift a b δ).1+FiniteCompiler.rhoA ha hb δ=(rankA δ : ZMod a) := by
      simp [FiniteCompiler.rhoA,fibreOrderA]
    rw [h]
    unfold compactRhoA shift
    simp only [Prod.map, Equiv.refl_apply]
    congr 1
    abel
  orderB_apply := by
    intro δ
    have he := shiftOrderB_apply ha hb δ
    simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,he,Units.mulLeft_apply,
      IsUnit.unit_spec]
    have h : (shift a b δ).2+FiniteCompiler.rhoB ha hb δ=(rankB δ : ZMod b) := by
      simp [FiniteCompiler.rhoB,fibreOrderB]
    rw [h]
    unfold compactRhoB shift
    simp only [Prod.map, Equiv.refl_apply]
    congr 1
    abel

end
end TranslationTiling.FiniteCompiler
