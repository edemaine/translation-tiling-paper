import TranslationTiling.EuclideanMembership.Syntax
import TranslationTiling.EuclideanMembership.SlotModel

namespace TranslationTiling.EuclideanMembership
open Rotations.General
open scoped BigOperators Matrix
noncomputable section
variable {d : ℕ}

def indices (d : ℕ) : List (Fin d) := List.ofFn id
@[simp] theorem mem_indices (i : Fin d) : i ∈ indices d := by simp [indices]
@[simp] theorem sum_indices {M : Type*} [AddCommMonoid M] (f : Fin d → M) :
    ((indices d).map f).sum=∑ i, f i := by simp [indices,List.map_ofFn,Fin.sum_ofFn]
@[simp] theorem prod_indices {M : Type*} [CommMonoid M] (f : Fin d → M) :
    ((indices d).map f).prod=∏ i, f i := by simp [indices,List.map_ofFn,Fin.prod_ofFn]

def localRow (i j : Fin d) := pVar (Nat.pair 2 (Nat.pair i.val j.val))
def localNormal (i : Fin d) := pVar (Nat.pair 3 i.val)
def localPresence := pVar (Nat.pair 0 0)
def localIdentity (i j : Fin d) := pConst (if i=j then 1 else 0)
def localOrthogonal (d : ℕ) : Formula :=
  fAll ((indices d).map fun i => fAll ((indices d).map fun j =>
    fEq (pSum ((indices d).map fun k => pMul (localRow k i) (localRow k j))) (localIdentity i j)))

def localDeterminant (d : ℕ) : Polynomial :=
  pSum ((Finset.univ : Finset (Equiv.Perm (Fin d))).toList.map fun σ =>
    pMul (pConst (Equiv.Perm.sign σ : ℤ))
      (pProd ((indices d).map fun i => localRow (σ i) i)))

def localAllowed (d : ℕ) (ar af : Bool) : Formula :=
  if ar then if af then fTrue else fEq (localDeterminant d) (pConst 1)
  else fOr
    (fAll ((indices d).map fun i => fAll ((indices d).map fun j =>
      fEq (localRow i j) (localIdentity i j))))
    (if af then fAnd
      (fEq (pSum ((indices d).map fun i => pMul (localNormal i) (localNormal i))) (pConst 1))
      (fAll ((indices d).map fun i => fAll ((indices d).map fun j =>
        fEq (localRow i j) (pSub (localIdentity i j)
          (pMul (pConst 2) (pMul (localNormal i) (localNormal j))))))) else fFalse)

def localSlot (d : ℕ) (ar af : Bool) : Formula :=
  fAnd (fOr (fEq localPresence (pConst 0)) (fEq localPresence (pConst 1)))
    (fOr (fEq localPresence (pConst 0)) (fAnd (localOrthogonal d) (localAllowed d ar af)))

def slotFormula (ar af : Bool) (z : Lattice d) : Formula :=
  renameFormula (slotIndex z) (localSlot d ar af)

def parameterRows (v : ℕ → ℝ) : RealMatrix d :=
  fun i j => v (Nat.pair 2 (Nat.pair i.val j.val))

@[simp] theorem localOrthogonal_iff (v : ℕ → ℝ) :
    Holds (localOrthogonal d) 0 v ↔
      (parameterRows (d := d) v)ᵀ*
        (parameterRows (d := d) v)=1 := by
  rw [← Matrix.ext_iff]
  simp [localOrthogonal,holds_all,
    localRow,localIdentity,evaluate_const,sum_indices,parameterRows,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.one_apply,Int.cast_ite,Int.cast_one,Int.cast_zero]

@[simp] theorem evaluate_localDeterminant (v : ℕ → ℝ) :
    evaluate (localDeterminant d) v=
      (parameterRows (d := d) v).det := by
  simp [localDeterminant,evaluate_sum,evaluate_mul,evaluate_prod,localRow,
    List.map_map,prod_indices,parameterRows,Matrix.det_apply',Finset.sum_toList]

 theorem localAllowed_iff (ar af : Bool) (v : ℕ → ℝ) :
    Holds (localAllowed d ar af) 0 v ↔
    AllowedRows ar af (parameterRows (d := d) v)
      (fun i => v (Nat.pair 3 i.val)) := by
  have hid : parameterRows (d := d) v=1 ↔ ∀ i j : Fin d, v (Nat.pair 2 (Nat.pair i.val j.val))=(if i=j then 1 else 0) := by
    rw [← Matrix.ext_iff]
    rfl
  cases ar <;> cases af <;>
    simp [localAllowed,AllowedRows,localIdentity,localRow,localNormal,
      List.map_map,sum_indices,hid,parameterRows,Matrix.one_apply,pow_two,mul_assoc]

 theorem slotFormula_iff (ar af : Bool) (x : Assignment) (z : Lattice d) :
    Holds (slotFormula ar af z) 0 (coordinates x) ↔ SlotCorrect ar af x z := by
  rw [slotFormula,holds_rename]
  simp only [localSlot,holds_and,holds_or,holds_eq,evaluate_var,evaluate_const,
    localPresence,localOrthogonal_iff,localAllowed_iff,Function.comp_def,
    parameterRows,coordinates,SlotCorrect,presence,slotRows,slotNormal,Enabled,Int.cast_zero,Int.cast_one]
  constructor
  · rintro ⟨hbool,h⟩
    refine ⟨hbool,fun he => ?_⟩
    rcases h with hz | h
    · linarith
    · exact h
  · rintro ⟨hbool,h⟩
    refine ⟨hbool,?_⟩
    rcases hbool with hz | he
    · exact Or.inl hz
    · exact Or.inr (h he)
end
end TranslationTiling.EuclideanMembership
