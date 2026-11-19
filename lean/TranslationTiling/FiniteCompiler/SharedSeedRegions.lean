/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.FiniteCompiler.Symbols
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation

namespace TranslationTiling

namespace FiniteCompiler.SharedSeed

variable [SeedFrame]

noncomputable section

abbrev Residues (T : System) := FiniteCompiler.Residues T
abbrev ActiveLabels := ZMod 3 ⊕ (Fin 2 × ZMod 2)
abbrev InactiveLabels (m : ℕ) := Fin m × (ZMod 2 × ZMod 3)
abbrev LabelledResidue (m : ℕ) :=
  ZMod 3 ⊕ ((Fin 2 × ZMod 2) ⊕ InactiveLabels m)

def residue (T : System) (x : ℤ × ℤ) : Residues T := (x.1, x.2)

def firstHeight (y : ZMod 3) : ℕ := ![1,2,16] ((ZMod.finEquiv 3).symm y)
def secondHeight (u : Fin 2 × ZMod 2) : ℕ :=
  ![4,13,18,19] ⟨2*u.1.val+u.2.val, by have := u.1.isLt; have := ZMod.val_lt u.2; omega⟩

def firstCoords (y : ZMod 3) : ℕ × ℕ :=
  if SeedFrame.compact then (0,firstHeight y) else (35*y.val,1)

def secondCoords (u : Fin 2 × ZMod 2) : ℕ × ℕ :=
  if SeedFrame.compact then (0,secondHeight u) else (35*(2*u.1.val+u.2.val),2)

def firstPoint (T : System) (y : ZMod 3) : Residues T :=
  if SeedFrame.compact then (0,firstHeight y) else ((35*y.val : ℕ),1)

def secondPoint (T : System) (u : Fin 2 × ZMod 2) : Residues T :=
  if SeedFrame.compact then (0,secondHeight u) else ((35*(2*u.1.val+u.2.val) : ℕ),2)

def activePoint (T : System) : ActiveLabels → Residues T :=
  Sum.elim (firstPoint T) (secondPoint T)

def firstRegion (T : System) : Set (Residues T) := Set.range (firstPoint T)
def secondRegion (T : System) : Set (Residues T) := Set.range (secondPoint T)
def Rest (T : System) := {s : Residues T // s ∉ Set.range (activePoint T)}
def copyCount (T : System) : ℕ := (residueModulus ^ 2 - 7) / 6

private theorem coords_first_injective : Function.Injective firstCoords := by
  cases h : SeedFrame.compact
  · intro y z he
    have hh := congrArg Prod.fst he
    simp [firstCoords,h] at hh
    exact ZMod.val_injective _ hh
  · have hh : Function.Injective firstHeight := by decide +kernel
    intro y z he
    apply hh
    simpa [firstCoords,h] using congrArg Prod.snd he

private theorem coords_second_injective : Function.Injective secondCoords := by
  cases h : SeedFrame.compact
  · rintro ⟨i,y⟩ ⟨j,z⟩ he
    have hh := congrArg Prod.fst he
    simp [secondCoords,h] at hh
    exact Prod.ext (Fin.ext (by change i.val=j.val; have hy := ZMod.val_lt y; have hz := ZMod.val_lt z; omega))
      (ZMod.val_injective _ (by change y.val=z.val; have hy := ZMod.val_lt y; have hz := ZMod.val_lt z; omega))
  · have hh : Function.Injective secondHeight := by decide +kernel
    intro y z he
    apply hh
    simpa [secondCoords,h] using congrArg Prod.snd he

private theorem firstCoords_lt (y : ZMod 3) :
    (firstCoords y).1 < residueModulus ∧ (firstCoords y).2 < residueModulus := by
  cases h : SeedFrame.compact
  · have hy := ZMod.val_lt y
    simp [firstCoords,residueModulus_value,h,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    omega
  · have hb : ∀ z : ZMod 3, firstHeight z < 35 := by decide +kernel
    simpa [firstCoords,residueModulus_value,h] using hb y

private theorem secondCoords_lt (u : Fin 2 × ZMod 2) :
    (secondCoords u).1 < residueModulus ∧ (secondCoords u).2 < residueModulus := by
  cases h : SeedFrame.compact
  · have hi := u.1.isLt
    have hu := ZMod.val_lt u.2
    simp [secondCoords,residueModulus_value,h,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    omega
  · have hb : ∀ z : Fin 2 × ZMod 2, secondHeight z < 35 := by decide +kernel
    simpa [secondCoords,residueModulus_value,h] using hb u

private theorem firstPoint_vals (T : System) (y : ZMod 3) :
    ((firstPoint T y).1.val,(firstPoint T y).2.val)=firstCoords y := by
  have h' : ((((firstCoords y).1 : ZMod residueModulus)).val,
      (((firstCoords y).2 : ZMod residueModulus)).val)=firstCoords y :=
    Prod.ext (ZMod.val_natCast_of_lt (firstCoords_lt y).1)
      (ZMod.val_natCast_of_lt (firstCoords_lt y).2)
  cases h : SeedFrame.compact <;>
    simpa [firstPoint,firstCoords,h,Nat.cast_ofNat] using h'

private theorem secondPoint_vals (T : System) (u : Fin 2 × ZMod 2) :
    ((secondPoint T u).1.val,(secondPoint T u).2.val)=secondCoords u := by
  have h' : ((((secondCoords u).1 : ZMod residueModulus)).val,
      (((secondCoords u).2 : ZMod residueModulus)).val)=secondCoords u :=
    Prod.ext (ZMod.val_natCast_of_lt (secondCoords_lt u).1)
      (ZMod.val_natCast_of_lt (secondCoords_lt u).2)
  cases h : SeedFrame.compact <;>
    simpa [secondPoint,secondCoords,h,Nat.cast_ofNat] using h'

theorem firstPoint_injective {T : System} [AlphabetFamily T] :
    Function.Injective (firstPoint T) := by
  intro y z he
  apply coords_first_injective
  rw [←firstPoint_vals T y,←firstPoint_vals T z,he]

theorem secondPoint_injective {T : System} [AlphabetFamily T] :
    Function.Injective (secondPoint T) := by
  intro y z he
  apply coords_second_injective
  rw [←secondPoint_vals T y,←secondPoint_vals T z,he]

theorem firstPoint_ne_secondPoint {T : System} [AlphabetFamily T]
    (y : ZMod 3) (u : Fin 2 × ZMod 2) : firstPoint T y ≠ secondPoint T u := by
  intro he
  have hh : firstCoords y=secondCoords u := by
    rw [←firstPoint_vals T y,←secondPoint_vals T u,he]
  have hs := congrArg Prod.snd hh
  cases h : SeedFrame.compact
  · simp [firstCoords,secondCoords,h] at hs
  · have hb : ∀ (y : ZMod 3) (u : Fin 2 × ZMod 2), firstHeight y ≠ secondHeight u := by decide +kernel
    exact hb y u (by simpa [firstCoords,secondCoords,h] using hs)

theorem activePoint_injective {T : System} [AlphabetFamily T] :
    Function.Injective (activePoint T) := by
  intro a b h
  cases a with
  | inl y =>
    cases b with
    | inl y' => exact congrArg Sum.inl (firstPoint_injective h)
    | inr u => exact (firstPoint_ne_secondPoint y u h).elim
  | inr u =>
    cases b with
    | inl y => exact (firstPoint_ne_secondPoint y u h.symm).elim
    | inr u' => exact congrArg Sum.inr (secondPoint_injective h)

theorem first_second_disjoint {T : System} [AlphabetFamily T] :
    Disjoint (firstRegion T) (secondRegion T) := by
  rw [Set.disjoint_left]
  rintro s ⟨y, rfl⟩ ⟨u, hu⟩
  exact firstPoint_ne_secondPoint y u hu.symm

theorem copyCount_mul_six (T : System) :
    copyCount T * 6 = residueModulus ^ 2 - 7 := by change ((residueModulus ^ 2 - 7) / 6) * 6 = _; rw [residueModulus_value]; split <;> decide +kernel

theorem six_mul_copyCount_add_seven (T : System) :
    6 * copyCount T + 7 = residueModulus ^ 2 := by
  change 6 * ((residueModulus ^ 2 - 7) / 6) + 7 = _
  rw [residueModulus_value]
  split <;> decide

noncomputable def restEquiv (T : System) :
    Rest T ≃ InactiveLabels (copyCount T) := by
  classical

  letI : Fintype (Rest T) := by unfold Rest; infer_instance
  apply Fintype.equivOfCardEq
  have hactive : Fintype.card (Set.range (activePoint T)) = 7 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (activePoint_injective))]
    norm_num [ActiveLabels]
  have hrest : Fintype.card (Rest T) = residueModulus ^ 2 - 7 := by
    change Fintype.card ((Set.range (activePoint T))ᶜ : Set (Residues T)) = _
    rw [Fintype.card_compl_set, hactive]
    simp only [Residues, FiniteCompiler.Residues, Fintype.card_prod, ZMod.card]
    ring
  rw [hrest]
  simpa [InactiveLabels, Fintype.card_prod, Nat.mul_assoc]
    using (copyCount_mul_six T).symm

noncomputable def residueAssembly (T : System) :
    LabelledResidue (copyCount T) ≃ Residues T := by
  classical
  exact (Equiv.sumAssoc (ZMod 3) (Fin 2 × ZMod 2)
      (InactiveLabels (copyCount T))).symm |>.trans
    ((Equiv.sumCongr (Equiv.ofInjective (activePoint T)
      (activePoint_injective)) (restEquiv T).symm).trans
      (Equiv.Set.sumCompl (Set.range (activePoint T))))

noncomputable def residueEquiv (T : System) :
    Residues T ≃ LabelledResidue (copyCount T) :=
  (residueAssembly T).symm

@[simp] theorem residueAssembly_first (T : System) (y : ZMod 3) :
    residueAssembly T (Sum.inl y) = firstPoint T y := rfl

@[simp] theorem residueAssembly_second (T : System) (u : Fin 2 × ZMod 2) :
    residueAssembly T (Sum.inr (Sum.inl u)) = secondPoint T u := rfl

@[simp] theorem residueEquiv_firstPoint (T : System) (y : ZMod 3) :
    residueEquiv T (firstPoint T y) = Sum.inl y :=
  (residueAssembly T).symm_apply_apply (Sum.inl y)

@[simp] theorem residueEquiv_secondPoint (T : System) (u : Fin 2 × ZMod 2) :
    residueEquiv T (secondPoint T u) = Sum.inr (Sum.inl u) :=
  (residueAssembly T).symm_apply_apply (Sum.inr (Sum.inl u))

theorem residueEquiv_first_iff (T : System) (s : Residues T) :
    (∃ y, residueEquiv T s = Sum.inl y) ↔ s ∈ firstRegion T := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (residueEquiv T).injective
    rw [residueEquiv_firstPoint, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨y, residueEquiv_firstPoint T y⟩

theorem residueEquiv_second_iff (T : System) (s : Residues T) :
    (∃ u, residueEquiv T s = Sum.inr (Sum.inl u)) ↔
      s ∈ secondRegion T := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (residueEquiv T).injective
    rw [residueEquiv_secondPoint, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨u, residueEquiv_secondPoint T u⟩

noncomputable def outputEquiv (T : System) :
    Residues T ≃ ZMod (residueModulus ^ 2) := by
  apply Fintype.equivOfCardEq
  simp only [Residues, FiniteCompiler.Residues, Fintype.card_prod, ZMod.card]
  ring

end

end FiniteCompiler.SharedSeed

end TranslationTiling
