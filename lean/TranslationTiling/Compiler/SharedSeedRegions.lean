/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.Symbols
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

namespace TranslationTiling

namespace Compiler.SharedSeed

noncomputable section

abbrev Residues (T : LeanWang.TileSet) := Compiler.Residues T
abbrev ActiveLabels := ZMod 3 ⊕ (Fin 2 × ZMod 2)
abbrev InactiveLabels (m : ℕ) := Fin m × (ZMod 2 × ZMod 3)
abbrev LabelledResidue (m : ℕ) :=
  ZMod 3 ⊕ ((Fin 2 × ZMod 2) ⊕ InactiveLabels m)

def residue (T : LeanWang.TileSet) (x : ℤ × ℤ) : Residues T := (x.1, x.2)

def firstPoint (T : LeanWang.TileSet) (y : ZMod 3) : Residues T :=
  (((Sudoku.p * Sudoku.q) * y.val : ℕ), 1)

def secondPoint (T : LeanWang.TileSet) (u : Fin 2 × ZMod 2) : Residues T :=
  (((Sudoku.p * Sudoku.q) * (2 * u.1.val + u.2.val) : ℕ), 2)

def activePoint (T : LeanWang.TileSet) : ActiveLabels → Residues T :=
  Sum.elim (firstPoint T) (secondPoint T)

def firstRegion (T : LeanWang.TileSet) : Set (Residues T) := Set.range (firstPoint T)
def secondRegion (T : LeanWang.TileSet) : Set (Residues T) := Set.range (secondPoint T)
def Rest (T : LeanWang.TileSet) := {s : Residues T // s ∉ Set.range (activePoint T)}
def copyCount (T : LeanWang.TileSet) : ℕ := (residueModulus ^ 2 - 7) / 6

private theorem nat_multiple_cast_injective {u v : ℕ}
    (hu : u < 4) (hv : v < 4)
    (h : ((Sudoku.p * Sudoku.q) * u : ZMod residueModulus) =
      ((Sudoku.p * Sudoku.q) * v : ZMod residueModulus)) : u = v := by
  have hu' : (Sudoku.p * Sudoku.q) * u < residueModulus := by
    have hb : (Sudoku.p * Sudoku.q) * 4 < residueModulus := by rw [residueModulus_eq]; decide
    exact (Nat.mul_lt_mul_of_pos_left hu (by decide)).trans hb
  have hv' : (Sudoku.p * Sudoku.q) * v < residueModulus := by
    have hb : (Sudoku.p * Sudoku.q) * 4 < residueModulus := by rw [residueModulus_eq]; decide
    exact (Nat.mul_lt_mul_of_pos_left hv (by decide)).trans hb
  have hn : (((Sudoku.p * Sudoku.q) * u : ℕ) : ZMod residueModulus) =
      (((Sudoku.p * Sudoku.q) * v : ℕ) : ZMod residueModulus) := by
    simpa only [Nat.cast_mul] using h
  have hh := congrArg ZMod.val hn
  rw [ZMod.val_natCast_of_lt hu', ZMod.val_natCast_of_lt hv'] at hh
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < Sudoku.p * Sudoku.q) hh

theorem firstPoint_injective {T : LeanWang.TileSet} :
    Function.Injective (firstPoint T) := by
  intro y y' h
  apply ZMod.val_injective 3
  apply nat_multiple_cast_injective
      (lt_trans (ZMod.val_lt y) (by decide : 3 < 4))
      (lt_trans (ZMod.val_lt y') (by decide : 3 < 4))
  simpa only [firstPoint, Nat.cast_mul] using congrArg Prod.fst h

theorem secondPoint_injective {T : LeanWang.TileSet} :
    Function.Injective (secondPoint T) := by
  rintro ⟨c,y⟩ ⟨c',y'⟩ h
  have hc := c.isLt
  have hc' := c'.isLt
  have hy := ZMod.val_lt y
  have hy' := ZMod.val_lt y'
  have hcode : 2 * c.val + y.val = 2 * c'.val + y'.val := by
    apply nat_multiple_cast_injective (by omega) (by omega)
    simpa only [secondPoint, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      using congrArg Prod.fst h
  have hcc : c.val = c'.val := by omega
  have hyy : y.val = y'.val := by omega
  exact Prod.ext (Fin.ext hcc) (ZMod.val_injective 2 hyy)

theorem firstPoint_ne_secondPoint {T : LeanWang.TileSet}
    (y : ZMod 3) (u : Fin 2 × ZMod 2) : firstPoint T y ≠ secondPoint T u := by
  intro h
  have hp2 : 2 < residueModulus := by rw [residueModulus_eq]; decide
  have hh := congrArg (fun s : Residues T => s.2.val) h
  change (1 : ZMod (residueModulus)).val = (2 : ZMod (residueModulus)).val at hh
  have h1 : (1 : ZMod (residueModulus)).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < residueModulus)
  have h2 : (2 : ZMod (residueModulus)).val = 2 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt hp2
  have h12 : (1 : ℕ) = 2 := h1.symm.trans (hh.trans h2)
  omega

theorem activePoint_injective {T : LeanWang.TileSet} :
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

theorem first_second_disjoint {T : LeanWang.TileSet} :
    Disjoint (firstRegion T) (secondRegion T) := by
  rw [Set.disjoint_left]
  rintro s ⟨y, rfl⟩ ⟨u, hu⟩
  exact firstPoint_ne_secondPoint y u hu.symm

theorem copyCount_mul_six (T : LeanWang.TileSet) :
    copyCount T * 6 = residueModulus ^ 2 - 7 := by change ((residueModulus ^ 2 - 7) / 6) * 6 = _; rw [residueModulus_eq]; decide

theorem six_mul_copyCount_add_seven (T : LeanWang.TileSet) :
    6 * copyCount T + 7 = residueModulus ^ 2 := by
  change 6 * ((residueModulus ^ 2 - 7) / 6) + 7 = _
  rw [residueModulus_eq]
  decide

noncomputable def restEquiv (T : LeanWang.TileSet) :
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
    simp only [Residues, Compiler.Residues, Fintype.card_prod, ZMod.card]
    ring
  rw [hrest]
  simpa [InactiveLabels, Fintype.card_prod, Nat.mul_assoc]
    using (copyCount_mul_six T).symm

noncomputable def residueAssembly (T : LeanWang.TileSet) :
    LabelledResidue (copyCount T) ≃ Residues T := by
  classical
  exact (Equiv.sumAssoc (ZMod 3) (Fin 2 × ZMod 2)
      (InactiveLabels (copyCount T))).symm |>.trans
    ((Equiv.sumCongr (Equiv.ofInjective (activePoint T)
      (activePoint_injective)) (restEquiv T).symm).trans
      (Equiv.Set.sumCompl (Set.range (activePoint T))))

noncomputable def residueEquiv (T : LeanWang.TileSet) :
    Residues T ≃ LabelledResidue (copyCount T) :=
  (residueAssembly T).symm

@[simp] theorem residueAssembly_first (T : LeanWang.TileSet) (y : ZMod 3) :
    residueAssembly T (Sum.inl y) = firstPoint T y := rfl

@[simp] theorem residueAssembly_second (T : LeanWang.TileSet) (u : Fin 2 × ZMod 2) :
    residueAssembly T (Sum.inr (Sum.inl u)) = secondPoint T u := rfl

@[simp] theorem residueEquiv_firstPoint (T : LeanWang.TileSet) (y : ZMod 3) :
    residueEquiv T (firstPoint T y) = Sum.inl y :=
  (residueAssembly T).symm_apply_apply (Sum.inl y)

@[simp] theorem residueEquiv_secondPoint (T : LeanWang.TileSet) (u : Fin 2 × ZMod 2) :
    residueEquiv T (secondPoint T u) = Sum.inr (Sum.inl u) :=
  (residueAssembly T).symm_apply_apply (Sum.inr (Sum.inl u))

theorem residueEquiv_first_iff (T : LeanWang.TileSet) (s : Residues T) :
    (∃ y, residueEquiv T s = Sum.inl y) ↔ s ∈ firstRegion T := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (residueEquiv T).injective
    rw [residueEquiv_firstPoint, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨y, residueEquiv_firstPoint T y⟩

theorem residueEquiv_second_iff (T : LeanWang.TileSet) (s : Residues T) :
    (∃ u, residueEquiv T s = Sum.inr (Sum.inl u)) ↔
      s ∈ secondRegion T := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (residueEquiv T).injective
    rw [residueEquiv_secondPoint, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨u, residueEquiv_secondPoint T u⟩

noncomputable def outputEquiv (T : LeanWang.TileSet) :
    Residues T ≃ ZMod (residueModulus ^ 2) := by
  apply Fintype.equivOfCardEq
  simp only [Residues, Compiler.Residues, Fintype.card_prod, ZMod.card]
  ring

end

end Compiler.SharedSeed

end TranslationTiling
