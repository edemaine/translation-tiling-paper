/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.EncodingParameters
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Basic

set_option maxRecDepth 1000

namespace TranslationTiling

noncomputable section

namespace Compiler

open scoped BigOperators

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

def digitEquivRing (i : Channel T) :
    ZMod (E.r i) ≃+* (∀ j : Label T i, ZMod (E.digitPrime i j)) := by
  rw [E.r_eq_prod]
  exact ZMod.prodEquivPi (E.digitPrime i) (E.digitPrime_pairwise i)

def digitEquiv (i : Channel T) :
    ZMod (E.r i) ≃+ (∀ j : Label T i, ZMod (E.digitPrime i j)) :=
  (digitEquivRing E i).toAddEquiv

theorem digitPrime_dvd_r (i : Channel T) (j : Label T i) :
    E.digitPrime i j ∣ E.r i := by
  rw [E.r_eq_prod]
  exact Finset.dvd_prod_of_mem (E.digitPrime i) (Finset.mem_univ j)

@[simp] theorem digitEquiv_intCast (i : Channel T) (z : ℤ) (j : Label T i) :
    digitEquiv E i (z : ZMod (E.r i)) j = (z : ZMod (E.digitPrime i j)) := by
  exact congrArg (fun f : ∀ j : Label T i, ZMod (E.digitPrime i j) => f j)
    (map_intCast (digitEquivRing E i) z)

theorem digitEquiv_apply (i : Channel T) (x : ZMod (E.r i)) (j : Label T i) :
    digitEquiv E i x j = (ZMod.cast x : ZMod (E.digitPrime i j)) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [digitEquiv_intCast, ZMod.cast_intCast (digitPrime_dvd_r E i j)]

def digitSubgroup (i : Channel T) (j : Label T i) : AddSubgroup (ZMod (E.r i)) where
  carrier := {x | ∀ k : Label T i, k ≠ j → digitEquiv E i x k = 0}
  zero_mem' := by
    intro k _hk
    simp
  add_mem' := by
    intro x y hx hy k hk
    simp [map_add, hx k hk, hy k hk]
  neg_mem' := by
    intro x hx k hk
    simp [map_neg, hx k hk]

@[simp] theorem mem_digitSubgroup (i : Channel T) (j : Label T i) (x : ZMod (E.r i)) :
    x ∈ digitSubgroup E i j ↔
      ∀ k : Label T i, k ≠ j → digitEquiv E i x k = 0 := Iff.rfl

theorem sub_mem_digitSubgroup_iff (i : Channel T) (j : Label T i)
    (x y : ZMod (E.r i)) :
    x - y ∈ digitSubgroup E i j ↔
      ∀ k : Label T i, k ≠ j → digitEquiv E i x k = digitEquiv E i y k := by
  simp [mem_digitSubgroup, map_sub, sub_eq_zero]

def digitSingle (i : Channel T) (j : Label T i) (x : ZMod (E.digitPrime i j)) :
    ZMod (E.r i) :=
  (digitEquiv E i).symm (Pi.single j x)

@[simp] theorem digitEquiv_digitSingle (i : Channel T) (j : Label T i)
    (x : ZMod (E.digitPrime i j)) :
    digitEquiv E i (digitSingle E i j x) = Pi.single j x :=
  (digitEquiv E i).apply_symm_apply _

theorem digitSingle_mem (i : Channel T) (j : Label T i)
    (x : ZMod (E.digitPrime i j)) : digitSingle E i j x ∈ digitSubgroup E i j := by
  intro k hk
  rw [digitEquiv_digitSingle]
  exact Pi.single_eq_of_ne (M := fun j : Label T i => ZMod (E.digitPrime i j)) hk x

end Compiler

end

end TranslationTiling
