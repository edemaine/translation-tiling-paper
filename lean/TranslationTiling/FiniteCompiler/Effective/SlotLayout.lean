import TranslationTiling.FiniteCompiler.Effective.FourValueDependence
import TranslationTiling.FiniteCompiler.SlotPrimes

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

/-- Each Wang word uses `k` digits with `m` independently queried slots per
digit. The pair of fallback primes for a slot is shared across digits of a
given slope. -/
abbrev WangSlot (k m : ℕ) := Bool × Fin k × Fin m
abbrev SlotFallback (m : ℕ) := Bool × Fin m × Bool
abbrev SlotRow (k m : ℕ) := FourValueRow 0 ⊕ (WangSlot k m ⊕ SlotFallback m)

/-- A slot has one low prime and one private output prime per active label. -/
abbrev SlotPrime (k m : ℕ) := (WangSlot k m × Option (Fin 3)) ⊕ SlotFallback m

structure SlotParameters (k m : ℕ) where
  prime : SlotPrime k m → ℕ
  prime_isPrime : ∀ i, (prime i).Prime
  prime_injective : Function.Injective prime
  coprime_arithmetic : ∀ i, (prime i).Coprime (order (fourValueLayout 0))
  block_budget : ∀ (i : WangSlot k m) (j : Option (Fin 3)),
    let a := prime (.inr (i.1,i.2.2,false))
    let b := match j with
      | none => prime (.inr (i.1,i.2.2,true))
      | some j => prime (.inl (i,some j))
    a*b < prime (.inl (i,none))

namespace SlotParameters

variable {k m : ℕ} (s : SlotParameters k m)

def low (i : WangSlot k m) : ℕ := s.prime (.inl (i,none))
def marker (i : WangSlot k m) (j : Fin 3) : ℕ := s.prime (.inl (i,some j))
def fallback (i : SlotFallback m) : ℕ := s.prime (.inr i)

def layout : SharedCoordinates.Layout (SlotRow k m) where
  lowSize
    | .inl i => (fourValueLayout 0).lowSize i
    | .inr (.inl i) => s.low i
    | .inr (.inr _) => 1
  firstSize
    | .inl i => (fourValueLayout 0).firstSize i
    | .inr _ => 1
  secondSize
    | .inl i => (fourValueLayout 0).secondSize i
    | .inr (.inl i) => ∏ j, s.marker i j
    | .inr (.inr i) => s.fallback i
  lowSize_pos
    | .inl i => (fourValueLayout 0).lowSize_pos i
    | .inr (.inl i) => (s.prime_isPrime (.inl (i,none))).pos
    | .inr (.inr _) => Nat.one_pos

/-- The arithmetic frame is fixed. Each slot costs five factors, and the
fallback primes contribute four factors per slot position. -/
theorem order_le {P Q : ℕ} (hP : ∀ i, s.fallback i ≤ P)
    (hQ : ∀ i, s.low i ≤ Q) (hB : ∀ i j, s.marker i j ≤ Q) :
    order s.layout ≤ order (fourValueLayout 0) * (Q^(10*k*m) * P^(4*m)) := by
  have hw (i : WangSlot k m) : rowModulus s.layout (.inr (.inl i)) ≤ Q^5 := by
    change (s.low i)^2*1*(∏ j, s.marker i j) ≤ _
    have h : (∏ j, s.marker i j) ≤ Q^3 := by
      simpa using (Finset.prod_le_prod (s := Finset.univ) (f := s.marker i)
        (g := fun _ => Q) (fun j _ => hB i j))
    rw [show 5 = 2+3 from rfl,pow_add,mul_one]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (hQ i) 2) h
  have hf (i : SlotFallback m) : rowModulus s.layout (.inr (.inr i)) ≤ P := by
    simpa [rowModulus,layout] using hP i
  rw [order,order,Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp_rw [show ∀ i : FourValueRow 0, rowModulus s.layout (.inl i) =
      rowModulus (fourValueLayout 0) i from fun _ => rfl]
  rw [← mul_assoc]
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
  · have h := Finset.prod_le_prod (s := Finset.univ) (g := fun _ : WangSlot k m => Q^5)
      (fun i _ => hw i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_bool,
      Fintype.card_fin,← pow_mul,← Nat.mul_assoc,show 5*2 = 10 from rfl] using h
  · have h := Finset.prod_le_prod (s := Finset.univ) (g := fun _ : SlotFallback m => P)
      (fun i _ => hf i)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,show 2*2 = 4 from rfl] using h

def slotBasePrimeCap : ℕ := 2048

open FiniteCompiler.Effective in
set_option maxRecDepth 10000 in
theorem slotBasePrimeBound : Effective.PrimeBound (order (fourValueLayout 0)) slotBasePrimeCap := by
  rw [fourValueLayout_order]
  have hprod : sharedOrder (fourValueRows 0) ∣
      (sharedReservedPrimes ++ sharedReservedPrimes).prod := by decide +kernel
  have hsmall : ∀ p ∈ sharedReservedPrimes, 0 < p ∧ p ≤ slotBasePrimeCap := by decide +kernel
  intro p _
  by_cases hp : p.Prime
  · right
    by_cases hd : p ∣ sharedOrder (fourValueRows 0)
    · right
      obtain ⟨q,hq,hpq⟩ := hp.prime.dvd_prod_iff.mp (hd.trans hprod)
      have h := hsmall q (by simpa only [List.mem_append,or_self] using hq)
      exact (Nat.le_of_dvd h.1 hpq).trans h.2
    · exact Or.inl hd
  · exact Or.inl hp

open Compiler.Size in
def fallbackCap (m : ℕ) : ℕ := guardedPrimeCap (slotBasePrimeCap+4*m+16)

open Compiler.Size in
def markerCap (k m : ℕ) : ℕ := guardedPrimeCap (fallbackCap m+6*k*m+16)

open Compiler.Size in
def lowCap (k m : ℕ) : ℕ := guardedPrimeCap (fallbackCap m*markerCap k m+2*k*m+16)

end SlotParameters

end

end TranslationTiling.FiniteCompiler.Packed
