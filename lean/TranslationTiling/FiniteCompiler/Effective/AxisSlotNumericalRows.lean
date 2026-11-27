import TranslationTiling.FiniteCompiler.Effective.AxisSlotPrimes

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler.Size Compiler.Effective FiniteCompiler.Effective
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] slotSearchCap slotPrimeAt axisPrimeAt axisFallbackAt

abbrev wangCode := SlotParameters.wangCode

def lowCode (k m i : ℕ) := axisPrimeAt k m i 3 * axisPrimeAt k m i 4

def numericalMarker := axisPrimeAt

def numericalFallback := axisFallbackAt

@[fun_prop] theorem lowCode_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => lowCode z.1 z.2.1 z.2.2) := by
  unfold lowCode
  have h₃ : Primrec (fun z : ℕ × ℕ × ℕ => (z.1,z.2.1,z.2.2,(3:ℕ))) := by fun_prop
  have h₄ : Primrec (fun z : ℕ × ℕ × ℕ => (z.1,z.2.1,z.2.2,(4:ℕ))) := by fun_prop
  exact Primrec.nat_mul.comp (axisPrimeAt_primrec.comp h₃) (axisPrimeAt_primrec.comp h₄)

@[fun_prop] theorem numericalMarker_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => numericalMarker z.1 z.2.1 z.2.2.1 z.2.2.2) :=
  axisPrimeAt_primrec.of_eq (by intro z; rfl)

@[fun_prop] theorem numericalFallback_primrec :
    Primrec (fun z : ℕ × ℕ => numericalFallback z.1 z.2) := axisFallbackAt_primrec.of_eq (by intro z; rfl)

def slotRowNumber {k m : ℕ} : AxisRow k m → ℕ
  | .inl i => i.val
  | .inr (.inl (g,d,i)) => 20+wangCode k m g d i
  | .inr (.inr (g,i,a,b)) => 20+2*k*m+axisFallbackCode m g i a b

theorem numericalMarker_eq {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (g : Bool) (d : Fin k) (i : Fin m) (j : Fin 3) :
    numericalMarker k m (wangCode k m g d i) j = s.marker (g,d,i) j := by
  unfold marker
  rw [hs]
  simp only [numericalMarker,rankedAxisPrime,axisGroupPrime,axisSlotRank_val,axisLabelIndex,axisPrimeAt]

theorem numericalFallback_eq {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (g : Bool) (i : Fin m) (a b : Bool) :
    numericalFallback m (axisFallbackCode m g i a b) = s.fallback (g,i,a,b) := by
  unfold fallback
  rw [hs]
  simp only [numericalFallback,rankedAxisPrime,axisFallbackPrime,axisFallbackRank_val]

theorem lowAxisCode_eq {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (g : Bool) (d : Fin k) (i : Fin m) (a : Bool) :
    axisPrimeAt k m (wangCode k m g d i) (3+a.toNat) = s.lowAxis (g,d,i) a := by
  unfold lowAxis
  rw [hs]
  cases a <;> simp only [rankedAxisPrime,axisGroupPrime,axisSlotRank_val,axisLabelIndex,axisPrimeAt,Bool.toNat] <;> rfl

private theorem lowCode_eq {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (g : Bool) (d : Fin k) (i : Fin m) :
    lowCode k m (wangCode k m g d i) = s.low (g,d,i) := by
  unfold lowCode low
  exact congrArg₂ (· * ·) (lowAxisCode_eq s hs g d i false) (lowAxisCode_eq s hs g d i true)

/-- Low and two useful moduli of a row in the numbered layout. -/
def numericalAxisRow (k m i : ℕ) : ℕ × ℕ × ℕ :=
  if i < 20 then
    let rs := fourValueRows 0
    (rowR rs i,sharedObservedA rs i,rowB rs i)
  else if i < 20+2*k*m then
    let j := i-20
    (lowCode k m j,1,numericalMarker k m j 0 * numericalMarker k m j 1 * numericalMarker k m j 2)
  else (1,1,numericalFallback m (i-(20+2*k*m)))

theorem numericalAxisRow_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => numericalAxisRow z.1 z.2.1 z.2.2) := by
  unfold numericalAxisRow
  fun_prop

theorem wangCode_lt {k m : ℕ} (g : Bool) (d : Fin k) (i : Fin m) :
    wangCode k m g d i < 2*k*m := by
  have h₁ : i.val + m*d.val < k*m := by
    calc
      _ < m+m*d.val := Nat.add_lt_add_right i.isLt _
      _ = (d.val+1)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ d.isLt
  rw [Nat.mul_assoc 2 k m]
  cases g <;> simp [wangCode,SlotParameters.wangCode,Bool.toNat] <;> omega

theorem numericalAxisRow_eq {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (i : AxisRow k m) :
    numericalAxisRow k m (slotRowNumber i) =
      (s.layout.lowSize i,s.layout.firstSize i,s.layout.secondSize i) := by
  rcases i with a | ⟨g,d,i⟩ | ⟨g,i,a,b⟩
  · have ha : a.val < 20 := by simpa only [fourValueRows_length, mul_zero, add_zero] using a.isLt
    simp [numericalAxisRow,slotRowNumber,ha,layout,fourValueLayout]
  · change numericalAxisRow k m (20+wangCode k m g d i) =
      (s.low (g,d,i),1,∏ j, s.marker (g,d,i) j)
    unfold numericalAxisRow
    rw [ite_eq_right (by omega),ite_eq_left (by have := wangCode_lt g d i; omega),Nat.add_sub_cancel_left]
    have h₀ : numericalMarker k m (wangCode k m g d i) 0 = s.marker (g,d,i) 0 :=
      numericalMarker_eq s hs g d i 0
    have h₁ : numericalMarker k m (wangCode k m g d i) 1 = s.marker (g,d,i) 1 :=
      numericalMarker_eq s hs g d i 1
    have h₂ : numericalMarker k m (wangCode k m g d i) 2 = s.marker (g,d,i) 2 :=
      numericalMarker_eq s hs g d i 2
    dsimp only
    rw [lowCode_eq s hs,h₀,h₁,h₂,Fin.prod_univ_three]
  · change numericalAxisRow k m (20+2*k*m+axisFallbackCode m g i a b) = (1,1,s.fallback (g,i,a,b))
    unfold numericalAxisRow
    rw [ite_eq_right (by omega),ite_eq_right (by omega),Nat.add_sub_cancel_left,numericalFallback_eq s hs]


/-- The arithmetic rows precede the Wang rows and the fallback rows. -/
def slotRowEquiv (k m : ℕ) : AxisRow k m ≃ Fin (20+2*k*m+8*m) :=
  let wang := axisSlotRank k m
  let fb := axisFallbackRank m
  ((Equiv.sumCongr (finCongr (by simp)) ((Equiv.sumCongr wang fb).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (Nat.add_assoc 20 (2*k*m) (8*m)).symm)

theorem slotRowEquiv_val {k m : ℕ} (i : AxisRow k m) :
    (slotRowEquiv k m i).val = slotRowNumber i := by
  rcases i with i | ⟨g,d,i⟩ | ⟨g,i,a,b⟩
  · rfl
  · cases g <;> rfl
  · change 20+(2*k*m+(axisFallbackRank m (g,i,a,b)).val) = 20+2*k*m+_
    rw [axisFallbackRank_val, Nat.add_assoc]

/-- Low moduli of all the rows, in their numerical order. -/
def numericalSlotLows (k m : ℕ) : List ℕ :=
  (List.range (20+2*k*m+8*m)).map fun i => (numericalAxisRow k m i).1

theorem numericalSlotLows_primrec :
    Primrec (fun z : ℕ × ℕ => numericalSlotLows z.1 z.2) := by
  unfold numericalSlotLows
  have h : Primrec (fun z : (ℕ × ℕ) × ℕ => (z.1.1,z.1.2,z.2)) := by fun_prop
  exact mapList (by fun_prop) (Primrec.fst.comp (numericalAxisRow_primrec.comp h))

theorem numericalSlotLows_mem {k m : ℕ} (s : AxisParameters k m)
    (hs : s.prime = rankedAxisPrime k m) (r : ℕ) :
    r ∈ numericalSlotLows k m ↔ ∃ i : AxisRow k m, s.layout.lowSize i = r := by
  simp only [numericalSlotLows,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    let a := (slotRowEquiv k m).symm ⟨i,hi⟩
    have he : slotRowNumber a = i := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨i,hi⟩)
    exact ⟨a,by rw [← he]; exact (congrArg Prod.fst (numericalAxisRow_eq s hs a)).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨slotRowNumber a,?_,congrArg Prod.fst (numericalAxisRow_eq s hs a)⟩
    rw [← slotRowEquiv_val]
    exact (slotRowEquiv k m a).isLt

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
