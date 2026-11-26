import TranslationTiling.FiniteCompiler.Effective.SlotRankedLayout

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler.Size Compiler.Effective FiniteCompiler.Effective
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] slotSearchCap slotPrimeAt

def wangCode (k m : ℕ) (g : Bool) (d i : ℕ) : ℕ :=
  i + m*d + (k*m)*g.toNat

def fallbackCode (m : ℕ) (g : Bool) (i : ℕ) (b : Bool) : ℕ :=
  b.toNat + 2*i + (m*2)*g.toNat

private abbrev lowCode := rankedLowAt

abbrev numericalMarker := rankedMarkerAt

abbrev numericalFallback := slotFallbackAt

@[fun_prop] private theorem lowCode_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => lowCode z.1 z.2.1 z.2.2) := rankedLowAt_primrec

@[fun_prop] theorem numericalMarker_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => numericalMarker z.1 z.2.1 z.2.2.1 z.2.2.2) :=
  rankedMarkerAt_primrec

@[fun_prop] theorem numericalFallback_primrec :
    Primrec (fun z : ℕ × ℕ => numericalFallback z.1 z.2) := slotFallbackAt_primrec

def slotRowNumber {k m : ℕ} : SlotRow k m → ℕ
  | .inl i => i.val
  | .inr (.inl (g,d,i)) => 20+wangCode k m g d i
  | .inr (.inr (g,i,b)) => 20+2*k*m+fallbackCode m g i b

theorem numericalMarker_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) (g : Bool) (d : Fin k) (i : Fin m) (j : Fin 3) :
    numericalMarker k m (wangCode k m g d i) j = s.marker (g,d,i) j := by
  unfold marker
  rw [hs]
  cases g <;> rfl

theorem numericalFallback_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) (g : Bool) (i : Fin m) (b : Bool) :
    numericalFallback m (fallbackCode m g i b) = s.fallback (g,i,b) := by
  unfold fallback
  rw [hs]
  cases g <;> cases b <;> rfl

private theorem lowCode_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) (g : Bool) (d : Fin k) (i : Fin m) :
    lowCode k m (wangCode k m g d i) = s.low (g,d,i) := by
  unfold low
  rw [hs]
  cases g <;> rfl

/-- Low and two useful moduli of a row in the numbered layout. -/
def numericalSlotRow (k m i : ℕ) : ℕ × ℕ × ℕ :=
  if i < 20 then
    let rs := fourValueRows 0
    (rowR rs i,sharedObservedA rs i,rowB rs i)
  else if i < 20+2*k*m then
    let j := i-20
    (lowCode k m j,1,numericalMarker k m j 0 * numericalMarker k m j 1 * numericalMarker k m j 2)
  else (1,1,numericalFallback m (i-(20+2*k*m)))

theorem numericalSlotRow_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => numericalSlotRow z.1 z.2.1 z.2.2) := by
  unfold numericalSlotRow
  fun_prop

theorem wangCode_lt {k m : ℕ} (g : Bool) (d : Fin k) (i : Fin m) :
    wangCode k m g d i < 2*k*m := by
  have h₁ : i.val + m*d.val < k*m := by
    calc
      _ < m+m*d.val := Nat.add_lt_add_right i.isLt _
      _ = (d.val+1)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ d.isLt
  rw [Nat.mul_assoc 2 k m]
  cases g <;> simp [wangCode,Bool.toNat] <;> omega

theorem numericalSlotRow_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) (i : SlotRow k m) :
    numericalSlotRow k m (slotRowNumber i) =
      (s.layout.lowSize i,s.layout.firstSize i,s.layout.secondSize i) := by
  rcases i with a | ⟨g,d,i⟩ | ⟨g,i,b⟩
  · have ha : a.val < 20 := by simpa only [fourValueRows_length, mul_zero, add_zero] using a.isLt
    simp [numericalSlotRow,slotRowNumber,ha,layout,fourValueLayout]
  · change numericalSlotRow k m (20+wangCode k m g d i) =
      (s.low (g,d,i),1,∏ j, s.marker (g,d,i) j)
    unfold numericalSlotRow
    rw [ite_eq_right (by omega),ite_eq_left (by have := wangCode_lt g d i; omega),Nat.add_sub_cancel_left]
    have h₀ : numericalMarker k m (wangCode k m g d i) 0 = s.marker (g,d,i) 0 :=
      numericalMarker_eq s hs g d i 0
    have h₁ : numericalMarker k m (wangCode k m g d i) 1 = s.marker (g,d,i) 1 :=
      numericalMarker_eq s hs g d i 1
    have h₂ : numericalMarker k m (wangCode k m g d i) 2 = s.marker (g,d,i) 2 :=
      numericalMarker_eq s hs g d i 2
    dsimp only
    rw [lowCode_eq s hs,h₀,h₁,h₂,Fin.prod_univ_three]
  · change numericalSlotRow k m (20+2*k*m+fallbackCode m g i b) = (1,1,s.fallback (g,i,b))
    unfold numericalSlotRow
    rw [ite_eq_right (by omega),ite_eq_right (by omega),Nat.add_sub_cancel_left,numericalFallback_eq s hs]


/-- The arithmetic rows precede the Wang rows and the fallback rows. -/
def slotRowEquiv (k m : ℕ) : SlotRow k m ≃ Fin (20+2*k*m+4*m) :=
  let wang : WangSlot k m ≃ Fin (2*k*m) :=
    ((finTwoEquiv.symm.prodCongr finProdFinEquiv).trans finProdFinEquiv).trans
      (finCongr (Nat.mul_assoc 2 k m).symm)
  let fb : SlotFallback m ≃ Fin (4*m) :=
    ((finTwoEquiv.symm.prodCongr (((Equiv.refl _).prodCongr finTwoEquiv.symm).trans
      finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by ring))
  ((Equiv.sumCongr (finCongr (by simp)) ((Equiv.sumCongr wang fb).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (Nat.add_assoc 20 (2*k*m) (4*m)).symm)

theorem slotRowEquiv_val {k m : ℕ} (i : SlotRow k m) :
    (slotRowEquiv k m i).val = slotRowNumber i := by
  rcases i with i | ⟨g,d,i⟩ | ⟨g,i,b⟩
  · rfl
  · cases g <;> rfl
  · cases g <;> cases b <;>
      change 20+(2*k*m+_) = 20+2*k*m+_
    all_goals rw [Nat.add_assoc]; rfl

/-- Low moduli of all the rows, in their numerical order. -/
def numericalSlotLows (k m : ℕ) : List ℕ :=
  (List.range (20+2*k*m+4*m)).map fun i => (numericalSlotRow k m i).1

theorem numericalSlotLows_primrec :
    Primrec (fun z : ℕ × ℕ => numericalSlotLows z.1 z.2) := by
  unfold numericalSlotLows
  have h : Primrec (fun z : (ℕ × ℕ) × ℕ => (z.1.1,z.1.2,z.2)) := by fun_prop
  exact mapList (by fun_prop) (Primrec.fst.comp (numericalSlotRow_primrec.comp h))

theorem numericalSlotLows_mem {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) (r : ℕ) :
    r ∈ numericalSlotLows k m ↔ ∃ i : SlotRow k m, s.layout.lowSize i = r := by
  simp only [numericalSlotLows,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    let a := (slotRowEquiv k m).symm ⟨i,hi⟩
    have he : slotRowNumber a = i := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨i,hi⟩)
    exact ⟨a,by rw [← he]; exact (congrArg Prod.fst (numericalSlotRow_eq s hs a)).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨slotRowNumber a,?_,congrArg Prod.fst (numericalSlotRow_eq s hs a)⟩
    rw [← slotRowEquiv_val]
    exact (slotRowEquiv k m a).isLt

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
