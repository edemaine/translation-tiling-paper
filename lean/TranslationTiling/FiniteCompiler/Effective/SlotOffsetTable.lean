import TranslationTiling.FiniteCompiler.Effective.SlotObservations
import Mathlib.Data.Finset.Sort

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

namespace SlotParameters

variable {k m : ℕ} (s : SlotParameters k m) (g : Bool) (d : Fin k) (S : Finset (Fin m))

abbrev SelectedSlot (S : Finset (Fin m)) := {i : Fin m // i ∈ S}

abbrev ShiftCount (S : Finset (Fin m)) := Fintype.card (SlotIndex S)

theorem shiftCount_eq : ShiftCount S = S.card * 4 := by
  simp [ShiftCount,SlotIndex]

private theorem zmodFinValue {n : ℕ} [NeZero n] (j : ZMod n) :
    ((ZMod.finEquiv n).symm j).val = j.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- Consecutive groups of four observe one selected slot in increasing
order, starting with its shared fallback coordinate. -/
def shiftIndex [NeZero (ShiftCount S)] : ZMod (ShiftCount S) ≃ SlotIndex S :=
  ((ZMod.finEquiv (ShiftCount S)).symm.toEquiv.trans (finCongr (shiftCount_eq S))).trans
    (finProdFinEquiv.symm.trans ((S.orderIsoOfFin rfl).toEquiv.prodCongr (finSuccEquiv 3)))

theorem shiftIndex_label [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    (shiftIndex S j).2 = finSuccEquiv 3 ⟨j.val % 4,Nat.mod_lt _ (by decide)⟩ := by
  apply congrArg (finSuccEquiv 3)
  apply Fin.ext
  change ((ZMod.finEquiv (ShiftCount S)).symm j).val % 4 = _
  rw [zmodFinValue]

theorem shiftIndex_slot [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    ((shiftIndex S j).1 : Fin m) =
      S.sort[j.val/4]'(by
        rw [Finset.length_sort]
        apply Nat.div_lt_of_lt_mul
        simpa only [Nat.mul_comm 4 S.card,← shiftCount_eq S] using ZMod.val_lt j) := by
  let i := (finCongr (shiftCount_eq S)) ((ZMod.finEquiv (ShiftCount S)).symm j)
  let q : Fin S.card := (finProdFinEquiv.symm i).1
  have hq : q.val = j.val / 4 := by
    change ((ZMod.finEquiv (ShiftCount S)).symm j).val / 4 = j.val / 4
    rw [zmodFinValue]
  change (S.orderIsoOfFin rfl q).val = _
  rw [Finset.coe_orderIsoOfFin_apply,Finset.orderEmbOfFin_apply]
  let a : Fin S.sort.length := ⟨q.val,by rw [Finset.length_sort];exact q.isLt⟩
  let b : Fin S.sort.length := ⟨j.val/4,by simpa only [← hq] using a.isLt⟩
  have hab : a = b := Fin.ext hq
  exact congrArg (fun i : Fin S.sort.length => S.sort[i.val]) hab

def shiftModulus [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) : ℕ :=
  s.observationPrime g d (shiftIndex S j)

abbrev LowShifts := ∀ i : SelectedSlot S, ZMod (s.low (g,d,i))

abbrev OffsetKey (S : Finset (Fin m)) := ZMod (ShiftCount S) ⊕ (SelectedSlot S × Bool)

private def offsetTagOfIndex : SlotIndex S ⊕ (SelectedSlot S × Bool) → SlotPrime k m
  | .inl (i,none) => .inr (g,i,false)
  | .inl (i,some v) => .inl ((g,d,i),some v)
  | .inr (i,false) => .inl ((g,d,i),none)
  | .inr (i,true) => .inr (g,i,true)

private theorem offsetTagOfIndex_injective : Function.Injective (offsetTagOfIndex g d S) := by
  rintro (⟨a,_ | i⟩ | ⟨a,_ | _⟩) (⟨b,_ | j⟩ | ⟨b,_ | _⟩) h <;>
    simp [offsetTagOfIndex] at h
  all_goals
    simp_all only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,Subtype.ext_iff,and_self]

private def offsetTag [NeZero (ShiftCount S)] : OffsetKey S → SlotPrime k m :=
  offsetTagOfIndex g d S ∘ ((shiftIndex S).sumCongr (.refl _))

def offsetModuli [NeZero (ShiftCount S)] : OffsetKey S → ℕ
  | .inl j => s.shiftModulus g d S j
  | .inr (i,false) => s.low (g,d,i)
  | .inr (i,true) => s.fallback (g,i,true)

private theorem offsetModuli_eq [NeZero (ShiftCount S)] (i : OffsetKey S) :
    s.offsetModuli g d S i = s.prime (offsetTag g d S i) := by
  rcases i with j | ⟨i,_ | _⟩
  · change s.observationPrime g d (shiftIndex S j) =
      s.prime (offsetTagOfIndex g d S (.inl (shiftIndex S j)))
    rcases shiftIndex S j with ⟨i,_ | j⟩ <;> rfl
  · rfl
  · rfl

theorem shiftModulus_prime [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    (s.shiftModulus g d S j).Prime := by
  change (s.observationPrime g d (shiftIndex S j)).Prime
  generalize shiftIndex S j = i
  rcases i with ⟨i,_ | q⟩
  · exact s.prime_isPrime (.inr (g,i,false))
  · exact s.prime_isPrime (.inl ((g,d,i),some q))

instance lowShiftNeZero (i : SelectedSlot S) : NeZero (s.low (g,d,i)) :=
  ⟨(s.prime_isPrime (.inl ((g,d,i),none))).ne_zero⟩

instance shiftModulusNeZero [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    NeZero (s.shiftModulus g d S j) :=
  ⟨(shiftModulus_prime s g d S j).ne_zero⟩

theorem offsetModuli_prime [NeZero (ShiftCount S)] (i : OffsetKey S) : (s.offsetModuli g d S i).Prime := by
  rw [offsetModuli_eq]
  exact s.prime_isPrime (offsetTag g d S i)

theorem offsetModuli_coprime [NeZero (ShiftCount S)] : Pairwise fun i j : OffsetKey S =>
    (s.offsetModuli g d S i).Coprime (s.offsetModuli g d S j) := by
  intro i j he
  apply (Nat.coprime_primes (s.offsetModuli_prime g d S i) (s.offsetModuli_prime g d S j)).mpr
  intro h
  rw [offsetModuli_eq,offsetModuli_eq] at h
  have inj := (offsetTagOfIndex_injective g d S).comp
    (((shiftIndex S).sumCongr (Equiv.refl (SelectedSlot S × Bool))).injective)
  exact he (inj (s.prime_injective h))

section Offsets
variable [NeZero (ShiftCount S)]

abbrev ShiftPair := LowShifts s g d S × SlotShift.Shift (s.shiftModulus g d S)

def lowShiftOrder := ∏ i : SelectedSlot S, s.low (g,d,i)
def outputShiftOrder := ∏ j : ZMod (ShiftCount S), s.shiftModulus g d S j
def offsetOrder := ∏ i, s.offsetModuli g d S i

instance : NeZero (s.lowShiftOrder g d S) :=
  ⟨by
    unfold lowShiftOrder
    exact (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (s.lowShiftNeZero g d S i).out).ne'⟩
instance : NeZero (s.outputShiftOrder g d S) :=
  ⟨(Finset.prod_pos fun j _ => NeZero.pos (s.shiftModulus g d S j)).ne'⟩
instance : NeZero (s.offsetOrder g d S) :=
  ⟨(Finset.prod_pos fun i _ => (s.offsetModuli_prime g d S i).pos).ne'⟩

def lowShiftCRT : ZMod (s.lowShiftOrder g d S) ≃+* LowShifts s g d S :=
  ZMod.prodEquivPi _ fun i j h =>
    @offsetModuli_coprime k m s g d S _ (.inr (i,false)) (.inr (j,false))
      (fun h' => h (congrArg (fun x : SelectedSlot S × Bool => x.1) (Sum.inr.inj h')))
def outputShiftCRT :
    ZMod (s.outputShiftOrder g d S) ≃+* SlotShift.Shift (s.shiftModulus g d S) :=
  ZMod.prodEquivPi _ fun i j h =>
    @offsetModuli_coprime k m s g d S _ (.inl i) (.inl j) (fun h' => h (Sum.inl.inj h'))
def offsetCRT : ZMod (s.offsetOrder g d S) ≃+* (∀ i : OffsetKey S, ZMod (s.offsetModuli g d S i)) :=
  ZMod.prodEquivPi _ (s.offsetModuli_coprime g d S)

def offsetResidues (v : ShiftPair s g d S) : ∀ i : OffsetKey S, ZMod (s.offsetModuli g d S i)
  | .inl j => v.2 j - SlotShift.shift v.2 j
  | .inr (i,false) => v.1 i
  | .inr (_,true) => 0

def offsetIndex (v : ShiftPair s g d S) : ℕ :=
  ((s.lowShiftCRT g d S).symm v.1).val * s.outputShiftOrder g d S +
    ((s.outputShiftCRT g d S).symm v.2).val

private theorem offsetIndex_injective : Function.Injective (s.offsetIndex g d S) := by
  intro u v h
  unfold offsetIndex at h
  have hB := NeZero.pos (s.outputShiftOrder g d S)
  apply Prod.ext
  · apply (s.lowShiftCRT g d S).symm.injective
    apply ZMod.val_injective
    simpa only [Nat.mul_comm _ (s.outputShiftOrder g d S),Nat.mul_add_div hB,
      Nat.div_eq_of_lt (ZMod.val_lt _),Nat.add_zero] using
      congrArg (· / s.outputShiftOrder g d S) h
  · apply (s.outputShiftCRT g d S).symm.injective
    apply ZMod.val_injective
    simpa only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (ZMod.val_lt _)] using
      congrArg (· % s.outputShiftOrder g d S) h

private theorem offsetIndex_lt (v : ShiftPair s g d S) :
    s.offsetIndex g d S v < Fintype.card (ShiftPair s g d S) := by
  have h := Nat.add_lt_add_left (ZMod.val_lt ((s.outputShiftCRT g d S).symm v.2))
    (((s.lowShiftCRT g d S).symm v.1).val * s.outputShiftOrder g d S)
  rw [Fintype.card_prod, ← Fintype.card_congr (s.lowShiftCRT g d S).toEquiv,
    ← Fintype.card_congr (s.outputShiftCRT g d S).toEquiv, ZMod.card, ZMod.card]
  apply h.trans_le
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (ZMod.val_lt ((s.lowShiftCRT g d S).symm v.1))

/-- The CRT representative fixes the displacement modulo the product,
and the packed low and output indices fix its quotient. -/
def slotOffset (slope : ℤ) (v : ShiftPair s g d S) : Plane :=
  let a := separatedResidueLift (s.offsetOrder g d S)
    (fun u => (s.offsetCRT g d S).symm (s.offsetResidues g d S u)) (s.offsetIndex g d S) v
  (a,-slope*a)

theorem slotOffset_spec (slope : ℤ) :
      Function.Injective (s.slotOffset g d S slope) ∧ ∀ v,
      (s.slotOffset g d S slope v).2 = -slope * (s.slotOffset g d S slope v).1 ∧
      (∀ i : SelectedSlot S, ((s.slotOffset g d S slope v).1 : ZMod (s.low (g,d,i))) = v.1 i) ∧
      (∀ i : SelectedSlot S, ((s.slotOffset g d S slope v).1 : ZMod (s.fallback (g,i,true))) = 0) ∧
      (∀ j, ((s.slotOffset g d S slope v).1 : ZMod (s.shiftModulus g d S j)) = v.2 j-SlotShift.shift v.2 j) ∧
      0 ≤ (s.slotOffset g d S slope v).1 ∧ (s.slotOffset g d S slope v).1 <
        ((s.offsetOrder g d S) * Fintype.card (ShiftPair s g d S) : ℕ) := by
  let M := s.offsetOrder g d S
  let e := s.offsetCRT g d S
  let val (v : ShiftPair s g d S) := e.symm (s.offsetResidues g d S v)
  let index := s.offsetIndex g d S
  let a := separatedResidueLift M val index
  have hc (v : ShiftPair s g d S) (i : OffsetKey S) : ((a v : ℤ) : ZMod (s.offsetModuli g d S i)) =
      s.offsetResidues g d S v i := by
    have he : e (a v : ZMod M) = s.offsetResidues g d S v := by
      rw [separatedResidueLift_cast]
      exact e.apply_symm_apply _
    have h := congrFun he i
    rwa [map_intCast] at h
  refine ⟨fun i j h => separatedResidueLift_injective M val index
    (s.offsetIndex_injective g d S) (congrArg Prod.fst h),fun v => ⟨rfl,?_,?_,?_,?_,?_⟩⟩
  · exact fun i => hc v (.inr (i,false))
  · exact fun i => hc v (.inr (i,true))
  · exact fun j => hc v (.inl j)
  · change 0 ≤ a v
    unfold a separatedResidueLift
    positivity
  · have hb : (val v).val + M * index v < M * Fintype.card (ShiftPair s g d S) := by
      calc
        _ < M + M * index v := Nat.add_lt_add_right (ZMod.val_lt (val v)) _
        _ = M * (index v+1) := by rw [Nat.mul_succ,Nat.add_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ (s.offsetIndex_lt g d S v)
    change ((val v).val : ℤ) + (M : ℤ) * (index v : ℤ) < _
    exact_mod_cast hb

end Offsets

end SlotParameters

end

end TranslationTiling.FiniteCompiler.Packed
