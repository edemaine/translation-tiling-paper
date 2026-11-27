import TranslationTiling.FiniteCompiler.Effective.AxisSlotObservations
import Mathlib.Data.Finset.Sort

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

namespace AxisParameters

variable {k m : ℕ} (s : AxisParameters k m) (g : Bool) (d : Fin k) (S : Finset (Fin m))

abbrev SelectedSlot (S : Finset (Fin m)) := {i : Fin m // i ∈ S}

abbrev ShiftCount (S : Finset (Fin m)) := Fintype.card (SlotIndex S)

theorem shiftCount_eq : ShiftCount S = S.card * 5 := by simp [ShiftCount,SlotIndex]

private theorem zmodFinValue {n : ℕ} [NeZero n] (j : ZMod n) :
    ((ZMod.finEquiv n).symm j).val = j.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

def observationIndex : Fin 5 ≃ Bool ⊕ Fin 3 :=
  (finSumFinEquiv (m := 2) (n := 3)).symm.trans (finTwoEquiv.sumCongr (.refl _))

def shiftIndex [NeZero (ShiftCount S)] : ZMod (ShiftCount S) ≃ SlotIndex S :=
  ((ZMod.finEquiv (ShiftCount S)).symm.toEquiv.trans (finCongr (shiftCount_eq S))).trans
    (finProdFinEquiv.symm.trans ((S.orderIsoOfFin rfl).toEquiv.prodCongr observationIndex))

theorem shiftIndex_label [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    (shiftIndex S j).2 = observationIndex ⟨j.val % 5,Nat.mod_lt _ (by decide)⟩ := by
  apply congrArg (observationIndex)
  apply Fin.ext
  change ((ZMod.finEquiv (ShiftCount S)).symm j).val % 5 = _
  rw [zmodFinValue]

theorem shiftIndex_slot [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    ((shiftIndex S j).1 : Fin m) =
      S.sort[j.val/5]'(by
        rw [Finset.length_sort]
        apply Nat.div_lt_of_lt_mul
        simpa only [Nat.mul_comm 5 S.card,← shiftCount_eq S] using ZMod.val_lt j) := by
  let i := (finCongr (shiftCount_eq S)) ((ZMod.finEquiv (ShiftCount S)).symm j)
  let q : Fin S.card := (finProdFinEquiv.symm i).1
  have hq : q.val = j.val / 5 := by
    change ((ZMod.finEquiv (ShiftCount S)).symm j).val / 5 = j.val / 5
    rw [zmodFinValue]
  change (S.orderIsoOfFin rfl q).val = _
  rw [Finset.coe_orderIsoOfFin_apply,Finset.orderEmbOfFin_apply]
  let a : Fin S.sort.length := ⟨q.val,by rw [Finset.length_sort];exact q.isLt⟩
  let b : Fin S.sort.length := ⟨j.val/5,by simpa only [← hq] using a.isLt⟩
  have hab : a = b := Fin.ext hq
  exact congrArg (fun i : Fin S.sort.length => S.sort[i.val]) hab

def shiftModulus [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) : ℕ :=
  s.observationPrime g d (shiftIndex S j)

abbrev LowShifts := ∀ i : SelectedSlot S, ZMod (s.low (g,d,i))

abbrev OffsetKey (S : Finset (Fin m)) := ZMod (ShiftCount S) ⊕ (SelectedSlot S × Bool × Bool)

private def offsetTagOfIndex : SlotIndex S ⊕ (SelectedSlot S × Bool × Bool) → AxisPrime k m
  | .inl (i,.inl a) => .inr (g,i,a,false)
  | .inl (i,.inr j) => .inl ((g,d,i),.inr j)
  | .inr (i,a,false) => .inl ((g,d,i),.inl a)
  | .inr (i,a,true) => .inr (g,i,a,true)

private theorem offsetTagOfIndex_injective : Function.Injective (offsetTagOfIndex g d S) := by
  rintro (⟨i,a | b⟩ | ⟨i,a,_ | _⟩) (⟨j,c | e⟩ | ⟨j,c,_ | _⟩) h <;>
    simp only [offsetTagOfIndex,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,
      Sum.inr_ne_inl,Sum.inl_ne_inr,
      and_true,true_and,and_false] at h ⊢ <;> simp_all

def offsetTag [NeZero (ShiftCount S)] : OffsetKey S → AxisPrime k m :=
  offsetTagOfIndex g d S ∘ ((shiftIndex S).sumCongr (.refl _))

def offsetModuli [NeZero (ShiftCount S)] : OffsetKey S → ℕ
  | .inl j => s.shiftModulus g d S j
  | .inr (i,a,false) => s.lowAxis (g,d,i) a
  | .inr (i,a,true) => s.fallback (g,i,a,true)

theorem offsetModuli_eq [NeZero (ShiftCount S)] (t : OffsetKey S) :
    s.offsetModuli g d S t = s.prime (offsetTag g d S t) := by
  rcases t with j | ⟨i,a,_ | _⟩
  · rcases h : shiftIndex S j with ⟨i,a | b⟩ <;>
      simp [h,shiftModulus,offsetModuli,offsetTag,offsetTagOfIndex,observationPrime,fallback,marker]
  · rfl
  · rfl

theorem shiftModulus_prime [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    (s.shiftModulus g d S j).Prime := by
  change (s.offsetModuli g d S (.inl j)).Prime
  rw [s.offsetModuli_eq]
  exact s.prime_isPrime _

instance lowShiftNeZero (i : SelectedSlot S) : NeZero (s.low (g,d,i)) :=
  ⟨(Nat.mul_pos (s.lowAxis_prime _ false).pos (s.lowAxis_prime _ true).pos).ne'⟩

instance shiftModulusNeZero [NeZero (ShiftCount S)] (j : ZMod (ShiftCount S)) :
    NeZero (s.shiftModulus g d S j) := ⟨(shiftModulus_prime s g d S j).ne_zero⟩

theorem offsetModuli_prime [NeZero (ShiftCount S)] (i : OffsetKey S) :
    (s.offsetModuli g d S i).Prime := by rw [s.offsetModuli_eq]; exact s.prime_isPrime _

theorem offsetModuli_coprime [NeZero (ShiftCount S)] : Pairwise fun i j : OffsetKey S =>
    (s.offsetModuli g d S i).Coprime (s.offsetModuli g d S j) := by
  intro i j h
  rw [s.offsetModuli_eq,s.offsetModuli_eq]
  exact s.prime_coprime (fun he => h
    (((offsetTagOfIndex_injective g d S).comp ((shiftIndex S).sumCongr (.refl _)).injective) he))

section Offsets
variable [NeZero (ShiftCount S)]

abbrev ShiftPair := LowShifts s g d S × SlotShift.Shift (s.shiftModulus g d S)

def lowShiftOrder := ∏ i : SelectedSlot S, s.low (g,d,i)
def outputShiftOrder := ∏ j : ZMod (ShiftCount S), s.shiftModulus g d S j

instance : NeZero (s.lowShiftOrder g d S) :=
  ⟨(Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (s.lowShiftNeZero g d S i).out).ne'⟩

instance : NeZero (s.outputShiftOrder g d S) :=
  ⟨(Finset.prod_pos fun j _ => NeZero.pos (s.shiftModulus g d S j)).ne'⟩

omit [NeZero (ShiftCount S)] in
private theorem lowAxisPair_coprime {i j : SelectedSlot S} (hne : i ≠ j) :
    (s.low (g,d,i)).Coprime (s.low (g,d,j)) := by
  have h (a b : Bool) : (s.lowAxis (g,d,i) a).Coprime (s.lowAxis (g,d,j) b) := by
    apply s.prime_coprime
    intro h
    have hs := (congrArg (fun t : WangSlot k m => t.2.2) (congrArg Prod.fst (Sum.inl.inj h)))
    exact hne (Subtype.ext hs)
  unfold low
  exact (h false false).mul_right (h false true) |>.mul_left
    ((h true false).mul_right (h true true))

def lowShiftCRT : ZMod (s.lowShiftOrder g d S) ≃+* LowShifts s g d S :=
  ZMod.prodEquivPi _ fun _ _ h => s.lowAxisPair_coprime g d S h

def outputShiftCRT : ZMod (s.outputShiftOrder g d S) ≃+* SlotShift.Shift (s.shiftModulus g d S) :=
  ZMod.prodEquivPi _ fun _ _ h => s.offsetModuli_coprime g d S (fun he => h (Sum.inl.inj he))

def offsetOrder := ∏ i, s.offsetModuli g d S i

instance : NeZero (s.offsetOrder g d S) :=
  ⟨(Finset.prod_pos fun i _ => (s.offsetModuli_prime g d S i).pos).ne'⟩

def offsetCRT : ZMod (s.offsetOrder g d S) ≃+* (∀ i : OffsetKey S, ZMod (s.offsetModuli g d S i)) :=
  ZMod.prodEquivPi _ (s.offsetModuli_coprime g d S)

def offsetResidues (v : ShiftPair s g d S) : ∀ i : OffsetKey S, ZMod (s.offsetModuli g d S i)
  | .inl j => v.2 j - SlotShift.shift v.2 j
  | .inr (i,false,false) => (s.lowEquiv (g,d,i) (v.1 i)).1
  | .inr (i,true,false) => (s.lowEquiv (g,d,i) (v.1 i)).2
  | .inr (_,_,true) => 0

/-- The horizontal displacement stores the CRT residues of the low shifts
and the changes in the observed coordinates. -/
def slotOffset (slope : ℤ) (v : ShiftPair s g d S) : Plane :=
  let a : ℤ := ((s.offsetCRT g d S).symm (s.offsetResidues g d S v)).val
  (a,-slope*a)

theorem slotOffset_spec (slope : ℤ) (v : ShiftPair s g d S) :
      (s.slotOffset g d S slope v).2 = -slope * (s.slotOffset g d S slope v).1 ∧
      (∀ i : SelectedSlot S, ((s.slotOffset g d S slope v).1 : ZMod (s.low (g,d,i))) = v.1 i) ∧
      (∀ (i : SelectedSlot S) (a : Bool), ((s.slotOffset g d S slope v).1 : ZMod (s.fallback (g,i,a,true))) = 0) ∧
      (∀ j, ((s.slotOffset g d S slope v).1 : ZMod (s.shiftModulus g d S j)) = v.2 j-SlotShift.shift v.2 j) ∧
      ((s.slotOffset g d S slope v).1).natAbs < s.offsetOrder g d S := by
  let e := s.offsetCRT g d S
  let r := e.symm (s.offsetResidues g d S v)
  let a : ℤ := r.val
  have hc (i : OffsetKey S) : (a : ZMod (s.offsetModuli g d S i)) =
      s.offsetResidues g d S v i := by
    have he : e (a : ZMod (s.offsetOrder g d S)) = s.offsetResidues g d S v := by
      change e ((↑(r.val) : ℤ) : ZMod (s.offsetOrder g d S)) = _
      rw [Int.cast_natCast,ZMod.natCast_zmod_val]
      exact e.apply_symm_apply _
    have h := congrFun he i
    rwa [map_intCast] at h
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro i
    apply (s.lowEquiv (g,d,i)).injective
    rw [map_intCast]
    exact Prod.ext (hc (.inr (i,false,false))) (hc (.inr (i,true,false)))
  · intro i b
    cases b <;> exact hc (.inr (i,_,true))
  · exact fun j => hc (.inl j)
  · change (Int.ofNat r.val).natAbs < _
    exact ZMod.val_lt r

end Offsets

end AxisParameters

end

end TranslationTiling.FiniteCompiler.Packed
