import TranslationTiling.FiniteCompiler.FourValueShift

namespace TranslationTiling.FiniteCompiler.SlotShift

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]

abbrev Bits (d : ℕ) := ZMod d → Bool
abbrev Shift (m : ZMod d → ℕ) := ∀ j, ZMod (m j)

def bitPoint {m : ZMod d → ℕ} (z : Bits d) : Shift m :=
  fun j => if z j then 1 else 0

def changeBits (z : Bits d) : Bits d :=
  fun j => xor (z j) (z (j+1))

def restoreBits (S : Set (ZMod d)) (z : Bits d) : Bits d :=
  fun j => if j ∈ S then z j else changeBits z j

/-- Restoring any nonempty collection of coordinates breaks the cycle. -/
theorem restoreBits_bijective {S : Set (ZMod d)} (hS : S.Nonempty) :
    Function.Bijective (restoreBits S) := by
  apply Finite.injective_iff_bijective.mp
  intro x y he
  obtain ⟨i, hi⟩ := hS
  have hsame (j : ZMod d) (hj : j ∈ S) : x j = y j := by
    simpa only [restoreBits, ite_eq_left hj] using congrFun he j
  have hstep (j : ZMod d) (hj : x (j+1) = y (j+1)) : x j = y j := by
    by_cases h : j ∈ S
    · exact hsame j h
    · have hc : xor (x j) (y (j+1)) = xor (y j) (y (j+1)) := by
        simpa only [restoreBits, ite_eq_right h, changeBits, hj] using congrFun he j
      cases hx : x j <;> cases hy : y j <;> cases hz : y (j+1) <;> simp_all
  have hiter (n : ℕ) : x (i - (n : ZMod d)) = y (i - (n : ZMod d)) := by
    induction n with
    | zero => simpa using hsame i hi
    | succ n ih =>
        apply hstep
        simpa only [Nat.cast_succ, ← sub_sub, sub_add_cancel] using ih
  funext j
  simpa only [ZMod.natCast_zmod_val, sub_sub_cancel] using hiter (i-j).val

variable {m : ZMod d → ℕ}

omit [NeZero d] in
theorem bitPoint_injective (hm : ∀ j, 1 < m j) : Function.Injective (bitPoint (m := m)) := by
  intro x y h
  funext j
  have : Fact (1 < m j) := ⟨hm j⟩
  have hj := congrFun h j
  cases hx : x j <;> cases hy : y j <;> simp_all [bitPoint]

def shift (z : Shift m) : Shift m :=
  if h : ∃ w : Bits d, bitPoint w = z then bitPoint (changeBits h.choose) else z

theorem shift_bitPoint (hm : ∀ j, 1 < m j) (z : Bits d) :
    shift (bitPoint (m := m) z) = bitPoint (changeBits z) := by
  have h : ∃ w : Bits d, bitPoint (m := m) w = bitPoint z := ⟨z,rfl⟩
  rw [shift,dite_eq_left h,(bitPoint_injective hm) h.choose_spec]

def restore (S : Set (ZMod d)) (z : Shift m) : Shift m :=
  fun j => if j ∈ S then z j else shift z j

theorem restore_bitPoint (hm : ∀ j, 1 < m j) (S : Set (ZMod d)) (z : Bits d) :
    restore S (bitPoint (m := m) z) = bitPoint (restoreBits S z) := by
  funext j
  by_cases hj : j ∈ S <;> simp [restore, restoreBits, hj, shift_bitPoint hm, bitPoint]

theorem restore_of_not_binary (S : Set (ZMod d)) {z : Shift m}
    (hz : ¬ ∃ w : Bits d, bitPoint w = z) : restore S z = z := by
  funext j
  simp [restore,shift,hz]

theorem restore_bijective (hm : ∀ j, 1 < m j) {S : Set (ZMod d)} (hS : S.Nonempty) :
    Function.Bijective (restore (m := m) S) := by
  have hb := restoreBits_bijective hS
  have hi := bitPoint_injective hm
  constructor
  · intro a b he
    by_cases ha : ∃ w : Bits d, bitPoint w = a
    · obtain ⟨u,rfl⟩ := ha
      rw [restore_bitPoint hm] at he
      by_cases hb' : ∃ w : Bits d, bitPoint w = b
      · obtain ⟨v,rfl⟩ := hb'
        rw [restore_bitPoint hm] at he
        exact congrArg bitPoint (hb.1 (hi he))
      · rw [restore_of_not_binary S hb'] at he
        exact (hb' ⟨_,he⟩).elim
    · rw [restore_of_not_binary S ha] at he
      by_cases hb' : ∃ w : Bits d, bitPoint w = b
      · obtain ⟨v,rfl⟩ := hb'
        rw [restore_bitPoint hm] at he
        exact (ha ⟨_,he.symm⟩).elim
      · rwa [restore_of_not_binary S hb'] at he
  · intro z
    by_cases hz : ∃ w : Bits d, bitPoint w = z
    · obtain ⟨w,rfl⟩ := hz
      obtain ⟨v,hv⟩ := hb.2 w
      exact ⟨bitPoint v,by rw [restore_bitPoint hm,hv]⟩
    · exact ⟨z,restore_of_not_binary S hz⟩

end

end TranslationTiling.FiniteCompiler.SlotShift
