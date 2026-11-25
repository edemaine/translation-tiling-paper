import TranslationTiling.FiniteCompiler.Effective.SlotMasks
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalInvariance

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000
variable {k m : ℕ} (s : SlotParameters k m)
local instance numericalBatchAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

private theorem congruence_val {p : ℕ} [NeZero p] (n : ℕ) (u : ZMod p) :
    n % p = u.val % p ↔ (n : ZMod p) = u := by
  rw [Nat.mod_eq_of_lt (ZMod.val_lt u), ← (ZMod.val_injective p).eq_iff, ZMod.val_natCast]

private theorem intResidue_val {p : ℕ} [NeZero p] (u : ℤ) :
    (u % (p : ℤ)).toNat = (u : ZMod p).val := by
  have h := ZMod.val_intCast (n := p) u
  exact (congrArg Int.toNat h).symm

private theorem congruences_append (a b : CongruenceList) (n : ℕ) :
    Congruences (a ++ b) n ↔ Congruences a n ∧ Congruences b n := by
  simp only [Congruences,List.mem_append,or_imp,forall_and]

variable (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]

private theorem projection_decode (n : ℕ) (j : ZMod (ShiftCount S)) :
    s.projection g d S (decode s.layout n) j = (n : ZMod (s.shiftModulus g d S j)) := by
  change s.observe g d (shiftIndex S j) (decode s.layout n) =
    (n : ZMod (s.observationPrime g d (shiftIndex S j)))
  generalize shiftIndex S j = i
  rcases i with ⟨i,_ | b⟩
  · exact s.observedFallback_decode (g,i,false) n
  · exact s.observedMarker_decode (g,d,i) b n

/-- The three lists of congruences specify the selected squares, remaining
low residues and observed outputs of a single activation batch. -/
theorem mem_numericalSlotBatch (h : Plane) (e : ShiftType s g d S)
    (selected remaining : List ℕ) (observed : CongruenceList)
    (hs : ∀ r, r ∈ selected ↔ ∃ i ∈ selectedRows g d S, s.layout.lowSize i = r)
    (hr : ∀ r, r ∈ remaining ↔ ∃ i ∉ selectedRows g d S, s.layout.lowSize i = r)
    (ho : ∀ c, c ∈ observed ↔ ∃ j, (s.shiftModulus g d S j,(e j).val) = c)
    (v : SharedCoordinates.Ambient s.layout) :
    let cs := (selected.map fun r => (r^2,(h.1 % (r^2 : ℕ)).toNat)) ++
      (remaining.map (·,0)) ++ observed
    v ∈ (((List.range (order s.layout)).filter fun n => decide (Congruences cs n)).map
      fun n => (h,n)).toFinset.image (decodePoint s.layout) ↔
        SlotActivationBatch s.layout (selectedRows g d S) (s.projection g d S) h e v := by
  let square := selected.map fun r => (r^2,(h.1 % (r^2 : ℕ)).toNat)
  let low := remaining.map (·,0)
  let cs := square ++ low ++ observed
  let ψ := s.projection g d S
  let rows := selectedRows g d S
  let P (f : Factor s.layout) :=
    ψ f = e ∧ (∀ i ∈ rows, (f.2 i).1.1 = (h.1 : Square s.layout i)) ∧
      (∀ i ∉ rows, CyclicShear.low (s.layout.lowSize i) (f.2 i).1.1 = 0)
  have hs' : ∀ n, Congruences square n ↔
      ∀ i ∈ rows, ((decode s.layout n).2 i).1.1 = (h.1 : Square s.layout i) := by
    intro n
    unfold square Congruences
    simp only [List.mem_map,hs,forall_exists_index]
    constructor
    · intro hnum i hi
      have : NeZero ((s.layout.lowSize i)^2) := ⟨pow_ne_zero _ (s.layout.lowSize_pos i).ne'⟩
      exact (congruence_val n _).mp (by
        rw [← intResidue_val]
        exact hnum _ _ ⟨⟨i,hi,rfl⟩,rfl⟩)
    · rintro hnum _ _ ⟨⟨i,hi,rfl⟩,rfl⟩
      have : NeZero ((s.layout.lowSize i)^2) := ⟨pow_ne_zero _ (s.layout.lowSize_pos i).ne'⟩
      rw [intResidue_val]
      exact (congruence_val n _).mpr (hnum i hi)
  have hr' : ∀ n, Congruences low n ↔
      ∀ i ∉ rows, CyclicShear.low (s.layout.lowSize i) ((decode s.layout n).2 i).1.1 = 0 := by
    intro n
    unfold low Congruences
    simp only [List.mem_map,hr,forall_exists_index,
      decode,CyclicShear.low_natCast,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
    constructor
    · intro hnum i hi
      simpa only [Nat.zero_mod] using hnum _ _ ⟨⟨i,hi,rfl⟩,rfl⟩
    · rintro hnum _ _ ⟨⟨i,hi,rfl⟩,rfl⟩
      simpa only [Nat.zero_mod] using hnum i hi
  have ho' : ∀ n, Congruences observed n ↔ ψ (decode s.layout n) = e := by
    intro n
    simp only [Congruences,ho,forall_exists_index,forall_apply_eq_imp_iff]
    rw [funext_iff]
    exact forall_congr' fun j => (congruence_val n (e j)).trans (by rw [s.projection_decode])
  have hP (n : ℕ) : decide (Congruences cs n) = true ↔ P (decode s.layout n) := by
    unfold P cs
    rw [decide_eq_true_eq,congruences_append,congruences_append,hs',hr',ho']
    tauto
  exact decoded_range_filter_iff s.layout s.crt h (fun n => decide (Congruences cs n)) P hP v

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
