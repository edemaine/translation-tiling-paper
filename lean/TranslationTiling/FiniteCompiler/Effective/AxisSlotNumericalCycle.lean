import TranslationTiling.FiniteCompiler.Effective.AxisSlotCycle
import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalInvariance
import TranslationTiling.FiniteCompiler.Effective.FixedPrimitives

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective FiniteCompiler.Effective
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000
variable {k m : ℕ} (s : AxisParameters k m)
local instance numericalCycleAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

/-- The two moduli read by a cycle. In a slot only the selected marker
is read, so its other modulus is one. -/
def cycleReadModuli (i : AxisRow k m) (a : RowLabel i) : ℕ × ℕ :=
  match i with
  | .inl j => ((fourValueLayout 0).firstSize j,(fourValueLayout 0).secondSize j)
  | .inr (.inl j) => (1,s.marker j a.2)
  | .inr (.inr _) => (1,1)

private theorem cycleReadModuli_pos (i : AxisRow k m) (a : RowLabel i) :
    0 < (s.cycleReadModuli i a).1 ∧ 0 < (s.cycleReadModuli i a).2 := by
  rcases i with i | i | i
  · exact (fourValueModuli_positive i).2
  · exact ⟨Nat.one_pos,(s.prime_isPrime (.inl (i,.inr a.2))).pos⟩
  · exact ⟨Nat.one_pos,Nat.one_pos⟩

private theorem cycleRead_zero (a : ∀ i : AxisRow k m, RowLabel i) (n : ℕ) (i : AxisRow k m) :
    s.cycleRead a (decode s.layout n) i = 0 ↔
      n % (s.cycleReadModuli i (a i)).1 = 0 ∧ n % (s.cycleReadModuli i (a i)).2 = 0 := by
  change s.readForRow i (a i) (decode s.layout n) = 0 ↔ _
  rcases i with i | i | i
  · let A := (fourValueLayout 0).firstSize i
    let B := (fourValueLayout 0).secondSize i
    change ((n : ZMod A),(n : ZMod B)) = (0,0) ↔ n % A = 0 ∧ n % B = 0
    simp only [Prod.mk.injEq,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  · let j := a (.inr (.inl i))
    let B := s.marker i j.2
    change s.observeMarker i j.2 (decode s.layout n) = (0 : ZMod B) ↔ n % 1 = 0 ∧ n % B = 0
    rw [s.observedMarker_decode]
    simp only [ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero,Nat.mod_one,true_and,B]
  · change (0 : ZMod 1) = 0 ↔ n % 1 = 0 ∧ n % 1 = 0
    simp [Nat.mod_one]

/-- Natural representative of the low step used by the cycle. -/
def cycleStepCode (s : AxisParameters k m) (i : AxisRow k m) (a : RowLabel i) : ℕ :=
  match i with
  | .inl j => fourValueStep j a
  | .inr (.inl j) => (AxisSlot.axisGenerator (s.lowAxis_coprime j) a.1).val.val
  | .inr (.inr _) => 0

private theorem cycleStepCode_cast (i : AxisRow k m) (a : RowLabel i) :
    (s.cycleStepCode i a : SharedCoordinates.Low s.layout i) = s.labelStep i a := by
  rcases i with i | i | i
  · rfl
  · exact ZMod.natCast_zmod_val ((AxisSlot.axisGenerator (s.lowAxis_coprime i) a.1).val)
  · rfl

def slotCycleRow (a : ∀ i : AxisRow k m, RowLabel i)
    (pred : AxisRow k m → Option (AxisRow k m)) (i : AxisRow k m) : CycleRow :=
  match pred i with
  | none => (s.layout.lowSize i,1,1,[0])
  | some j =>
    let mods := s.cycleReadModuli j (a j)
    (s.layout.lowSize i,mods.1,mods.2,triggerTable mods.1 mods.2 (s.cycleStepCode i (a i)))

/-- Reading the numerical cycle rows recovers the ordinary vertical mask. -/
theorem numericalCycle_correct {t : ℕ} [NeZero t] (cyc : ZMod t ↪ AxisRow k m)
    (a : ∀ i : AxisRow k m, RowLabel i)
    (pred : AxisRow k m → Option (AxisRow k m))
    (hon : ∀ j, pred (cyc j) = some (cyc (j-1)))
    (hoff : ∀ i, (∀ j, cyc j ≠ i) → pred i = none)
    (rows : List CycleRow) (hrows : ∀ r, r ∈ rows ↔ ∃ i, s.slotCycleRow a pred i = r) :
    (cycleCodes (order s.layout) rows).toFinset.image (decodePoint s.layout) = s.rowCycleMask cyc a := by
  let U (j : ZMod t) := s.labelSubgroup (cyc j) (a (cyc j))
  let step (j : ZMod t) := s.labelStep (cyc j) (a (cyc j))
  let offset := fun f => gateOffset s.layout cyc U step (s.cycleRead a f)
  have htest (n : ℕ) (i : AxisRow k m) : CycleRowTest (s.slotCycleRow a pred i) n ↔
      (n : SharedCoordinates.Low s.layout i) = offset (decode s.layout n) i := by
    by_cases hi : ∃ j, cyc j = i
    · obtain ⟨j,rfl⟩ := hi
      let p := cyc (j-1)
      let mods := s.cycleReadModuli p (a p)
      have hpos := s.cycleReadModuli_pos p (a p)
      have : NeZero mods.1 := ⟨hpos.1.ne'⟩
      have : NeZero mods.2 := ⟨hpos.2.ne'⟩
      have he := triggerTable_apply (s.cycleStepCode (cyc j) (a (cyc j)))
        ((n : ZMod mods.1),(n : ZMod mods.2))
      simp only [ZMod.val_natCast] at he
      have hz : ((n : ZMod mods.1),(n : ZMod mods.2)) = 0 ↔
          s.cycleRead a (decode s.layout n) p = 0 := by
        rw [show (0 : ZMod mods.1 × ZMod mods.2) = (0,0) from rfl,Prod.mk.injEq]
        simp only [ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero,s.cycleRead_zero,mods]
      rw [slotCycleRow,hon]
      unfold offset gateOffset
      rw [cycleShift_apply]
      change n % s.layout.lowSize (cyc j) =
          ((triggerTable mods.1 mods.2 (s.cycleStepCode (cyc j) (a (cyc j)))).getD
            (rectangularIndex mods.2 (n % mods.1) (n % mods.2)) 0) % s.layout.lowSize (cyc j) ↔ _
      rw [he]
      by_cases hzero : s.cycleRead a (decode s.layout n) p = 0
      · simp [cycleGeneratorMaps,p,hzero,hz.mpr hzero,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
      · simp only [ite_eq_right (mt hz.mp hzero),cycleGeneratorMaps,ite_eq_right hzero,step,p]
        rw [← s.cycleStepCode_cast]
        let r := s.layout.lowSize (cyc j)
        let sc := s.cycleStepCode (cyc j) (a (cyc j))
        change n % r = sc % r ↔ (n : ZMod r) = (sc : ZMod r)
        constructor
        · intro h
          apply ZMod.val_injective r
          simpa only [ZMod.val_natCast] using h
        · intro h
          have hv := congrArg (fun z : ZMod r => z.val) h
          simpa only [ZMod.val_natCast] using hv
    · have hout : ∀ j, cyc j ≠ i := not_exists.mp hi
      rw [slotCycleRow,hoff i hout,cycleRowTest_zero]
      unfold offset gateOffset
      rw [cycleShift_eq_zero _ _ _ _ hout]
      simp [ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  ext v
  have hdecode (n : ℕ) : decide (CycleTest rows n) = true ↔
      ∀ i, CyclicShear.low (s.layout.lowSize i) ((decode s.layout n).2 i).1.1 =
        offset (decode s.layout n) i := by
    simp only [decide_eq_true_eq,CycleTest,hrows,forall_exists_index,forall_apply_eq_imp_iff,
      decode,CyclicShear.low_natCast]
    exact forall_congr' (htest n)
  have he := decoded_range_filter_iff s.layout s.crt 0 (fun n => decide (CycleTest rows n))
    (fun f => ∀ i, CyclicShear.low (s.layout.lowSize i) (f.2 i).1.1 = offset f i) hdecode v
  apply he.trans
  change _ ↔ v ∈ productCycle s.layout cyc U step (s.cycleRead a)
  rw [mem_productCycle]
  constructor
  · rintro ⟨hv,hh⟩
    exact Prod.ext hv (funext hh)
  · intro h
    exact ⟨congrArg Prod.fst h,fun i => congrFun (congrArg Prod.snd h) i⟩

end

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
