import TranslationTiling.FiniteCompiler.Effective.SlotNumericalDeck
import TranslationTiling.Compiler.SlotLogBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective Compiler.Effective
open Compiler.StripLift

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2500000

private def assemblyPrimeCap (m Q : ℕ) : ℕ :=
  slotStackPrimeCap (if m = 0 then 0 else Q)

/-- The same numerical compiler is used at every positive input length. -/
def compileSlotWith (T : LeanWang.TileSet) (k m w : ℕ) : Tile 3 :=
  let nr := rankedSlotOrders k m
  let Q := slotPrimeCap k m
  let P := assemblyPrimeCap m Q
  let L := numericalKernel nr.1 nr.2 :: numericalSlotTests T nr.1 k m w
  guardedAssembly (((nr.1,P,stackTestCap P L.length),nr.2,slotRadius Q m),L)

private def slotDimensions (n : ℕ) : ℕ × ℕ × ℕ :=
  if n ≤ 1 then (0,0,0) else
    let t := slotLengthParameter n
    (slotPackedDigits n t,4*t,3*t)

def compileSlot (T : LeanWang.TileSet) : Tile 3 :=
  let p := slotDimensions T.length
  compileSlotWith T p.1 p.2.1 p.2.2

private theorem slotPrimeCap_primrec : Primrec (fun z : ℕ × ℕ => slotPrimeCap z.1 z.2) := by
  have h : Primrec (fun _ : ℕ × ℕ => order (fourValueLayout 0)) := Primrec.const _
  have hA : Primrec (fun z : ℕ × ℕ => fallbackCap z.2) := by unfold fallbackCap; fun_prop
  have hB : Primrec (fun z : ℕ × ℕ => markerCap z.1 z.2) := by unfold markerCap; fun_prop
  have hR : Primrec (fun z : ℕ × ℕ => SlotParameters.lowCap z.1 z.2) := by unfold SlotParameters.lowCap; fun_prop
  unfold slotPrimeCap
  exact Primrec.nat_max.comp hA (Primrec.nat_max.comp hB hR)

private theorem slotStackPrimeCap_primrec : Primrec slotStackPrimeCap := by
  unfold slotStackPrimeCap
  have h : Primrec (fun _ : ℕ => slotBasePrimeCap) := Primrec.const _
  fun_prop

private abbrev SlotInput := LeanWang.TileSet × ℕ × ℕ × ℕ

theorem compileSlotWith_computable :
    Computable (fun z : SlotInput => compileSlotWith z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let coords (z : SlotInput) := (z.2.1,z.2.2.1)
  have hc : Primrec coords := by unfold coords; fun_prop
  let nr (z : SlotInput) := rankedSlotOrders (coords z).1 (coords z).2
  have hn : Primrec nr := rankedSlotOrders_primrec.comp hc
  let Q (z : SlotInput) := slotPrimeCap (coords z).1 (coords z).2
  have hQ : Primrec Q := slotPrimeCap_primrec.comp hc
  let P (z : SlotInput) := assemblyPrimeCap z.2.2.1 (Q z)
  have hP : Primrec P := by
    unfold P assemblyPrimeCap
    exact slotStackPrimeCap_primrec.comp (Primrec.ite (by fun_prop) (Primrec.const 0) hQ)
  let L (z : SlotInput) :=
    numericalKernel (nr z).1 (nr z).2 :: numericalSlotTests z.1 (nr z).1 z.2.1 z.2.2.1 z.2.2.2
  let args (z : SlotInput) : LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ :=
    (z.1,(nr z).1,z.2.1,z.2.2.1,z.2.2.2)
  have hargs : Primrec args := by unfold args; fun_prop
  have hker := numericalKernel_primrec.comp hn
  have htests := numericalSlotTests_primrec.comp hargs
  have hL : Primrec L :=
    (Primrec.list_cons.comp hker htests).of_eq (by intro z; rfl)
  let X (z : SlotInput) := stackTestCap (P z) (L z).length
  let H (z : SlotInput) := slotRadius (Q z) z.2.2.1
  have hX : Primrec X := by unfold X stackTestCap; fun_prop
  have hH : Primrec H := by
    unfold H slotRadius
    have h : Primrec (fun _ : SlotInput => fourValueRadius 0) := Primrec.const _
    fun_prop
  let data (z : SlotInput) : GuardedAssemblyData := ((((nr z).1,P z,X z),(nr z).2,H z),L z)
  have hdata : Primrec data :=
    (((Primrec.fst.comp hn).pair (hP.pair hX)).pair ((Primrec.snd.comp hn).pair hH)).pair hL
  exact (guardedAssembly_computable.comp hdata.to_comp).of_eq (by intro z; rfl)

theorem compileSlot_computable : Computable compileSlot := by
  let t (T : LeanWang.TileSet) := slotLengthParameter T.length
  have ht : Primrec t := slotLengthParameter_primrec.comp Primrec.list_length
  have hk := slotPackedDigits_primrec.comp (Primrec.list_length.pair ht)
  have hm := Primrec.nat_mul.comp (Primrec.const 4) ht
  have hw := Primrec.nat_mul.comp (Primrec.const 3) ht
  have hdim : Primrec (fun T : LeanWang.TileSet => slotDimensions T.length) :=
    Primrec.ite (by fun_prop) (Primrec.const _) (hk.pair (hm.pair hw))
  exact (compileSlotWith_computable.comp (Primrec.id.pair hdim).to_comp).of_eq
    (by intro T; rfl)

set_option maxHeartbeats 8000000 in
theorem compileSlotWith_correct (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hk : 0 < k) (hw : 0 < w) (hwm : w ≤ m)
    (hcap : T.length ≤ (slotRadix m w)^k) :
    let U := compileSlotWith T k m w
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ slotSizeBound k m w := by
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  have hm : m ≠ 0 := by omega
  obtain ⟨s,hs,hA,hB,hR⟩ := exists_ranked_parameters k m
  have hBQ : markerCap k m ≤ Q := (le_max_left ..).trans (le_max_right ..)
  have hRQ : SlotParameters.lowCap k m ≤ Q := (le_max_right ..).trans (le_max_right ..)
  have hQ : ∀ i, s.prime i ≤ Q := by
    rintro (⟨i,_ | j⟩ | i)
    · exact (hR i).trans hRQ
    · exact (hB i j).trans hBQ
    · exact (hA i).trans (le_max_left ..)
  have hQP : Q ≤ P := (le_max_right ..).trans (le_max_right ..)
  have h₀ : slotBasePrimeCap ≤ P := (le_max_left ..).trans (le_max_right ..)
  have hPr := s.primeBound h₀ (fun i => (hQ i).trans hQP)
  have hP : 3 < P := (show 3 < 4 by decide).trans_le (le_max_left ..)
  let N := order s.layout
  let L := numericalKernel N s.period :: numericalSlotTests T N k m w
  let X := stackTestCap P L.length
  let U := guardedAssembly (((N,P,X),s.period,slotRadius Q m),L)
  have hu : compileSlotWith T k m w = U := by
    unfold compileSlotWith
    rw [rankedSlotOrders_eq s hs]
    simp only [assemblyPrimeCap, if_neg hm, U, Q, P, N, L, X]
  dsimp only
  rw [hu]
  obtain ⟨hU,hcon,he,hvol⟩ := s.numericalSlotPolycube hn hcap hs hwm hPr hP hQ
  refine ⟨hU,hcon,he,?_⟩
  let X' := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  let H := slotRadius Q m
  have hX : X ≤ X' := by
    unfold X X' stackTestCap
    apply max_le_max_left
    apply max_le_max_left
    exact numericalSlotTests_length T N k m w
  have hXp : 1 ≤ X := le_trans (by decide : 1 ≤ 2313) (le_max_left ..)
  have hPX : P ≤ X := (le_max_left ..).trans (le_max_right ..)
  have hvolume := slotVolume_le H s.period (N/s.period) N (reservedCap X P) s.period_pos
    (Nat.div_mul_le_self _ _)
  have hO := s.order_le hA (fun i => (hR i).trans hRQ) (fun i j => (hB i j).trans hBQ)
  have hx := (slotStack_le X P hXp hPX).trans
    (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hX 3))
  calc
    _ ≤ _ := hvol.trans hvolume
    _ ≤ 10^32 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        (128*X'^3) * (H+1)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hO) hx)
    _ ≤ _ := by
      change _ ≤ 10^35 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        X'^3 * (H+1)^2
      rw [show 10^32 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        (128*X'^3) * (H+1)^2 =
        (128*10^32) * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
          X'^3 * (H+1)^2 by ring]
      gcongr
      decide

private theorem emptyWord_volume :
    let nr := rankedSlotOrders 0 0
    let P := slotBasePrimeCap
    let X := stackTestCap P (slotDeckCap 0 0 1)
    reservedVolumeCap 35 (fun _ => slotRadius (slotPrimeCap 0 0) 0) nr.2 (nr.1 / nr.2)
      (reservedCap X P) ≤ 2^2067 := by
  decide +kernel

private theorem compileSlotWith_volume (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hwm : w ≤ m) (hcap : T.length ≤ (slotRadix m w)^k) :
    let nr := rankedSlotOrders k m
    let Q := slotPrimeCap k m
    let P := assemblyPrimeCap m Q
    let X := stackTestCap P (numericalSlotTests T nr.1 k m w).length.succ
    let U := compileSlotWith T k m w
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => slotRadius Q m) nr.2 (nr.1 / nr.2)
        (reservedCap X P) := by
  obtain ⟨s,hs,hA,hB,hR⟩ := exists_ranked_parameters k m
  let Q := slotPrimeCap k m
  let P := assemblyPrimeCap m Q
  have hQ (i : SlotPrime k m) : s.prime i ≤ Q := by
    rcases i with ⟨i,_ | j⟩ | j
    · exact (hR i).trans ((le_max_right ..).trans (le_max_right ..))
    · exact (hB i j).trans ((le_max_left ..).trans (le_max_right ..))
    · exact (hA j).trans (le_max_left ..)
  have hPrime (i : SlotPrime k m) : s.prime i ≤ P := by
    by_cases hm : m = 0
    · subst m
      rcases i with ⟨⟨_,_,j⟩,_⟩ | ⟨_,j,_⟩
      · exact j.elim0
      · exact j.elim0
    · exact (hQ i).trans (by
        simp only [P,assemblyPrimeCap,ite_eq_right hm]
        exact (le_max_right ..).trans (le_max_right ..))
  have hb : slotBasePrimeCap ≤ P := (le_max_left ..).trans (le_max_right ..)
  have hP : 3 < P := (show 3 < 4 by decide).trans_le (le_max_left ..)
  dsimp only
  unfold compileSlotWith
  rw [rankedSlotOrders_eq s hs]
  exact s.numericalSlotPolycube hn hcap hs hwm (s.primeBound hb hPrime) hP hQ

/-- A singleton alphabet uses the empty word. The Sudoku masks, arithmetic
guards, and final geometric assembly are still those of the slot compiler. -/
theorem compileSlotWith_emptyWord (T : LeanWang.TileSet) (hn : T.length = 1) :
    let U := compileSlotWith T 0 0 0
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ 2^2067 := by
  obtain ⟨hne,hcon,hiff,hvol⟩ := compileSlotWith_volume T (k := 0) (m := 0) (w := 0)
    (by omega) (by decide) (by simp [hn])
  refine ⟨hne,hcon,hiff,hvol.trans ?_⟩
  let nr := rankedSlotOrders 0 0
  let P := slotBasePrimeCap
  let Q := slotPrimeCap 0 0
  let X := stackTestCap P (numericalSlotTests T nr.1 0 0 0).length.succ
  let X' := stackTestCap P (slotDeckCap 0 0 1)
  have hX : X ≤ X' := max_le_max_left _ (max_le_max_left _ (by
    simpa only [pow_zero] using numericalSlotTests_length T nr.1 0 0 0))
  have hlog : Stacking.differenceLog X ≤ Stacking.differenceLog X' :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left _ hX)) _
  have hL : reservedCap X P ≤ reservedCap X' P := by
    unfold reservedCap reservedThreshold
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 2)) hlog
  have hV : reservedVolumeCap 35 (fun _ => slotRadius Q 0) nr.2 (nr.1/nr.2) (reservedCap X P) ≤
      reservedVolumeCap 35 (fun _ => slotRadius Q 0) nr.2 (nr.1/nr.2) (reservedCap X' P) := by
    unfold reservedVolumeCap
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL))
  exact hV.trans emptyWord_volume

theorem compileSlot_correct (T : LeanWang.TileSet) (hn : 0 < T.length) :
    let t := slotLengthParameter T.length
    let k := slotPackedDigits T.length t
    let U := compileSlot T
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ slotSizeBound k (4*t) (3*t) := by
  dsimp only
  by_cases h : T.length ≤ 1
  · have he : T.length = 1 := by omega
    have hc : compileSlot T = compileSlotWith T 0 0 0 := by
      simp [compileSlot,slotDimensions,h]
    rw [hc]
    obtain ⟨hne,hconn,hiff,hsize⟩ := compileSlotWith_emptyWord T he
    refine ⟨hne,hconn,hiff,hsize.trans ?_⟩
    rw [he]
    decide +kernel
  unfold compileSlot
  simp only [slotDimensions,if_neg h]
  have ht : 0 < slotLengthParameter T.length := (by decide : 0 < 1).trans_le (le_max_left ..)
  apply compileSlotWith_correct T hn
  · exact (by decide : 0 < 1).trans_le (le_max_left ..)
  · omega
  · omega
  · exact slotPackedDigits_capacity _ _ ht

/-- The one-tile size estimate for the same compiler. -/
theorem compileSlot_one (T : LeanWang.TileSet) (hn : T.length = 1) :
    (compileSlot T).length ≤ 2^2067 := by
  simpa [compileSlot,slotDimensions,hn] using (compileSlotWith_emptyWord T hn).2.2.2

/-- Asymptotic size of the computable slot compiler. -/
theorem compileSlot_logarithmic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : LeanWang.TileSet, 4 ≤ T.length →
      16 ≤ Real.logb 2 (Real.logb 2 (T.length : ℝ)) →
      let n := (T.length : ℝ)
      let g := Real.logb 2 (Real.logb 2 n)
      let U := compileSlot T
      U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
        (U.length : ℝ) ≤ n^(5*g+C*(1+Real.logb 2 g)) := by
  obtain ⟨C,hC,h⟩ := slot_size_log_bound
  refine ⟨C,hC,?_⟩
  intro T hn hg
  let n := T.length
  let t := slotLengthParameter n
  let k := slotPackedDigits n t
  let U := compileSlot T
  obtain ⟨hne,hconn,hiff,hU⟩ := compileSlot_correct T (by omega)
  refine ⟨hne,hconn,hiff,?_⟩
  have hsize : 0 < (slotSizeBound k (4*t) (3*t) : ℝ) := by
    have hp : 0 < U.length := List.length_pos_iff.mpr hne
    exact Nat.cast_pos.mpr (hp.trans_le hU)
  have hnpos : 0 < (n : ℝ) := by
    change 0 < (T.length : ℝ)
    exact Nat.cast_pos.mpr (show 0 < T.length by omega)
  let u := Real.logb 2 (n : ℝ)
  let g := Real.logb 2 u
  let p := 5*g+C*(1+Real.logb 2 g)
  change 4 ≤ n at hn
  change 16 ≤ g at hg
  have hh : Real.logb 2 (slotSizeBound k (4*t) (3*t) : ℝ) ≤ u*p := h n hn hg
  have hpow : Real.logb 2 ((n : ℝ)^p) = u*p :=
    (Real.logb_rpow_eq_mul_logb_of_pos hnpos).trans (mul_comm p u)
  have hb : (slotSizeBound k (4*t) (3*t) : ℝ) ≤ (n : ℝ)^p :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) hsize
      (Real.rpow_pos_of_pos hnpos p)).mp (hpow.symm ▸ hh)
  exact (Nat.cast_le.mpr hU).trans hb

end
end TranslationTiling.Compiler.Size
