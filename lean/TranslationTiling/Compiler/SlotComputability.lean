import TranslationTiling.FiniteCompiler.Effective.SlotNumericalDeck
import TranslationTiling.Compiler.SlotLogBound
import TranslationTiling.FiniteCompiler.Effective.SlotSmallPrimeCertificates

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective Compiler.Effective
open Compiler.StripLift
open scoped BigOperators

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 2500000
attribute [local irreducible] slotSearchCap slotPrimeAt

def assemblyPrimeCap (m Q : ℕ) : ℕ :=
  slotStackPrimeCap (if m = 0 then 0 else Q)

/-- The same numerical compiler is used at every positive input length. -/
def compileSlotWith (T : LeanWang.TileSet) (k m w : ℕ) : Tile 3 :=
  let nr := rankedSlotOrders k m
  let Q := slotPrimeCap k m
  let P := assemblyPrimeCap m Q
  let L := numericalKernel nr.1 nr.2 :: numericalSlotTests T nr.1 k m w
  guardedAssemblyBySlope (((nr.1,P,slotStackTestCap P L.length),nr.2,slotAssemblyRadii k m w),L)

/-- Wider constant-weight digits absorb the rounding loss in the exponent. -/
def wideSlotLength (n : ℕ) : ℕ :=
  let b := Nat.log 2 (Nat.log 2 n)
  max 1 (b * Nat.log 2 b / 4)

private theorem wideSlotLength_primrec : Primrec wideSlotLength := by
  unfold wideSlotLength
  have h := natLog_primrec 2 (by decide)
  fun_prop

private def slotDimensions (n : ℕ) : ℕ × ℕ × ℕ :=
  if n ≤ 1 then (0,0,0) else if n ≤ 9 then (if n ≤ 3 then 1 else 2,1,1) else
    let t := wideSlotLength n
    (slotPackedDigits n t,4*t,3*t)

def compileSlot (T : LeanWang.TileSet) : Tile 3 :=
  let p := slotDimensions T.length
  compileSlotWith T p.1 p.2.1 p.2.2

private theorem slotPrimeCap_primrec : Primrec (fun z : ℕ × ℕ => slotPrimeCap z.1 z.2) := by
  have h : Primrec (fun _ : ℕ × ℕ => order (fourValueLayout 0)) := Primrec.const _
  have hA : Primrec (fun z : ℕ × ℕ => fallbackCap z.2) := by unfold fallbackCap; fun_prop
  have hB := markerCap_primrec
  have hR := lowCap_primrec
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
  let X (z : SlotInput) := slotStackTestCap (P z) (L z).length
  let H (z : SlotInput) := slotAssemblyRadii z.2.1 z.2.2.1 z.2.2.2
  have hX : Primrec X := by
    have hs : Primrec (fun z => (P z).sqrt) := Primrec.nat_sqrt.comp hP
    unfold X slotStackTestCap
    fun_prop
  have hH : Primrec H := by
    have hA : Primrec (fun z : SlotInput => fallbackCap z.2.2.1) := by unfold fallbackCap; fun_prop
    have hB : Primrec (fun z : SlotInput => markerCap z.2.1 z.2.2.1) :=
      markerCap_primrec.comp hc
    have hC : Primrec (fun z : SlotInput => SlotParameters.lowCap z.2.1 z.2.2.1) :=
      lowCap_primrec.comp hc
    let D (z : SlotInput) := slotOffsetFactorCap z.2.1 z.2.2.1
    have hD : Primrec D := by
      unfold D slotOffsetFactorCap
      fun_prop
    let A (z : SlotInput) := D z ^ (min z.2.2.1 (z.2.2.1+1-z.2.2.2))
    have h : Primrec A := by
      unfold A
      simp only [show ∀ a b : ℕ, min a b = a-(a-b) by intro a b; omega]
      fun_prop
    have hm : Primrec (fun z : SlotInput × ℕ => max z.2 (A z.1)) :=
      Primrec.nat_max.comp Primrec.snd (h.comp Primrec.fst)
    exact Primrec.list_map (Primrec.const arithmeticStripRadii) hm
  let data (z : SlotInput) : GuardedAssemblyBySlopeData := ((((nr z).1,P z,X z),(nr z).2,H z),L z)
  have hdata : Primrec data :=
    (((Primrec.fst.comp hn).pair (hP.pair hX)).pair ((Primrec.snd.comp hn).pair hH)).pair hL
  exact (guardedAssemblyBySlope_computable.comp hdata.to_comp).of_eq (by intro z; rfl)

theorem compileSlot_computable : Computable compileSlot := by
  let t (T : LeanWang.TileSet) := wideSlotLength T.length
  have ht : Primrec t := wideSlotLength_primrec.comp Primrec.list_length
  have hk := slotPackedDigits_primrec.comp (Primrec.list_length.pair ht)
  have hm := Primrec.nat_mul.comp (Primrec.const 4) ht
  have hw := Primrec.nat_mul.comp (Primrec.const 3) ht
  have hsmall : Primrec (fun T : LeanWang.TileSet => (if T.length ≤ 3 then 1 else 2,1,1)) := by
    fun_prop
  have hdim : Primrec (fun T : LeanWang.TileSet => slotDimensions T.length) :=
    Primrec.ite (by fun_prop) (Primrec.const _)
      (Primrec.ite (by fun_prop) hsmall (hk.pair (hm.pair hw)))
  exact (compileSlotWith_computable.comp (Primrec.id.pair hdim).to_comp).of_eq
    (by intro T; rfl)

private theorem arithmeticBaseline_length_exact : arithmeticBaseline.length = 424 := by
  decide +kernel

private theorem singletonStackPrime : Nat.Prime 2380737823 := by
  rw [Nat.prime_def_minFac]
  decide +kernel

private theorem oneSlotStackPrime : Nat.Prime 4045604611 := by
  rw [Nat.prime_def_minFac]
  decide +kernel

private theorem emptyWord_volume :
    let nr := rankedSlotOrders 0 0
    reservedVolumeCap 35 (fun j => (slotAssemblyRadii 0 0 0).getD j 0) nr.2 (nr.1 / nr.2)
      2380737823 ≤ 2^2056 := by
  dsimp only
  rw [rankedSlotOrders_zero,show slotAssemblyRadii 0 0 0 = arithmeticStripRadii by
    simp only [slotAssemblyRadii, Nat.zero_min, pow_zero]
    decide]
  decide +kernel

private theorem oneSlot_volume :
    let nr := rankedSlotOrders 1 1
    reservedVolumeCap 35 (fun j => (slotAssemblyRadii 1 1 1).getD j 0) nr.2 (nr.1 / nr.2)
      4045604611 ≤ 2^2199 := by
  decide +kernel

private theorem compileSlotWith_volume (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hwm : w ≤ m) (hcap : T.length ≤ (slotRadix m w)^k) :
    let nr := rankedSlotOrders k m
    let Q := slotPrimeCap k m
    let P := assemblyPrimeCap m Q
    let X := slotStackTestCap P (numericalSlotTests T nr.1 k m w).length.succ
    let U := compileSlotWith T k m w
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun j => (slotAssemblyRadii k m w).getD j 0) nr.2 (nr.1 / nr.2)
        (reservedPrimeCap X P) := by
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
  exact s.numericalSlotPolycube hn hcap hs hwm (s.primeBound hb hPrime) hP hA hB hR

private theorem reservedThreshold_mono {X Y : ℕ} (P : ℕ) (hXY : X ≤ Y) :
    reservedThreshold X P ≤ reservedThreshold Y P := by
  have hlog : Stacking.differenceLog X ≤ Stacking.differenceLog Y :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left _ hXY)) _
  unfold reservedThreshold
  gcongr

private theorem reservedCap_mono {X Y : ℕ} (P : ℕ) (hXY : X ≤ Y) :
    reservedCap X P ≤ reservedCap Y P := Nat.mul_le_mul_left _ (reservedThreshold_mono P hXY)

private theorem countCapAt_mono {H H' : ℕ → ℕ} (h : ∀ j < 17, H j ≤ H' j) :
    Rails.Strips.countCapAt 35 H ≤ Rails.Strips.countCapAt 35 H' := by
  unfold Rails.Strips.countCapAt
  apply listSumMap_le
  intro j hj
  unfold Rails.Strips.radius
  gcongr
  exact h j (List.mem_range.mp hj)

private theorem uniformSlotVolume (k m w R J L : ℕ) :
    reservedVolumeCap 35 (fun j => (slotAssemblyRadii k m w).getD j 0) R J L ≤
      reservedVolumeCap 35 (fun _ => slotAssemblyRadius k m w) R J L := by
  have h := countCapAt_mono (fun j hj => slotAssemblyRadii_le (k := k) (m := m) (w := w) hj)
  unfold reservedVolumeCap
  dsimp only
  gcongr

def slotRefinedEstimate (k m w : ℕ) :=
  let A := fallbackCap m
  let B := markerCap k m
  let C := SlotParameters.lowCap k m
  let N := order (fourValueLayout 0) * ((C^2*B^3)^(2*k*m) * A^(4*m))
  let P := slotStackPrimeCap (slotPrimeCap k m)
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  10^35*N*X^3*(slotAssemblyRadius k m w+1)^2

theorem compileSlotWith_correct (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hm : 0 < m) (hwm : w ≤ m) (hcap : T.length ≤ (slotRadix m w)^k) :
    let U := compileSlotWith T k m w
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ slotRefinedEstimate k m w := by
  obtain ⟨hne,hconn,hiff,hvol⟩ := compileSlotWith_volume T hn hwm hcap
  refine ⟨hne,hconn,hiff,?_⟩
  obtain ⟨s,hs,hA,hB,hC⟩ := exists_ranked_parameters k m
  rw [rankedSlotOrders_eq s hs] at hvol
  let N := order s.layout
  let H := slotAssemblyRadius k m w
  let P := slotStackPrimeCap (slotPrimeCap k m)
  let count := (numericalSlotTests T N k m w).length.succ
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  have hP : 3 < P := (by decide : 3 < 4).trans_le (le_max_left ..)
  have hX : slotStackTestCap P count ≤ X :=
    (slotStackTestCap_le (by omega : 1 < P)).trans
      (max_le_max_left _ (max_le_max_left _ (numericalSlotTests_length T N k m w)))
  have hXpos : 1 ≤ X := (by decide : 1 ≤ 2313).trans (le_max_left ..)
  have hPX : P ≤ X := (le_max_left ..).trans (le_max_right ..)
  have hV := slotVolume_le H s.period (N/s.period) N
    (reservedCap (slotStackTestCap P count) P) s.period_pos (Nat.div_mul_le_self ..)
  have hN := s.order_le_factors hA hC hB
  have hL := (reservedCap_mono P hX).trans (slotStack_le X P hXpos hPX)
  simp only [assemblyPrimeCap,ite_eq_right hm.ne'] at hvol
  apply hvol.trans ((reservedVolumeCap_mono (reservedPrimeCap_le_reservedCap _ _)).trans
    ((uniformSlotVolume k m w _ _ _).trans (hV.trans ?_)))
  unfold slotRefinedEstimate
  calc
    _ ≤ 10^32*_*(128*X^3)*(H+1)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) hL)
    _ ≤ _ := by
      rw [show 10^32 * (order (fourValueLayout 0) *
          ((SlotParameters.lowCap k m^2*markerCap k m^3)^(2*k*m)*fallbackCap m^(4*m))) *
          (128*X^3)*(H+1)^2 =
          (128*10^32)*(order (fourValueLayout 0) *
          ((SlotParameters.lowCap k m^2*markerCap k m^3)^(2*k*m)*fallbackCap m^(4*m))) *
          X^3*(H+1)^2 by ring]
      dsimp only
      gcongr
      decide

/-- Bound the volume using the linear shell estimate and separate prime caps. -/
def slotShortEstimate (k m w : ℕ) : ℕ :=
  let A := fallbackCap m
  let B := markerCap k m
  let C := SlotParameters.lowCap k m
  let N := 2^1893 * ((C^2*B^3)^(2*k*m) * A^(4*m))
  let P := assemblyPrimeCap m (slotPrimeCap k m)
  let X := slotStackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  mssPieceCap*N*(reservedCap X P)*216*4222*(4*Rails.Strips.countCapAt 35
    (fun _ => slotAssemblyRadius k m w)+1)

theorem compileSlotWith_short (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hwm : w ≤ m) (hcap : T.length ≤ (slotRadix m w)^k)
    (hH : 4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k m w)+4229 ≤ 2^811) :
    (compileSlotWith T k m w).length ≤ slotShortEstimate k m w := by
  obtain ⟨s,hs,hA,hB,hC⟩ := exists_ranked_parameters k m
  have he := rankedSlotOrders_eq s hs
  have hR : 2^811 ≤ s.period := by
    have hbase : 2^811 ≤ (guardedModuli (fourValueRows 0)).prod := by decide +kernel
    apply hbase.trans
    rw [fourValueInputOrder_eq]
    unfold period
    rw [Fintype.prod_sum_type]
    have hp : 0 < ∏ i : AddedRow k m, s.layout.lowSize (.inr i) :=
      Finset.prod_pos fun i _ => s.layout.lowSize_pos _
    exact Nat.le_mul_of_pos_right _ hp
  have hbase : order (fourValueLayout 0) ≤ 2^1893 := by
    rw [fourValueLayout_order]
    simpa only [Nat.mul_zero,pow_zero,Nat.mul_one] using fourValueRows_order_bound 0
  have hN := (s.order_le_factors hA hC hB).trans (Nat.mul_le_mul_right _ hbase)
  let P := assemblyPrimeCap m (slotPrimeCap k m)
  let X := slotStackTestCap P ((numericalSlotTests T (order s.layout) k m w).length.succ)
  let X' := slotStackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  have hX : X ≤ X' := max_le_max_left _ (max_le_max_left _ (numericalSlotTests_length T _ k m w))
  have hv := (compileSlotWith_volume T hn hwm hcap).2.2.2
  rw [he] at hv
  apply hv.trans ((reservedVolumeCap_mono (reservedPrimeCap_le_reservedCap _ _)).trans
    ((uniformSlotVolume k m w _ _ _).trans
      ((slotVolume_linear_le _ _ _ _ _ (Nat.div_mul_le_self _ _) (hH.trans hR)).trans ?_)))
  unfold slotShortEstimate
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) (reservedCap_mono P hX))))

/-- A singleton alphabet uses the empty word. The Sudoku masks, arithmetic
guards, and final geometric assembly are still those of the slot compiler. -/
theorem compileSlotWith_emptyWord (T : LeanWang.TileSet) (hn : T.length = 1) :
    let U := compileSlotWith T 0 0 0
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ 2^2056 := by
  obtain ⟨hne,hcon,hiff,hvol⟩ := compileSlotWith_volume T (k := 0) (m := 0) (w := 0)
    (by omega) (by decide) (by simp [hn])
  refine ⟨hne,hcon,hiff,hvol.trans ?_⟩
  let nr := rankedSlotOrders 0 0
  let P := slotBasePrimeCap
  let X := slotStackTestCap P (numericalSlotTests T nr.1 0 0 0).length.succ
  let X' := slotStackTestCap P (slotDeckCap 0 0 1)
  have hX : X ≤ X' := max_le_max_left _ (max_le_max_left _ (by
    simpa only [pow_zero] using numericalSlotTests_length T nr.1 0 0 0))
  have hM : reservedThreshold X' P < 2380737823 := by
    change reservedThreshold (slotStackTestCap slotBasePrimeCap (slotDeckCap 0 0 1)) slotBasePrimeCap < _
    simp only [slotDeckCap,arithmeticBaseline_length_exact]
    decide +kernel
  exact (reservedVolumeCap_mono
    (reservedPrimeCap_le_of_prime singletonStackPrime ((reservedThreshold_mono P hX).trans_lt hM))).trans
    emptyWord_volume

theorem compileSlot_twoOrThree (T : LeanWang.TileSet) (hlo : 2 ≤ T.length)
    (hhi : T.length ≤ 3) : (compileSlot T).length ≤ 2^2199 := by
  have hv := (compileSlotWith_volume T (k := 1) (m := 1) (w := 1) (by omega) (by decide)
    (by exact hhi)).2.2.2
  let nr := rankedSlotOrders 1 1
  let P := assemblyPrimeCap 1 (slotPrimeCap 1 1)
  let X := slotStackTestCap P (numericalSlotTests T nr.1 1 1 1).length.succ
  let X' := slotStackTestCap P (slotDeckCap 1 1 3)
  have hX : X ≤ X' := max_le_max_left _ (max_le_max_left _ (numericalSlotTests_length T nr.1 1 1 1))
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hB : separateMarkerCap 1 1 = 2432 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2208_6
  have hC : separateLowCap 1 1 = 5369952 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_5369856_2
  have hP : P = 5369952 := by
    simp only [P,assemblyPrimeCap,slotPrimeCap,slotStackPrimeCap,markerCap,SlotParameters.lowCap,
      show ¬ 24 ≤ (1 : ℕ) by decide,show (1 : ℕ) ≠ 0 by decide,ite_eq_right,hA,hB,hC]
    decide
  have hM : reservedThreshold X' P < 4045604611 := by
    unfold X'
    rw [hP]
    simp only [slotDeckCap,arithmeticBaseline_length_exact]
    decide +kernel
  have hvol := hv.trans ((reservedVolumeCap_mono
    (reservedPrimeCap_le_of_prime oneSlotStackPrime ((reservedThreshold_mono P hX).trans_lt hM))).trans oneSlot_volume)
  simpa only [compileSlot,slotDimensions,ite_eq_right (by omega : ¬ T.length ≤ 1),
    ite_eq_left (show T.length ≤ 9 by omega),ite_eq_left hhi] using hvol

theorem compileSlot_correct (T : LeanWang.TileSet) (hn : 0 < T.length) :
    let U := compileSlot T
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) := by
  dsimp only
  by_cases h : T.length ≤ 1
  · have he : T.length = 1 := by omega
    obtain ⟨hne,hconn,hiff,_⟩ := compileSlotWith_emptyWord T he
    simpa only [compileSlot,slotDimensions,ite_eq_left h] using And.intro hne (And.intro hconn hiff)
  by_cases hs : T.length ≤ 9
  · by_cases h₃ : T.length ≤ 3
    · obtain ⟨hne,hconn,hiff,_⟩ := compileSlotWith_correct T (k := 1) (m := 1) (w := 1)
        hn (by decide) (by decide) (by exact h₃)
      simpa only [compileSlot,slotDimensions,ite_eq_right h,ite_eq_left hs,ite_eq_left h₃] using
        And.intro hne (And.intro hconn hiff)
    · obtain ⟨hne,hconn,hiff,_⟩ := compileSlotWith_correct T (k := 2) (m := 1) (w := 1)
        hn (by decide) (by decide) (by exact hs)
      simpa only [compileSlot,slotDimensions,ite_eq_right h,ite_eq_left hs,ite_eq_right h₃] using
        And.intro hne (And.intro hconn hiff)
  let t := wideSlotLength T.length
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  obtain ⟨hne,hconn,hiff,_⟩ := compileSlotWith_correct T
    (k := slotPackedDigits T.length t) (m := 4*t) (w := 3*t)
    hn (by omega) (by omega) (slotPackedDigits_capacity _ _ ht)
  simpa only [compileSlot,slotDimensions,ite_eq_right h,ite_eq_right hs,t] using
    And.intro hne (And.intro hconn hiff)

theorem compileSlot_large (T : LeanWang.TileSet) (h : 10 ≤ T.length) :
    let t := wideSlotLength T.length
    (compileSlot T).length ≤ slotRefinedEstimate (slotPackedDigits T.length t) (4*t) (3*t) := by
  let t := wideSlotLength T.length
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  simpa only [compileSlot,slotDimensions,ite_eq_right (by omega : ¬ T.length ≤ 1),
      ite_eq_right (by omega : ¬ T.length ≤ 9),t] using
    (compileSlotWith_correct T (k := slotPackedDigits T.length t) (m := 4*t) (w := 3*t)
      (by omega) (by omega) (by omega) (slotPackedDigits_capacity _ _ ht)).2.2.2

/-- The one-tile size estimate for the same compiler. -/
theorem compileSlot_one (T : LeanWang.TileSet) (hn : T.length = 1) :
    (compileSlot T).length ≤ 2^2056 := by
  simpa [compileSlot,slotDimensions,hn] using (compileSlotWith_emptyWord T hn).2.2.2

theorem compileSlot_smallWidth (T : LeanWang.TileSet) (hlo : 2 ≤ T.length) (hhi : T.length ≤ 9)
    (hH : 4*Rails.Strips.countCapAt 35
        (fun _ => slotAssemblyRadius (if T.length ≤ 3 then 1 else 2) 1 1)+4229 ≤ 2^811) :
    (compileSlot T).length ≤ slotShortEstimate (if T.length ≤ 3 then 1 else 2) 1 1 := by
  have hn : ¬ T.length ≤ 1 := by omega
  have hc : T.length ≤ (slotRadix 1 1)^(if T.length ≤ 3 then 1 else 2) := by
    split <;> assumption
  simpa only [compileSlot,slotDimensions,ite_eq_right hn,ite_eq_left hhi] using
    compileSlotWith_short T (by omega) (by decide) hc hH

theorem compileSlot_widthFour (T : LeanWang.TileSet) (hn : 10 ≤ T.length)
    (ht : wideSlotLength T.length = 1)
    (hH : 4*Rails.Strips.countCapAt 35
        (fun _ => slotAssemblyRadius (slotPackedDigits T.length 1) 4 3)+4229 ≤ 2^811) :
    (compileSlot T).length ≤ slotShortEstimate (slotPackedDigits T.length 1) 4 3 := by
  have hn₁ : ¬ T.length ≤ 1 := by omega
  have hn₉ : ¬ T.length ≤ 9 := by omega
  have hcap := slotPackedDigits_capacity T.length 1 (by decide)
  simpa only [compileSlot,slotDimensions,ite_eq_right hn₁,ite_eq_right hn₉,ht] using
    compileSlotWith_short T (k := slotPackedDigits T.length 1) (m := 4) (w := 3)
      (by omega) (by decide) hcap hH

end
end TranslationTiling.Compiler.Size
