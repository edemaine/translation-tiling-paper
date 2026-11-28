import TranslationTiling.Compiler.SlotWideEstimate
import TranslationTiling.FiniteCompiler.Effective.PackedTotalCompiler
import TranslationTiling.FiniteCompiler.Effective.SlotSmallPrimeCertificates

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 40000
attribute [local irreducible] slotSearchCap slotPrimeAt

def slotExplicitBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    ((n : ℝ)+4)^(5*Real.logb 2 (Real.logb 2 ((n : ℝ)+4)) +
      5*Real.logb 2 (Real.logb 2 (Real.logb 2 ((n : ℝ)+4)))+330+1322/Real.logb 2 ((n : ℝ)+4))

abbrev slotPublicBound := slotExplicitBound

private theorem dyadic_log_le {x : ℝ} (hx : 0 < x) {i : ℕ} (h : x ≤ (2 : ℝ)^i) :
    Real.logb 2 x ≤ i := by simpa only [lg_two_pow] using lg_mono hx h

private theorem explicit_small_width {n : ℕ} (hn : n < 65536) : wideSlotLength n = 1 := by
  have h : Nat.log 2 n ≤ 15 :=
    (Nat.log_mono_right (by omega : n ≤ 65535)).trans (by decide)
  have hb : Nat.log 2 (Nat.log 2 n) ≤ 3 :=
    (Nat.log_mono_right h).trans (by decide)
  have hj : Nat.log 2 (Nat.log 2 (Nat.log 2 n)) ≤ 1 :=
    (Nat.log_mono_right hb).trans (by decide)
  simp only [wideSlotLength]
  have hm := Nat.mul_le_mul hb hj
  have ht : Nat.log 2 (Nat.log 2 n) * Nat.log 2 (Nat.log 2 (Nat.log 2 n)) < 4 :=
    Nat.lt_succ_of_le hm
  rw [Nat.div_eq_of_lt ht] <;> decide

private theorem slot_digits_at_four {n k : ℕ} (hk : 1 ≤ k) (hn : n ≤ 108^k)
    (hl : k = 1 ∨ 108^(k-1) < n) :
    slotPackedDigits n 1 = k := by
  change max 1 (Nat.clog 108 n) = k
  have h : Nat.clog 108 n ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr hn
  have h' : k ≤ max 1 (Nat.clog 108 n) := by
    rcases hl with rfl | hl
    · exact le_max_left ..
    · have : ¬ Nat.clog 108 n ≤ k-1 := by
        intro hc
        exact hl.not_ge ((Nat.clog_le_iff_le_pow (by decide)).mp hc)
      omega
  exact le_antisymm (max_le hk h) h'

private theorem arithmeticBaseline_length_exact : arithmeticBaseline.length = 424 := by
  decide +kernel

private def shortVolumeCheck (k m w A B C e : ℕ) : Prop :=
  let D := (slotRadix m w)^k
  let count := slotDeckCap k m D
  let P := max 4 (max slotBasePrimeCap (max A (max B C)))
  let X := slotStackTestCap P count
  let H := max (2^68) ((C*B^3*A^2)^(min m (m+1-w)))
  let S := 4*Rails.Strips.countCapAt 35 (fun _ => H)
  S+4229 ≤ 2^811 ∧
    mssPieceCap*(2^1893*((C^2*B^3)^(2*k*m)*A^(4*m)))*reservedCap X P*216*4222*(S+1) ≤ 2^e

private theorem shortSize_of {k m w A B C e : ℕ}
    (hm : m ≠ 0) (hs : ¬ (k = 1 ∧ m = 1)) (hs₂ : ¬ (k = 2 ∧ m = 1)) (ha : fallbackCap m = A) (hb : markerCap k m = B)
    (hc : SlotParameters.lowCap k m = C) (h : shortVolumeCheck k m w A B C e) :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k m w)+4229 ≤ 2^811) ∧
      slotShortEstimate k m w ≤ 2^e := by
  simpa only [shortVolumeCheck,slotAssemblyRadius,slotOffsetFactorCap,ite_eq_right hs,ite_eq_right hs₂,slotShortEstimate,assemblyPrimeCap,slotPrimeCap,
    slotStackPrimeCap,ite_eq_right hm,ha,hb,hc,
    show fourValueRadius 0 = 2^68 by decide] using h

private theorem shortVolumeChecks :
    shortVolumeCheck 3 1 1 2208 2816 6217952 2606 ∧
    shortVolumeCheck 1 4 3 2592 3392 8792352 3007 ∧
    shortVolumeCheck 2 4 3 2592 4160 10783264 3711 ∧
    shortVolumeCheck 3 4 3 2592 4928 12774176 4432 := by
  simp only [shortVolumeCheck,slotDeckCap,arithmeticBaseline_length_exact]
  decide +kernel

private theorem shortSize_3_1 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 3 1 1)+4229 ≤ 2^811) ∧
      slotShortEstimate 3 1 1 ≤ 2^2606 := by
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hm : ¬ 24 ≤ (1 : ℕ) := by decide
  have hB : separateMarkerCap 3 1 = 2816 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2208_18
  have hC : separateLowCap 3 1 = 6217952 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_6217728_6
  exact shortSize_of (by decide) (by decide) (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.1

private theorem shortSize_1_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 1 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 1 4 3 ≤ 2^3007 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 1 4 = 3392 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_24
  have hC : separateLowCap 1 4 = 8792352 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_8792064_8
  exact shortSize_of (by decide) (by decide) (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.1

private theorem shortSize_2_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 2 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 2 4 3 ≤ 2^3711 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 2 4 = 4160 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_48
  have hC : separateLowCap 2 4 = 10783264 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_10782720_16
  exact shortSize_of (by decide) (by decide) (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.2.1

private theorem shortSize_3_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 3 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 3 4 3 ≤ 2^4432 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 3 4 = 4928 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_72
  have hC : separateLowCap 3 4 = 12774176 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_12773376_24
  exact shortSize_of (by decide) (by decide) (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.2.2

private theorem widthEight_sizes :
    shortVolumeCheck 2 8 6 3104 6208 19270688 5500 ∧
      shortVolumeCheck 3 8 6 3104 7744 24038944 7020 := by
  simp only [shortVolumeCheck,slotDeckCap,arithmeticBaseline_length_exact]
  decide +kernel

private theorem widthEight_two :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 2 8 6)+4229 ≤ 2^811) ∧
      slotShortEstimate 2 8 6 ≤ 2^5500 := by
  have ha : fallbackCap 8 = 3104 := slotSearchCap_2048_32
  have hb : separateMarkerCap 2 8 = 6208 := by
    rw [separateMarkerCap,ha]
    exact slotSearchCap_3104_96
  have hc : separateLowCap 2 8 = 19270688 := by
    rw [separateLowCap,ha,hb]
    exact slotSearchCap_19269632_32
  exact shortSize_of (by decide) (by decide) (by decide) ha
    (by simpa only [markerCap,show ¬24 ≤ (8:ℕ) by decide,ite_false] using hb)
    (by simpa only [SlotParameters.lowCap,show ¬24 ≤ (8:ℕ) by decide,ite_false] using hc) widthEight_sizes.1

private theorem widthEight_three :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 3 8 6)+4229 ≤ 2^811) ∧
      slotShortEstimate 3 8 6 ≤ 2^7020 := by
  have ha : fallbackCap 8 = 3104 := slotSearchCap_2048_32
  have hb : separateMarkerCap 3 8 = 7744 := by
    rw [separateMarkerCap,ha]
    exact slotSearchCap_3104_144
  have hc : separateLowCap 3 8 = 24038944 := by
    rw [separateLowCap,ha,hb]
    exact slotSearchCap_24037376_48
  exact shortSize_of (by decide) (by decide) (by decide) ha
    (by simpa only [markerCap,show ¬24 ≤ (8:ℕ) by decide,ite_false] using hb)
    (by simpa only [SlotParameters.lowCap,show ¬24 ≤ (8:ℕ) by decide,ite_false] using hc) widthEight_sizes.2

theorem compileSlot_widthEight (T : LeanWang.TileSet) (hn : 65536 ≤ T.length)
    (hb : Nat.log 2 (Nat.log 2 T.length) = 4) :
    if T.length ≤ 20412^2 then (compileSlot T).length ≤ 2^5500
    else (compileSlot T).length ≤ 2^7020 := by
  have ht : wideSlotLength T.length = 2 := by unfold wideSlotLength; rw [hb]; decide
  have hlo : 16 ≤ Nat.log 2 T.length :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by simpa using hn)
  have hlog : Nat.log 2 T.length < 2^5 := by
    exact (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mp (by rw [hb]; decide)
  have hn32 : T.length < 2^32 := by
    exact (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mp hlog
  let k := slotPackedDigits T.length 2
  have hdim : compileSlot T = compileSlotWith T k 8 6 := by
    change compileSlot T = compileSlotWith T (slotPackedDigits T.length 2) (4*2) (3*2)
    rw [compileSlot_wide T (by omega),ht]
  have hD : slotRadix 8 6 = 20412 := by decide
  have hge : 2 ≤ k := by
    change 2 ≤ max 1 (Nat.clog (slotRadix 8 6) T.length)
    rw [hD]
    by_contra! h
    have hh := (Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mp
      (show Nat.clog 20412 T.length ≤ 1 by omega)
    omega
  have hbound : k ≤ 3 := by
    change max 1 (Nat.clog (slotRadix 8 6) T.length) ≤ 3
    rw [hD]
    exact max_le (by decide) ((Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mpr
      (hn32.le.trans (by decide)))
  by_cases h : T.length ≤ 20412^2
  · have hk : k = 2 := by
      have he := (Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mpr h
      have hK : k ≤ 2 := by
        change max 1 (Nat.clog (slotRadix 8 6) T.length) ≤ 2
        rw [hD]
        exact max_le (by decide) he
      omega
    rw [ite_eq_left h,hdim,hk]
    exact (compileSlotWith_short T (by omega) (by decide) (by simpa only [hD] using h)
      widthEight_two.1).trans widthEight_two.2
  · have hk : k = 3 := by
      by_contra! hk
      have he : Nat.clog 20412 T.length ≤ 2 := by
        change max 1 (Nat.clog (slotRadix 8 6) T.length) ≠ 3 at hk
        rw [hD] at hk
        have hK : Nat.clog 20412 T.length ≤ 3 := by
          change max 1 (Nat.clog (slotRadix 8 6) T.length) ≤ 3 at hbound
          rw [hD] at hbound
          omega
        omega
      exact h ((Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mp he)
    rw [ite_eq_right h,hdim,hk]
    exact (compileSlotWith_short T (by omega) (by decide)
      (by rw [hD]; exact hn32.le.trans (by decide)) widthEight_three.1).trans widthEight_three.2

private theorem input_logs_lower {n : ℕ} {a b c d e f h : ℕ} (hb : 0<b) (hd : 0<d) (hf : 0<f)
      (hh : h≤n+4) (ha : 2^a≤h^b)
      (hc : (2:ℝ)^c≤((a:ℝ)/b)^d) (he : (2:ℝ)^e≤((c:ℝ)/d)^f)
      (ha₀ : 0<a) (hc₀ : 0<c) :
    let u := Real.logb 2 ((n:ℝ)+4)
    let g := Real.logb 2 u
    (a:ℝ)/b ≤ u ∧ (c:ℝ)/d ≤ g ∧ (e:ℝ)/f ≤ Real.logb 2 g := by
  let x := (n:ℝ)+4
  have hx : 0 < x := by dsimp [x]; positivity
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  change (a:ℝ)/b ≤ u ∧ (c:ℝ)/d ≤ g ∧ (e:ℝ)/f ≤ l
  have ha' : (a:ℝ)/b ≤ u := by
    apply lg_lower hb _ hx
    have hh' : (h:ℝ)≤x := by dsimp [x]; exact_mod_cast hh
    exact (by exact_mod_cast ha : (2:ℝ)^a≤(h:ℝ)^b).trans
      (pow_le_pow_left₀ (by positivity) hh' _)
  have hapos : 0<(a:ℝ)/b := div_pos (Nat.cast_pos.mpr ha₀) (Nat.cast_pos.mpr hb)
  have hc' : (c:ℝ)/d ≤ g :=
    lg_lower hd (hc.trans (pow_le_pow_left₀ hapos.le ha' _)) (hapos.trans_le ha')
  have hcpos : 0<(c:ℝ)/d := div_pos (Nat.cast_pos.mpr hc₀) (Nat.cast_pos.mpr hd)
  exact ⟨ha',hc',lg_lower hf (he.trans (pow_le_pow_left₀ hcpos.le hc' _)) (hcpos.trans_le hc')⟩

private theorem small_slot_log {T : LeanWang.TileSet} (hn : 2 ≤ T.length)
    (hlt : T.length < 65536) (hB : 0 < ((compileSlot T).length : ℝ)) :
    let u := Real.logb 2 ((T.length : ℝ)+4)
    let g := Real.logb 2 u
    Real.logb 2 ((compileSlot T).length : ℝ) ≤ 1322+u*(5*g+5*Real.logb 2 g+330) := by
  let x := (T.length : ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hx : 0<x := by dsimp [x]; positivity
  have dyadic {E : ℕ} {U G L : ℝ} (he : (compileSlot T).length ≤ 2^E)
      (hlower : U≤u ∧ G≤g ∧ L≤l) (hU : 0≤U) (hE : (E:ℝ)≤1322+U*(5*G+5*L+330))
      (hP : 0≤5*G+5*L+330) :
      Real.logb 2 ((compileSlot T).length : ℝ) ≤ 1322+u*(5*g+5*l+330) := by
    refine (dyadic_log_le hB (by exact_mod_cast he)).trans (hE.trans ?_)
    have htail : 5*G+5*L+330≤5*g+5*l+330 := by linarith [hlower.2.1,hlower.2.2]
    exact add_le_add_right (mul_le_mul hlower.1 htail hP (hU.trans hlower.1)) _
  change _≤1322+u*(5*g+5*l+330)
  by_cases h₃ : T.length≤3
  · refine dyadic (compileSlot_twoOrThree T hn h₃) (U:=137/53) (G:=41/30) (L:=9/20) ?_ (by norm_num) (by norm_num) (by norm_num)
    exact input_logs_lower (a:=137) (b:=53) (c:=41) (d:=30) (e:=9) (f:=20) (h:=6)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide)
  by_cases h₉ : T.length≤9
  · refine dyadic (compileSlot_fourToNine T (by omega) h₉) (U:=3) (G:=1) (L:=0) ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa using (input_logs_lower (a:=3) (b:=1) (c:=1) (d:=1) (e:=0) (f:=1) (h:=8)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide))
  by_cases h₂₇ : T.length≤27
  · have h := (compileSlot_widthOneThree T (by omega) h₂₇ shortSize_3_1.1).trans shortSize_3_1.2
    refine dyadic h (U:=19/5) (G:=7/4) (L:=3/4) ?_ (by norm_num) (by norm_num) (by norm_num)
    exact input_logs_lower (a:=19) (b:=5) (c:=7) (d:=4) (e:=3) (f:=4) (h:=14)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide)
  have ht := explicit_small_width hlt
  let k := slotPackedDigits T.length 1
  have bound {j : ℕ} (hj : k = j)
      (hf : 4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius j 4 3)+4229 ≤ 2^811) :
      (compileSlot T).length ≤ slotShortEstimate j 4 3 := by
    have hb := compileSlot_widthFour T (by omega) ht (show
      4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k 4 3)+4229 ≤ 2^811 by
        rw [hj]
        exact hf)
    change (compileSlot T).length ≤ slotShortEstimate k 4 3 at hb
    rwa [hj] at hb
  by_cases h₁ : T.length ≤ 108
  · have hk : k = 1 := slot_digits_at_four (by decide) (by simpa using h₁) (Or.inl rfl)
    have hb := (bound hk shortSize_1_4.1).trans shortSize_1_4.2
    refine dyadic hb (U:=5) (G:=2) (L:=1) ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa using (input_logs_lower (a:=5) (b:=1) (c:=2) (d:=1) (e:=1) (f:=1) (h:=32)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide))
  by_cases h₂ : T.length ≤ 11664
  · have hk : k = 2 := slot_digits_at_four (by decide) h₂ (Or.inr (by omega))
    have hb := (bound hk shortSize_2_4.1).trans shortSize_2_4.2
    refine dyadic hb (U:=109/16) (G:=11/4) (L:=7/5) ?_ (by norm_num) (by norm_num) (by norm_num)
    exact input_logs_lower (a:=109) (b:=16) (c:=11) (d:=4) (e:=7) (f:=5) (h:=113)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide)
  · have hk : k = 3 := slot_digits_at_four (by decide) (by omega) (Or.inr (by omega))
    have hb := (bound hk shortSize_3_4.1).trans shortSize_3_4.2
    refine dyadic hb (U:=13) (G:=1) (L:=0) ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa using (input_logs_lower (a:=13) (b:=1) (c:=1) (d:=1) (e:=0) (f:=1) (h:=8192)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by norm_num) (by norm_num) (by decide) (by decide))

private theorem slotBoundLog {x : ℝ} (hx : 4<x) :
    let u := Real.logb 2 x
    let g := Real.logb 2 u
    Real.logb 2 (x^(5*g+5*Real.logb 2 g+330+1322/u)) =
      1322+u*(5*g+5*Real.logb 2 g+330) := by
  have h : 0<Real.logb 2 x := Real.logb_pos (by norm_num) (by linarith)
  dsimp only
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by linarith : 0<x)]
  field_simp
  <;> ring

theorem slot_size_bound_explicit {n : ℕ} (hn : 65536 ≤ n) :
    let t := wideSlotLength n
    (slotRefinedEstimate (slotPackedDigits n t) (4*t) (3*t) : ℝ) ≤ slotExplicitBound n := by
  let x := (n : ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let S := slotRefinedEstimate (slotPackedDigits n (wideSlotLength n))
    (4*wideSlotLength n) (3*wideSlotLength n)
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : Real.logb 2 (S : ℝ) ≤ 1322+u*(5*g+5*l+330) :=
    slotRefinedEstimate_log hn
  change (S : ℝ) ≤ slotExplicitBound n
  rw [slotExplicitBound,ite_eq_right (by omega : ¬ n ≤ 1)]
  change (S : ℝ) ≤ x^(5*g+5*l+330+1322/u)
  by_cases hS : 0 < (S : ℝ)
  · apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) hS (Real.rpow_pos_of_pos hx _)).mp
    have hx' : 4 < x := by
      have h : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      dsimp [x]
      linarith
    rw [slotBoundLog hx']
    exact hlog
  · exact (le_of_not_gt hS).trans (Real.rpow_nonneg hx.le _)

/-- The uniform computable compiler meets the explicit bound. -/
theorem compileSlot_explicit (T : LeanWang.TileSet) (hn : 0 < T.length) :
    (compileSlot T).length ≤ slotExplicitBound T.length := by
  by_cases h : T.length ≤ 1
  · rw [slotExplicitBound,ite_eq_left h]
    exact_mod_cast compileSlot_one T (by omega)
  · by_cases hlarge : 65536 ≤ T.length
    · exact (Nat.cast_le.mpr (compileSlot_large T (by omega))).trans (slot_size_bound_explicit hlarge)
    · have hp : 0 < ((compileSlot T).length : ℝ) := by
        exact_mod_cast List.length_pos_iff.mpr (compileSlot_correct T hn).1
      rw [slotExplicitBound,ite_eq_right h]
      have hx : 0 < (T.length : ℝ)+4 := by positivity
      apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) hp (Real.rpow_pos_of_pos hx _)).mp
      have hx' : (4:ℝ)<(T.length:ℝ)+4 := by
        have hp' : (0:ℝ)<T.length := by exact_mod_cast hn
        linarith
      rw [slotBoundLog hx']
      exact small_slot_log (by omega) (by omega) hp

/-- Asymptotic size of the computable slot compiler. -/
theorem compileSlot_logarithmic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : LeanWang.TileSet, 4 ≤ T.length →
      16 ≤ Real.logb 2 (Real.logb 2 (T.length : ℝ)) →
      let n := (T.length : ℝ)
      let g := Real.logb 2 (Real.logb 2 n)
      let U := compileSlot T
      U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
        (U.length : ℝ) ≤ n^(5*g+C*(1+Real.logb 2 g)) := by
  refine ⟨2000,by norm_num,?_⟩
  intro T hn hg
  have hn' : (4 : ℝ) ≤ T.length := by exact_mod_cast hn
  let n := (T.length : ℝ)
  let v := Real.logb 2 n
  let g₀ := Real.logb 2 v
  let l₀ := Real.logb 2 g₀
  let x := n+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hv : 2 ≤ v := by
    have he := lg_mono (by norm_num : 0 < (2 : ℝ)^2) (show (2 : ℝ)^2 ≤ n by norm_num; exact hn')
    simpa only [lg_two_pow,Nat.cast_ofNat] using he
  have hlog2 {z : ℝ} (hz : 0 < z) : Real.logb 2 (2*z) = 1+Real.logb 2 z := by
    rw [Real.logb_mul (by norm_num) hz.ne',Real.logb_self_eq_one (by norm_num)]
  have hu : u ≤ 1+v := by
    have h := lg_mono (by dsimp [x,n]; positivity : 0 < x) (show x ≤ 2*n by dsimp [x]; linarith)
    rwa [hlog2 (by linarith)] at h
  have hg' : g ≤ 1+g₀ := by
    have h := lg_mono (by linarith [show v ≤ u from lg_mono (by linarith) (by dsimp [x]; linarith)]
      : 0 < u) (show u ≤ 2*v by linarith)
    rwa [hlog2 (by linarith)] at h
  change 16 ≤ g₀ at hg
  have hgu : g₀ ≤ v := by
    have h := lg_le_twice_sub_one (show 1 ≤ v by linarith)
    have h₂ := lg_ratio (t := v) (b := 2) (by decide) (by
      have : (2 : ℝ)^16 ≤ v :=
        (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by linarith)).mp (by
          simpa only [lg_two_pow,Nat.cast_ofNat] using hg)
      norm_num at this ⊢
      linarith)
    norm_num at h₂
    change Real.logb 2 v ≤ _
    linarith
  have hg₀g : g₀ ≤ g := lg_mono (by linarith) (lg_mono (by linarith : 0 < n) (by dsimp [x]; linarith))
  have hl : l ≤ 1+l₀ := by
    have h := lg_mono (by linarith : 0 < g) (show g ≤ 2*g₀ by linarith)
    rwa [hlog2 (by linarith)] at h
  have hl₀ : 0 ≤ l₀ := Real.logb_nonneg (by norm_num) (by linarith)
  have hlpos : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  have hE : 5*g+5*l+842 ≤ 5*g₀+5*l₀+852 := by linarith
  have hfinal : u*(5*g+5*l+842) ≤ v*(5*g₀+2000*(1+l₀)) := by
    have hu₀ : 0 ≤ u := (by linarith : 0 ≤ v).trans
      (lg_mono (by linarith : 0 < n) (by dsimp [x]; linarith))
    have h := mul_le_mul hu hE (by linarith : 0 ≤ 5*g+5*l+842) (by linarith)
    nlinarith only [h,hgu,hl₀,mul_nonneg hl₀ (show 0 ≤ v-1 by linarith),
      show 1 ≤ v by linarith]
  obtain ⟨hne,hconn,hiff⟩ := compileSlot_correct T (by omega)
  refine ⟨hne,hconn,hiff,?_⟩
  apply (compileSlot_explicit T (by omega)).trans
  rw [slotExplicitBound,ite_eq_right (by omega : ¬ T.length ≤ 1)]
  change x^(5*g+5*l+330+1322/u) ≤ n^(5*g₀+2000*(1+l₀))
  have hx : 0 < x := by dsimp [x]; linarith
  have hn₀ : 0 < n := by linarith
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hn₀ _)).mp
  rw [slotBoundLog (by dsimp [x]; linarith),Real.logb_rpow_eq_mul_logb_of_pos hn₀]
  have hu₀ : 0 < u := Real.logb_pos (by norm_num) (by dsimp [x]; linarith)
  have hu₄ : 4 ≤ u := by
    have hp : (2:ℝ)^4 ≤ u :=
      (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) hu₀).mp
        (by rw [lg_two_pow]; norm_num; linarith [hg₀g])
    norm_num at hp
    linarith
  change 1322+u*(5*g+5*l+330) ≤ (5*g₀+2000*(1+l₀))*v
  nlinarith only [hfinal,hu₄]

/-- Totalize the compiler by encoding the empty alphabet as a single Wang tile
that cannot tile the plane. -/
def compileSlotTotal (T : LeanWang.TileSet) : Tile 3 :=
  compileSlot (nonemptyInput T)

theorem compileSlotTotal_computable : Computable compileSlotTotal :=
  compileSlot_computable.comp nonemptyInput_primrec.to_comp

theorem compileSlotTotal_facts (T : LeanWang.TileSet) :
    compileSlotTotal T ≠ [] ∧ FaceConnected (compileSlotTotal T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compileSlotTotal T)) ∧
      ((compileSlotTotal T).length : ℝ) ≤ slotExplicitBound T.length := by
  have hlen := nonemptyInput_length T
  have hp : 0 < (nonemptyInput T).length := by
    rw [hlen]
    exact Nat.zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨hne,hconn,hiff⟩ := compileSlot_correct (nonemptyInput T) hp
  refine ⟨hne,hconn,(nonemptyInput_tiles T).symm.trans hiff,?_⟩
  by_cases h : T.length ≤ 1
  · rw [slotExplicitBound,ite_eq_left h]
    exact_mod_cast compileSlot_one (nonemptyInput T) (hlen.trans (max_eq_left h))
  · have h₁ : (nonemptyInput T).length = T.length := hlen.trans (max_eq_right (by omega))
    have hb := compileSlot_explicit (nonemptyInput T) hp
    rwa [h₁] at hb

theorem compileSlotTotal_public_bound (T : LeanWang.TileSet) :
    ((compileSlotTotal T).length : ℝ) ≤ slotPublicBound T.length :=
  (compileSlotTotal_facts T).2.2.2

/-- Short alphabets fit in at most six width-one digits of the slot compiler. -/
def compactSlotDigits (n : ℕ) : ℕ :=
  if n ≤ 27 then 3 else if n ≤ 81 then 4 else if n ≤ 243 then 5 else 6

def compileCompactSlot (T : LeanWang.TileSet) : Tile 3 :=
  if 10 ≤ T.length ∧ T.length ≤ 729 then compileSlotWith T (compactSlotDigits T.length) 1 1
  else compileSlotTotal T

theorem compileCompactSlot_computable : Computable compileCompactSlot := by
  have hk : Primrec (fun T : LeanWang.TileSet => compactSlotDigits T.length) := by
    unfold compactSlotDigits
    fun_prop
  have hd : Primrec (fun T : LeanWang.TileSet => (T,compactSlotDigits T.length,1,1)) :=
    Primrec.id.pair (hk.pair (Primrec.const _))
  exact (Computable.cond
    (show Primrec (fun T : LeanWang.TileSet => decide (10 ≤ T.length ∧ T.length ≤ 729)) by fun_prop).to_comp
    (compileSlotWith_computable.comp hd.to_comp) compileSlotTotal_computable).of_eq
    (by intro T; by_cases h : 10 ≤ T.length ∧ T.length ≤ 729 <;> simp [compileCompactSlot,h])

private theorem compactSlotDigits_bounds {n : ℕ} (hn : n ≤ 729) :
    3 ≤ compactSlotDigits n ∧ compactSlotDigits n ≤ 6 ∧ n ≤ 3^(compactSlotDigits n) := by
  unfold compactSlotDigits
  split
  · norm_num at *; omega
  · split
    · norm_num at *; omega
    · split <;> (norm_num at *; omega)

theorem compileCompactSlot_correct (T : LeanWang.TileSet) :
    compileCompactSlot T ≠ [] ∧ FaceConnected (compileCompactSlot T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compileCompactSlot T)) := by
  unfold compileCompactSlot
  split
  · rename_i h
    obtain ⟨hk,hk',hc⟩ := compactSlotDigits_bounds h.2
    obtain ⟨hne,hconn,hiff,_⟩ := compileSlotWith_widthOne_bound T hk hk' (by omega) hc
    exact ⟨hne,hconn,hiff⟩
  · obtain ⟨hne,hconn,hiff,_⟩ := compileSlotTotal_facts T
    exact ⟨hne,hconn,hiff⟩


theorem compileCompactSlot_small_log {T : LeanWang.TileSet} (hn : 2 ≤ T.length)
    (hlt : T.length < 65536) :
    let u := Real.logb 2 ((T.length : ℝ)+4)
    let g := Real.logb 2 u
    Real.logb 2 ((compileCompactSlot T).length : ℝ) ≤ 1539+u*(4.986901*(g+Real.logb 2 g)+247) := by
  let u := Real.logb 2 ((T.length : ℝ)+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let U := compileCompactSlot T
  have hU : 0 < (U.length : ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr (compileCompactSlot_correct T).1
  have compare {E A G L : ℝ} (he : Real.logb 2 (U.length:ℝ) ≤ E)
      (hlo : A≤u ∧ G≤g ∧ L≤l) (hA : 0≤A)
      (hE : E≤1539+A*(4.986901*(G+L)+247)) (hP : 0≤4.986901*(G+L)+247) :
      Real.logb 2 (U.length:ℝ) ≤ 1539+u*(4.986901*(g+l)+247) := by
    have hP' : 4.986901*(G+L)+247 ≤ 4.986901*(g+l)+247 := by linarith [hlo.2.1,hlo.2.2]
    exact he.trans (hE.trans (add_le_add_right (mul_le_mul hlo.1 hP' hP (hA.trans hlo.1)) _))
  have dyad {e : ℕ} (h : U.length ≤ 2^e) : Real.logb 2 (U.length:ℝ) ≤ e :=
    dyadic_log_le hU (by exact_mod_cast h)
  have hsame (hn' : ¬ (10 ≤ T.length ∧ T.length ≤ 729)) : U = compileSlot T := by
    simp [U,compileCompactSlot,compileSlotTotal,hn',nonemptyInput,show T.length ≠ 0 by omega]
  change Real.logb 2 (U.length:ℝ) ≤ 1539+u*(4.986901*(g+l)+247)
  by_cases h₃ : T.length ≤ 3
  · have he := compileSlot_twoOrThree T hn h₃
    rw [← hsame (by omega)] at he
    refine compare (dyad he) (A:=137/53) (G:=41/30) (L:=9/20)
      ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=6) (a:=137) (b:=53) (c:=41) (d:=30) (e:=9) (f:=20)
      (by decide) (by decide) (by decide) (by omega) (by decide)
      (by norm_num) (by norm_num) (by decide) (by decide))
  by_cases h₉ : T.length ≤ 9
  · have he := compileSlot_fourToNine_square T (by omega) h₉
    rw [← hsame (by omega)] at he
    have hpow : (U.length:ℝ)^2 ≤ (2:ℝ)^4627 := by exact_mod_cast he
    have hh := dyadic_log_le (pow_pos hU 2) hpow
    rw [Real.logb_pow] at hh
    have hE : Real.logb 2 (U.length:ℝ) ≤ (4627:ℝ)/2 := by norm_num at hh; linarith
    refine compare hE (A:=3/1) (G:=19/12) (L:=33/50)
      ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=8) (a:=3) (b:=1) (c:=19) (d:=12) (e:=33) (f:=50)
      (by decide) (by decide) (by decide) (by omega) (by decide)
      (by norm_num) (by norm_num) (by decide) (by decide))
  by_cases h₇ : T.length ≤ 729
  · obtain ⟨hk,hk',hc⟩ := compactSlotDigits_bounds h₇
    have he := (compileSlotWith_widthOne_bound T hk hk' (by omega) hc).2.2.2
    have hu : U = compileSlotWith T (compactSlotDigits T.length) 1 1 := by
      simp [U,compileCompactSlot,show 10 ≤ T.length ∧ T.length ≤ 729 from ⟨by omega,h₇⟩]
    rw [← hu] at he
    by_cases h₂₇ : T.length ≤ 27
    · have he : U.length ≤ 2^2475 := by simpa [compactSlotDigits,h₂₇] using he
      refine compare (dyad he) (A:=19/5) (G:=7/4) (L:=3/4)
        ?_ (by norm_num) (by norm_num) (by norm_num)
      simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=14) (a:=19) (b:=5) (c:=7) (d:=4) (e:=3) (f:=4)
        (by decide) (by decide) (by decide) (by omega) (by decide)
        (by norm_num) (by norm_num) (by decide) (by decide))
    by_cases h₈₁ : T.length ≤ 81
    · have he : U.length ≤ 2^2595 := by simpa [compactSlotDigits,h₂₇,h₈₁] using he
      refine compare (dyad he) (A:=5/1) (G:=2/1) (L:=1/1)
        ?_ (by norm_num) (by norm_num) (by norm_num)
      simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=32) (a:=5) (b:=1) (c:=2) (d:=1) (e:=1) (f:=1)
        (by decide) (by decide) (by decide) (by omega) (by decide)
        (by norm_num) (by norm_num) (by decide) (by decide))
    · have he : U.length ≤ 2^2835 := he.trans (Nat.pow_le_pow_right (by decide) (by omega))
      refine compare (dyad he) (A:=6/1) (G:=2/1) (L:=1/1)
        ?_ (by norm_num) (by norm_num) (by norm_num)
      simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=86) (a:=6) (b:=1) (c:=2) (d:=1) (e:=1) (f:=1)
        (by decide) (by decide) (by decide) (by omega) (by decide)
        (by norm_num) (by norm_num) (by decide) (by decide))
  let k := slotPackedDigits T.length 1
  have bound {j : ℕ} (hj : k = j)
      (hf : 4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius j 4 3)+4229 ≤ 2^811) :
      (compileSlot T).length ≤ slotShortEstimate j 4 3 := by
    have hb := compileSlot_widthFour T (by omega) (explicit_small_width hlt) (show
      4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k 4 3)+4229 ≤ 2^811 by rw [hj]; exact hf)
    change (compileSlot T).length ≤ slotShortEstimate k 4 3 at hb
    rwa [hj] at hb
  by_cases h₂ : T.length ≤ 11664
  · have hk : k = 2 := slot_digits_at_four (by decide) h₂ (Or.inr (by omega))
    have he : U.length ≤ 2^3711 := by rw [hsame (by omega)]; exact (bound hk shortSize_2_4.1).trans shortSize_2_4.2
    refine compare (dyad he) (A:=9/1) (G:=3/1) (L:=3/2)
      ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=734) (a:=9) (b:=1) (c:=3) (d:=1) (e:=3) (f:=2)
      (by decide) (by decide) (by decide) (by omega) (by decide)
      (by norm_num) (by norm_num) (by decide) (by decide))
  · have hk : k = 3 := slot_digits_at_four (by decide) (by omega) (Or.inr (by omega))
    have he : U.length ≤ 2^4432 := by rw [hsame (by omega)]; exact (bound hk shortSize_3_4.1).trans shortSize_3_4.2
    refine compare (dyad he) (A:=13/1) (G:=1/1) (L:=0/1)
      ?_ (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,div_one] using (input_logs_lower (n:=T.length) (h:=11669) (a:=13) (b:=1) (c:=1) (d:=1) (e:=0) (f:=1)
      (by decide) (by decide) (by decide) (by omega) (by decide)
      (by norm_num) (by norm_num) (by decide) (by decide))


end
end TranslationTiling.Compiler.Size
