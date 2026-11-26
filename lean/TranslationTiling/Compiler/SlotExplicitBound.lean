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
  if n ≤ 1 then 2^2058 else
    ((n : ℝ)+4)^(5*Real.logb 2 (Real.logb 2 ((n : ℝ)+4)) +
      5*Real.logb 2 (Real.logb 2 (Real.logb 2 ((n : ℝ)+4)))+898)

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
  let H := max (2^68) ((C^2*B^8*A)^(min m (m+1-w)))
  let S := 4*Rails.Strips.countCapAt 35 (fun _ => H)
  S+4229 ≤ 2^811 ∧
    mssPieceCap*(2^1893*((C^2*B^3)^(2*k*m)*A^(4*m)))*reservedCap X P*216*4222*(S+1) ≤ 2^e

private theorem shortSize_of {k m w A B C e : ℕ}
    (hm : m ≠ 0) (ha : fallbackCap m = A) (hb : markerCap k m = B)
    (hc : SlotParameters.lowCap k m = C) (h : shortVolumeCheck k m w A B C e) :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k m w)+4229 ≤ 2^811) ∧
      slotShortEstimate k m w ≤ 2^e := by
  simpa only [shortVolumeCheck,slotAssemblyRadius,slotShortEstimate,assemblyPrimeCap,slotPrimeCap,
    slotStackPrimeCap,ite_eq_right hm,ha,hb,hc,
    show fourValueRadius 0 = 2^68 by decide] using h

private theorem shortVolumeChecks :
    shortVolumeCheck 1 1 1 2208 2432 5369952 2344 ∧
    shortVolumeCheck 2 1 1 2208 2624 5793952 2507 ∧
    shortVolumeCheck 1 4 3 2592 3392 8792352 3148 ∧
    shortVolumeCheck 2 4 3 2592 4160 10783264 3856 ∧
    shortVolumeCheck 3 4 3 2592 4928 12774176 4580 := by
  simp only [shortVolumeCheck,slotDeckCap,arithmeticBaseline_length_exact]
  decide +kernel

private theorem shortSize_1_1 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 1 1 1)+4229 ≤ 2^811) ∧
      slotShortEstimate 1 1 1 ≤ 2^2344 := by
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hm : ¬ 24 ≤ (1 : ℕ) := by decide
  have hB : separateMarkerCap 1 1 = 2432 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2208_6
  have hC : separateLowCap 1 1 = 5369952 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_5369856_2
  exact shortSize_of (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.1

private theorem shortSize_2_1 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 2 1 1)+4229 ≤ 2^811) ∧
      slotShortEstimate 2 1 1 ≤ 2^2507 := by
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hm : ¬ 24 ≤ (1 : ℕ) := by decide
  have hB : separateMarkerCap 2 1 = 2624 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2208_12
  have hC : separateLowCap 2 1 = 5793952 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_5793792_4
  exact shortSize_of (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.1

private theorem shortSize_1_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 1 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 1 4 3 ≤ 2^3148 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 1 4 = 3392 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_24
  have hC : separateLowCap 1 4 = 8792352 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_8792064_8
  exact shortSize_of (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.2.1

private theorem shortSize_2_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 2 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 2 4 3 ≤ 2^3856 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 2 4 = 4160 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_48
  have hC : separateLowCap 2 4 = 10783264 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_10782720_16
  exact shortSize_of (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.2.2.1

private theorem shortSize_3_4 :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius 3 4 3)+4229 ≤ 2^811) ∧
      slotShortEstimate 3 4 3 ≤ 2^4580 := by
  have hA : fallbackCap 4 = 2592 := slotSearchCap_2048_16
  have hm : ¬ 24 ≤ (4 : ℕ) := by decide
  have hB : separateMarkerCap 3 4 = 4928 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2592_72
  have hC : separateLowCap 3 4 = 12774176 := by
    rw [separateLowCap,hA,hB]
    exact slotSearchCap_12773376_24
  exact shortSize_of (by decide) hA
    (by simpa only [markerCap,ite_eq_right hm] using hB)
    (by simpa only [SlotParameters.lowCap,ite_eq_right hm] using hC) shortVolumeChecks.2.2.2.2

private theorem small_slot_log {T : LeanWang.TileSet} (hn : 2 ≤ T.length)
    (hlt : T.length < 65536) (hB : 0 < ((compileSlot T).length : ℝ)) :
    let u := Real.logb 2 ((T.length : ℝ)+4)
    let g := Real.logb 2 u
    Real.logb 2 ((compileSlot T).length : ℝ) ≤ u*(5*g+5*Real.logb 2 g+898) := by
  let x := (T.length : ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hnr : (2 : ℝ) ≤ T.length := by exact_mod_cast hn
  have hu : (137 : ℝ)/53 ≤ u := by
    apply lg_lower (a := 137) (b := 53) (by decide) _ (by dsimp [x]; positivity)
    exact (by norm_num : (2 : ℝ)^137 ≤ 6^53).trans
      (pow_le_pow_left₀ (by norm_num) (by dsimp [x]; linarith) _)
  have hg : (41 : ℝ)/30 ≤ g := by
    apply lg_lower (a := 41) (b := 30) (by decide) _ (by linarith : 0 < u)
    exact (by norm_num : (2 : ℝ)^41 ≤ ((137 : ℝ)/53)^30).trans
      (pow_le_pow_left₀ (by norm_num) hu _)
  have hl : (9 : ℝ)/20 ≤ l := by
    apply lg_lower (a := 9) (b := 20) (by decide) _ (by linarith : 0 < g)
    exact (by norm_num : (2 : ℝ)^9 ≤ ((41 : ℝ)/30)^20).trans
      (pow_le_pow_left₀ (by norm_num) hg _)
  have hmain : (2344 : ℝ) ≤ u*(5*g+5*l+898) := by
    have h := mul_le_mul hu (show (10885 : ℝ)/12 ≤ 5*g+5*l+898 by norm_num; linarith)
      (by norm_num) (by linarith)
    linarith
  have hu898 : 898*u ≤ u*(5*g+5*l+898) := by
    have h := mul_le_mul_of_nonneg_left (show (898 : ℝ) ≤ 5*g+5*l+898 by
      norm_num
      linarith) (show 0 ≤ u by linarith)
    linarith
  have dyadic {e : ℕ} (he : (compileSlot T).length ≤ 2^e)
      (h : (e : ℝ) ≤ u*(5*g+5*l+898)) :
      Real.logb 2 ((compileSlot T).length : ℝ) ≤ u*(5*g+5*l+898) :=
    (dyadic_log_le hB (by exact_mod_cast he)).trans h
  have log_lower {d : ℕ} (hd : 2^d ≤ T.length+4) : (d : ℝ) ≤ u := by
    have hh := lg_mono (by positivity : 0 < (2 : ℝ)^d)
      (show (2 : ℝ)^d ≤ x by dsimp [x]; exact_mod_cast hd)
    rwa [lg_two_pow] at hh
  change _ ≤ u*(5*g+5*l+898)
  by_cases hs : T.length ≤ 9
  · by_cases h₃ : T.length ≤ 3
    · have hb := compileSlot_smallWidth T hn hs (by simpa only [ite_eq_left h₃] using shortSize_1_1.1)
      rw [ite_eq_left h₃] at hb
      exact dyadic (hb.trans shortSize_1_1.2) (by simpa only [Nat.cast_ofNat] using hmain)
    · have hb := compileSlot_smallWidth T hn hs (by simpa only [ite_eq_right h₃] using shortSize_2_1.1)
      rw [ite_eq_right h₃] at hb
      have h := log_lower (d := 3) (by omega)
      exact dyadic (hb.trans shortSize_2_1.2) (by norm_num at h ⊢; linarith)
  · have ht := explicit_small_width hlt
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
      have hb := bound hk shortSize_1_4.1
      have hu' : (15 : ℝ)/4 ≤ u := by
        apply lg_lower (a := 15) (b := 4) (by decide) _ (by dsimp [x]; positivity)
        have hn' : (10 : ℝ) ≤ T.length := by exact_mod_cast (show 10 ≤ T.length by omega)
        exact (by norm_num : (2 : ℝ)^15 ≤ 14^4).trans
          (pow_le_pow_left₀ (by norm_num) (by dsimp [x]; linarith) _)
      exact dyadic (hb.trans shortSize_1_4.2) (by norm_num; linarith)
    · have hv := log_lower (d := 6) (by omega)
      by_cases h₂ : T.length ≤ 11664
      · have hk : k = 2 := slot_digits_at_four (by decide) h₂ (Or.inr (by omega))
        have hb := bound hk shortSize_2_4.1
        exact dyadic (hb.trans shortSize_2_4.2) (by norm_num at hv ⊢; linarith)
      · have hk : k = 3 := slot_digits_at_four (by decide) (by omega) (Or.inr (by omega))
        have hb := bound hk shortSize_3_4.1
        exact dyadic (hb.trans shortSize_3_4.2) (by norm_num at hv ⊢; linarith)

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
  have hlog : Real.logb 2 (S : ℝ) ≤ u*(5*g+5*l+898) :=
    slotRefinedEstimate_log hn
  change (S : ℝ) ≤ slotExplicitBound n
  rw [slotExplicitBound,ite_eq_right (by omega : ¬ n ≤ 1)]
  change (S : ℝ) ≤ x^(5*g+5*l+898)
  by_cases hS : 0 < (S : ℝ)
  · apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) hS (Real.rpow_pos_of_pos hx _)).mp
    rw [Real.logb_rpow_eq_mul_logb_of_pos hx,mul_comm]
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
      rw [Real.logb_rpow_eq_mul_logb_of_pos hx,mul_comm]
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
  have hE : 5*g+5*l+898 ≤ 5*g₀+5*l₀+908 := by linarith
  have hfinal : u*(5*g+5*l+898) ≤ v*(5*g₀+2000*(1+l₀)) := by
    have hu₀ : 0 ≤ u := (by linarith : 0 ≤ v).trans
      (lg_mono (by linarith : 0 < n) (by dsimp [x]; linarith))
    have h := mul_le_mul hu hE (by linarith : 0 ≤ 5*g+5*l+898) (by linarith)
    nlinarith only [h,hgu,hl₀,mul_nonneg hl₀ (show 0 ≤ v-1 by linarith),
      show 1 ≤ v by linarith]
  obtain ⟨hne,hconn,hiff⟩ := compileSlot_correct T (by omega)
  refine ⟨hne,hconn,hiff,?_⟩
  apply (compileSlot_explicit T (by omega)).trans
  rw [slotExplicitBound,ite_eq_right (by omega : ¬ T.length ≤ 1)]
  change x^(5*g+5*l+898) ≤ n^(5*g₀+2000*(1+l₀))
  have hx : 0 < x := by dsimp [x]; linarith
  have hn₀ : 0 < n := by linarith
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hn₀ _)).mp
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx,Real.logb_rpow_eq_mul_logb_of_pos hn₀]
  simpa only [mul_comm] using hfinal

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

end
end TranslationTiling.Compiler.Size
