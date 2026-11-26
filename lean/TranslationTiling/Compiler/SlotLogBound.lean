import TranslationTiling.Compiler.SlotAsymptotic
import TranslationTiling.Compiler.SlotPrimeEstimate
import TranslationTiling.Compiler.SlotDeckEstimate

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective

noncomputable section
set_option maxHeartbeats 1200000

private theorem log_mul_pow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (j : ℕ) :
    Real.logb 2 (c*x^j) = Real.logb 2 c + j*Real.logb 2 x := by
  rw [Real.logb_mul hc.ne' (pow_pos hx j).ne', Real.logb_pow]

theorem slot_log_bound_factors {c q a x h : ℝ}
    (hc : 0 < c) (hq : 0 < q) (ha : 0 < a) (hx : 0 < x) (hh : 0 < h)
    (j i : ℕ) :
    Real.logb 2 (c*(q^j*a^i)*x^3*h^2) =
      Real.logb 2 c + j*Real.logb 2 q + i*Real.logb 2 a + 3*Real.logb 2 x + 2*Real.logb 2 h := by
  rw [log_mul_pow (by positivity) hh,log_mul_pow (by positivity) hx,
    Real.logb_mul hc.ne' (by positivity),Real.logb_mul (pow_pos hq j).ne' (pow_pos ha i).ne',
    Real.logb_pow 2 q j,Real.logb_pow 2 a i]
  push_cast
  ring

/-- The exact slot bound has leading coefficient five in the second
logarithm, with a remainder bounded by a constant times one plus the
third logarithm. -/
theorem slot_size_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      16 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) →
      let u := Real.logb 2 (n : ℝ)
      let g := Real.logb 2 u
      let t := slotLengthParameter n
      let k := slotPackedDigits n t
      Real.logb 2 (slotSizeBound k (4*t) (3*t) : ℝ) ≤ u*(5*g+C*(1+Real.logb 2 g)) := by
  obtain ⟨C,hC,hcaps⟩ := slot_prime_caps_scale
  let L := Real.logb 2 C+4
  let N := order (fourValueLayout 0)
  let K := C+(N : ℝ)+6317+arithmeticBaseline.length
  let F := (fourValueRadius 0 : ℝ)+2
  let Z := Real.logb 2 (10^35*(N : ℝ))
  have hN : 0 < N := fourValueOrder_pos 0
  have hL : 0 ≤ L := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hC
    dsimp [L]
    linarith
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) arithmeticBaseline.length]
  have hF : 1 ≤ F := by dsimp [F]; linarith [Nat.cast_nonneg (α := ℝ) (fourValueRadius 0)]
  have hKL := Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hK
  have hFL := Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hF
  have hZ : 0 ≤ Z := by
    have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact Real.logb_nonneg (by norm_num) (by nlinarith only [hnr] : (1 : ℝ) ≤ 10^35*(N : ℝ))
  let E := Z+4*(1+L)+3*(Real.logb 2 K+6)+2*(Real.logb 2 F+11*(1+L))
  have hE : 0 ≤ E := by dsimp [E]; linarith
  refine ⟨30+20*L+E,by linarith,?_⟩
  intro n hn hgn
  let u := Real.logb 2 (n : ℝ)
  let g := Real.logb 2 u
  let e := 1+Real.logb 2 g
  let t := slotLengthParameter n
  let k := slotPackedDigits n t
  let m := 4*t
  let w := 3*t
  let A := fallbackCap m
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  let H := slotRadius Q m
  change 16 ≤ g at hgn
  change Real.logb 2 (slotSizeBound k m w : ℝ) ≤ u*(5*g+(30+20*L+E)*e)
  have hu : 1 ≤ u := by
    have h := lg_mono (x := 2) (y := n) (by norm_num)
      (by exact_mod_cast (show 2 ≤ n by omega))
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  have hg : 1 ≤ g := by linarith
  have hg0 : 0 < g := by linarith
  have hg2 : g^2 ≤ u := slot_log_squared_le (by linarith : 0 < u) hgn
  have hgu : g ≤ u := by
    nlinarith only [hg2,mul_nonneg hg0.le (sub_nonneg.mpr hg)]
  have hgpow : (2 : ℝ)^4 ≤ g := by norm_num; exact hgn
  have hl := lg_ratio (b := 4) (by decide) hgpow
  have hlg : Real.logb 2 g ≤ g/4 := by norm_num at hl; linarith
  have he₁ : 1 ≤ e := le_add_of_nonneg_right (Real.logb_nonneg (by norm_num) hg)
  have heg : e ≤ g := by dsimp [e]; linarith
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hk : 1 ≤ k := le_max_left ..
  have hm : 1 ≤ m := by unfold m; omega
  have hwidth := slot_width_bounds (by omega : 2 ≤ n) hgn
  have hm2 : (m : ℝ) ≤ g := by simpa only [m,t,Nat.cast_mul,Nat.cast_ofNat] using hwidth.2
  have hmain := slot_leading_log (by omega : 2 ≤ n) hgn hL
  have hmain' : ((10*k*m : ℕ) : ℝ) * (g+L*e) ≤ u*(5*g+(30+20*L)*e) := by
    simpa only [k,t,m,Nat.cast_mul,Nat.cast_ofNat] using hmain
  have hwork := slot_leading_log (by omega : 2 ≤ n) hgn (A := 0) le_rfl
  have hwk : 10*(k : ℝ)*(m : ℝ)*g ≤ u*(20*g) := by
    have hh : 5*g+30*e ≤ 20*g := by dsimp [e]; linarith
    have h : 10*(k : ℝ)*(m : ℝ)*g ≤ u*(5*g+30*e) := by
      simpa [u,g,e,k,t,m] using hwork
    exact h.trans (mul_le_mul_of_nonneg_left hh (by linarith))
  have hkm : (k : ℝ)*(m : ℝ) ≤ 2*u := by
    apply le_of_mul_le_mul_right _ hg0
    nlinarith only [hwk]
  have hₙu : 2*u ≤ (n : ℝ) := by
    have hh := lg_ratio (b := 2) (by decide) (show (2 : ℝ)^2 ≤ n by
      norm_num
      exact_mod_cast hn)
    norm_num at hh
    linarith
  have hn0 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn' : 0 < (n : ℝ) := by linarith
  have hkmn : k*m ≤ n := by exact_mod_cast hkm.trans hₙu
  have hkn : k ≤ n := (Nat.le_mul_of_pos_right _ hm).trans hkmn
  have hmn : m ≤ n := (Nat.le_mul_of_pos_left _ hk).trans hkmn
  have he2 : 2^m ≤ n := by
    have h : (2 : ℝ)^m ≤ n := by
      apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) (by positivity) hn').mp
      rw [lg_two_pow]
      exact hm2.trans hgu
    exact_mod_cast h
  have hd : (slotRadix m w)^k ≤ n^3 := by
    have hh := slot_digit_capacity_upper (by omega : 0 < n) ht
    change (slotRadix m w)^k ≤ n*4^m at hh
    have hpow : 4^m = (2^m)^2 := by
      calc
        4^m = (2^2)^m := rfl
        _ = 2^(2*m) := (pow_mul 2 2 m).symm
        _ = 2^(m*2) := by rw [Nat.mul_comm 2 m]
        _ = _ := pow_mul 2 m 2
    calc
      _ ≤ n*4^m := hh
      _ = n*(2^m)^2 := congrArg (n * ·) hpow
      _ ≤ n*n^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he2 _)
      _ = n^3 := by ring
  obtain ⟨ha,hb,hr⟩ := hcaps k m u g hu hg hg2 le_rfl (hlg.trans (by linarith)) hm2 hkm
  have hAq : A ≤ Q := le_max_left ..
  have hA0 : 0 < A := fallbackCap_pos m
  have hQ0 : 0 < Q := hA0.trans_le hAq
  have hg4 : g^2 ≤ g^4 := pow_le_pow_right₀ hg (by decide)
  have hQ : (Q : ℝ) ≤ C*u*g^4 := by
    change (↑(max (fallbackCap m) (max (markerCap k m) (SlotParameters.lowCap k m))) : ℝ) ≤ _
    simp only [Nat.cast_max]
    apply max_le _ (max_le hb hr)
    have hc : C ≤ C*u := by
      simpa using mul_le_mul_of_nonneg_left hu (show 0 ≤ C by linarith)
    exact ha.trans ((mul_le_mul_of_nonneg_left hg4 (by linarith)).trans
      (mul_le_mul_of_nonneg_right hc (by positivity)))
  have hQL : Real.logb 2 (Q : ℝ) ≤ g+L*e := by
    have hh := lg_mono (show 0 < (Q : ℝ) by exact_mod_cast hQ0) hQ
    rw [log_mul_pow (by positivity) hg0,Real.logb_mul (by positivity) (by positivity)] at hh
    change Real.logb 2 (Q : ℝ) ≤ Real.logb 2 C+g+4*Real.logb 2 g at hh
    dsimp [L,e]
    nlinarith only [hh,hC, mul_nonneg (Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hC)
      (Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hg)]
  have hQM : Real.logb 2 (Q : ℝ) ≤ (1+L)*g := by
    nlinarith only [hQL,mul_le_mul_of_nonneg_left heg hL]
  have hmg : (m : ℝ)*g ≤ u :=
    (mul_le_mul_of_nonneg_right hm2 hg0.le).trans (by rwa [← pow_two])
  have hmQL : (m : ℝ)*Real.logb 2 (Q : ℝ) ≤ (1+L)*u := by
    have ha' := mul_le_mul_of_nonneg_left hQM (Nat.cast_nonneg (α := ℝ) m)
    have hb' := mul_le_mul_of_nonneg_left hmg (show 0 ≤ 1+L by linarith)
    nlinarith only [ha',hb']
  have hAL : 4*(m : ℝ)*Real.logb 2 (A : ℝ) ≤ 4*(1+L)*u := by
    have hh := lg_mono (show 0 < (A : ℝ) by exact_mod_cast hA0)
      (show (A : ℝ) ≤ Q by exact_mod_cast hAq)
    have hm' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) m)
    linarith only [hm',hmQL]
  have hX0 : 0 < X := (by decide : 0 < 2313).trans_le (le_max_left ..)
  have hn6 : (1 : ℝ) ≤ (n : ℝ)^6 := one_le_pow₀ hn0
  have hX : (X : ℝ) ≤ K*(n : ℝ)^6 := by
    have hdc := slot_deck_cap_polynomial k m ((slotRadix m w)^k) n (by omega) hkn hmn hkmn he2 hd
    have hgN : g ≤ (n : ℝ) := by linarith
    have huN : u ≤ (n : ℝ) := by linarith
    have hQN : (Q : ℝ) ≤ C*(n : ℝ)^6 := by
      calc
        _ ≤ C*u*g^4 := hQ
        _ ≤ C*(n : ℝ)*(n : ℝ)^4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left huN (by linarith)) (pow_le_pow_left₀ hg0.le hgN 4)
            (by positivity) (by positivity)
        _ ≤ _ := by
          rw [mul_assoc,← pow_succ']
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn0 (by decide : 5 ≤ 6)) (by linarith)
    unfold X stackTestCap P slotStackPrimeCap
    simp only [Nat.cast_max,Nat.cast_ofNat]
    apply max_le _ (max_le (max_le _ (max_le _ _)) _)
    · exact (by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) N,
        Nat.cast_nonneg (α := ℝ) arithmeticBaseline.length] : 2313 ≤ K).trans
        (by simpa using mul_le_mul_of_nonneg_left hn6 (show 0 ≤ K by linarith))
    · exact (by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) N,
        Nat.cast_nonneg (α := ℝ) arithmeticBaseline.length] : 4 ≤ K).trans
        (by simpa using mul_le_mul_of_nonneg_left hn6 (show 0 ≤ K by linarith))
    · exact (by dsimp [K, slotBasePrimeCap]; norm_num; linarith [Nat.cast_nonneg (α := ℝ) N,
        Nat.cast_nonneg (α := ℝ) arithmeticBaseline.length] : (slotBasePrimeCap : ℝ) ≤ K).trans
        (by simpa using mul_le_mul_of_nonneg_left hn6 (show 0 ≤ K by linarith))
    · exact hQN.trans (mul_le_mul_of_nonneg_right
        (by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) N,
          Nat.cast_nonneg (α := ℝ) arithmeticBaseline.length]) (by positivity))
    · exact (show (↑(slotDeckCap k m ((slotRadix m w)^k)) : ℝ) ≤
          (4000+(arithmeticBaseline.length : ℝ))*(n : ℝ)^6 by exact_mod_cast hdc).trans
        (mul_le_mul_of_nonneg_right
          (by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) N]) (by positivity))
  have hXL : Real.logb 2 (X : ℝ) ≤ (Real.logb 2 K+6)*u := by
    have hh := lg_mono (show 0 < (X : ℝ) by exact_mod_cast hX0) hX
    rw [log_mul_pow (by positivity) hn'] at hh
    change Real.logb 2 (X : ℝ) ≤ Real.logb 2 K+6*u at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hu hKL]
  have hH : ((H : ℝ)+1) ≤ F*(Q : ℝ)^(11*m) := by
    have hq : 1 ≤ (Q : ℝ)^(11*m) := one_le_pow₀ (by exact_mod_cast hQ0)
    unfold H slotRadius
    simp only [Nat.cast_max,Nat.cast_pow]
    rw [← max_add_add_right]
    apply max_le
    · dsimp [F]
      nlinarith only [hq, mul_le_mul_of_nonneg_left hq
        (show 0 ≤ (fourValueRadius 0 : ℝ)+2 by positivity)]
    · dsimp [F]
      nlinarith only [hq,mul_nonneg (Nat.cast_nonneg (α := ℝ) (fourValueRadius 0))
        (show 0 ≤ (Q : ℝ)^(11*m) by positivity)]
  have hHL : Real.logb 2 ((H : ℝ)+1) ≤ (Real.logb 2 F+11*(1+L))*u := by
    have hh := lg_mono (by positivity : 0 < (H : ℝ)+1) hH
    rw [log_mul_pow (by positivity) (by exact_mod_cast hQ0)] at hh
    push_cast at hh
    nlinarith only [hh,hmQL,mul_le_mul_of_nonneg_left hu hFL]
  have hform : Real.logb 2 (slotSizeBound k m w : ℝ) =
      Z+((10*k*m : ℕ) : ℝ)*Real.logb 2 (Q : ℝ) + 4*(m : ℝ)*Real.logb 2 (A : ℝ) +
        3*Real.logb 2 (X : ℝ)+2*Real.logb 2 ((H : ℝ)+1) := by
    have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
    have hA' : 0 < (A : ℝ) := by exact_mod_cast hA0
    have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ0
    have hX' : 0 < (X : ℝ) := by exact_mod_cast hX0
    have hsz : (slotSizeBound k m w : ℝ) =
        (10^35*(N : ℝ))*((Q : ℝ)^(10*k*m)*(A : ℝ)^(4*m))*(X : ℝ)^3*((H : ℝ)+1)^2 := by
      change ((10^35*(N*(Q^(10*k*m)*A^(4*m)))*X^3*(H+1)^2 : ℕ) : ℝ) = _
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
      ring
    rw [hsz]
    have h := slot_log_bound_factors (c := 10^35*(N : ℝ)) (by positivity)
      hQ' hA' hX' (by positivity : 0 < (H : ℝ)+1) (10*k*m) (4*m)
    simpa only [Z,Nat.cast_mul,Nat.cast_ofNat] using h
  rw [hform]
  have hQL' := mul_le_mul_of_nonneg_left hQL (Nat.cast_nonneg (α := ℝ) (10*k*m))
  have hZu : Z ≤ Z*u := by simpa using mul_le_mul_of_nonneg_left hu hZ
  have hEu : E*u ≤ E*u*e := by simpa using mul_le_mul_of_nonneg_left he₁ (mul_nonneg hE (by linarith))
  dsimp only [E] at hEu
  dsimp only [E]
  nlinarith only [hmain',hQL',hAL,hXL,hHL,hZu,hEu]

/-- The adaptive construction satisfies the logarithmic size estimate
for all inputs whose second logarithm is at least sixteen. -/
theorem exists_connected_tile_slot_logarithmic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : LeanWang.TileSet, 4 ≤ T.length →
      16 ≤ Real.logb 2 (Real.logb 2 (T.length : ℝ)) →
      let n := (T.length : ℝ)
      let g := Real.logb 2 (Real.logb 2 n)
      ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
        (U.length : ℝ) ≤ n^(5*g+C*(1+Real.logb 2 g)) := by
  obtain ⟨C,hC,h⟩ := slot_size_log_bound
  refine ⟨C,hC,?_⟩
  intro T hn hg
  let n := T.length
  let t := slotLengthParameter n
  let k := slotPackedDigits n t
  obtain ⟨U,hne,hconn,hiff,hU⟩ := exists_connected_tile_slot_adaptive T (by omega)
  refine ⟨U,hne,hconn,hiff,?_⟩
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
