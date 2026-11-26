import TranslationTiling.FiniteCompiler.SlotPrimes
import TranslationTiling.Compiler.SharedUsefulPrimes
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective

def slotWindowCap (threshold count : ℕ) : ℕ :=
  8 * max threshold (guardedPrimeCap (count+16))

theorem slotWindowCap_count {threshold count : ℕ} (ht : 512 ≤ threshold) :
    count + Nat.primeCounting threshold ≤ Nat.primeCounting (slotWindowCap threshold count) := by
  let d := count+16
  let s := Nat.log 2 d+1
  let Q := guardedPrimeCap d
  let M := max threshold Q
  have hM : 512 ≤ M := ht.trans (le_max_left ..)
  have hs : 4 ≤ s := by
    have h := (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by dsimp [d]; omega : d ≠ 0)).mpr
      (by dsimp [d]; omega : 2^4 ≤ d)
    dsimp [s]
    omega
  have hd : d ≤ 2^s := (Nat.lt_pow_succ_log_self (by decide) d).le
  have hp (i : ℕ) (hi : 4 ≤ i) : 4*i ≤ 2^i := by
    induction i, hi using Nat.le_induction with
    | base => decide
    | succ i hi ih => rw [pow_succ]; omega
  have hQ : Q ≤ 2^(2*s) := by
    rw [mul_comm 2 s, pow_mul, pow_two]
    change 4*d*s ≤ _
    calc
      _ = (4*s)*d := by ring
      _ ≤ _ := Nat.mul_le_mul (hp s hs) hd
  have hQr : (Q : ℝ) ≤ (2 : ℝ)^(2*s) := by exact_mod_cast hQ
  have hMr : (512 : ℝ) ≤ M := by exact_mod_cast hM
  have hM₀ : (0 : ℝ) < M := by linarith
  have hLog : 0 < Real.logb 2 (M : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hds : (Q : ℝ) = 4*(d : ℝ)*(s : ℝ) := by simp only [Q,guardedPrimeCap,Nat.cast_mul,Nat.cast_ofNat,s]
  have hMq : (Q : ℝ) ≤ M := by exact_mod_cast le_max_right threshold Q
  have hbound : 2*(d : ℝ) ≤ (M : ℝ)/Real.logb 2 M := by
    apply (le_div_iff₀ hLog).mpr
    by_cases he : (M : ℝ) ≤ (2 : ℝ)^(2*s)
    · have hl := lg_mono hM₀ he
      rw [lg_two_pow,Nat.cast_mul,Nat.cast_ofNat] at hl
      have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(d : ℝ) by positivity)
      linarith only [h,hds,hMq]
    · have hl := lg_ratio (b := 2*s) (by omega) (le_of_not_ge he)
      push_cast at hl
      have hz : 2*(d : ℝ)*(2*(s : ℝ)) ≤ (2 : ℝ)^(2*s) := by linarith only [hds,hQr]
      have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(d : ℝ) by positivity)
      have h' := mul_le_mul_of_nonneg_right hz (show 0 ≤ (M : ℝ)/(2 : ℝ)^(2*s) by positivity)
      have h'' : (2 : ℝ)^(2*s)*((M : ℝ)/(2 : ℝ)^(2*s)) = M := by field_simp
      nlinarith only [h,h',h'']
  have hi := shared_prime_interval hM
  have hNat : count + Nat.primeCounting M ≤ Nat.primeCounting (8*M) := by
    have hc : (count : ℝ) ≤ 2*(d : ℝ)-2 := by dsimp [d]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) count]
    exact_mod_cast le_sub_iff_add_le.mp (by linarith only [hbound,hi,hc] :
      (count : ℝ) ≤ (Nat.primeCounting (8*M) : ℝ) - Nat.primeCounting M)
  exact (Nat.add_le_add_left (Nat.monotone_primeCounting (le_max_left threshold Q)) count).trans hNat


def slotPrimeInterval (t C : ℕ) : List ℕ :=
  ((List.range (C-t)).map fun v => t+1+v).filter fun p => decide p.Prime

theorem mem_slotPrimeInterval {t C p : ℕ} :
    p ∈ slotPrimeInterval t C ↔ p.Prime ∧ t < p ∧ p ≤ C := by
  simp only [slotPrimeInterval,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v,hv,rfl⟩,hp⟩
    exact ⟨hp,by omega,by omega⟩
  · rintro ⟨hp,ht,hp'⟩
    exact ⟨⟨p-(t+1),by omega,by omega⟩,hp⟩

theorem slotPrimeInterval_nodup (t C : ℕ) : (slotPrimeInterval t C).Nodup := by
  unfold slotPrimeInterval
  exact (List.nodup_range.map (by intro a b h; dsimp at h; omega)).filter _

theorem slotPrimeInterval_length (t C : ℕ) :
    (slotPrimeInterval t C).length = Nat.primeCounting C - Nat.primeCounting t := by
  rw [← List.toFinset_card_of_nodup (slotPrimeInterval_nodup t C)]
  by_cases h : t ≤ C
  · have he : (slotPrimeInterval t C).toFinset = C.primesLE \ t.primesLE := by
      ext p
      simp only [List.mem_toFinset,mem_slotPrimeInterval,Finset.mem_sdiff,Nat.mem_primesLE]
      grind
    rw [he,Finset.card_sdiff_of_subset (fun p hp => Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans h,(Nat.mem_primesLE.mp hp).2⟩),
      Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting]
  · simp [slotPrimeInterval,Nat.sub_eq_zero_of_le (by omega : C ≤ t),
      Nat.sub_eq_zero_of_le (Nat.monotone_primeCounting (by omega : C ≤ t))]

private def slotLargeCap (t c : ℕ) : ℕ :=
  min (guardedPrimeCap (t+c+16))
    (if 512 ≤ t then slotWindowCap t c else guardedPrimeCap (t+c+16))

def slotSearchCap (t c : ℕ) : ℕ :=
  if t+32*(c+1) ≤ slotLargeCap t c ∧ c ≤ (slotPrimeInterval t (t+32*(c+1))).length then
    t+32*(c+1)
  else slotLargeCap t c

theorem slotSearchCap_eq_short {t c : ℕ}
    (hsmall : t+32*(c+1) ≤ guardedPrimeCap (t+c+16))
    (hw : t+32*(c+1) ≤ slotWindowCap t c)
    (hc : c ≤ (slotPrimeInterval t (t+32*(c+1))).length) :
    slotSearchCap t c = t+32*(c+1) := by
  unfold slotSearchCap
  apply ite_eq_left
  refine ⟨le_min hsmall ?_,hc⟩
  split <;> assumption

theorem slotSearchCap_le_guarded (t c : ℕ) :
    slotSearchCap t c ≤ guardedPrimeCap (t+c+16) := by
  unfold slotSearchCap
  split <;> rename_i h
  · exact h.1.trans (min_le_left ..)
  · exact min_le_left ..

theorem slotSearchCap_le_window {t c : ℕ} (ht : 512 ≤ t) :
    slotSearchCap t c ≤ slotWindowCap t c := by
  have hlarge : slotLargeCap t c ≤ slotWindowCap t c := by
    unfold slotLargeCap
    rw [ite_eq_left ht]
    exact min_le_right ..
  unfold slotSearchCap
  split <;> rename_i h
  · exact h.1.trans hlarge
  · exact hlarge

theorem threshold_le_slotSearchCap (t c : ℕ) : t ≤ slotSearchCap t c := by
  have h : t ≤ guardedPrimeCap (t+c+16) := by
    unfold guardedPrimeCap
    exact (show t ≤ 4*(t+c+16) by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  unfold slotSearchCap
  split
  · omega
  · unfold slotLargeCap
    apply le_min h
    split
    · unfold slotWindowCap
      exact (le_max_left ..).trans (Nat.le_mul_of_pos_left _ (by decide))
    · exact h

@[fun_prop] theorem slotPrimeInterval_primrec : Primrec (fun z : ℕ × ℕ => slotPrimeInterval z.1 z.2) := by
  unfold slotPrimeInterval
  have hlist : Primrec (fun z : ℕ × ℕ => (List.range (z.2-z.1)).map
      (fun v => z.1+1+v)) := by fun_prop
  exact filterList hlist (nat_prime_primrec.comp Primrec.snd)

@[fun_prop] theorem slotSearchCap_primrec : Primrec (fun z : ℕ × ℕ => slotSearchCap z.1 z.2) := by
  unfold slotSearchCap slotLargeCap slotWindowCap
  simp only [show ∀ a b : ℕ, min a b = a-(a-b) by intro a b; omega]
  fun_prop

def slotPrimePool (t c : ℕ) := slotPrimeInterval t (slotSearchCap t c)

@[simp] theorem slotPrimePool_mem (t c p : ℕ) :
    p ∈ slotPrimePool t c ↔ p.Prime ∧ t < p ∧ p ≤ slotSearchCap t c :=
  mem_slotPrimeInterval

theorem slotPrimePool_length (t c : ℕ) : c ≤ (slotPrimePool t c).length := by
  have hold : c ≤ (slotPrimeInterval t (guardedPrimeCap (t+c+16))).length := by
    rw [slotPrimeInterval_length]
    have hcount := guardedPrimeCap_count (m := t+c+16) (by omega)
    have hbad : Nat.primeCounting t ≤ t+1 := by
      rw [← Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_range]
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  unfold slotPrimePool slotSearchCap
  split <;> rename_i h
  · exact h.2
  · unfold slotLargeCap
    by_cases ht : 512 ≤ t
    · simp only [ite_eq_left ht]
      rw [slotPrimeInterval_length] at hold ⊢
      have hw := slotWindowCap_count (count := c) ht
      by_cases h' : guardedPrimeCap (t+c+16) ≤ slotWindowCap t c
      · rwa [min_eq_left h']
      · rw [min_eq_right (le_of_not_ge h')]
        omega
    · simpa only [ite_eq_right ht,min_self] using hold

def slotPrimeAt (threshold count index : ℕ) : ℕ :=
  (slotPrimePool threshold count).getD index 0

theorem slotPrimeAt_spec {threshold count index : ℕ} (hi : index < count) :
    (slotPrimeAt threshold count index).Prime ∧ threshold < slotPrimeAt threshold count index ∧
      slotPrimeAt threshold count index ≤ slotSearchCap threshold count := by
  have h := hi.trans_le (slotPrimePool_length threshold count)
  apply (slotPrimePool_mem _ _ _).mp
  unfold slotPrimeAt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

theorem slotPrimeAt_injective (threshold count : ℕ) :
    Function.Injective (fun i : Fin count => slotPrimeAt threshold count i.val) := by
  intro i j h
  have hi := i.isLt.trans_le (slotPrimePool_length threshold count)
  have hj := j.isLt.trans_le (slotPrimePool_length threshold count)
  have hd : (slotPrimePool threshold count).Nodup :=
    slotPrimeInterval_nodup ..
  simp only [slotPrimeAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] at h
  apply Fin.ext
  exact hd.getElem_inj_iff.mp h

theorem slotPrimePool_primrec : Primrec (fun z : ℕ × ℕ => slotPrimePool z.1 z.2) := by
  unfold slotPrimePool
  exact slotPrimeInterval_primrec.comp (Primrec.fst.pair slotSearchCap_primrec)

theorem slotPrimeAt_primrec : Primrec (fun z : (ℕ × ℕ) × ℕ => slotPrimeAt z.1.1 z.1.2 z.2) := by
  unfold slotPrimeAt
  have hp := slotPrimePool_primrec.comp (Primrec.fst : Primrec (Prod.fst : (ℕ × ℕ) × ℕ → ℕ × ℕ))
  exact (Primrec.list_getD 0).comp hp Primrec.snd

end TranslationTiling.FiniteCompiler.Packed
