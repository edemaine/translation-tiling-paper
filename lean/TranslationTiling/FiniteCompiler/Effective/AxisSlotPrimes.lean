import TranslationTiling.FiniteCompiler.Effective.SlotPrimeMatching
import TranslationTiling.FiniteCompiler.Effective.AxisSlotLayout
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalRows
import TranslationTiling.FiniteCompiler.Effective.MixedInput

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open Compiler.Size Compiler.Effective SlotParameters FiniteCompiler.Effective

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
attribute [local irreducible] slotSearchCap slotPrimeAt


def axisFallbackCap (m : ℕ) := slotSearchCap slotBasePrimeCap (8*m)

def axisPrimeCap (m count : ℕ) :=
  let J := 5*count+5*(axisFallbackCap m)^2+16
  let h := Nat.log 2 J+1
  let j := Nat.log 2 h+1
  J*(h+2*j+4)

theorem axisPrimeCap_square_le (m count : ℕ) : (axisFallbackCap m)^2 ≤ axisPrimeCap m count := by
  unfold axisPrimeCap
  dsimp only
  apply le_trans (by omega : (axisFallbackCap m)^2 ≤ 5*count+5*(axisFallbackCap m)^2+16)
  exact Nat.le_mul_of_pos_right _ (by omega)

@[fun_prop] theorem axisPrimeCap_primrec :
    Primrec (fun v : ℕ × ℕ => axisPrimeCap v.1 v.2) := by
  have hl := FiniteCompiler.Effective.natLog_primrec 2 (by decide)
  unfold axisPrimeCap axisFallbackCap
  dsimp only
  fun_prop

private theorem primeCap_le_pow (J : ℕ) :
    let h := Nat.log 2 J+1
    let j := Nat.log 2 h+1
    let L := h+2*j+4
    J*L ≤ 2^L := by
  let h := Nat.log 2 J+1
  let j := Nat.log 2 h+1
  let L := h+2*j+4
  have hh : h ≤ 2^j := (Nat.lt_pow_succ_log_self (by decide) h).le
  have hj_aux (v : ℕ) : v ≤ (2:ℕ)^v := by
    induction v with
    | zero => decide
    | succ n ih =>
      rw [pow_succ]
      have hpos : (0:ℕ) < 2^n := by positivity
      omega
  have hj := hj_aux j
  have hx : L ≤ 2^(j+4) := by
    rw [pow_add]
    have hpos : (0:ℕ) < 2^j := by positivity
    dsimp only [L]
    norm_num
    omega
  show J*L ≤ 2^L
  rw [show (2:ℕ)^L = 2^h*2^(j+4)*2^j by
      rw [show L = (h+(j+4))+j by dsimp [L]; omega,pow_add,pow_add]]
  have hJ' : J ≤ 2^h := (Nat.lt_pow_succ_log_self (by decide) J).le
  calc
    J * L ≤ 2^h * 2^(j+4) := Nat.mul_le_mul hJ' hx
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)

private theorem primeCounting_of_pow {J L : ℕ} (hJ : 16 ≤ J) (hL : 0 < L)
    (hpow : J*L ≤ 2^L) : J ≤ Nat.primeCounting (J*L)+2 := by
  let P := J*L
  have hP : P = J*L := rfl
  have hP0 : 16 ≤ P := hJ.trans (Nat.le_mul_of_pos_right _ hL)
  have hp' : (16:ℝ) ≤ P := by exact_mod_cast hP0
  have hlog := lg_mono (show 0 < (P:ℝ) by linarith)
    (show (P:ℝ) ≤ (2:ℝ)^L by exact_mod_cast hpow)
  rw [lg_two_pow] at hlog
  have hp1 := lg_mono (show 0 < (P:ℝ)+1 by positivity)
    (show (P:ℝ)+1 ≤ (P:ℝ)^2 by nlinarith)
  rw [Real.logb_pow] at hp1
  norm_num only [Nat.cast_ofNat] at hp1
  have hp2 := (div_le_iff₀ (Real.log_pos (show 1 < (P:ℝ) by linarith))).mp (Chebyshev.pi_ge P)
  have hcount : (P:ℝ) ≤ ((Nat.primeCounting P:ℝ)+2)*Real.logb 2 P := by
    have hl : (P:ℝ) ≤ (Nat.primeCounting P:ℝ)*Real.logb 2 P + Real.logb 2 ((P:ℝ)+1) := by
      simp only [Real.logb, ← mul_div_assoc, ← add_div]
      exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr (by linarith only [hp2])
    nlinarith only [hl,hp1]
  have hJR : (J:ℝ) ≤ (Nat.primeCounting P:ℝ)+2 := by
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (Nat.primeCounting P:ℝ)+2 by positivity)
    have he : (P:ℝ) = (J:ℝ)*L := by exact_mod_cast hP
    apply le_of_mul_le_mul_right _ (show (0:ℝ)<L by exact_mod_cast hL)
    linarith only [h,hcount,he]
  exact_mod_cast hJR

private theorem axisPrimeCap_count (m count : ℕ) :
    5*count+4*(axisFallbackCap m)^2+Nat.primeCounting ((axisFallbackCap m)^2) ≤
      Nat.primeCounting (axisPrimeCap m count) := by
  let A := (axisFallbackCap m)^2
  let J := 5*count+5*A+16
  let h := Nat.log 2 J+1
  let j := Nat.log 2 h+1
  let L := h+2*j+4
  have hJ : 16 ≤ J := by dsimp only [J]; omega
  have hh : 0 < L := by dsimp only [L]; omega
  have h := primeCounting_of_pow hJ hh (primeCap_le_pow J)
  change 5*count+4*A+Nat.primeCounting A ≤ Nat.primeCounting (J*L)
  have hA : Nat.primeCounting A ≤ A+1 := by
    rw [← Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_range]
    simpa using (Finset.card_filter_le (s := Finset.range (A+1)) Nat.Prime)
  change 5*count+5*A+16 ≤ Nat.primeCounting (J*L)+2 at h
  omega

def axisPrimePool (m count : ℕ) :=
  slotPrimeInterval ((axisFallbackCap m)^2) (axisPrimeCap m count)

def axisPrimeTable (m : ℕ) (moduli : List ℕ) :=
  (allocatePrimeGroups 4 moduli (axisPrimePool m moduli.length)).2

set_option maxHeartbeats 1000000 in
theorem axisPrimeTable_primrec :
    Primrec (fun z : ℕ × List ℕ => axisPrimeTable z.1 z.2) := by
  have hp : Primrec (fun z : ℕ × List ℕ => axisPrimePool z.1 z.2.length) := by
    unfold axisPrimePool
    have h : Primrec axisFallbackCap := by unfold axisFallbackCap; fun_prop
    fun_prop
  exact Primrec.snd.comp ((allocatePrimeGroups_primrec 4).comp (Primrec.snd.pair hp))

theorem axisPrimeTable_spec (m : ℕ) (moduli : List ℕ)
    (hmod : ∀ a ∈ moduli, 0<a ∧ a ≤ (axisFallbackCap m)^2) :
    let L := axisPrimeTable m moduli
    L.length = 5*moduli.length ∧ L.Nodup ∧
      (∀ p ∈ L, p.Prime ∧ (axisFallbackCap m)^2<p ∧ p≤axisPrimeCap m moduli.length) ∧
      ∀ i < moduli.length, ∀ j j' : ℕ, j<j' → j'<5 →
        L.getD (5*i+j) 0 < L.getD (5*i+j') 0 ∧
        L.getD (5*i+j') 0 % moduli.getD i 0 = L.getD (5*i+j) 0 % moduli.getD i 0 := by
  let P := axisPrimePool m moduli.length
  have hsort : P.Pairwise (· < ·) := by
    unfold P axisPrimePool slotPrimeInterval
    apply List.Pairwise.filter
    rw [List.pairwise_map]
    exact (List.sortedLT_range _).pairwise.imp (fun h => by omega)
  have hplen : 5*moduli.length+4*(axisFallbackCap m)^2 ≤ P.length := by
    unfold P axisPrimePool
    rw [slotPrimeInterval_length]
    have h := axisPrimeCap_count m moduli.length
    omega
  obtain ⟨hp,_,hlen,h⟩ := allocatePrimeGroups_spec 4 moduli P _ hmod hsort hplen
  refine ⟨hlen,(List.nodup_append'.mp (hp.nodup_iff.mpr (hsort.imp fun h => Nat.ne_of_lt h))).2.1,
    fun p hx => ?_,h⟩
  have hm : p ∈ P := hp.mem_iff.mp (List.mem_append_right _ hx)
  exact mem_slotPrimeInterval.mp hm

open SharedCoordinates

/-- Number the low rows first by slope and then by digit and position. -/
def axisSlotRank (k m : ℕ) : WangSlot k m ≃ Fin (2*k*m) :=
  ((finTwoEquiv.symm.prodCongr finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_assoc 2 k m).symm)

def axisFallbackRank (m : ℕ) : AxisFallback m ≃ Fin (8*m) :=
  ((finTwoEquiv.symm.prodCongr
    (((Equiv.refl _).prodCongr
      ((finTwoEquiv.symm.prodCongr finTwoEquiv.symm).trans finProdFinEquiv)).trans
      finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by ring))

def axisFallbackAt (m i : ℕ) : ℕ := slotPrimeAt slotBasePrimeCap (8*m) i

@[fun_prop] theorem axisFallbackAt_primrec :
    Primrec (fun z : ℕ × ℕ => axisFallbackAt z.1 z.2) :=
  slotPrimeAt_primrec.comp (show Primrec (fun z : ℕ × ℕ =>
    ((slotBasePrimeCap,8*z.1),z.2)) by fun_prop)

def axisFallbackPrime {m : ℕ} (i : AxisFallback m) : ℕ :=
  axisFallbackAt m (axisFallbackRank m i)

private theorem axisFallbackPrime_spec {m : ℕ} (i : AxisFallback m) :
    (axisFallbackPrime i).Prime ∧ slotBasePrimeCap < axisFallbackPrime i ∧
      axisFallbackPrime i ≤ axisFallbackCap m :=
  slotPrimeAt_spec (axisFallbackRank m i).isLt

private theorem axisFallbackPrime_injective (m : ℕ) :
    Function.Injective (axisFallbackPrime (m := m)) :=
  (slotPrimeAt_injective _ _).comp (axisFallbackRank m).injective

def axisFallbackModuli (k m : ℕ) : List ℕ :=
  (List.finRange (2*k*m)).map fun j =>
    let i := (axisSlotRank k m).symm j
    axisFallbackPrime (i.1,i.2.2,false,false) * axisFallbackPrime (i.1,i.2.2,true,false)

private theorem axisFallbackModuli_length (k m : ℕ) :
    (axisFallbackModuli k m).length = 2*k*m := by simp [axisFallbackModuli]

private theorem axisFallbackModuli_getD {k m : ℕ} (i : WangSlot k m) :
    (axisFallbackModuli k m).getD (axisSlotRank k m i) 0 =
      axisFallbackPrime (i.1,i.2.2,false,false) * axisFallbackPrime (i.1,i.2.2,true,false) := by
  unfold axisFallbackModuli
  have h : (axisSlotRank k m i).val <
      ((List.finRange (2*k*m)).map fun j =>
        let i := (axisSlotRank k m).symm j
        axisFallbackPrime (i.1,i.2.2,false,false)*axisFallbackPrime (i.1,i.2.2,true,false)).length :=
    by simp
  rw [List.getD_eq_getElem _ _ h,List.getElem_map,List.getElem_finRange]
  simp

private theorem axisFallbackModuli_bounded (k m : ℕ) :
    ∀ a ∈ axisFallbackModuli k m, 0 < a ∧ a ≤ (axisFallbackCap m)^2 := by
  intro a ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
  dsimp only
  exact ⟨Nat.mul_pos (axisFallbackPrime_spec _).1.pos (axisFallbackPrime_spec _).1.pos,
    (Nat.mul_le_mul (axisFallbackPrime_spec _).2.2 (axisFallbackPrime_spec _).2.2).trans_eq
      (pow_two _).symm⟩

def axisGroupPrime {k m : ℕ} (i : WangSlot k m) (j : ℕ) : ℕ :=
  (axisPrimeTable m (axisFallbackModuli k m)).getD (5*(axisSlotRank k m i).val+j) 0

private theorem axisGroupPrime_index_lt {k m : ℕ} (i : WangSlot k m) {j : ℕ} (hj : j<5) :
    5*(axisSlotRank k m i).val+j < (axisPrimeTable m (axisFallbackModuli k m)).length := by
  rw [(axisPrimeTable_spec m _ (axisFallbackModuli_bounded k m)).1,axisFallbackModuli_length]
  have := (axisSlotRank k m i).isLt
  omega

theorem axisGroupPrime_spec {k m : ℕ} (i : WangSlot k m) {j : ℕ} (hj : j<5) :
    (axisGroupPrime i j).Prime ∧ (axisFallbackCap m)^2 < axisGroupPrime i j ∧
      axisGroupPrime i j ≤ axisPrimeCap m (2*k*m) := by
  have h := (axisPrimeTable_spec m _ (axisFallbackModuli_bounded k m)).2.2.1
  rw [axisFallbackModuli_length] at h
  apply h
  unfold axisGroupPrime
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (axisGroupPrime_index_lt i hj)]
  exact List.getElem_mem _

private theorem axisGroupPrime_index_eq {k m : ℕ} (i i' : WangSlot k m) {j j' : ℕ}
    (hj : j<5) (hj' : j'<5) (h : axisGroupPrime i j = axisGroupPrime i' j') :
    i = i' ∧ j = j' := by
  have hN := (axisPrimeTable_spec m _ (axisFallbackModuli_bounded k m)).2.1
  unfold axisGroupPrime at h
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (axisGroupPrime_index_lt i hj),
    List.getElem?_eq_getElem (axisGroupPrime_index_lt i' hj')] at h
  have e := List.Nodup.getElem_inj_iff hN |>.mp h
  have er : (axisSlotRank k m i).val = (axisSlotRank k m i').val := by omega
  exact ⟨(axisSlotRank k m).injective (Fin.ext er),by omega⟩

private theorem axisGroupPrime_compare {k m : ℕ} (i : WangSlot k m) {j j' : ℕ}
    (hj : j<j') (hj' : j'<5) :
    axisGroupPrime i j < axisGroupPrime i j' ∧
      axisGroupPrime i j' % (axisFallbackPrime (i.1,i.2.2,false,false) *
        axisFallbackPrime (i.1,i.2.2,true,false)) =
      axisGroupPrime i j % (axisFallbackPrime (i.1,i.2.2,false,false) *
        axisFallbackPrime (i.1,i.2.2,true,false)) := by
  have hlt : (axisSlotRank k m i).val < (axisFallbackModuli k m).length := by
    rw [axisFallbackModuli_length]
    exact (axisSlotRank k m i).isLt
  have h := (axisPrimeTable_spec m _ (axisFallbackModuli_bounded k m)).2.2.2 _ hlt _ _ hj hj'
  rwa [axisFallbackModuli_getD] at h

def axisLabelIndex : Bool ⊕ Fin 3 → ℕ
  | .inl false => 3
  | .inl true => 4
  | .inr j => j

theorem axisLabelIndex_lt (a : Bool ⊕ Fin 3) : axisLabelIndex a < 5 := by
  rcases a with (_ | _) | j
  · decide
  · decide
  · exact j.isLt.trans (by decide)

private theorem axisLabelIndex_injective : Function.Injective axisLabelIndex := by
  rintro (a | j) (a' | j') h
  · cases a <;> cases a' <;> simp_all [axisLabelIndex]
  · have hj := j'.isLt
    cases a <;> simp [axisLabelIndex] at h <;> omega
  · have hj := j.isLt
    cases a' <;> simp [axisLabelIndex] at h <;> omega
  · exact congrArg Sum.inr (Fin.ext h)

def rankedAxisPrime (k m : ℕ) : AxisPrime k m → ℕ
  | .inl (i,j) => axisGroupPrime i (axisLabelIndex j)
  | .inr i => axisFallbackPrime i

private theorem axisFallbackCap_ge (m : ℕ) : slotBasePrimeCap ≤ axisFallbackCap m :=
  threshold_le_slotSearchCap ..

private theorem axisFallbackCap_le_sq (m : ℕ) : axisFallbackCap m ≤ (axisFallbackCap m)^2 := by
  have hp := axisFallbackCap_ge m
  have h : 1 ≤ axisFallbackCap m := (by decide : 1 ≤ slotBasePrimeCap).trans hp
  simpa only [one_mul,pow_two] using Nat.mul_le_mul_right (axisFallbackCap m) h

private theorem rankedAxisPrime_data {k m : ℕ} (i : AxisPrime k m) :
    (rankedAxisPrime k m i).Prime ∧ slotBasePrimeCap < rankedAxisPrime k m i := by
  rcases i with ⟨i,j⟩ | i
  · have h := axisGroupPrime_spec i (axisLabelIndex_lt j)
    exact ⟨h.1,((axisFallbackCap_ge m).trans (axisFallbackCap_le_sq m)).trans_lt h.2.1⟩
  · exact ⟨(axisFallbackPrime_spec i).1,(axisFallbackPrime_spec i).2.1⟩

private theorem rankedAxisPrime_injective (k m : ℕ) : Function.Injective (rankedAxisPrime k m) := by
  have hneq (i : WangSlot k m) (j : Bool ⊕ Fin 3) (i' : AxisFallback m) :
      axisGroupPrime i (axisLabelIndex j) ≠ axisFallbackPrime i' := by
    exact ne_of_gt (((axisFallbackPrime_spec i').2.2.trans (axisFallbackCap_le_sq m)).trans_lt
      (axisGroupPrime_spec i (axisLabelIndex_lt j)).2.1)
  intro i i' h
  rcases i with ⟨i,j⟩ | i <;> rcases i' with ⟨i',j'⟩ | i'
  · obtain ⟨hi,hj⟩ := axisGroupPrime_index_eq i i' (axisLabelIndex_lt j) (axisLabelIndex_lt j') h
    exact congrArg Sum.inl (Prod.ext hi (axisLabelIndex_injective hj))
  · exact (hneq i j i' h).elim
  · exact (hneq i' j' i h.symm).elim
  · exact congrArg Sum.inr (axisFallbackPrime_injective _ h)

private theorem positive_block_counts {a b r : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) (hr : a*b < r) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u*a+v*b := by
  have hadd := Nat.add_le_mul ha.one_lt hb.one_lt
  have hmem : r-a-b ∈ AddSubmonoid.closure ({a,b} : Set ℕ) := by
    by_contra hnot
    have hF := (frobeniusNumber_pair ((Nat.coprime_primes ha hb).mpr hab)
      ha.one_lt hb.one_lt).2 hnot
    omega
  obtain ⟨u,v,huv⟩ := (AddSubmonoid.mem_closure_pair _ _ _).mp hmem
  simp only [smul_eq_mul] at huv
  refine ⟨u+1,v+1,by omega,by omega,?_⟩
  calc
    r = (r-a-b)+a+b := by omega
    _ = (u*a+v*b)+a+b := by rw [huv]
    _ = (u+1)*a+(v+1)*b := by ring

private theorem low_marker_budget {k m : ℕ} (i : WangSlot k m) (a : Bool) (j : Fin 3) :
    let r := axisGroupPrime i (axisLabelIndex (.inl a))
    let b := axisGroupPrime i j
    let p := axisFallbackPrime (i.1,i.2.2,a,false)
    b < r ∧ r % p = b % p := by
  have hlt : j.val < axisLabelIndex (.inl a) := by
    have := j.isLt
    cases a <;> simp [axisLabelIndex] <;> omega
  have h := axisGroupPrime_compare i hlt (axisLabelIndex_lt (.inl a))
  have hd : axisFallbackPrime (i.1,i.2.2,a,false) ∣
      axisFallbackPrime (i.1,i.2.2,false,false)*axisFallbackPrime (i.1,i.2.2,true,false) := by
    cases a
    · exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left _ _
  exact ⟨h.1,(Nat.mod_mod_of_dvd _ hd).symm.trans
    ((congrArg (fun v : ℕ => v % axisFallbackPrime (i.1,i.2.2,a,false)) h.2).trans
      (Nat.mod_mod_of_dvd _ hd))⟩

noncomputable def rankedAxisParameters (k m : ℕ) : AxisParameters k m where
  prime := rankedAxisPrime k m
  prime_isPrime i := (rankedAxisPrime_data i).1
  prime_injective := rankedAxisPrime_injective k m
  coprime_arithmetic i := (FiniteCompiler.Effective.coprime_of_primeBound (fourValueOrder_pos 0)
    slotBasePrimeBound (rankedAxisPrime_data i).1 (rankedAxisPrime_data i).2).symm
  block_counts i a j := by
    let p := axisFallbackPrime (i.1,i.2.2,a,false)
    let r := axisGroupPrime i (axisLabelIndex (.inl a))
    cases j with
    | none =>
      let q := axisFallbackPrime (i.1,i.2.2,a,true)
      change ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u*p+v*q
      refine positive_block_counts (axisFallbackPrime_spec _).1 (axisFallbackPrime_spec _).1 ?_ ?_
      · intro h
        have he := axisFallbackPrime_injective m h
        have hb := congrArg (fun x : AxisFallback m => x.2.2.2) he
        cases hb
      · have hp := Nat.mul_le_mul (axisFallbackPrime_spec (i.1,i.2.2,a,false)).2.2
          (axisFallbackPrime_spec (i.1,i.2.2,a,true)).2.2
        exact (hp.trans_eq (pow_two _).symm).trans_lt (axisGroupPrime_spec i (axisLabelIndex_lt (.inl a))).2.1
    | some j =>
      let b := axisGroupPrime i j
      change ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u*p+v*b
      obtain ⟨hlt,hmod⟩ := low_marker_budget i a j
      change b < r at hlt
      change r % p = b % p at hmod
      have h₁ := Nat.mod_add_div b p
      have h₂ := Nat.mod_add_div r p
      rw [hmod,mul_comm p (r/p)] at h₂
      rw [mul_comm p (b/p)] at h₁
      have hd : b/p < r/p := by
        by_contra! he
        have := Nat.mul_le_mul_right p he
        omega
      refine ⟨r/p-b/p,1,by omega,by decide,?_⟩
      rw [Nat.sub_mul,one_mul]
      have := Nat.mul_le_mul_right p hd.le
      omega


def axisFallbackCode (m : ℕ) (g : Bool) (i : ℕ) (a b : Bool) : ℕ :=
  b.toNat+2*a.toNat+4*i+(m*4)*g.toNat

theorem axisFallbackRank_val {m : ℕ} (i : AxisFallback m) :
    (axisFallbackRank m i).val = axisFallbackCode m i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨g,i,a,b⟩
  cases g <;> cases a <;> cases b <;> rfl

theorem axisSlotRank_val {k m : ℕ} (i : WangSlot k m) :
    (axisSlotRank k m i).val = SlotParameters.wangCode k m i.1 i.2.1 i.2.2 := by
  rcases i with ⟨g,d,i⟩
  cases g <;> rfl

private def numericalFallbackModulus (k m i : ℕ) : ℕ :=
  let j := 4*(i%m)+(if i<k*m then 0 else 4*m)
  axisFallbackAt m j * axisFallbackAt m (j+2)

private theorem numericalFallbackModulus_eq {k m : ℕ} (i : WangSlot k m) :
    numericalFallbackModulus k m (axisSlotRank k m i).val =
      axisFallbackPrime (i.1,i.2.2,false,false) * axisFallbackPrime (i.1,i.2.2,true,false) := by
  rcases i with ⟨g,d,i⟩
  have hdi : i.val + m*d.val < k*m := by
    calc
      _ < m+m*d.val := Nat.add_lt_add_right i.isLt _
      _ = (d.val+1)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ d.isLt
  simp only [numericalFallbackModulus,axisFallbackPrime,axisFallbackRank_val,axisSlotRank_val,
    axisFallbackCode,SlotParameters.wangCode]
  have h₀ : (i.val+m*d.val)%m = i.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  have h₁ : (i.val+m*d.val+k*m)%m = i.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  cases g
  · simp [Bool.toNat,h₀,hdi,show 4*i.val+2 = 2+4*i.val by omega]
  · simp [Bool.toNat,h₁,show ¬ i.val+m*d.val+k*m < k*m by omega,
      show 4*i.val+4*m = 4*i.val+m*4 by omega,
      show 4*i.val+m*4+2 = 2+4*i.val+m*4 by omega]

private theorem numericalFallbackModuli_eq (k m : ℕ) :
    (List.range (2*k*m)).map (numericalFallbackModulus k m) = axisFallbackModuli k m := by
  apply List.ext_getElem
  · simp [axisFallbackModuli]
  · intro i h₁ h₂
    have hi : i < 2*k*m := by simpa using h₁
    simp only [axisFallbackModuli,List.getElem_map,List.getElem_range,List.getElem_finRange]
    let j := (axisSlotRank k m).symm ⟨i,hi⟩
    have h := numericalFallbackModulus_eq j
    have he : (axisSlotRank k m j).val = i :=
      congrArg Fin.val ((axisSlotRank k m).apply_symm_apply ⟨i,hi⟩)
    change numericalFallbackModulus k m i =
      axisFallbackPrime (j.1,j.2.2,false,false) * axisFallbackPrime (j.1,j.2.2,true,false)
    rwa [he] at h

@[fun_prop] theorem axisFallbackModuli_primrec :
    Primrec (fun z : ℕ × ℕ => axisFallbackModuli z.1 z.2) := by
  have h : Primrec (fun p : (ℕ × ℕ) × ℕ => numericalFallbackModulus p.1.1 p.1.2 p.2) := by
    unfold numericalFallbackModulus
    fun_prop
  exact (Compiler.Effective.mapList (by fun_prop : Primrec (fun z : ℕ × ℕ =>
    List.range (2*z.1*z.2))) h).of_eq (fun z => numericalFallbackModuli_eq z.1 z.2)

def axisPrimeAt (k m i j : ℕ) : ℕ :=
  (axisPrimeTable m (axisFallbackModuli k m)).getD (5*i+j) 0

@[fun_prop] theorem axisPrimeAt_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => axisPrimeAt p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : Primrec (fun p : ℕ × ℕ => axisPrimeTable p.2 (axisFallbackModuli p.1 p.2)) :=
    axisPrimeTable_primrec.comp (Primrec.snd.pair axisFallbackModuli_primrec)
  exact (Primrec.list_getD 0).comp (h.comp
    (show Primrec (fun p : ℕ × ℕ × ℕ × ℕ => (p.1,p.2.1)) by fun_prop)) (by fun_prop)

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
