import TranslationTiling.FiniteCompiler.Effective.SlotLayout
import Mathlib.Combinatorics.Pigeonhole

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open Compiler.Effective Compiler.Size
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] slotSearchCap slotPrimeAt

private def bucket (a : ℕ) (pool : List ℕ) (r : ℕ) : List ℕ :=
  pool.filter fun p => decide (p % a = r)

@[fun_prop] private theorem bucket_primrec :
    Primrec (fun z : ℕ × List ℕ × ℕ => bucket z.1 z.2.1 z.2.2) := by
  unfold bucket
  exact filterList (by fun_prop) (by fun_prop)

private def quartet (a : ℕ) (pool : List ℕ) : List ℕ :=
  let r := (List.range a).findIdx fun r => decide (4 ≤ (bucket a pool r).length)
  (bucket a pool r).take 4

@[fun_prop] private theorem quartet_primrec :
    Primrec (fun z : ℕ × List ℕ => quartet z.1 z.2) := by
  have hr : Primrec (fun z : ℕ × List ℕ =>
      (List.range z.1).findIdx fun r => decide (4 ≤ (bucket z.1 z.2 r).length)) :=
    Primrec.list_findIdx (by fun_prop) (by
      change Primrec (fun z : (ℕ × List ℕ) × ℕ => decide (4 ≤ (bucket z.1.1 z.1.2 z.2).length))
      fun_prop)
  unfold quartet
  exact Primrec.list_take.comp (Primrec.const 4) (bucket_primrec.comp (Primrec.fst.pair (Primrec.snd.pair hr)))

private theorem quartet_spec (a : ℕ) (pool : List ℕ) (ha : 0 < a)
    (hp : pool.Pairwise (· < ·)) (hlen : 3*a < pool.length) :
    let q := quartet a pool
    q.length = 4 ∧ q.Pairwise (· < ·) ∧ (∀ p ∈ q, p ∈ pool) ∧
      ∀ p ∈ q, ∀ t ∈ q, p % a = t % a := by
  have hn := hp.imp (fun h => Nat.ne_of_lt h)
  have ⟨r,hr,hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun p : ℕ => p % a) (s := pool.toFinset) (t := Finset.range a) (n := 3)
    (fun p _ => Finset.mem_range.mpr (Nat.mod_lt p ha))
    (by simpa [List.toFinset_card_of_nodup hn, Nat.mul_comm] using hlen)
  have hbucket (r : ℕ) :
      (bucket a pool r).toFinset = pool.toFinset.filter (fun p => p % a = r) := by
    ext p
    simp [bucket]
  have hr' : 4 ≤ (bucket a pool r).length := by
    rw [← hbucket] at hcard
    exact hcard.trans_le (List.toFinset_card_le _)
  let j := (List.range a).findIdx fun r => decide (4 ≤ (bucket a pool r).length)
  have hj : j < (List.range a).length :=
    List.findIdx_lt_length_of_exists ⟨r,List.mem_range.mpr (Finset.mem_range.mp hr),by simp [hr']⟩
  have hgood : 4 ≤ (bucket a pool j).length := by
    have h := List.findIdx_getElem (xs := List.range a)
      (p := fun r => decide (4 ≤ (bucket a pool r).length)) (w := hj)
    simpa [j] using h
  have hsub : ((bucket a pool j).take 4).Sublist (bucket a pool j) := List.take_sublist ..
  have hfilter : (bucket a pool j).Sublist pool := List.filter_sublist ..
  refine ⟨by simp [quartet,j,min_eq_left hgood], hp.sublist (hsub.trans hfilter),
    fun p h => (hsub.trans hfilter).subset h, ?_⟩
  intro p hp' t ht
  have h₁ := (List.mem_filter.mp (hsub.subset hp')).2
  have h₂ := (List.mem_filter.mp (hsub.subset ht)).2
  exact (of_decide_eq_true h₁).trans (of_decide_eq_true h₂).symm

private def allocate (as pool : List ℕ) : List ℕ × List ℕ :=
  as.foldr (fun a acc =>
    let group := quartet a acc.1
    (acc.1.filter (fun p => decide (∀ q ∈ group, q ≠ p)), group ++ acc.2)) (pool, [])

private theorem allocate_primrec : Primrec (fun z : List ℕ × List ℕ => allocate z.1 z.2) := by
  unfold allocate
  apply Primrec.list_foldr (h := fun _ (z : ℕ × List ℕ × List ℕ) =>
    let group := quartet z.1 z.2.1
    (z.2.1.filter (fun p => decide (∀ q ∈ group, q ≠ p)), group ++ z.2.2))
    Primrec.fst (Primrec.snd.pair (Primrec.const []))
  change Primrec (fun z : (List ℕ × List ℕ) × ℕ × List ℕ × List ℕ =>
    let group := quartet z.2.1 z.2.2.1
    (z.2.2.1.filter (fun p => decide (∀ q ∈ group, q ≠ p)), group ++ z.2.2.2))
  have hq : Primrec (fun z : (List ℕ × List ℕ) × ℕ × List ℕ × List ℕ =>
    quartet z.2.1 z.2.2.1) := by fun_prop
  apply Primrec.pair _ (by fun_prop)
  apply filterList (f := fun z : (List ℕ × List ℕ) × ℕ × List ℕ × List ℕ => z.2.2.1)
    (p := fun z p => ∀ q ∈ quartet z.2.1 z.2.2.1, q ≠ p) (by fun_prop)
  apply allList (hq.comp Primrec.fst)
  fun_prop

private theorem allocate_spec (as pool : List ℕ) (A : ℕ)
    (ha : ∀ a ∈ as, 0 < a ∧ a ≤ A) (hp : pool.Pairwise (· < ·))
    (hpool : 4*as.length + 3*A ≤ pool.length) :
    let R := (allocate as pool).1
    let L := (allocate as pool).2
    (R ++ L).Perm pool ∧ R.Pairwise (· < ·) ∧ L.length = 4*as.length ∧
    ∀ i < as.length, ∀ j < 3,
      L.getD (4*i+j) 0 < L.getD (4*i+3) 0 ∧
      L.getD (4*i+3) 0 % as.getD i 0 = L.getD (4*i+j) 0 % as.getD i 0 := by
  induction as with
  | nil => simp [allocate,hp]
  | cons a as ih =>
    have h₀ := ha a (by simp)
    obtain ⟨hperm,hsort,hlen,hrows⟩ := ih (fun b hb => ha b (by simp [hb])) (by simpa only [List.length_cons] using (show 4*as.length + 3*A ≤ pool.length by simp only [List.length_cons] at hpool; omega))
    let R := (allocate as pool).1
    let L := (allocate as pool).2
    let Q := quartet a R
    let U := R.filter (fun p => decide (∀ q ∈ Q, q ≠ p))
    have hlenR := hperm.length_eq
    simp only [List.length_append,hlen] at hlenR
    change R.length + 4*as.length = pool.length at hlenR
    change L.length = 4*as.length at hlen
    obtain ⟨hQ,hsQ,hQR,hmod⟩ := quartet_spec a R h₀.1 hsort (by
      have := h₀.2
      simp only [List.length_cons] at hpool
      omega)
    change Q.length = 4 at hQ
    change Q.Pairwise (· < ·) at hsQ
    change ∀ p ∈ Q, p ∈ R at hQR
    change ∀ p ∈ Q, ∀ t ∈ Q, p % a = t % a at hmod
    have he : allocate (a::as) pool = (U,Q ++ L) := by
      rw [allocate,List.foldr_cons]
      rfl
    dsimp only
    rw [he]
    have hUR : (U ++ Q).Perm R := by
      apply (List.perm_ext_iff_of_nodup ?_ (hsort.imp (fun h => Nat.ne_of_lt h))).mpr
      · intro p
        simp only [List.mem_append,U,List.mem_filter]
        simp only [decide_eq_true_eq]
        have hmem : (∀ q ∈ Q, q ≠ p) ↔ p ∉ Q := by
          constructor
          · exact fun hn hp' => hn p hp' rfl
          · rintro hn q hq rfl
            exact hn hq
        rw [hmem]
        by_cases h : p ∈ Q
        · simpa only [h,or_true, true_iff] using hQR p h
        · simp [h,R]
      · apply List.nodup_append'.mpr
        refine ⟨(hsort.imp (fun h => Nat.ne_of_lt h)).filter _, hsQ.imp (fun h => Nat.ne_of_lt h), ?_⟩
        intro p hp' hq
        have hh := of_decide_eq_true (List.mem_filter.mp hp').2
        exact hh p hq rfl
    refine ⟨(by rw [← List.append_assoc]; exact (hUR.append_right L).trans hperm),
      hsort.sublist (List.filter_sublist ..),by simp [hQ,hlen]; omega,?_⟩
    intro i hi j hj
    cases i with
    | zero =>
      have hj' : j < Q.length := by omega
      have h3 : 3 < Q.length := by omega
      have hlt := (List.pairwise_iff_getElem.mp hsQ) j 3 hj' h3 hj
      have hh := hmod _ (List.getElem_mem h3) _ (List.getElem_mem hj')
      simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left,hj',h3] using And.intro hlt hh
    | succ i =>
      have hj' : Q.length ≤ 4*(i+1)+j := by omega
      have h3 : Q.length ≤ 4*(i+1)+3 := by omega
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_right hj',
        List.getElem?_append_right h3,List.getElem?_cons_succ,
        show 4*(i+1)+j-Q.length = 4*i+j by omega,
        show 4*(i+1)+3-Q.length = 4*i+3 by omega] using hrows i (by simpa using hi) j hj

def slotFirstFallbackIndex (k m i : ℕ) : ℕ :=
  2*(i % m) + if i < k*m then 0 else m*2

def slotFallbackAt (m i : ℕ) : ℕ :=
  if m = 1 then [811,257,227,653].getD i 0
  else slotPrimeAt slotBasePrimeCap (4*m) i

theorem slotFallbackAt_le {m i : ℕ} (hi : i < 4*m) :
    0 < slotFallbackAt m i ∧ slotFallbackAt m i ≤ fallbackCap m := by
  by_cases h : m = 1
  · subst m
    have h := (by decide +kernel : ∀ i : Fin 4,
      0 < slotFallbackAt 1 i ∧ slotFallbackAt 1 i ≤ slotBasePrimeCap) ⟨i,hi⟩
    exact ⟨h.1,h.2.trans (threshold_le_slotSearchCap ..)⟩
  · rw [slotFallbackAt,ite_eq_right h]
    have hp := slotPrimeAt_spec hi (threshold := slotBasePrimeCap)
    exact ⟨hp.1.pos,hp.2.2⟩

@[fun_prop] theorem slotFallbackAt_primrec :
    Primrec (fun z : ℕ × ℕ => slotFallbackAt z.1 z.2) :=
  Primrec.ite (by fun_prop)
    ((Primrec.list_getD 0).comp (Primrec.const _) Primrec.snd)
    (slotPrimeAt_primrec.comp (show Primrec (fun z : ℕ × ℕ => ((slotBasePrimeCap,4*z.1),z.2)) by
      fun_prop))

private def slotFallbacks (k m : ℕ) : List ℕ :=
  (List.range (2*k*m)).map (fun i => slotFallbackAt m (slotFirstFallbackIndex k m i))

private def matchedPool (k m : ℕ) : List ℕ :=
  slotPrimeInterval ((fallbackCap m)^2) (matchedSlotCap k m)

private def matchedPrimes (k m : ℕ) : List ℕ :=
  (allocate (slotFallbacks k m) (matchedPool k m)).2

def matchedPrimeAt (k m i j : ℕ) : ℕ := (matchedPrimes k m).getD (4*i+j) 0

@[fun_prop] theorem matchedPrimeAt_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => matchedPrimeAt z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : ℕ × ℕ => matchedPool z.1 z.2) := by
    unfold matchedPool matchedSlotCap matchedSlotCount fallbackCap slotWindowCap
    fun_prop
  have hf : Primrec (fun z : ℕ × ℕ => slotFallbacks z.1 z.2) := by
    unfold slotFallbacks slotFirstFallbackIndex
    fun_prop
  have hm : Primrec (fun z : ℕ × ℕ => matchedPrimes z.1 z.2) :=
    Primrec.snd.comp (allocate_primrec.comp (hf.pair hp))
  unfold matchedPrimeAt
  exact (Primrec.list_getD 0).comp (hm.comp (show Primrec
    (fun z : ℕ × ℕ × ℕ × ℕ => (z.1,z.2.1)) by fun_prop)) (by fun_prop)

private theorem matchedPool_sorted (k m : ℕ) : (matchedPool k m).Pairwise (· < ·) := by
  unfold matchedPool slotPrimeInterval
  apply List.Pairwise.filter
  rw [List.pairwise_map]
  exact (List.sortedLT_range _).pairwise.imp (fun h => by omega)

private theorem slotFallbackIndex_lt {k m i : ℕ} (hi : i < 2*k*m) :
    slotFirstFallbackIndex k m i < 4*m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have := Nat.mod_lt i hm
  unfold slotFirstFallbackIndex
  split <;> omega

private theorem matchedPrimes_valid (k m : ℕ) :
    (matchedPrimes k m).length = 4*(2*k*m) ∧ (matchedPrimes k m).Nodup ∧
      (∀ p ∈ matchedPrimes k m, p ∈ matchedPool k m) ∧
      ∀ i < 2*k*m, ∀ j < 3,
        matchedPrimeAt k m i j < matchedPrimeAt k m i 3 ∧
        matchedPrimeAt k m i 3 % slotFallbackAt m (slotFirstFallbackIndex k m i) =
          matchedPrimeAt k m i j % slotFallbackAt m (slotFirstFallbackIndex k m i) := by
  have ha : ∀ a ∈ slotFallbacks k m, 0 < a ∧ a ≤ fallbackCap m := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact slotFallbackAt_le (slotFallbackIndex_lt (List.mem_range.mp hi))
  have hlen : (slotFallbacks k m).length = 2*k*m := by simp [slotFallbacks]
  have hc : 512 ≤ (fallbackCap m)^2 := by
    have h : 2048 ≤ fallbackCap m := threshold_le_slotSearchCap ..
    exact (by decide : 512 ≤ 2048^2).trans (Nat.pow_le_pow_left h 2)
  have hpool : 4*(slotFallbacks k m).length+3*fallbackCap m ≤ (matchedPool k m).length := by
    unfold matchedPool
    rw [hlen,slotPrimeInterval_length,matchedSlotCap]
    have h := slotWindowCap_count (count := matchedSlotCount k m) hc
    rw [show 4*(2*k*m)+3*fallbackCap m = matchedSlotCount k m by unfold matchedSlotCount; ring]
    omega
  obtain ⟨hperm,_,hlen',hrow⟩ := allocate_spec _ _ _ ha (matchedPool_sorted k m) hpool
  refine ⟨by simpa [matchedPrimes,hlen] using hlen',
    (List.nodup_append'.mp (hperm.nodup_iff.mpr
      ((matchedPool_sorted k m).imp fun h => Nat.ne_of_lt h))).2.1,
    fun p hp => hperm.mem_iff.mp (List.mem_append_right _ hp), ?_⟩
  intro i hi j hj
  simpa [matchedPrimeAt,matchedPrimes,slotFallbacks,List.getD_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_eq_getElem (show i < (List.range (2*k*m)).length by simpa using hi)]
    using hrow i (hlen.symm ▸ hi) j hj

theorem matchedPrimeAt_spec {k m i j : ℕ} (hi : i < 2*k*m) (hj : j < 4) :
    (matchedPrimeAt k m i j).Prime ∧ (fallbackCap m)^2 < matchedPrimeAt k m i j ∧
      matchedPrimeAt k m i j ≤ matchedSlotCap k m := by
  have h := matchedPrimes_valid k m
  have hij : 4*i+j < (matchedPrimes k m).length := by rw [h.1]; omega
  apply mem_slotPrimeInterval.mp (h.2.2.1 _ ?_)
  rw [matchedPrimeAt,List.getD_eq_getElem _ _ hij]
  exact List.getElem_mem hij

theorem matchedPrimeAt_injective {k m i i' j j' : ℕ} (hi : i < 2*k*m)
    (hi' : i' < 2*k*m) (hj : j < 4) (hj' : j' < 4)
    (he : matchedPrimeAt k m i j = matchedPrimeAt k m i' j') : i = i' ∧ j = j' := by
  have h := matchedPrimes_valid k m
  have hij : 4*i+j < (matchedPrimes k m).length := by rw [h.1]; omega
  have hij' : 4*i'+j' < (matchedPrimes k m).length := by rw [h.1]; omega
  unfold matchedPrimeAt at he
  rw [List.getD_eq_getElem _ _ hij,List.getD_eq_getElem _ _ hij'] at he
  have := h.2.1.getElem_inj_iff.mp he
  omega

theorem matchedPrimeAt_congruent {k m i j : ℕ} (hi : i < 2*k*m) (hj : j < 3) :
    matchedPrimeAt k m i j < matchedPrimeAt k m i 3 ∧
      matchedPrimeAt k m i 3 % slotFallbackAt m (slotFirstFallbackIndex k m i) =
        matchedPrimeAt k m i j % slotFallbackAt m (slotFirstFallbackIndex k m i) :=
  (matchedPrimes_valid k m).2.2.2 i hi j hj

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
