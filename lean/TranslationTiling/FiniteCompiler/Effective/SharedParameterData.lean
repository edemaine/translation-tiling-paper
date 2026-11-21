import TranslationTiling.Compiler.SharedUsefulPrimes
import TranslationTiling.FiniteCompiler.Effective.SharedNumericalDeck
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective
open scoped Classical

noncomputable section

set_option maxRecDepth 10000
set_option exponentiation.threshold 2000
set_option maxHeartbeats 2000000

def sharedArithmeticRow (i : ℕ) : ℕ × ℕ × List ℕ :=
  (profile1.a i, profile1.b i, (profile1.row i).map Prod.fst)

def sharedFixedRows : GuardedRows := (List.range 18).map sharedArithmeticRow

def sharedSeedRows : GuardedRows := [(2,1229,[1231]),(3,773,[797])]

def sharedReservedPrimes : List ℕ :=
  5 :: 7 :: 199 :: 163 :: (sharedFixedRows ++ sharedSeedRows).flatMap
    (fun (a,b,ds) => a :: b :: ds)

theorem sharedReservedPrimes_length : sharedReservedPrimes.length = 136 := by decide +kernel

theorem sharedReservedPrimes_nodup : sharedReservedPrimes.Nodup := by decide +kernel

def sharedUsefulPool (k : ℕ) : List ℕ :=
  (List.range (guardedPrimeCap (2*k+136)+1)).filter fun p =>
    decide (p.Prime ∧ p ∉ sharedReservedPrimes)

def sharedDigitPool (k : ℕ) : List ℕ :=
  (List.range (1600*guardedPrimeCap (2*k+136)+1)).filter fun p =>
    decide (p.Prime ∧ 200*guardedPrimeCap (2*k+136)<p)

theorem sharedUsefulPool_length (k : ℕ) : 2*k ≤ (sharedUsefulPool k).length := by
  let x := guardedPrimeCap (2*k+136)
  let reserve := sharedReservedPrimes.toFinset
  have hcount : 2*k+136 ≤ Nat.primeCounting x := guardedPrimeCap_count (by omega)
  have hs : x.primesLE \ reserve = (sharedUsefulPool k).toFinset := by
    ext q
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, List.mem_toFinset, reserve,
      sharedUsefulPool, List.mem_filter, List.mem_range, decide_eq_true_eq, x, Nat.lt_succ_iff,
      and_assoc]
  have h := Finset.card_le_card_sdiff_add_card (s := x.primesLE) (t := reserve)
  have hc : reserve.card ≤ 136 := by
    rw [← sharedReservedPrimes_length]
    exact List.toFinset_card_le _
  rw [Nat.primesLE_card_eq_primeCounting,hs] at h
  have hl := List.toFinset_card_le (sharedUsefulPool k)
  omega

theorem sharedDigitPool_length (k : ℕ) : 6*k ≤ (sharedDigitPool k).length := by
  let x := guardedPrimeCap (2*k+136)
  let M := 200*x
  let P := 1600*x
  have hMP : M ≤ P := by unfold M P; omega
  have hsub : M.primesLE ⊆ P.primesLE := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hMP,(Nat.mem_primesLE.mp hp).2⟩
  have hs : P.primesLE \ M.primesLE = (sharedDigitPool k).toFinset := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, List.mem_toFinset, sharedDigitPool,
      List.mem_filter, List.mem_range, decide_eq_true_eq, P, M, x, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨hP,hp⟩,hM⟩
      exact ⟨hP,hp,lt_of_not_ge (fun h => hM ⟨h,hp⟩)⟩
    · rintro ⟨hP,hp,hM⟩
      exact ⟨⟨hP,hp⟩,fun h => (not_le_of_gt hM) h.1⟩
  have hc := Finset.card_le_card_sdiff_add_card (s := P.primesLE) (t := M.primesLE)
  rw [Nat.primesLE_card_eq_primeCounting, hs,Nat.primesLE_card_eq_primeCounting] at hc
  have hl := List.toFinset_card_le (sharedDigitPool k)
  have h := shared_digit_count k
  change 6*k + Nat.primeCounting M ≤ Nat.primeCounting P at h
  omega

theorem sharedUsefulPool_facts {k p : ℕ} (hp : p ∈ sharedUsefulPool k) :
    p.Prime ∧ p ∉ sharedReservedPrimes ∧ p ≤ guardedPrimeCap (2*k+136) := by
  simp only [sharedUsefulPool,List.mem_filter,List.mem_range,decide_eq_true_eq] at hp
  exact ⟨hp.2.1,hp.2.2,Nat.le_of_lt_succ hp.1⟩

theorem sharedDigitPool_facts {k p : ℕ} (hp : p ∈ sharedDigitPool k) :
    p.Prime ∧ 200*guardedPrimeCap (2*k+136)<p ∧ p ≤ 1600*guardedPrimeCap (2*k+136) := by
  simp only [sharedDigitPool,List.mem_filter,List.mem_range,decide_eq_true_eq] at hp
  exact ⟨hp.2.1,hp.2.2,Nat.le_of_lt_succ hp.1⟩

def sharedWangRow (k i : ℕ) : ℕ × ℕ × List ℕ :=
  (if i < k then 199 else 163, (sharedUsefulPool k).getD i 0,
    (List.range 3).map fun j => (sharedDigitPool k).getD (3*i+j) 0)

def sharedRows (k : ℕ) : GuardedRows :=
  sharedFixedRows ++ (List.range (2*k)).map (sharedWangRow k) ++ sharedSeedRows

@[simp] theorem sharedRows_length (k : ℕ) : (sharedRows k).length = 20+2*k := by
  simp only [sharedRows,sharedFixedRows,sharedSeedRows,List.length_append,List.length_map,
    List.length_range,List.length_cons,List.length_nil]
  omega

theorem sharedWangRow_facts {k i : ℕ} (hi : i < 2*k) :
    let (a,b,ds) := sharedWangRow k i
    (a = 199 ∨ a = 163) ∧
    b.Prime ∧ b ∉ sharedReservedPrimes ∧ b ≤ guardedPrimeCap (2*k+136) ∧
    ds.length = 3 ∧
    ∀ d ∈ ds, d.Prime ∧ 200*guardedPrimeCap (2*k+136) < d ∧
      d ≤ 1600*guardedPrimeCap (2*k+136) := by
  dsimp [sharedWangRow]
  obtain ⟨hb,hbr,hbx⟩ := sharedUsefulPool_facts
    (getD_mem_of_lt _ _ _ (hi.trans_le (sharedUsefulPool_length k)))
  refine ⟨by split <;> simp, hb,hbr,hbx, by simp, ?_⟩
  intro d hd
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
  have h : 3*i+j < 6*k := by
    have := List.mem_range.mp hj
    omega
  exact sharedDigitPool_facts (getD_mem_of_lt _ _ _ (h.trans_le (sharedDigitPool_length k)))

private theorem positive_combination {a b d : ℕ} (ha : Nat.Prime a) (hb : Nat.Prime b)
    (hne : a ≠ b) (hd : a*b < d) : ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ d = A*a+B*b := by
  have hab := Nat.add_le_mul ha.one_lt hb.one_lt
  have hmem : d-a-b ∈ AddSubmonoid.closure ({a,b} : Set ℕ) := by
    by_contra hn
    have h := (frobeniusNumber_pair ((Nat.coprime_primes ha hb).mpr hne) ha.one_lt hb.one_lt).2 hn
    omega
  obtain ⟨A,B,hAB⟩ := (AddSubmonoid.mem_closure_pair _ _ _).mp hmem
  refine ⟨A+1,B+1,by omega,by omega,?_⟩
  simp only [smul_eq_mul] at hAB
  calc
    d = (d-a-b)+a+b := by omega
    _ = (A*a+B*b)+a+b := by rw [hAB]
    _ = (A+1)*a+(B+1)*b := by ring

theorem sharedWangRow_representation {k i d : ℕ} (hi : i < 2*k)
    (hd : d ∈ (sharedWangRow k i).2.2) :
    let (a,b,_) := sharedWangRow k i
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ d = A*a+B*b := by
  let a := (sharedWangRow k i).1
  let b := (sharedWangRow k i).2.1
  change ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ d = A*a+B*b
  obtain ⟨ha,hb,hr,hcap,_,hds⟩ := sharedWangRow_facts hi
  change a = 199 ∨ a = 163 at ha
  have hap : a.Prime := by rcases ha with h|h <;> rw [h] <;> decide
  have har : a ∈ sharedReservedPrimes := by
    rcases ha with h|h <;> rw [h] <;> simp only [sharedReservedPrimes,List.mem_cons,true_or,or_true]
  have hne : a ≠ b := by
    intro he
    apply hr
    change b ∈ sharedReservedPrimes
    rwa [← he]
  have hA : a ≤ 200 := by rcases ha with h|h <;> omega
  exact positive_combination hap hb hne ((Nat.mul_le_mul hA hcap).trans_lt (hds d hd).2.1)


theorem sharedRows_fixed_at {k i : ℕ} (hi : i < 18) :
    (sharedRows k).getD i (0,0,[]) = sharedArithmeticRow i := by
  rw [sharedRows, List.append_assoc]
  rw [List.getD_append _ _ _ _ (show i < sharedFixedRows.length by simpa [sharedFixedRows] using hi)]
  simp [sharedFixedRows,List.getD_eq_getElem?_getD,hi]

theorem sharedRows_wang_at {k i : ℕ} (hi : i < 2*k) :
    (sharedRows k).getD (18+i) (0,0,[]) = sharedWangRow k i := by
  rw [sharedRows, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (show sharedFixedRows.length ≤ 18+i by simp [sharedFixedRows])]
  simp only [sharedFixedRows,List.length_map,List.length_range,Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD,hi]

theorem sharedRows_seed_at (k t : ℕ) :
    (sharedRows k).getD (18+2*k+t) (0,0,[]) = sharedSeedRows.getD t (0,0,[]) := by
  rw [sharedRows, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (show sharedFixedRows.length ≤ 18+2*k+t by simp [sharedFixedRows]; omega)]
  simp only [sharedFixedRows,List.length_map,List.length_range,
    show 18+2*k+t-18=2*k+t by omega]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private def fullRowOrder (row : ℕ × ℕ × List ℕ) : ℕ :=
  row.2.2.prod^2 * row.1 * row.2.1

private theorem sharedWangRow_order_le {k i : ℕ} (hi : i < 2*k) :
    ((sharedWangRow k i).2.2.prod)^2*(sharedWangRow k i).2.1 ≤
      (1600*guardedPrimeCap (2*k+136))^6*guardedPrimeCap (2*k+136) := by
  obtain ⟨_,_,_,hb,hlen,hds⟩ := sharedWangRow_facts hi
  have hr : (sharedWangRow k i).2.2.prod ≤ (1600*guardedPrimeCap (2*k+136))^3 := by
    let P := 1600*guardedPrimeCap (2*k+136)
    have hbnd (ds : List ℕ) (h : ∀ d ∈ ds, d ≤ P) : ds.prod ≤ P^ds.length := by
      induction ds with
      | nil => simp
      | cons d ds ih =>
        rw [List.prod_cons,List.length_cons,pow_succ']
        exact Nat.mul_le_mul (h d (by simp)) (ih (fun q hq => h q (by simp [hq])))
    exact hlen ▸ hbnd _ (fun d hd => (hds d hd).2.2)
  exact (Nat.mul_le_mul (Nat.pow_le_pow_left hr 2) hb).trans_eq (by rw [← pow_mul])

set_option maxHeartbeats 3500000 in
theorem sharedRows_order_bound (k : ℕ) :
    sharedOrder (sharedRows k) ≤
      2^1893 * (1600*guardedPrimeCap (2*k+136))^(12*k)*guardedPrimeCap (2*k+136)^(2*k) := by
  let rs := sharedRows k
  let x := guardedPrimeCap (2*k+136)
  let P := 1600*x
  let rowOrder i := (rowR rs i)^2 * sharedObservedA rs i * rowB rs i
  let fixed := ((List.range 18).map (fun i => fullRowOrder (sharedArithmeticRow i))).prod
  let seeds := ((List.range 2).map (fun t => fullRowOrder (sharedSeedRows.getD t (0,0,[])))).prod
  let j := ((List.range (2*k)).map (fun i => rowOrder (18+i))).prod
  have hfix : ((List.range 18).map rowOrder).prod = fixed := by
    unfold fixed
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    have h := List.mem_range.mp hi
    unfold rowOrder rowR rowDigits sharedObservedA rowB rowA
    simp only [not_le.mpr h,false_and,ite_false,rs,sharedRows_fixed_at h,fullRowOrder]
  have hseed : ((List.range 2).map (fun t => rowOrder (18+2*k+t))).prod = seeds := by
    unfold seeds
    apply congrArg List.prod
    apply List.map_congr_left
    intro t _
    have h : ¬ (18 ≤ 18+2*k+t ∧ 18+2*k+t < rs.length - 2) := by
      rw [show rs.length = 20+2*k by exact sharedRows_length k]
      omega
    unfold rowOrder rowR rowDigits sharedObservedA rowB rowA
    simp only [h,ite_false,rs,sharedRows_seed_at,fullRowOrder]
  have hj : j ≤ P^(12*k)*x^(2*k) := by
    unfold j
    have hj' : ((List.range (2*k)).map (fun i => rowOrder (18+i))).prod ≤ (P^6*x)^(2*k) := by
      have hrow (i : ℕ) (hi : i ∈ List.range (2*k)) : rowOrder (18+i) ≤ P^6*x := by
        have hi := List.mem_range.mp hi
        have h : 18 ≤ 18+i ∧ 18+i < (sharedRows k).length - 2 := by
          rw [sharedRows_length]
          omega
        change (rowR (sharedRows k) (18+i))^2 * sharedObservedA (sharedRows k) (18+i) *
          rowB (sharedRows k) (18+i) ≤ P^6*x
        unfold rowR rowDigits sharedObservedA rowB
        rw [if_pos h,Nat.mul_one,sharedRows_wang_at hi]
        exact sharedWangRow_order_le hi
      have hp (ls : List ℕ) (h : ∀ i ∈ ls, i ∈ List.range (2*k)) :
          (ls.map (fun i => rowOrder (18+i))).prod ≤ (P^6*x)^ls.length := by
        induction ls with
        | nil => simp
        | cons i ls ih =>
          rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
          exact Nat.mul_le_mul (hrow i (h i (by simp))) (ih (fun q hq => h q (by simp [hq])))
      simpa only [List.length_range] using hp (List.range (2*k)) (fun _ h => h)

    rw [mul_pow, ← pow_mul, show 6*(2*k)=12*k by omega] at hj'
    exact hj'
  have hsplit : rs.length = (18+2*k)+2 := by rw [show rs.length=20+2*k from sharedRows_length k]; omega
  have horder : sharedOrder rs = (1225*199*163*fixed*seeds)*j := by
    change 1225*199*163*((List.range rs.length).map rowOrder).prod = _
    rw [hsplit,List.range_add (n := 18+2*k),List.range_add (n := 18)]
    simp only [List.map_append,List.map_map,List.prod_append,hfix]
    change 1225*199*163*(fixed*j*((List.range 2).map (fun t => rowOrder (18+2*k+t))).prod)
      = (1225*199*163*fixed*seeds)*j
    rw [hseed]
    ac_rfl
  have hconst : 1225*199*163*fixed*seeds ≤ 2^1893 := by
    dsimp only [fixed,seeds]
    decide +kernel
  change sharedOrder rs ≤ 2^1893 * P^(12*k) * x^(2*k)
  rw [horder, Nat.mul_assoc (2^1893)]
  exact Nat.mul_le_mul hconst hj

private theorem sharedUsefulPool_primrec : Primrec sharedUsefulPool := by
  unfold sharedUsefulPool
  have hmem : PrimrecPred (fun z : ℕ × ℕ => z.2 ∈ sharedReservedPrimes) := by
    apply (someList (f := fun _ : ℕ × ℕ => sharedReservedPrimes) (p := fun z p => z.2 = p)
      (Primrec.const _) (by fun_prop)).of_eq
    intro z
    simp
  exact filterList (by fun_prop) ((nat_prime_primrec.comp Primrec.snd).and hmem.not)

private theorem sharedDigitPool_primrec : Primrec sharedDigitPool := by
  unfold sharedDigitPool
  exact filterList (by fun_prop) ((nat_prime_primrec.comp Primrec.snd).and (by fun_prop))

theorem sharedRows_primrec : Primrec sharedRows := by
  unfold sharedRows sharedWangRow
  have hu := sharedUsefulPool_primrec
  have hd := sharedDigitPool_primrec
  fun_prop

end
end TranslationTiling.FiniteCompiler.Packed
