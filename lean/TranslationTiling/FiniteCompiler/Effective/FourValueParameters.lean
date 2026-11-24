import TranslationTiling.FiniteCompiler.Effective.ConcreteSharedCRT

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective SharedCoordinates
open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000

def fourValueLow (k i : ℕ) : ℕ := (sharedDigitPool (4*k)).getD i 0

def fourValueOutput (k i j : ℕ) : ℕ := (sharedUsefulPool (4*k)).getD (4*i+j) 0

/-- A Wang row has a single prime for the low input and four primes for
its value outputs. The two shared, slope-dependent primes remain fixed. -/
def fourValueWangRow (k i : ℕ) : ℕ × ℕ × List ℕ :=
  (if i < k then 199 else 163,
    ((List.range 4).map fun j => fourValueOutput k i j).prod,
    [fourValueLow k i])

def fourValueRows (k : ℕ) : GuardedRows :=
  sharedFixedRows ++ (List.range (2*k)).map (fourValueWangRow k) ++ sharedSeedRows

@[simp] theorem fourValueRows_length (k : ℕ) : (fourValueRows k).length = 20+2*k := by
  simp [fourValueRows,sharedFixedRows,sharedSeedRows]
  omega

theorem fourValueRows_fixed_at {k i : ℕ} (hi : i < 18) :
    (fourValueRows k).getD i (0,0,[]) = sharedArithmeticRow i := by
  rw [fourValueRows, List.append_assoc]
  rw [List.getD_append _ _ _ _ (show i < sharedFixedRows.length by simpa [sharedFixedRows] using hi)]
  simp [sharedFixedRows,List.getD_eq_getElem?_getD,hi]

theorem fourValueRows_wang_at {k i : ℕ} (hi : i < 2*k) :
    (fourValueRows k).getD (18+i) (0,0,[]) = fourValueWangRow k i := by
  rw [fourValueRows, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (show sharedFixedRows.length ≤ 18+i by simp [sharedFixedRows])]
  simp only [sharedFixedRows,List.length_map,List.length_range,Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD,hi]

theorem fourValueRows_seed_at (k t : ℕ) :
    (fourValueRows k).getD (18+2*k+t) (0,0,[]) = sharedSeedRows.getD t (0,0,[]) := by
  rw [fourValueRows, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (show sharedFixedRows.length ≤ 18+2*k+t by simp [sharedFixedRows]; omega)]
  simp only [sharedFixedRows,List.length_map,List.length_range,
    show 18+2*k+t-18=2*k+t by omega]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp


private def outputTag {k : ℕ} (i : Fin (2*k)) (j : Fin 4) : SharedPrimeTag (4*k) :=
  .inr (.inl ⟨4*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩)

private def lowTag {k : ℕ} (i : Fin (2*k)) : SharedPrimeTag (4*k) :=
  .inr (.inr ⟨i.val,by have := i.isLt; omega⟩)

theorem fourValueLow_prime {k i : ℕ} (hi : i < 2*k) : (fourValueLow k i).Prime :=
  sharedPrimeAt_prime (4*k) (lowTag ⟨i,hi⟩)

theorem fourValueLow_le {k i : ℕ} (hi : i < 2*k) :
    fourValueLow k i ≤ sharedPrimeCap (4*k) :=
  sharedPrimeAt_le (4*k) (lowTag ⟨i,hi⟩)

theorem fourValueOutput_prime {k i j : ℕ} (hi : i < 2*k) (hj : j < 4) :
    (fourValueOutput k i j).Prime :=
  sharedPrimeAt_prime (4*k) (outputTag ⟨i,hi⟩ ⟨j,hj⟩)

theorem fourValueOutput_le {k i j : ℕ} (hi : i < 2*k) (hj : j < 4) :
    fourValueOutput k i j ≤ sharedPairCap (4*k) :=
  (sharedUsefulPool_facts
    (getD_mem_of_lt _ _ _ ((show 4*i+j < 2*(4*k) by omega).trans_le
      (sharedUsefulPool_length (4*k))))).2.2

theorem fourValueOutput_lt_low {k i j : ℕ} (hi : i < 2*k) (hj : j < 4) :
    200 * fourValueOutput k i j < fourValueLow k i := by
  have h := sharedDigitPool_facts
    (getD_mem_of_lt _ _ 0 ((show i < 6*(4*k) by omega).trans_le
      (sharedDigitPool_length (4*k))))
  exact (Nat.mul_le_mul_left 200 (fourValueOutput_le hi hj)).trans_lt h.2.1

theorem fourValueOutput_inj {k : ℕ} {i i' : Fin (2*k)} {j j' : Fin 4}
    (h : fourValueOutput k i j = fourValueOutput k i' j') : i = i' ∧ j = j' := by
  have he := sharedPrimeAt_injective (4*k) (show
    sharedPrimeAt (4*k) (outputTag i j) = sharedPrimeAt (4*k) (outputTag i' j') from h)
  have hn := congrArg Fin.val (Sum.inl.inj (Sum.inr.inj he))
  change 4*i.val+j.val = 4*i'.val+j'.val at hn
  have hj := j.isLt
  have hj' := j'.isLt
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

theorem fourValueOutput_not_reserved {k i j : ℕ} (hi : i < 2*k) (hj : j < 4) :
    fourValueOutput k i j ∉ sharedReservedPrimes :=
  (sharedUsefulPool_facts
    (getD_mem_of_lt _ _ _ ((show 4*i+j < 2*(4*k) by omega).trans_le
      (sharedUsefulPool_length (4*k))))).2.1

theorem fourValueLow_not_reserved {k i : ℕ} (hi : i < 2*k) :
    fourValueLow k i ∉ sharedReservedPrimes := by
  intro h
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp h
  have eq : sharedPrimeAt (4*k) (.inl ⟨j,hj⟩) =
      sharedPrimeAt (4*k) (lowTag ⟨i,hi⟩) := by
    change sharedReservedPrimes.getD j 0 = _
    rwa [List.getD_eq_getElem _ _ hj]
  have hu := sharedPrimeAt_injective (4*k) eq
  cases hu

theorem fourValueLow_inj {k i j : ℕ} (hi : i < 2*k) (hj : j < 2*k)
    (h : fourValueLow k i = fourValueLow k j) : i = j := by
  have he := sharedPrimeAt_injective (4*k) (show
    sharedPrimeAt (4*k) (lowTag ⟨i,hi⟩) = sharedPrimeAt (4*k) (lowTag ⟨j,hj⟩) from h)
  exact congrArg Fin.val (Sum.inr.inj (Sum.inr.inj he))

theorem fourValueLow_ne_output {k i j s : ℕ} (hi : i < 2*k) (hj : j < 2*k) (hs : s < 4) :
    fourValueLow k i ≠ fourValueOutput k j s := by
  intro h
  have he := sharedPrimeAt_injective (4*k) (show
    sharedPrimeAt (4*k) (lowTag ⟨i,hi⟩) = sharedPrimeAt (4*k) (outputTag ⟨j,hj⟩ ⟨s,hs⟩) from h)
  unfold lowTag outputTag at he
  have he' := Sum.inr.inj he
  cases he'


theorem fourValueOutputProduct_le {k i : ℕ} (hi : i < 2*k) :
    (fourValueWangRow k i).2.1 ≤ (sharedPairCap (4*k))^4 := by
  change ((List.range 4).map (fourValueOutput k i)).prod ≤ _
  have h (l : List ℕ) (hl : ∀ j ∈ l, j < 4) :
      (l.map (fourValueOutput k i)).prod ≤ (sharedPairCap (4*k))^l.length := by
    induction l with
    | nil => simp
    | cons j l ih =>
        rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
        exact Nat.mul_le_mul (fourValueOutput_le hi (hl j (by simp)))
          (ih fun q hq => hl q (by simp [hq]))
  simpa using h (List.range 4) (fun _ => List.mem_range.mp)

private theorem positive_combination {a b r : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) (h : a*b < r) : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u*a+v*b := by
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

theorem fourValueLow_representation {k i j : ℕ} (hi : i < 2*k) (hj : j < 4) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ fourValueLow k i =
      u*(fourValueWangRow k i).1 + v*fourValueOutput k i j := by
  let a := (fourValueWangRow k i).1
  have ha : a = 199 ∨ a = 163 := by dsimp [a,fourValueWangRow]; split <;> simp
  have hap : a.Prime := by rcases ha with h|h <;> rw [h] <;> decide
  have hares : a ∈ sharedReservedPrimes := by
    rcases ha with h|h <;> rw [h] <;> simp only [sharedReservedPrimes,List.mem_cons,true_or,or_true]
  have hane : a ≠ fourValueOutput k i j := fun e =>
    fourValueOutput_not_reserved hi hj (e ▸ hares)
  have ha200 : a ≤ 200 := by rcases ha with h|h <;> omega
  exact positive_combination hap (fourValueOutput_prime hi hj) hane
    ((Nat.mul_le_mul_right _ ha200).trans_lt (fourValueOutput_lt_low hi hj))


private def fullRowOrder (row : ℕ × ℕ × List ℕ) : ℕ :=
  row.2.2.prod^2 * row.1 * row.2.1

private theorem fourValueWangRow_order_le {k i : ℕ} (hi : i < 2*k) :
    ((fourValueWangRow k i).2.2.prod)^2*(fourValueWangRow k i).2.1 ≤
      (sharedPrimeCap (4*k))^6 := by
  let P := sharedPrimeCap (4*k)
  have hx : sharedPairCap (4*k) ≤ P := by unfold P sharedPrimeCap; omega
  rw [show P^6 = P^2*P^4 by rw [← pow_add]]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by
    simpa [fourValueWangRow] using fourValueLow_le hi) 2)
    ((fourValueOutputProduct_le hi).trans (Nat.pow_le_pow_left hx 4))

set_option maxHeartbeats 3500000 in
theorem fourValueRows_order_bound (k : ℕ) :
    sharedOrder (fourValueRows k) ≤
      2^1893 * (sharedPrimeCap (4*k))^(12*k) := by
  let rs := fourValueRows k
  let P := sharedPrimeCap (4*k)
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
    simp only [not_le.mpr h,false_and,ite_false,rs,fourValueRows_fixed_at h,fullRowOrder]
  have hseed : ((List.range 2).map (fun t => rowOrder (18+2*k+t))).prod = seeds := by
    unfold seeds
    apply congrArg List.prod
    apply List.map_congr_left
    intro t _
    have h : ¬ (18 ≤ 18+2*k+t ∧ 18+2*k+t < rs.length - 2) := by
      rw [show rs.length = 20+2*k by exact fourValueRows_length k]
      omega
    unfold rowOrder rowR rowDigits sharedObservedA rowB rowA
    simp only [h,ite_false,rs,fourValueRows_seed_at,fullRowOrder]
  have hj : j ≤ P^(12*k) := by
    unfold j
    have hj' : ((List.range (2*k)).map (fun i => rowOrder (18+i))).prod ≤ (P^6)^(2*k) := by
      have hrow (i : ℕ) (hi : i ∈ List.range (2*k)) : rowOrder (18+i) ≤ P^6 := by
        have hi := List.mem_range.mp hi
        have h : 18 ≤ 18+i ∧ 18+i < (fourValueRows k).length - 2 := by
          rw [fourValueRows_length]
          omega
        change (rowR (fourValueRows k) (18+i))^2 * sharedObservedA (fourValueRows k) (18+i) *
          rowB (fourValueRows k) (18+i) ≤ P^6
        unfold rowR rowDigits sharedObservedA rowB
        rw [if_pos h,Nat.mul_one,fourValueRows_wang_at hi]
        exact fourValueWangRow_order_le hi
      have hp (ls : List ℕ) (h : ∀ i ∈ ls, i ∈ List.range (2*k)) :
          (ls.map (fun i => rowOrder (18+i))).prod ≤ (P^6)^ls.length := by
        induction ls with
        | nil => simp
        | cons i ls ih =>
          rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
          exact Nat.mul_le_mul (hrow i (h i (by simp))) (ih (fun q hq => h q (by simp [hq])))
      simpa only [List.length_range] using hp (List.range (2*k)) (fun _ h => h)

    rw [← pow_mul, show 6*(2*k)=12*k by omega] at hj'
    exact hj'
  have hsplit : rs.length = (18+2*k)+2 := by rw [show rs.length=20+2*k from fourValueRows_length k]; omega
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
  change sharedOrder rs ≤ 2^1893 * P^(12*k)
  rw [horder]
  exact Nat.mul_le_mul hconst hj

@[fun_prop] theorem fourValueLow_primrec :
    Primrec (fun z : ℕ × ℕ => fourValueLow z.1 z.2) := by
  unfold fourValueLow
  have h := sharedDigitPool_primrec.comp (show Primrec (fun z : ℕ × ℕ => 4*z.1) by fun_prop)
  fun_prop

@[fun_prop] theorem fourValueOutput_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => fourValueOutput z.1 z.2.1 z.2.2) := by
  unfold fourValueOutput
  have h := sharedUsefulPool_primrec.comp (show Primrec (fun z : ℕ × ℕ × ℕ => 4*z.1) by fun_prop)
  fun_prop

@[fun_prop] theorem fourValueWangRow_primrec :
    Primrec (fun z : ℕ × ℕ => fourValueWangRow z.1 z.2) := by
  unfold fourValueWangRow
  have hp := product_primrec.comp (show Primrec (fun z : ℕ × ℕ =>
    (List.range 4).map (fourValueOutput z.1 z.2)) by fun_prop)
  fun_prop

@[fun_prop] theorem fourValueRows_primrec : Primrec fourValueRows := by
  unfold fourValueRows
  fun_prop


end
end TranslationTiling.FiniteCompiler.Packed
