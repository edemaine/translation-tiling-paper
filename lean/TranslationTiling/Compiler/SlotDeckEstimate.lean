import TranslationTiling.Compiler.SlotBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open scoped BigOperators

theorem slot_radix_le_four_pow {m w : ℕ} (hw : w ≤ m) :
    slotRadix m w ≤ 4^m := by
  let f (j : ℕ) := m.choose j * 3^j
  calc
    slotRadix m w ≤ ∑ j ∈ Finset.range (m+1), f j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_range.mpr (by omega))
    _ = 4^m := by
      simpa [f,mul_comm] using (add_pow (3 : ℕ) 1 m).symm

theorem slot_digit_capacity_upper {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    (slotRadix (4*t) (3*t))^(slotPackedDigits n t) ≤ n*4^(4*t) := by
  let D := slotRadix (4*t) (3*t)
  let k := slotPackedDigits n t
  have hk : 1 ≤ k := le_max_left ..
  have hD : 1 < D := slotRadix_one_lt ht
  have he : k-1 = Nat.clog D n-1 := by unfold k slotPackedDigits D; omega
  have hp : D^(k-1) ≤ n := by
    rw [he]
    by_cases h : 1 < n
    · exact (Nat.pow_pred_clog_lt_self hD h).le
    · have : n = 1 := by omega
      simp [this]
  change D^k ≤ _
  calc
    D^k = D^(k-1)*D := by rw [← pow_succ, Nat.sub_add_cancel hk]
    _ ≤ _ := Nat.mul_le_mul hp (slot_radix_le_four_pow (by omega))

/-- The unrefined guarded tests contribute quadratically in the
alphabet size. The remaining tests fit in the same polynomial budget. -/
theorem slot_deck_cap_polynomial (k m D n : ℕ)
    (hn : 1 ≤ n) (hk : k ≤ n) (hm : m ≤ n) (hkm : k*m ≤ n)
    (he : 2^m ≤ n) (hD : D ≤ n^3) :
    slotDeckCap k m D ≤ (4000+arithmeticBaseline.length)*n^6 := by
  have h1 : 20*(2*k*m+4*m) ≤ 120*n := by nlinarith only [hm,hkm]
  have h2 : 6*k*m+2*m ≤ 8*n := by nlinarith only [hm,hkm]
  have h3 : 21+2*k*m+4*m ≤ 27*n := by nlinarith only [hm,hkm,hn]
  have h4 : 2*k*2^m ≤ 2*n*n := Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) he
  have h5 := Nat.mul_le_mul h2 h3
  have h6 := Nat.mul_le_mul_left 72 (Nat.pow_le_pow_left hD 2)
  have h16 : 1 ≤ n^6 := by
    simpa using Nat.pow_le_pow_left hn 6
  have hn6 : n ≤ n^6 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < n) (show 1 ≤ 6 by decide)
  have hn26 : n^2 ≤ n^6 := Nat.pow_le_pow_right (by omega : 0 < n) (by decide)
  unfold slotDeckCap
  have ha := Nat.mul_le_mul_left arithmeticBaseline.length h16
  change 2600 + arithmeticBaseline.length + _ + _ + _ + _ ≤ _
  nlinarith only [h1,h4,h5,h6,h16,hn6,hn26,ha]

end TranslationTiling.Compiler.Size
