import TranslationTiling.Compiler.SmallBudgetPrimeList

namespace TranslationTiling.Compiler.Size
open SmallBudgetCertificate
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem count_from_prefix (n k : ℕ)
    (hbound : ∀ q∈certifiedPrimes.take k, q≤n)
    (hlen : (certifiedPrimes.take k).length=k) : k≤Nat.primeCounting n := by
  have hn : (certifiedPrimes.take k).Nodup := certifiedPrimes_nodup.take
  rw [←hlen,←List.toFinset_card_of_nodup hn,
    ←Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro q hq
  have hmem := List.mem_toFinset.mp hq
  exact Nat.mem_primesLE.mpr ⟨hbound q hmem,
    certifiedPrimes_prime q (List.mem_of_mem_take hmem)⟩

private theorem useful_count_0 :
    285≤Nat.primeCounting 1920 ∧ 563≤Nat.primeCounting 4096 := by
  constructor
  · exact count_from_prefix 1920 285 (by decide) (by decide)
  · exact count_from_prefix 4096 563 (by decide) (by decide)

private theorem useful_count_1 :
    295≤Nat.primeCounting 2092 ∧ 583≤Nat.primeCounting 4464 := by
  constructor
  · exact count_from_prefix 2092 295 (by decide) (by decide)
  · exact count_from_prefix 4464 583 (by decide) (by decide)

private theorem useful_count_2 :
    330≤Nat.primeCounting 2302 ∧ 653≤Nat.primeCounting 4913 := by
  constructor
  · exact count_from_prefix 2302 330 (by decide) (by decide)
  · exact count_from_prefix 4913 653 (by decide) (by decide)

private theorem useful_count_3 :
    367≤Nat.primeCounting 2733 ∧ 727≤Nat.primeCounting 5832 := by
  constructor
  · exact count_from_prefix 2733 367 (by decide) (by decide)
  · exact count_from_prefix 5832 727 (by decide) (by decide)

private theorem useful_count_4 :
    406≤Nat.primeCounting 3215 ∧ 805≤Nat.primeCounting 6859 := by
  constructor
  · exact count_from_prefix 3215 406 (by decide) (by decide)
  · exact count_from_prefix 6859 805 (by decide) (by decide)

private theorem useful_count_5 :
    447≤Nat.primeCounting 3750 ∧ 887≤Nat.primeCounting 8000 := by
  constructor
  · exact count_from_prefix 3750 447 (by decide) (by decide)
  · exact count_from_prefix 8000 887 (by decide) (by decide)

private theorem useful_count_6 :
    490≤Nat.primeCounting 4341 ∧ 973≤Nat.primeCounting 9261 := by
  constructor
  · exact count_from_prefix 4341 490 (by decide) (by decide)
  · exact count_from_prefix 9261 973 (by decide) (by decide)

private theorem useful_count_7 :
    535≤Nat.primeCounting 4991 ∧ 1063≤Nat.primeCounting 10648 := by
  constructor
  · exact count_from_prefix 4991 535 (by decide) (by decide)
  · exact count_from_prefix 10648 1063 (by decide) (by decide)

private theorem useful_count_8 :
    582≤Nat.primeCounting 5703 ∧ 1157≤Nat.primeCounting 12167 := by
  constructor
  · exact count_from_prefix 5703 582 (by decide) (by decide)
  · exact count_from_prefix 12167 1157 (by decide) (by decide)

private theorem useful_count_9 :
    631≤Nat.primeCounting 6480 ∧ 1255≤Nat.primeCounting 13824 := by
  constructor
  · exact count_from_prefix 6480 631 (by decide) (by decide)
  · exact count_from_prefix 13824 1255 (by decide) (by decide)

private theorem useful_count_10 :
    682≤Nat.primeCounting 7324 ∧ 1357≤Nat.primeCounting 15625 := by
  constructor
  · exact count_from_prefix 7324 682 (by decide) (by decide)
  · exact count_from_prefix 15625 1357 (by decide) (by decide)

private theorem useful_count_11 :
    735≤Nat.primeCounting 8238 ∧ 1463≤Nat.primeCounting 17576 := by
  constructor
  · exact count_from_prefix 8238 735 (by decide) (by decide)
  · exact count_from_prefix 17576 1463 (by decide) (by decide)

private theorem useful_count_12 :
    790≤Nat.primeCounting 9226 ∧ 1573≤Nat.primeCounting 19683 := by
  constructor
  · exact count_from_prefix 9226 790 (by decide) (by decide)
  · exact count_from_prefix 19683 1573 (by decide) (by decide)

private theorem useful_count_13 :
    847≤Nat.primeCounting 10290 ∧ 1687≤Nat.primeCounting 21952 := by
  constructor
  · exact count_from_prefix 10290 847 (by decide) (by decide)
  · exact count_from_prefix 21952 1687 (by decide) (by decide)

private theorem useful_count_14 :
    906≤Nat.primeCounting 11432 ∧ 1805≤Nat.primeCounting 24389 := by
  constructor
  · exact count_from_prefix 11432 906 (by decide) (by decide)
  · exact count_from_prefix 24389 1805 (by decide) (by decide)

private theorem useful_count_15 :
    967≤Nat.primeCounting 12656 ∧ 1927≤Nat.primeCounting 27000 := by
  constructor
  · exact count_from_prefix 12656 967 (by decide) (by decide)
  · exact count_from_prefix 27000 1927 (by decide) (by decide)

private theorem useful_count_16 :
    968≤Nat.primeCounting 13964 ∧ 1929≤Nat.primeCounting 29791 := by
  constructor
  · exact count_from_prefix 13964 968 (by decide) (by decide)
  · exact count_from_prefix 29791 1929 (by decide) (by decide)

private theorem useful_caps_mono {a b : ℕ} (h : a≤b) :
    economicalUsefulCap a≤economicalUsefulCap b := by
  unfold economicalUsefulCap
  apply Nat.mul_le_mul h
  apply (Nat.le_nthRoot_iff (by decide : 2≠0)).mpr
  exact (Nat.pow_nthRoot_le (Or.inl (by decide))).trans h

private theorem count_interval (C lo hi : ℕ) (hlo : lo≤C) (hhi : C≤hi)
    (hc : hi+7≤Nat.primeCounting (asymmetricUsefulCap lo) ∧
      2*hi+7≤Nat.primeCounting (economicalUsefulCap lo)) :
    C+7≤Nat.primeCounting (asymmetricUsefulCap C) ∧
      2*C+7≤Nat.primeCounting (economicalUsefulCap C) := by
  have hu := useful_caps_mono hlo
  have hs : asymmetricUsefulCap lo≤asymmetricUsefulCap C :=
    Nat.div_le_div_right (Nat.mul_le_mul_left 15 hu)
  exact ⟨(by omega : C+7≤hi+7).trans (hc.1.trans (Nat.monotone_primeCounting hs)),
    (by omega : 2*C+7≤2*hi+7).trans (hc.2.trans (Nat.monotone_primeCounting hu))⟩

theorem small_useful_counts {C : ℕ} (hC : 256≤C) :
    C+7≤Nat.primeCounting (asymmetricUsefulCap C) ∧
      2*C+7≤Nat.primeCounting (economicalUsefulCap C) := by
  by_cases hbig : 962≤C
  · exact ⟨asymmetric_useful_count hbig,(economical_caps hbig).2.2.1⟩
  by_cases h0 : C≤278
  · apply count_interval C 256 278 (by omega) h0
    have hr : Nat.nthRoot 2 256=16 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_0 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h1 : C≤288
  · apply count_interval C 279 288 (by omega) h1
    have hr : Nat.nthRoot 2 279=16 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_1 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h2 : C≤323
  · apply count_interval C 289 323 (by omega) h2
    have hr : Nat.nthRoot 2 289=17 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_2 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h3 : C≤360
  · apply count_interval C 324 360 (by omega) h3
    have hr : Nat.nthRoot 2 324=18 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_3 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h4 : C≤399
  · apply count_interval C 361 399 (by omega) h4
    have hr : Nat.nthRoot 2 361=19 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_4 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h5 : C≤440
  · apply count_interval C 400 440 (by omega) h5
    have hr : Nat.nthRoot 2 400=20 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_5 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h6 : C≤483
  · apply count_interval C 441 483 (by omega) h6
    have hr : Nat.nthRoot 2 441=21 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_6 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h7 : C≤528
  · apply count_interval C 484 528 (by omega) h7
    have hr : Nat.nthRoot 2 484=22 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_7 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h8 : C≤575
  · apply count_interval C 529 575 (by omega) h8
    have hr : Nat.nthRoot 2 529=23 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_8 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h9 : C≤624
  · apply count_interval C 576 624 (by omega) h9
    have hr : Nat.nthRoot 2 576=24 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_9 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h10 : C≤675
  · apply count_interval C 625 675 (by omega) h10
    have hr : Nat.nthRoot 2 625=25 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_10 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h11 : C≤728
  · apply count_interval C 676 728 (by omega) h11
    have hr : Nat.nthRoot 2 676=26 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_11 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h12 : C≤783
  · apply count_interval C 729 783 (by omega) h12
    have hr : Nat.nthRoot 2 729=27 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_12 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h13 : C≤840
  · apply count_interval C 784 840 (by omega) h13
    have hr : Nat.nthRoot 2 784=28 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_13 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h14 : C≤899
  · apply count_interval C 841 899 (by omega) h14
    have hr : Nat.nthRoot 2 841=29 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_14 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  by_cases h15 : C≤960
  · apply count_interval C 900 960 (by omega) h15
    have hr : Nat.nthRoot 2 900=30 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
    convert useful_count_15 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]
  apply count_interval C 961 961 (by omega) (by omega)
  have hr : Nat.nthRoot 2 961=31 := Nat.nthRoot_eq_of_le_of_lt (by norm_num) (by norm_num)
  convert useful_count_16 using 1 <;> norm_num [asymmetricUsefulCap,economicalUsefulCap,hr]


theorem small_asymmetric_useful_count {C : ℕ} (hC : 256≤C) :
    C+7≤Nat.primeCounting (asymmetricUsefulCap C) := (small_useful_counts hC).1

theorem small_useful_caps {C : ℕ} (hC : 256≤C) :
    let U := economicalUsefulCap C
    U^2≤C^3 ∧ U≤C^2 ∧ 2*C+7≤Nat.primeCounting U := by
  have hr : (Nat.nthRoot 2 C)^2≤C := Nat.pow_nthRoot_le (Or.inl (by decide))
  refine ⟨?_,?_,(small_useful_counts hC).2⟩
  · unfold economicalUsefulCap
    nlinarith [Nat.mul_le_mul_left (C^2) hr]
  · unfold economicalUsefulCap
    have hh : Nat.nthRoot 2 C≤C := by nlinarith
    nlinarith

def smallSeedPrime0 : ℕ := 511237
def smallSeedPrime1 : ℕ := 511243
theorem smallSeedPrime0_prime : smallSeedPrime0.Prime := by norm_num [smallSeedPrime0]
theorem smallSeedPrime1_prime : smallSeedPrime1.Prime := by norm_num [smallSeedPrime1]

end
end TranslationTiling.Compiler.Size
