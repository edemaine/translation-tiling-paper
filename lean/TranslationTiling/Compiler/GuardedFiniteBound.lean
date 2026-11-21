import TranslationTiling.Compiler.GuardedLogBound
import TranslationTiling.FiniteCompiler.PackedExtendedProfiles

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size

noncomputable section

set_option exponentiation.threshold 20000

/-- Choose primes by alphabet capacity, using the same guarded reduction in every row. -/
def guardedProfile (n : ℕ) : CheckedProfile :=
  if n ≤ 1 then checked1
  else if n ≤ 12 then checked12
  else if n ≤ 15 then checked15
  else if n ≤ 36 then checked36
  else if n ≤ 242 then checked243
  else if n ≤ 19683 then checked19683
  else checked10460353203

theorem guardedProfile_capacity {n : ℕ} (hn : n ≤ 3^21) :
    n ≤ (guardedProfile n).profile.radices.prod := by
  unfold guardedProfile
  split_ifs with h1 h12 h15 h36 h243 h19683
  · exact h1
  · exact h12
  · exact h15
  · exact h36
  · exact h243.trans (by decide : 242 ≤ 243)
  · exact h19683
  · exact hn

theorem guardedProfile_bound (n : ℕ) :
    ((2^(guardedProfile (max 1 n)).exponent : ℕ) : ℝ) ≤ guardedBound n := by
  have hbudget (d : ℕ) (hd : d ≤ 2392) : ((2^d : ℕ) : ℝ) ≤ guardedBound n := by
    apply le_trans _ (le_max_right _ _)
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hd
  have hlog (m a b : ℕ) (hm : m ≤ n) (h : (2 : ℝ)^a ≤ ((m : ℝ)+4)^b) :
      (2 : ℝ)^a ≤ ((n : ℝ)+4)^b := by
    exact h.trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.add_le_add_right hm 4)) b)
  unfold guardedProfile
  split_ifs with h1 h12 h15 h36 h243 h19683
  · exact hbudget 2112 (by decide)
  · exact hbudget 2392 (by decide)
  · exact guarded_bound_dyadic (a:=94) (b:=23) (c:=67) (d:=33)
      (by decide) (by decide) (hlog 13 94 23 (by omega) (by norm_num))
      (by norm_num) (by decide) (by change (2438 : ℝ) ≤ _; norm_num)
  · exact guarded_bound_dyadic (a:=69) (b:=16) (c:=21) (d:=10)
      (by decide) (by decide) (hlog 16 69 16 (by omega) (by norm_num))
      (by norm_num) (by decide) (by change (2573 : ℝ) ≤ _; norm_num)
  · exact guarded_bound_dyadic (a:=5) (b:=1) (c:=2) (d:=1)
      (by decide) (by decide) (hlog 37 5 1 (by omega) (by norm_num))
      (by norm_num) (by decide) (by change (2876 : ℝ) ≤ _; norm_num)
  · exact guarded_bound_dyadic (a:=7) (b:=1) (c:=2) (d:=1)
      (by decide) (by decide) (hlog 243 7 1 (by omega) (by norm_num))
      (by norm_num) (by decide) (by change (3594 : ℝ) ≤ _; norm_num)
  · exact guarded_bound_dyadic (a:=14) (b:=1) (c:=3) (d:=1)
      (by decide) (by decide) (hlog 19684 14 1 (by omega) (by norm_num))
      (by norm_num) (by decide) (by change (5954 : ℝ) ≤ _; norm_num)

end
end TranslationTiling.FiniteCompiler.Packed
