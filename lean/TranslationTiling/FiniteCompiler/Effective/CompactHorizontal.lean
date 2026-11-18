import TranslationTiling.FiniteCompiler.Effective.SmallMetrics

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def compactHorizontal (d : ParameterData) : ℕ :=
  if d.1=48 ∧ d.2.1=3 then SmallProfiles.horizontal48 else
  if d.1=64 ∧ d.2.1=3 then SmallProfiles.horizontal64 else
  if d.1=80 ∧ d.2.1=3 then SmallProfiles.horizontal80 else
  if d.1=96 ∧ d.2.1=3 then SmallProfiles.horizontal96 else
  if d.1=112 ∧ d.2.1=3 then SmallProfiles.horizontal112 else
  (max (d.1+2) 256)^16

@[fun_prop] theorem compactHorizontal_primrec : Primrec compactHorizontal := by
  unfold compactHorizontal
  fun_prop

theorem compactHorizontal_small (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3) :
    compactHorizontal (parameterData T)=SmallProfiles.horizontal i := by
  fin_cases i <;> simp [compactHorizontal,parameterData,hw,hB,SmallProfiles.width,SmallProfiles.horizontal]

theorem compactHorizontal_le (T : System) : compactHorizontal (parameterData T)≤primeBudget T^16 := by
  have hC : 256≤primeBudget T := le_max_right _ _
  unfold compactHorizontal parameterData
  split_ifs <;> first | rfl |
    exact (by norm_num [SmallProfiles.horizontal48,SmallProfiles.horizontal64,
      SmallProfiles.horizontal80,SmallProfiles.horizontal96,SmallProfiles.horizontal112] : _≤256^16).trans
      (Nat.pow_le_pow_left hC 16)

theorem compactHorizontal_support (T : System) (hB : T.alphabet=3)
    (hS : ∀ n, (T.slope n).natAbs≤16) :
    CompactSupport.Bound (parameters T) (compactHorizontal (parameterData T)) := by
  unfold compactHorizontal parameterData
  split_ifs with h0 h1 h2 h3 h4
  · exact parameters_small_support T 0 h0.1 hB hS
  · exact parameters_small_support T 1 h1.1 hB hS
  · exact parameters_small_support T 2 h2.1 hB hS
  · exact parameters_small_support T 3 h3.1 hB hS
  · exact parameters_small_support T 4 h4.1 hB hS
  · exact CompactSupport.budget_bound (parameters T) (le_max_right _ _) hB
      (parameters_bounded_budget T hB) hS

end
end TranslationTiling.FiniteCompiler.Effective
