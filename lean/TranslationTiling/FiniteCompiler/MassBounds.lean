import TranslationTiling.FiniteCompiler.FixedBounds
import TranslationTiling.FiniteCompiler.CoreMassBounds

/-! Count the actual finite fibres of the test tiles, instead of their boxes. -/
namespace TranslationTiling.FiniteCompiler.MassSize
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} (E : EncodingParameters T)

theorem mass_bound (hB : T.alphabet=3) (hp : BudgetPrimes E (primeBudget T)) :
    mass E≤(primeBudget T)^(12*T.width+20) := by
  let P := primeBudget T
  have hP : 256≤P := le_max_right _ _
  have ho (n : Column T) : E.r (.inl n)*(E.a (.inl n)*E.b (.inl n))≤P^12 := by
    calc
      _ ≤ P^9*P^3 := Nat.mul_le_mul (BudgetSize.r_le_nine E hP hB hp _) (hp.2.2.2.1 n)
      _ = _ := by ring
  have hs (t : Fin 2) : E.r (.inr t)*(E.a (.inr t)*E.b (.inr t))≤P^8 := by
    calc
      _ ≤ P^4*P^4 := Nat.mul_le_mul (BudgetSize.seed_r_le E hp t) (hp.2.2.1 _)
      _ = _ := by ring
  unfold mass
  rw [Fintype.prod_sum_type]
  calc
    _ ≤ (P^2)^2*((∏ _n : Column T, P^12)*(∏ _t : Fin 2, P^8)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (EconomicalSize.seedModulus_le_square hP) 2)
        (Nat.mul_le_mul (Finset.prod_le_prod (fun n _ => ho n)) (Finset.prod_le_prod (fun t _ => hs t)))
    _ = _ := by simp [Column,←pow_mul,←pow_add]; congr 1; ring
end
end TranslationTiling.FiniteCompiler.MassSize
