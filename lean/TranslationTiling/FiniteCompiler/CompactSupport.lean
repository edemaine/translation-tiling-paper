import TranslationTiling.FiniteCompiler.CoreSupport
import TranslationTiling.FiniteCompiler.JointBounds
import TranslationTiling.FiniteCompiler.BudgetBounds

namespace TranslationTiling.FiniteCompiler.CompactSupport
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} (E : EncodingParameters T)

theorem joint_test_horizontal {W : LeanWang.TileSet} {m : ℕ} (code : JointSystem.Code W m)
    (E : EncodingParameters (JointSystem.system code)) {H : ℕ} (hb : Bound E H)
    (hS : ∀ n, ((JointSystem.system code).slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F∈JointSystem.testTiles code E) {g : Ambient E} (hg : g∈F) :
    g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact test_horizontal E hb hS hF hg
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    have hh : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [hh]

theorem budget_bound {C : ℕ} (hC : 256≤C) (hB : T.alphabet=3)
    (hp : BudgetPrimes E C) (hS : ∀ n, (T.slope n).natAbs≤16) : Bound E (C^16) := by
  have hM : residueModulus≤C := (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : residueModulus≤256).trans hC
  have hself : C≤C^16 := Nat.le_self_pow (by decide) _
  refine ⟨hM.trans hself,fun n => (hS n).trans ((by omega : 16≤C).trans hself),?_,?_⟩
  · intro n
    have hh : B E (.inl n)≤C^15 := by
      calc
        _ ≤ C^9*(C^3)^2 := Nat.mul_le_mul
          (BudgetSize.r_le_nine E hC hB hp _) (Nat.pow_le_pow_left (hp.2.2.2.1 n) 2)
        _ = _ := by ring
    calc
      _ ≤ C*C^15 := Nat.mul_le_mul (by omega) hh
      _ = _ := by ring
  · intro t
    have hh : B E (.inr t)≤C^12 := by
      calc
        _ ≤ C^4*(C^4)^2 := Nat.mul_le_mul
          (BudgetSize.seed_r_le E hp t) (Nat.pow_le_pow_left (hp.2.2.1 _) 2)
        _ = _ := by ring
    have hs : E.a (.inr (otherSeed t))≤3 := by rw [E.seed_a]; have := (otherSeed t).isLt; omega
    calc
      _ = (2*residueModulus^3)*(E.a (.inr (otherSeed t))*B E (.inr t)) := by ring
      _ ≤ (2*residueModulus^3)*(3*C^12) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hs hh)
      _ = (6*residueModulus^3)*C^12 := by ring
      _ ≤ C^4*C^12 := Nat.mul_le_mul_right _
        ((by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 6*residueModulus^3≤256^4).trans (Nat.pow_le_pow_left hC 4))
      _ = _ := by ring

end
end TranslationTiling.FiniteCompiler.CompactSupport
