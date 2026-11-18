import TranslationTiling.FiniteCompiler.JointBounds
import TranslationTiling.FiniteCompiler.BudgetBounds

namespace TranslationTiling.FiniteCompiler.CompactSupport
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} (E : EncodingParameters T)

def A (i : Channel T) : ℕ := E.r i*E.a i*E.b i

theorem ordinary_bound (hS : ∀ n, (T.slope n).natAbs≤16) (n : Column T)
    (j : ActivationIndex E (.inl n)) :
    (ordinaryOffset E n j).1.natAbs≤32*(A E (.inl n))^2 ∧
    (ordinaryOffset E n j).2.natAbs≤32*(A E (.inl n))^2 := by
  have hc : activationIndexCode E (.inl n) j+1≤2*A E (.inl n) := activationIndexCode_lt E _ j
  have hf : (ordinaryFirst E n j).natAbs≤2*(A E (.inl n))^2 := by
    have hh := Size.separated_natAbs_le (activationModulus E (.inl n))
      (activationResidue E (.inl n)) (activationIndexCode E (.inl n)) j (Nat.le_refl _)
    have hm := Nat.mul_le_mul_left (A E (.inl n)) hc
    change (ordinaryFirst E n j).natAbs≤activationModulus E (.inl n)*(activationIndexCode E (.inl n) j+1) at hh
    change (ordinaryFirst E n j).natAbs≤A E (.inl n)*(activationIndexCode E (.inl n) j+1) at hh
    nlinarith only [hh,hm]
  constructor
  · exact hf.trans (by nlinarith)
  · change (-T.slope n*ordinaryFirst E n j).natAbs≤_
    rw [Int.natAbs_mul,Int.natAbs_neg]
    exact (Nat.mul_le_mul (hS n) hf).trans (by ring_nf; rfl)

theorem seed_bound (t : Fin 2) (j : SeedActivationIndex E t) :
    (seedOffset E t j).1.natAbs≤2*E.a (.inr (otherSeed t))*(A E (.inr t))^2*residueModulus^3 ∧
    (seedOffset E t j).2.natAbs≤residueModulus := by
  have hc : seedActivationIndexCode E t j+1≤2*A E (.inr t)*residueModulus^2 := seedActivationIndexCode_lt E t j
  have hh := Size.separated_natAbs_le (seedModulus E t) (seedActivationResidue E t)
    (seedActivationIndexCode E t) j (Nat.le_refl _)
  have hm := Nat.mul_le_mul_left (seedModulus E t) hc
  refine ⟨?_,?_⟩
  · change (seedFirst E t j).natAbs≤_ at hh
    apply hh.trans
    apply hm.trans_eq
    unfold seedModulus activationModulus A
    ring
  · exact (ZMod.val_lt j.2.2).le

structure Bound (H : ℕ) : Prop where
  modulus : residueModulus≤H
  slope : ∀ n, (T.slope n).natAbs≤H
  ordinary : ∀ n, 32*(A E (.inl n))^2≤H
  seed : ∀ t, 2*E.a (.inr (otherSeed t))*(A E (.inr t))^2*residueModulus^3≤H

theorem test_horizontal {H : ℕ} (hb : Bound E H)
    (hS : ∀ n, (T.slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F ∈ testTiles E) {g : Ambient E} (hg : g ∈ F) :
    g.1.1.natAbs ≤ H ∧ g.1.2.natAbs ≤ H := by
  have hzero : (0 : ℤ).natAbs ≤ H := Nat.zero_le _
  have hb2 : 2≤H := (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 2≤residueModulus).trans hb.modulus
  have hq (h : q0 E g = 0) : g.1 = 0 := congrArg Prod.fst h
  have hoff {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T)
      (labels : ∀ j, Label T (cycle j)) (hf : F ∈ fixedCycleTiles E cycle labels) : g.1 = 0 := by
    obtain rfl := Finset.mem_singleton.mp hf
    exact congrArg Prod.fst ((mem_offsetTile E _ _).mp hg)
  rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n, rfl⟩ | ⟨t, rfl⟩
  · rw [hq ((mem_kernelTile E g).mp hg)]
    exact ⟨hzero, hzero⟩
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hF
    rcases (mem_invarianceTile E _ _ g).mp hg with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hq h]; exact ⟨hzero, hzero⟩
    · have hh := congrArg Prod.fst h
      change g.1 = (dependenceShift E d).1 at hh
      rw [hh]
      cases d with
      | inl d => exact ⟨hzero, hzero⟩
      | inr d =>
        cases d with
        | inl n =>
          change (1 : ℤ).natAbs ≤ _ ∧ (-T.slope n).natAbs ≤ _
          have hn := hb.slope n
          simpa using And.intro (by omega : 1 ≤ H) hn
        | inr d =>
          rcases d with ⟨t, axis⟩
          cases axis <;> simpa [dependenceShift, seedStep] using
            And.intro hb.modulus hzero
  · obtain ⟨w, _, hF⟩ := Finset.mem_biUnion.mp hF
    rw [hoff _ _ hF]
    exact ⟨hzero, hzero⟩
  · obtain ⟨q, _, hF⟩ := Finset.mem_biUnion.mp hF
    rw [hoff _ _ hF]
    exact ⟨hzero, hzero⟩
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact ⟨(ordinary_bound E hS n j).1.trans (hb.ordinary n),(ordinary_bound E hS n j).2.trans (hb.ordinary n)⟩
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact ⟨(seed_bound E t j).1.trans (hb.seed t),(seed_bound E t j).2.trans hb.modulus⟩

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
    (hp : BudgetPrimes E C) (hS : ∀ n, (T.slope n).natAbs≤16) : Bound E (C^25) := by
  have h1 : 1≤C := by omega
  have hM : residueModulus≤C := (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : residueModulus≤256).trans hC
  have hself : C≤C^25 := Nat.le_self_pow (by decide) _
  refine ⟨hM.trans hself,fun n => (hS n).trans ((by omega : 16≤C).trans hself),?_,?_⟩
  · intro n
    have ha : A E (.inl n)≤C^12 := by
      calc
        _ = E.r (.inl n)*(E.a (.inl n)*E.b (.inl n)) := by unfold A; ring
        _ ≤ C^9*C^3 := Nat.mul_le_mul (BudgetSize.r_le_nine E hC hB hp _) (hp.2.2.2.1 n)
        _ = _ := by ring
    calc
      _ ≤ C*(C^12)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left ha 2)
      _ = _ := by ring
  · intro t
    have ha : A E (.inr t)≤C^8 := by
      calc
        _ = E.r (.inr t)*(E.a (.inr t)*E.b (.inr t)) := by unfold A; ring
        _ ≤ C^4*C^4 := Nat.mul_le_mul (BudgetSize.seed_r_le E hp t) (hp.2.2.1 _)
        _ = _ := by ring
    have hs : E.a (.inr (otherSeed t))≤3 := by rw [E.seed_a]; have := (otherSeed t).isLt; omega
    calc
      _ = (2*residueModulus^3)*(E.a (.inr (otherSeed t))*(A E (.inr t))^2) := by ring
      _ ≤ (2*residueModulus^3)*(3*(C^8)^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hs (Nat.pow_le_pow_left ha 2))
      _ = 6*residueModulus^3*(C^8)^2 := by ring
      _ ≤ C^4*(C^8)^2 := Nat.mul_le_mul_right _
        ((by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 6*residueModulus^3≤256^4).trans (Nat.pow_le_pow_left hC 4))
      _ = C^20 := by ring
      _ ≤ _ := Nat.pow_le_pow_right h1 (by decide)

end
end TranslationTiling.FiniteCompiler.CompactSupport
