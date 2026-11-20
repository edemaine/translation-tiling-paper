import TranslationTiling.FiniteCompiler.EncodedSystem

namespace TranslationTiling.FiniteCompiler.CompactSupport

variable [SeedFrame]
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

def A (i : Channel T) : ℕ := E.r i*E.a i*E.b i

def B (i : Channel T) : ℕ := E.r i*(E.a i*E.b i)^2

private theorem separated_natAbs_le {J : Type*} (M : ℕ) [NeZero M]
    (v : J → ZMod M) (code : J → ℕ) (j : J) :
    (separatedResidueLift M v code j).natAbs≤M*(code j+1) := by
  have hv := ZMod.val_lt (v j)
  have he : separatedResidueLift M v code j=((v j).val+M*code j : ℕ) := by
    simp [separatedResidueLift,Nat.cast_add,Nat.cast_mul]
  rw [he,Int.natAbs_natCast]
  nlinarith

theorem ordinary_bound (hS : ∀ n, (T.slope n).natAbs≤16) (n : Column T)
    (j : ActivationIndex E (.inl n)) :
    (ordinaryOffset E n j).1.natAbs≤32*B E (.inl n) ∧
    (ordinaryOffset E n j).2.natAbs≤32*B E (.inl n) := by
  have hc : ordinaryLiftCode E n j+1≤2*(E.a (.inl n)*E.b (.inl n)) :=
    ordinaryLiftCode_sharp_lt E n j
  have hf : (ordinaryFirst E n j).natAbs≤2*B E (.inl n) := by
    have hh := separated_natAbs_le (activationModulus E (.inl n))
      (ordinaryResidue E n) (ordinaryLiftCode E n) j
    have hm := Nat.mul_le_mul_left (A E (.inl n)) hc
    change (ordinaryFirst E n j).natAbs≤A E (.inl n)*(ordinaryLiftCode E n j+1) at hh
    dsimp [A,B] at hh hm ⊢
    nlinarith only [hh,hm]
  constructor
  · exact hf.trans (by nlinarith)
  · change (-T.slope n*ordinaryFirst E n j).natAbs≤_
    rw [Int.natAbs_mul,Int.natAbs_neg]
    exact (Nat.mul_le_mul (hS n) hf).trans (by ring_nf; rfl)

theorem seed_bound (t : Fin 2) (j : SeedActivationIndex E t) :
    (seedOffset E t j).1.natAbs≤2*E.a (.inr (otherSeed t))*B E (.inr t)*residueModulus^3 ∧
    (seedOffset E t j).2.natAbs≤residueModulus := by
  have hc : seedActivationIndexCode E t j+1≤2*(E.a (.inr t)*E.b (.inr t))*residueModulus^2 := seedActivationIndexCode_sharp_lt E t j
  have hh := separated_natAbs_le (seedModulus E t) (seedActivationResidue E t)
    (seedActivationIndexCode E t) j
  have hm := Nat.mul_le_mul_left (seedModulus E t) hc
  refine ⟨?_,?_⟩
  · change (seedFirst E t j).natAbs≤_ at hh
    apply hh.trans
    apply hm.trans_eq
    unfold seedModulus activationModulus B
    ring
  · exact (ZMod.val_lt j.2.2).le

structure Bound (H : ℕ) : Prop where
  modulus : residueModulus≤H
  slope : ∀ n, (T.slope n).natAbs≤H
  ordinary : ∀ n, 32*B E (.inl n)≤H
  seed : ∀ t, 2*E.a (.inr (otherSeed t))*B E (.inr t)*residueModulus^3≤H

theorem test_horizontal {H : ℕ} (hb : Bound E H)
    (hS : ∀ n, (T.slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F ∈ testTiles E) {g : Ambient E} (hg : g ∈ F) :
    g.1.1.natAbs ≤ H ∧ g.1.2.natAbs ≤ H := by
  have hzero : (0 : ℤ).natAbs ≤ H := Nat.zero_le _
  have hb2 : 2≤H := residueModulus_two_le.trans hb.modulus
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

end
end TranslationTiling.FiniteCompiler.CompactSupport
