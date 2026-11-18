import TranslationTiling.FiniteCompiler.Parameters
import TranslationTiling.FiniteCompiler.EncodedSystem
import TranslationTiling.FiniteCompiler.CyclicFactorCRT
import TranslationTiling.Compiler.ClosedSupportBound
import Mathlib.Tactic.GCongr

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler.Size

open scoped Classical BigOperators
noncomputable section

def pairCap (b : ℕ) : ℕ := b * b + 2 * b
def indexCap (b : ℕ) : ℕ := pairCap (pairCap (pairCap (pairCap b)))
def horizontalCap (b : ℕ) : ℕ := b * (b ^ 5 * (indexCap b + 1) + 1)


/-- Iterating the square-pair bound has an exact closed form. -/
theorem indexCap_add_one (b : ℕ) : indexCap b+1=(b+1)^16 := by
  unfold indexCap pairCap
  ring

theorem horizontalCap_eq (b : ℕ) : horizontalCap b=b^6*(b+1)^16+b := by
  unfold horizontalCap
  rw [indexCap_add_one]
  ring

theorem horizontalCap_le_factor {b : ℕ} (hb : 2≤b) : horizontalCap b≤658*b^22 := by
  have hp := Nat.pow_le_pow_left (show 2*(b+1)≤3*b by omega) 16
  simp only [mul_pow] at hp
  have hself : b≤b^22 := Nat.le_self_pow (by decide) _
  have hh : 2^16*horizontalCap b≤2^16*(658*b^22) := by
    calc
      _ = b^6*(2^16*(b+1)^16)+2^16*b := by rw [horizontalCap_eq]; ring
      _ ≤ b^6*(3^16*b^16)+2^16*b^22 := Nat.add_le_add (Nat.mul_le_mul_left _ hp)
        (Nat.mul_le_mul_left _ hself)
      _ = (3^16+2^16)*b^22 := by ring
      _ ≤ (2^16*658)*b^22 := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by ring
  exact (Nat.mul_le_mul_left_iff (by decide : 0<2^16)).mp hh

theorem horizontalCap_channel_le {C : ℕ} (hC : 962≤C) : horizontalCap (C^12)≤C^265 := by
  calc
    _ ≤ 658*(C^12)^22 := horizontalCap_le_factor ((by omega : 2≤C).trans (Nat.le_self_pow (by decide) _))
    _ ≤ C*(C^12)^22 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem horizontalCap_channel_nine_le {C : ℕ} (hC : 256≤C) : horizontalCap (C^9)≤C^200 := by
  calc
    _ ≤ 658*(C^9)^22 := horizontalCap_le_factor ((by omega : 2≤C).trans (Nat.le_self_pow (by decide) _))
    _ ≤ C^2*(C^9)^22 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = _ := by ring

theorem le_horizontalCap (b : ℕ) : b ≤ horizontalCap b := by
  unfold horizontalCap
  calc
    b = b * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left b (Nat.succ_pos _)

theorem payload_le_horizontalCap {b : ℕ} (hb : 1 ≤ b) :
    b ^ 5 * (indexCap b + 1) ≤ horizontalCap b := by
  let x := b ^ 5 * (indexCap b + 1)
  calc
    x = 1 * x := by omega
    _ ≤ b * x := Nat.mul_le_mul_right x hb
    _ ≤ b * (x + 1) := Nat.mul_le_mul_left b (Nat.le_succ x)

theorem le_pairCap (b : ℕ) : b ≤ pairCap b := by unfold pairCap; omega

theorem pairCap_mono {a b : ℕ} (h : a ≤ b) : pairCap a ≤ pairCap b := by
  unfold pairCap
  gcongr

theorem pair_le_cap {x y b : ℕ} (hx : x ≤ b) (hy : y ≤ b) : Nat.pair x y ≤ pairCap b := by
  have hxx : x * x ≤ b * b := Nat.mul_le_mul hx hx
  have hyy : y * y ≤ b * b := Nat.mul_le_mul hy hy
  unfold Nat.pair pairCap
  split_ifs <;> omega

structure ParameterBudget {T : System} (E : EncodingParameters T) (b : ℕ) : Prop where
  two : 2 ≤ b
  width : residueModulus ≤ b
  r : ∀ i, E.r i ≤ b
  a : ∀ i, E.a i ≤ b
  usefulB : ∀ i, E.b i ≤ b
  slope : ∀ n, (T.slope n).natAbs ≤ b

variable {T : System} {E : EncodingParameters T} {b : ℕ}

theorem activation_code_le (hb : ParameterBudget E b) (i : Channel T)
    (j : ActivationIndex E i) : activationIndexCode E i j ≤ pairCap (pairCap (pairCap b)) := by
  have hd : j.2.2.val ≤ b := by
    have hb2 := hb.two
    have h := j.2.2.isLt
    have hm : shiftMultiplicity (E.a i) (E.b i) j.2.1 ≤ 2 := by
      unfold shiftMultiplicity
      split_ifs <;> omega
    omega
  have hk := (ZMod.val_lt j.1).le.trans (hb.r i)
  have ha := (ZMod.val_lt j.2.1.1).le.trans (hb.a i)
  have hc := (ZMod.val_lt j.2.1.2).le.trans (hb.usefulB i)
  have hp {base u x c : ℕ} (hbase : base≤c) (hu : u≤c) (hx : x≤c) :
      CompactIndex.pack base u x≤pairCap c := by
    have hm := Nat.mul_le_mul hbase hu
    unfold CompactIndex.pack pairCap
    nlinarith
  have h1 := hp (hb.a i) hk ha
  have h2 := hp ((hb.usefulB i).trans (le_pairCap b)) h1 (hc.trans (le_pairCap b))
  exact hp ((hb.two.trans (le_pairCap b)).trans (le_pairCap _)) h2
    ((hd.trans (le_pairCap b)).trans (le_pairCap _))

theorem seed_code_le (hb : ParameterBudget E b) (t : Fin 2)
    (j : SeedActivationIndex E t) : seedActivationIndexCode E t j ≤ indexCap b := by
  have hprod : E.r (.inr t)*E.a (.inr t)*E.b (.inr t)*residueModulus^2≤b^5 := by
    calc
      _ ≤ b*b*b*b^2 := by gcongr <;> first | exact hb.r _ | exact hb.a _ | exact hb.usefulB _ | exact hb.width
      _ = _ := by ring
  have hcode : seedActivationIndexCode E t j≤2*b^5 := by
    have hc := seedActivationIndexCode_lt E t j
    nlinarith only [hc,hprod]
  have hcap : b ^ 16 ≤ indexCap b := by
    unfold indexCap pairCap
    ring_nf
    omega
  apply hcode.trans
  apply (show 2*b^5≤b^6 from ?_).trans
    ((Nat.pow_le_pow_right (by have := hb.two; omega) (by decide : 6≤16)).trans hcap)
  have hh := Nat.mul_le_mul_right (b^5) hb.two
  nlinarith only [hh]

theorem modulus_le (hb : ParameterBudget E b) (i : Channel T) :
    activationModulus E i ≤ b ^ 3 := by
  unfold activationModulus
  calc
    _ ≤ (b * b) * b := by gcongr <;> first | exact hb.r i | exact hb.a i | exact hb.usefulB i
    _ = _ := by ring

theorem seed_modulus_le (hb : ParameterBudget E b) (t : Fin 2) :
    seedModulus E t ≤ b ^ 5 := by
  unfold seedModulus
  calc
    _ ≤ (b ^ 3 * b) * b := by
      gcongr
      · exact modulus_le hb _
      · exact hb.width
      · exact hb.a _
    _ = _ := by ring

theorem separated_natAbs_le {J : Type*} (M : ℕ) [NeZero M]
    (v : J → ZMod M) (code : J → ℕ) (j : J) {c : ℕ} (hc : code j ≤ c) :
    (separatedResidueLift M v code j).natAbs ≤ M * (c + 1) := by
  have hval := ZMod.val_lt (v j)
  have he : separatedResidueLift M v code j = ((v j).val + M * code j : ℕ) := by
    simp [separatedResidueLift, Nat.cast_add, Nat.cast_mul]
  rw [he, Int.natAbs_natCast]
  have hm := Nat.mul_le_mul_left M hc
  nlinarith

theorem ordinaryOffset_bound (hb : ParameterBudget E b) (n : Column T)
    (j : ActivationIndex E (.inl n)) :
    (ordinaryOffset E n j).1.natAbs ≤ horizontalCap b ∧
      (ordinaryOffset E n j).2.natAbs ≤ horizontalCap b := by
  have hb2 := hb.two
  have hcode : activationIndexCode E (.inl n) j ≤ indexCap b :=
    (activation_code_le hb _ j).trans (le_pairCap _)
  have hfirst : (ordinaryFirst E n j).natAbs ≤ b ^ 5 * (indexCap b + 1) := by
    apply (separated_natAbs_le _ _ _ _ hcode).trans
    apply Nat.mul_le_mul_right
    exact (modulus_le hb _).trans (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 5))
  have hn : (T.slope n).natAbs ≤ b := hb.slope n
  have hscale := payload_le_horizontalCap (by omega : 1 ≤ b)
  constructor
  · exact hfirst.trans hscale
  · change (-T.slope n * ordinaryFirst E n j).natAbs ≤ _
    rw [Int.natAbs_mul, Int.natAbs_neg]
    exact (Nat.mul_le_mul hn hfirst).trans
      (Nat.mul_le_mul_left b (Nat.le_succ _))

theorem seedOffset_bound (hb : ParameterBudget E b) (t : Fin 2)
    (j : SeedActivationIndex E t) :
    (seedOffset E t j).1.natAbs ≤ horizontalCap b ∧
      (seedOffset E t j).2.natAbs ≤ horizontalCap b := by
  have hb2 := hb.two
  have hfirst : (seedFirst E t j).natAbs ≤ b ^ 5 * (indexCap b + 1) := by
    apply (separated_natAbs_le _ _ _ _ (seed_code_le hb t j)).trans
    exact Nat.mul_le_mul_right _ (seed_modulus_le hb t)
  have hscale := payload_le_horizontalCap (by omega : 1 ≤ b)
  refine ⟨hfirst.trans hscale, ?_⟩
  change (j.2.2.val : ℤ).natAbs ≤ _
  rw [Int.natAbs_natCast]
  have hy := (ZMod.val_lt j.2.2).le.trans hb.width
  apply hy.trans
  exact le_horizontalCap b

/-- All graph, dependence, cycle, and activation equations have this bounded
horizontal support, regardless of the number of tested functions. -/
theorem testTile_horizontal_bound (hb : ParameterBudget E b)
    {F : Finset (Ambient E)} (hF : F ∈ testTiles E) {g : Ambient E} (hg : g ∈ F) :
    g.1.1.natAbs ≤ horizontalCap b ∧ g.1.2.natAbs ≤ horizontalCap b := by
  have hzero : (0 : ℤ).natAbs ≤ horizontalCap b := Nat.zero_le _
  have hb2 := hb.two
  have hbase : b ≤ horizontalCap b := le_horizontalCap b
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
          simpa using And.intro (by omega : 1 ≤ horizontalCap b) (hn.trans hbase)
        | inr d =>
          rcases d with ⟨t, axis⟩
          cases axis <;> simpa [dependenceShift, seedStep] using
            And.intro (hb.width.trans hbase) hzero
  · obtain ⟨w, _, hF⟩ := Finset.mem_biUnion.mp hF
    rw [hoff _ _ hF]
    exact ⟨hzero, hzero⟩
  · obtain ⟨q, _, hF⟩ := Finset.mem_biUnion.mp hF
    rw [hoff _ _ hF]
    exact ⟨hzero, hzero⟩
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact ordinaryOffset_bound hb n j
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact seedOffset_bound hb t j

def parameterBase (B S C : ℕ) : ℕ :=
  digitPrimeCap B C ^ (B + 1) + usefulPrimeCap C + residueModulus + C + (B + 1) + S + 2

theorem exists_parameterBudget (T : System) (S : ℕ)
    (hS : ∀ n, (T.slope n).natAbs ≤ S) :
    ∃ E : EncodingParameters T, ParameterBudget E (parameterBase T.alphabet S (channelCount T)) ∧
      channelCount T ≤ parameterBase T.alphabet S (channelCount T) ∧
      T.alphabet + 1 ≤ parameterBase T.alphabet S (channelCount T) := by
  obtain ⟨E, hu, hp⟩ := exists_bounded_parameters T
  have hQ : 1 ≤ digitPrimeCap T.alphabet (channelCount T) := by
    unfold digitPrimeCap
    have : 1 ≤ primeThreshold (usefulPrimeCap (channelCount T)) +
        channelCount T * (T.alphabet + 1) + 1 := by omega
    nlinarith [Nat.mul_le_mul_left 8 this]
  have hr (i : Channel T) :
      E.r i ≤ digitPrimeCap T.alphabet (channelCount T) ^ (T.alphabet + 1) := by
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, digitPrimeCap T.alphabet (channelCount T) :=
        Finset.prod_le_prod (fun j _ => hp i j)
      _ = digitPrimeCap T.alphabet (channelCount T) ^ Fintype.card (Label T i) := by simp
      _ ≤ _ := Nat.pow_le_pow_right hQ (label_card_le T i)
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold parameterBase; omega
  · unfold parameterBase; omega
  · intro i; have := hr i; unfold parameterBase; omega
  · intro i; have := (hu i).1; unfold parameterBase; omega
  · intro i; have := (hu i).2; unfold parameterBase; omega
  · intro n; have := hS n; unfold parameterBase; omega
  · unfold parameterBase; omega
  · unfold parameterBase; omega

end
end TranslationTiling.FiniteCompiler.Size
