import TranslationTiling.FiniteCompiler.ExplicitDegrees

namespace TranslationTiling.FiniteCompiler.Size
open Compiler.Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The ternary compiler has at least twenty copies of the smaller board. -/
theorem seedModulus_le_channels_sq {C : ℕ} (hC : 20 * Sudoku.Width + 2 ≤ C) :
    residueModulus ≤ C^2 := by
  rw [residueModulus_eq]
  norm_num [Sudoku.SeedModulus,Sudoku.Width,Sudoku.p,Sudoku.q] at *
  nlinarith

theorem ternary_usefulPrimeCap_le {C : ℕ} (hC : 994582 ≤ C) :
    usefulPrimeCap C ≤ C ^ 4 := by
  have hbig : 994582 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have hs : 8 * (usefulStart + 2 * C + 1) ≤ C ^ 2 := by
    unfold usefulStart
    rw [residueModulus_eq]
    norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    nlinarith [Nat.mul_le_mul_left C hbig]
  calc
    _ ≤ (C ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
    _ = _ := by ring

theorem ternary_digitPrimeCap_le {C : ℕ} (hC : 994582 ≤ C) :
    digitPrimeCap 3 C ≤ C ^ 18 := by
  have hbig : 994582 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1 ≤ C := by omega
  have hU := ternary_usefulPrimeCap_le hC
  have hU2 := Nat.pow_le_pow_left hU 2
  have h14 : C ≤ C ^ 4 := Nat.le_self_pow (by decide) _
  have h4 : 7 ≤ C ^ 4 := (by omega : 7 ≤ C).trans h14
  have hmul := Nat.mul_le_mul_left (C ^ 4) h4
  have ht : primeThreshold (usefulPrimeCap C) + C * (3 + 1) + 1 ≤ 2 * C ^ 8 := by
    unfold primeThreshold
    norm_num [Sudoku.p,Sudoku.q]
    nlinarith [show (C ^ 4) ^ 2 = C ^ 8 by ring]
  calc
    _ ≤ (8 * (2 * C ^ 8)) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 ht) 2
    _ = 256 * C ^ 16 := by ring
    _ ≤ C ^ 2 * C ^ 16 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = _ := by ring

theorem ternary_parameterBase_le {C : ℕ} (hC : 994582 ≤ C) :
    parameterBase 3 Sudoku.Width C ≤ C ^ 73 := by
  have hbig : 256 ≤ C := by
    omega
  have hC1 : 1 ≤ C := by omega
  have hQ := ternary_digitPrimeCap_le hC
  have hU : usefulPrimeCap C ≤ C ^ 5 := by
    calc
      _ ≤ C ^ 4 := ternary_usefulPrimeCap_le hC
      _ ≤ C * C ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
      _ = _ := by ring
  have hDigits : digitPrimeCap 3 C ^ 4 ≤ C ^ 72 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hQ 4
  have hpow {k : ℕ} (hk : k ≤ 72) : C ^ k ≤ C ^ 72 := Nat.pow_le_pow_right hC1 hk
  have h1 : C ≤ C ^ 72 := by simpa using hpow (k := 1) (by omega)
  have h5 := hpow (k := 5) (by omega)
  have hN : Sudoku.Width ≤ C := (show Sudoku.Width≤994582 by norm_num [Sudoku.Width,Sudoku.q]).trans hC
  have hSeed : Sudoku.SeedModulus ≤ C := by norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]; omega
  have hsum : parameterBase 3 Sudoku.Width C ≤ 7 * C ^ 72 := by
    unfold parameterBase
    rw [residueModulus_eq]
    calc
      _ ≤ C ^ 72 + C ^ 72 + C ^ 72 + C ^ 72 + C ^ 72 + C ^ 72 + C ^ 72 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hDigits (hU.trans h5)) (hSeed.trans h1)) h1)
          ((by omega : 4 ≤ C).trans h1)) (hN.trans h1)) ((by omega : 2 ≤ C).trans h1)
      _ = _ := by ring
  calc
    _ ≤ 7 * C ^ 72 := hsum
    _ ≤ C * C ^ 72 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

variable {T : System} (E : EncodingParameters T)

/-- Separate useful primes and digit primes instead of using their product as
one common bound. -/
def SmallPrimes : Prop :=
  (∀ i, E.a i ≤ channelCount T ^ 5 ∧ E.b i ≤ channelCount T ^ 5) ∧
  ∀ i j, E.digitPrime i j ≤ channelCount T ^ 18

theorem smallPrimes_of_caps (hB : T.alphabet = 3) (hC : 994582 ≤ channelCount T)
    (hu : ∀ i, E.a i ≤ usefulPrimeCap (channelCount T) ∧ E.b i ≤ usefulPrimeCap (channelCount T))
    (hp : ∀ i j, E.digitPrime i j ≤ digitPrimeCap T.alphabet (channelCount T)) : SmallPrimes E := by
  have hbig : 256 ≤ channelCount T := by
    omega
  have hU : usefulPrimeCap (channelCount T) ≤ channelCount T ^ 5 := by
    calc
      _ ≤ channelCount T ^ 4 := ternary_usefulPrimeCap_le hC
      _ ≤ channelCount T * channelCount T ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
      _ = _ := by ring
  exact ⟨fun i => ⟨(hu i).1.trans hU, (hu i).2.trans hU⟩,
    fun i j => (hp i j).trans (by simpa only [hB] using ternary_digitPrimeCap_le hC)⟩

theorem ternary_label_card (hB : T.alphabet = 3) (i : Channel T) :
    Fintype.card (Label T i) ≤ 3 := by cases i <;> simp [Label, Symbol, hB]

theorem ternary_r_le (hB : T.alphabet = 3) (hp : SmallPrimes E) (i : Channel T) :
    E.r i ≤ channelCount T ^ 54 := by
  have hC : 1 ≤ channelCount T := by unfold channelCount; omega
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T i, channelCount T ^ 18 := Finset.prod_le_prod (fun j _ => hp.2 i j)
    _ = channelCount T ^ (18 * Fintype.card (Label T i)) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right hC (by have := ternary_label_card hB i; omega)

theorem ternary_cyclicOrder_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 20 * Sudoku.Width + 2 ≤ channelCount T) :
    E.cyclicOrder ≤ channelCount T ^ (119 * channelCount T) := by
  let C := channelCount T
  have h1 : 1 ≤ C := by unfold C channelCount; omega
  have hblock (i : Channel T) : E.blockModulus i ≤ C ^ 118 := by
    calc
      _ ≤ (C ^ 54) ^ 2 * C ^ 5 * C ^ 5 := by
        unfold EncodingParameters.blockModulus
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (ternary_r_le E hB hp i) 2)
          (hp.1 i).1) (hp.1 i).2
      _ = _ := by ring
  have hN : residueModulus ≤ C^2 := seedModulus_le_channels_sq hC
  calc
    _ ≤ C ^ 4 * ∏ _i : Channel T, C ^ 118 :=
      by simpa only [EncodingParameters.cyclicOrder,← pow_mul] using Nat.mul_le_mul (Nat.pow_le_pow_left hN 2) (Finset.prod_le_prod (fun i _ => hblock i))
    _ = C ^ 4 * (C ^ 118) ^ C := by
      simp only [Finset.prod_const, Finset.card_univ, channel_card]
      rfl
    _ = C ^ (118 * C + 4) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right h1 (by
      have hW : 1≤Sudoku.Width := by decide
      change 118*channelCount T+4≤119*channelCount T
      omega)

theorem digitSubgroup_card_le_prime (i : Channel T) (j : Label T i) :
    Fintype.card (digitSubgroup E i j) ≤ E.digitPrime i j := by
  have hi : Function.Injective (fun x : digitSubgroup E i j => digitEquiv E i x.val j) := by
    intro x y h
    apply Subtype.ext
    apply (digitEquiv E i).injective
    funext k
    by_cases hk : k = j
    · subst k; exact h
    · exact (x.property k hk).trans (y.property k hk).symm
  simpa only [ZMod.card] using Fintype.card_le_of_injective _ hi

set_option maxHeartbeats 200000 in
theorem ternary_cycleTiles_card_le (hp : SmallPrimes E)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    (fixedCycleTiles E cycle labels).card ≤ channelCount T ^ (28 * channelCount T) := by
  have ht : t ≤ channelCount T := by
    simpa only [ZMod.card, channel_card] using Fintype.card_le_of_injective cycle cycle.injective
  have hP (i : Channel T) : Fintype.card (P E i) ≤ channelCount T ^ 10 := by
    simpa only [P, Fintype.card_prod, ZMod.card, ← pow_add] using
      Nat.mul_le_mul (hp.1 i).1 (hp.1 i).2
  calc
    _ ≤ ∏ j : ZMod t, Fintype.card (P E (cycle (j-1))) *
        Fintype.card (digitSubgroup E (cycle j) (labels j)) := fixedCycleTiles_card_le E cycle labels
    _ ≤ ∏ _j : ZMod t, (channelCount T ^ 10 * channelCount T ^ 18) :=
      Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hP _)
        ((digitSubgroup_card_le_prime E _ _).trans (hp.2 _ _)))
    _ = channelCount T ^ (28 * t) := by
      simp only [← pow_add, Finset.prod_const, Finset.card_univ, ZMod.card, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by unfold channelCount; omega) (by omega)

theorem smallPrimes_budget (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 20 * Sudoku.Width + 2 ≤ channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    ParameterBudget E (channelCount T ^ 73) := by
  have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
  have hself : channelCount T ≤ channelCount T ^ 73 := Nat.le_self_pow (by decide) _
  have hN : residueModulus ≤ channelCount T^73 := (seedModulus_le_channels_sq hC).trans (Nat.pow_le_pow_right h1 (by decide))
  exact ⟨(by unfold channelCount; omega : 2 ≤ channelCount T).trans hself, hN,
    fun i => (ternary_r_le E hB hp i).trans (Nat.pow_le_pow_right h1 (by omega)),
    fun i => (hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by omega)),
    fun i => (hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by omega)),
    fun n => (hS n).trans ((by omega : Sudoku.Width ≤ channelCount T).trans hself)⟩

theorem ternary_wordConstraintTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E) :
    (wordConstraintTiles E).card ≤ channelCount T ^ (29 * channelCount T) := by
  let C := channelCount T
  have hwords : Fintype.card (Word T) ≤ C ^ C := by
    simp only [Word, Symbol, Fintype.card_fun, Fintype.card_fin, hB]
    exact (Nat.pow_le_pow_left (by unfold C channelCount; have := T.width_pos; omega) _).trans
      (Nat.pow_le_pow_right (by unfold C channelCount; omega) (by unfold C channelCount; omega))
  unfold wordConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)), C ^ (28 * C) :=
      Finset.sum_le_sum (fun _ _ => ternary_cycleTiles_card_le E hp _ _)
    _ ≤ Fintype.card (Word T) * C ^ (28 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ C * C ^ (28 * C) := Nat.mul_le_mul_right _ hwords
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem ternary_seedConstraintTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hbig : 6 ≤ channelCount T) :
    (seedConstraintTiles E).card ≤ channelCount T ^ (29 * channelCount T) := by
  let C := channelCount T
  have hindex : Fintype.card (Fin 2 × Column T × Symbol T) ≤ C ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Column, Symbol, hB]
    unfold C channelCount at *
    nlinarith [T.width_pos]
  unfold seedConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q ∈ (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
        ¬ SeedSet T q.1 q.2.2)), C ^ (28 * C) :=
      Finset.sum_le_sum (fun _ _ => ternary_cycleTiles_card_le E hp _ _)
    _ ≤ Fintype.card (Fin 2 × Column T × Symbol T) * C ^ (28 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ 2 * C ^ (28 * C) := Nat.mul_le_mul_right _ hindex
    _ = C ^ (28 * C + 2) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by unfold C channelCount; omega) (by dsimp [C]; omega)

theorem ternary_testTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 20 * Sudoku.Width + 2 ≤ channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    (testTiles E).card ≤ channelCount T ^ (30 * channelCount T) := by
  let C := channelCount T
  have hbig : 300 ≤ C := by
    have : 15 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  have h1 : 1 ≤ C := by omega
  have hself : C ≤ C ^ 73 := Nat.le_self_pow (by decide) _
  have hb := smallPrimes_budget E hB hp hC hS
  have hdep : (dependenceTiles E).card ≤ C ^ (29 * C) := by
    have hd := dependenceTiles_card_le hb hself
    apply hd.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hword := ternary_wordConstraintTiles_card_le E hB hp
  have hseed := ternary_seedConstraintTiles_card_le E hB hp (by omega)
  change (wordConstraintTiles E).card ≤ C ^ (29 * C) at hword
  change (seedConstraintTiles E).card ≤ C ^ (29 * C) at hseed
  have hsingle : 1 ≤ C ^ (29 * C) := Nat.one_le_pow _ _ h1
  have hsmall : C ≤ C ^ (29 * C) := Nat.le_self_pow (by omega) _
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card ≤ C ^ (29 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hw : Fintype.card (Column T) ≤ C := by
      simp only [Column, Fintype.card_fin]; unfold C channelCount; omega
    exact hw.trans hsmall
  have hseeds : (Finset.univ.image (seedActivationTile E)).card ≤ C ^ (29 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ, Fintype.card_fin]
    exact (by omega : 2 ≤ C).trans hsmall
  have hsum : (testTiles E).card ≤ 6 * C ^ (29 * C) := by
    unfold testTiles
    have h := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E ∪
        Finset.univ.image (ordinaryActivationTile E)) (Finset.univ.image (seedActivationTile E))
    have h' := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E)
        (Finset.univ.image (ordinaryActivationTile E))
    have h'' := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E) (seedConstraintTiles E)
    have h''' := Finset.card_union_le ({kernelTile E} ∪ dependenceTiles E) (wordConstraintTiles E)
    have h'''' := Finset.card_union_le {kernelTile E} (dependenceTiles E)
    simp only [Finset.card_singleton] at h''''
    omega
  calc
    _ ≤ 6 * C ^ (29 * C) := hsum
    _ ≤ C * C ^ (29 * C) := Nat.mul_le_mul_right _ (by omega)
    _ = C ^ (29 * C + 1) := by rw [pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

def separateModulusCap (V s : ℕ) : ℕ := V * (2 * (8 * s ^ 5 + V + 3))

theorem separateModulusCap_mono {V V' s s' : ℕ} (hV : V ≤ V') (hs : s ≤ s') :
    separateModulusCap V s ≤ separateModulusCap V' s' := by
  unfold separateModulusCap
  gcongr

theorem ternary_modulus_cap_le {C : ℕ} (hC : 20 * Sudoku.Width + 2 ≤ C) :
    separateModulusCap (C ^ (119 * C)) (C ^ (30 * C)) ≤ C ^ (270 * C) := by
  have hbig : 24 ≤ C := by
    norm_num [Sudoku.Width,Sudoku.q] at hC
    omega
  have h1 : 1 ≤ C := by omega
  have hV : C ^ (119 * C) ≤ C ^ (150 * C) := Nat.pow_le_pow_right h1 (by omega)
  have hp : 1 ≤ C ^ (150 * C) := Nat.one_le_pow _ _ h1
  have hq : 2 * (8 * (C ^ (30 * C)) ^ 5 + C ^ (119 * C) + 3) ≤ C ^ (151 * C) := by
    calc
      _ ≤ 24 * C ^ (150 * C) := by
        have he : (C ^ (30 * C)) ^ 5 = C ^ (150 * C) := by rw [← pow_mul]; congr 1; ring
        rw [he]
        omega
      _ ≤ C * C ^ (150 * C) := Nat.mul_le_mul_right _ hbig
      _ = C ^ (150 * C + 1) := by rw [pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)
  calc
    _ ≤ C ^ (119 * C) * C ^ (151 * C) := Nat.mul_le_mul_left _ hq
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem ternary_geometry_bound {C b : ℕ} (hC : 20 * Sudoku.Width + 2 ≤ C) (hb : b ≤ C ^ 73)
    (hb2 : 2 ≤ b) :
    Compiler.Size.geometryCap (horizontalCap b) (C ^ (270 * C)) ≤ C ^ (3510 * C) := by
  let M := C ^ (270 * C)
  have hbig : 300 ≤ C := by
    have : 15 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  have h1 : 1 ≤ C := by omega
  have hM : 2 ^ 166 ≤ M :=
    (Nat.pow_le_pow_left (by omega : 2 ≤ C) 166).trans
      (Nat.pow_le_pow_right h1 (by omega))
  have hM1 : 1 ≤ M := by norm_num at hM; omega
  have hH : horizontalCap b ≤ M := by
    calc
      _ ≤ b ^ 211 := horizontalCap_degree_211 b hb2
      _ ≤ (C ^ 73) ^ 211 := Nat.pow_le_pow_left hb _
      _ = C ^ 15403 := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)
  let S := Compiler.Size.latticeSide (horizontalCap b) M
  have hS : S ≤ 8003 * M := by
    dsimp [S, Compiler.Size.latticeSide, Compiler.Size.latticeRadius]
    omega
  have hS1 : 1 ≤ S := by dsimp [S, Compiler.Size.latticeSide]; omega
  have hinside : 3 * S ^ 3 + 6 ≤ 9 * S ^ 3 := by
    have : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS1
    omega
  have hcoeff : 729 * 8003 ^ 12 ≤ M :=
    (by norm_num : 729 * 8003 ^ 12 ≤ 2 ^ 166).trans hM
  calc
    _ ≤ S ^ 3 * (9 * S ^ 3) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinside 3)
    _ = 729 * S ^ 12 := by ring
    _ ≤ 729 * (8003 * M) ^ 12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 12)
    _ = (729 * 8003 ^ 12) * M ^ 12 := by ring
    _ ≤ M * M ^ 12 := Nat.mul_le_mul_right _ hcoeff
    _ = C ^ (3510 * C) := by dsimp [M]; rw [← pow_succ', ← pow_mul]; congr 1; ring

end
end TranslationTiling.FiniteCompiler.Size
