import TranslationTiling.FiniteCompiler.TernaryBounds
import TranslationTiling.Compiler.SparseGeometryBound

namespace TranslationTiling.FiniteCompiler.MixedSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The ternary compiler has at least twelve copies of the smaller board. -/
theorem seedModulus_le_channels {C : ℕ} (hC : 596750 ≤ C) :
    residueModulus ≤ C := by
  rw [residueModulus_eq]
  norm_num [Sudoku.SeedModulus,Sudoku.Width,Sudoku.p,Sudoku.q] at *
  omega

theorem mixed_usefulPrimeCap_le {C : ℕ} (hC : 596750 ≤ C) :
    usefulPrimeCap C ≤ 2 * C ^ 4 := by
  have hbig : 596750 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have hs : 6 * (usefulStart + 2 * C + 1) ≤ C ^ 2 := by
    unfold usefulStart
    rw [residueModulus_eq]
    norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    nlinarith [Nat.mul_le_mul_left C hbig]
  unfold usefulPrimeCap
  nlinarith [sq_nonneg (C ^ 2 - 6 * (usefulStart + 2 * C + 1) : ℤ),
    Nat.pow_le_pow_left hs 2,show (C ^ 2)^2 = C ^ 4 by ring]

theorem mixed_digitPrimeCap_le {C : ℕ} (hC : 596750 ≤ C) :
    digitPrimeCap 3 C ≤ C ^ 17 := by
  have hbig : 596750 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have hU := mixed_usefulPrimeCap_le hC
  have hU2 := Nat.pow_le_pow_left hU 2
  have h14 : C ≤ C ^ 4 := Nat.le_self_pow (by decide) _
  have h4 : 500 ≤ C ^ 4 := (by omega : 500 ≤ C).trans h14
  have hmul := Nat.mul_le_mul_left (C ^ 4) h4
  have ht : primeThreshold (usefulPrimeCap C) + C * (3+1) + 1 ≤ 5 * C ^ 8 := by
    unfold primeThreshold
    norm_num [Sudoku.p,Sudoku.q]
    nlinarith [show (2 * C ^ 4)^2 = 4 * C ^ 8 by ring]
  calc
    _ ≤ (8 * (5 * C ^ 8))^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 ht) 2
    _ = 1600 * C ^ 16 := by ring
    _ ≤ C * C ^ 16 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem mixed_parameterBase_le {C : ℕ} (hC : 596750 ≤ C) :
    parameterBase 3 Sudoku.Width C ≤ C ^ 73 := by
  have hbig : 256 ≤ C := by
    omega
  have hC1 : 1 ≤ C := by omega
  have hQ : digitPrimeCap 3 C ≤ C ^ 18 :=
    (mixed_digitPrimeCap_le hC).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hU : usefulPrimeCap C ≤ C ^ 5 := by
    calc
      _ ≤ 2 * C ^ 4 := mixed_usefulPrimeCap_le hC
      _ ≤ C * C ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hDigits : digitPrimeCap 3 C ^ 4 ≤ C ^ 72 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hQ 4
  have hpow {k : ℕ} (hk : k ≤ 72) : C ^ k ≤ C ^ 72 := Nat.pow_le_pow_right hC1 hk
  have h1 : C ≤ C ^ 72 := by simpa using hpow (k := 1) (by omega)
  have h5 := hpow (k := 5) (by omega)
  have hN : Sudoku.Width ≤ C := (show Sudoku.Width≤596750 by norm_num [Sudoku.Width,Sudoku.q]).trans hC
  have hSeed : Sudoku.SeedModulus ≤ C := by simpa only [residueModulus_eq] using seedModulus_le_channels hC
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
  (∀ i, E.a i ≤ 2 * channelCount T ^ 4 ∧ E.b i ≤ 2 * channelCount T ^ 4) ∧
  ∀ i j, E.digitPrime i j ≤ channelCount T ^ 17

theorem smallPrimes_of_caps (hB : T.alphabet = 3) (hC : 596750 ≤ channelCount T)
    (hu : ∀ i, E.a i ≤ usefulPrimeCap (channelCount T) ∧ E.b i ≤ usefulPrimeCap (channelCount T))
    (hp : ∀ i j, E.digitPrime i j ≤ digitPrimeCap T.alphabet (channelCount T)) : SmallPrimes E := by
  have hbig : 256 ≤ channelCount T := by
    omega
  exact ⟨fun i => ⟨(hu i).1.trans (mixed_usefulPrimeCap_le hC),
    (hu i).2.trans (mixed_usefulPrimeCap_le hC)⟩,
    fun i j => (hp i j).trans (by simpa only [hB] using mixed_digitPrimeCap_le hC)⟩

theorem mixed_label_card (hB : T.alphabet = 3) (i : Channel T) :
    Fintype.card (Label T i) ≤ 3 := by cases i <;> simp [Label, Symbol, hB]

theorem mixed_r_le (hB : T.alphabet = 3) (hp : SmallPrimes E) (i : Channel T) :
    E.r i ≤ channelCount T ^ 51 := by
  have hC : 1 ≤ channelCount T := by unfold channelCount; omega
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T i, channelCount T ^ 17 := Finset.prod_le_prod (fun j _ => hp.2 i j)
    _ = channelCount T ^ (17 * Fintype.card (Label T i)) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right hC (by have := mixed_label_card hB i; omega)

theorem mixed_cyclicOrder_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 596750 ≤ channelCount T) :
    E.cyclicOrder ≤ channelCount T ^ (112 * channelCount T) := by
  let C := channelCount T
  have h1 : 1 ≤ C := by unfold C channelCount; omega
  have hblock (i : Channel T) : E.blockModulus i ≤ C ^ 111 := by
    calc
      _ ≤ (C ^ 51) ^ 2 * (2*C ^ 4) * (2*C ^ 4) := by
        unfold EncodingParameters.blockModulus
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (mixed_r_le E hB hp i) 2)
          (hp.1 i).1) (hp.1 i).2
      _ = 4 * C ^ 110 := by ring
      _ ≤ C * C ^ 110 := Nat.mul_le_mul_right _ (by
        have hw : 4 ≤ Sudoku.Width := by decide
        change 4 ≤ channelCount T
        omega)
      _ = _ := by ring
  have hN : residueModulus ≤ C := seedModulus_le_channels hC
  calc
    _ ≤ C ^ 2 * ∏ _i : Channel T, C ^ 111 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hN 2) (Finset.prod_le_prod (fun i _ => hblock i))
    _ = C ^ 2 * (C ^ 111) ^ C := by
      simp only [Finset.prod_const, Finset.card_univ, channel_card]
      rfl
    _ = C ^ (111 * C + 2) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right h1 (by unfold C channelCount; omega)

set_option maxHeartbeats 200000 in
theorem mixed_cycleTiles_card_le (hp : SmallPrimes E) (hC : 596750 ≤ channelCount T)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    (fixedCycleTiles E cycle labels).card ≤ channelCount T ^ (26 * channelCount T) := by
  have ht : t ≤ channelCount T := by
    simpa only [ZMod.card, channel_card] using Fintype.card_le_of_injective cycle cycle.injective
  have hP (i : Channel T) : Fintype.card (P E i) ≤ channelCount T ^ 9 := by
    calc
      _ ≤ (2*channelCount T^4) * (2*channelCount T^4) := by
        simpa only [P,Fintype.card_prod,ZMod.card] using Nat.mul_le_mul (hp.1 i).1 (hp.1 i).2
      _ = 4 * channelCount T^8 := by ring
      _ ≤ channelCount T * channelCount T^8 := Nat.mul_le_mul_right _ (by
        have hw : 4 ≤ Sudoku.Width := by decide
        omega)
      _ = _ := by ring
  calc
    _ ≤ ∏ j : ZMod t, Fintype.card (P E (cycle (j-1))) *
        Fintype.card (digitSubgroup E (cycle j) (labels j)) := fixedCycleTiles_card_le E cycle labels
    _ ≤ ∏ _j : ZMod t, (channelCount T ^ 9 * channelCount T ^ 17) :=
      Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hP _)
        ((digitSubgroup_card_le_prime E _ _).trans (hp.2 _ _)))
    _ = channelCount T ^ (26 * t) := by
      simp only [← pow_add, Finset.prod_const, Finset.card_univ, ZMod.card, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by unfold channelCount; omega) (by omega)

theorem smallPrimes_budget (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 596750 ≤ channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    ParameterBudget E (channelCount T ^ 73) := by
  have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
  have hself : channelCount T ≤ channelCount T ^ 73 := Nat.le_self_pow (by decide) _
  have hN : residueModulus ≤ channelCount T := seedModulus_le_channels hC
  exact ⟨(by unfold channelCount; omega : 2 ≤ channelCount T).trans hself, hN.trans hself,
    fun i => (mixed_r_le E hB hp i).trans (Nat.pow_le_pow_right h1 (by omega)),
    fun i => (hp.1 i).1.trans ((show 2*channelCount T^4 ≤ channelCount T^5 by
      calc _ ≤ channelCount T * channelCount T^4 := Nat.mul_le_mul_right _ (by unfold channelCount; omega)
           _ = _ := by ring).trans (Nat.pow_le_pow_right h1 (by omega))),
    fun i => (hp.1 i).2.trans ((show 2*channelCount T^4 ≤ channelCount T^5 by
      calc _ ≤ channelCount T * channelCount T^4 := Nat.mul_le_mul_right _ (by unfold channelCount; omega)
           _ = _ := by ring).trans (Nat.pow_le_pow_right h1 (by omega))),
    fun n => (hS n).trans (((show Sudoku.Width≤596750 by norm_num [Sudoku.Width,Sudoku.q]).trans hC).trans hself)⟩

theorem mixed_wordConstraintTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 596750 ≤ channelCount T) :
    (wordConstraintTiles E).card ≤ channelCount T ^ (27 * channelCount T) := by
  let C := channelCount T
  have hwords : Fintype.card (Word T) ≤ C ^ C := by
    simp only [Word, Symbol, Fintype.card_fun, Fintype.card_fin, hB]
    exact (Nat.pow_le_pow_left (by unfold C channelCount; have := T.width_pos; omega) _).trans
      (Nat.pow_le_pow_right (by unfold C channelCount; omega) (by unfold C channelCount; omega))
  unfold wordConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)), C ^ (26 * C) :=
      Finset.sum_le_sum (fun _ _ => mixed_cycleTiles_card_le E hp hC _ _)
    _ ≤ Fintype.card (Word T) * C ^ (26 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ C * C ^ (26 * C) := Nat.mul_le_mul_right _ hwords
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem mixed_seedConstraintTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hbig : 6 ≤ channelCount T) (hC : 596750 ≤ channelCount T) :
    (seedConstraintTiles E).card ≤ channelCount T ^ (27 * channelCount T) := by
  let C := channelCount T
  have hindex : Fintype.card (Fin 2 × Column T × Symbol T) ≤ C ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Column, Symbol, hB]
    unfold C channelCount at *
    nlinarith [T.width_pos]
  unfold seedConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q ∈ (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
        ¬ SeedSet T q.1 q.2.2)), C ^ (26 * C) :=
      Finset.sum_le_sum (fun _ _ => mixed_cycleTiles_card_le E hp hC _ _)
    _ ≤ Fintype.card (Fin 2 × Column T × Symbol T) * C ^ (26 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ 2 * C ^ (26 * C) := Nat.mul_le_mul_right _ hindex
    _ = C ^ (26 * C + 2) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by unfold C channelCount; omega) (by dsimp [C]; omega)

theorem mixed_testTiles_card_le (hB : T.alphabet = 3) (hp : SmallPrimes E)
    (hC : 596750 ≤ channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    (testTiles E).card ≤ channelCount T ^ (28 * channelCount T) := by
  let C := channelCount T
  have hbig : 300 ≤ C := by
    have : 15 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  have h1 : 1 ≤ C := by omega
  have hself : C ≤ C ^ 73 := Nat.le_self_pow (by decide) _
  have hb := smallPrimes_budget E hB hp hC hS
  have hdep : (dependenceTiles E).card ≤ C ^ (27 * C) := by
    have hd := dependenceTiles_card_le hb hself
    apply hd.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hword := mixed_wordConstraintTiles_card_le E hB hp hC
  have hseed := mixed_seedConstraintTiles_card_le E hB hp (by omega) hC
  change (wordConstraintTiles E).card ≤ C ^ (27 * C) at hword
  change (seedConstraintTiles E).card ≤ C ^ (27 * C) at hseed
  have hsingle : 1 ≤ C ^ (27 * C) := Nat.one_le_pow _ _ h1
  have hsmall : C ≤ C ^ (27 * C) := Nat.le_self_pow (by omega) _
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card ≤ C ^ (27 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hw : Fintype.card (Column T) ≤ C := by
      simp only [Column, Fintype.card_fin]; unfold C channelCount; omega
    exact hw.trans hsmall
  have hseeds : (Finset.univ.image (seedActivationTile E)).card ≤ C ^ (27 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ, Fintype.card_fin]
    exact (by omega : 2 ≤ C).trans hsmall
  have hsum : (testTiles E).card ≤ 6 * C ^ (27 * C) := by
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
    _ ≤ 6 * C ^ (27 * C) := hsum
    _ ≤ C * C ^ (27 * C) := Nat.mul_le_mul_right _ (by omega)
    _ = C ^ (27 * C + 1) := by rw [pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)


theorem mixed_modulus_cap_le {C : ℕ} (hC : 596750 ≤ C) :
    separateModulusCap (C ^ (112*C)) (C ^ (28*C)) ≤ C ^ (253*C) := by
  have hbig : 24 ≤ C := by omega
  have h1 : 1 ≤ C := by omega
  have hV : C ^ (112*C) ≤ C ^ (140*C) := Nat.pow_le_pow_right h1 (by omega)
  have hp : 1 ≤ C ^ (140*C) := Nat.one_le_pow _ _ h1
  have hq : 2 * (8 * (C ^ (28*C))^5 + C ^ (112*C) + 3) ≤ C ^ (141*C) := by
    calc
      _ ≤ 24 * C ^ (140*C) := by
        have he : (C ^ (28*C))^5 = C ^ (140*C) := by rw [← pow_mul]; congr 1; ring
        rw [he]
        omega
      _ ≤ C * C ^ (140*C) := Nat.mul_le_mul_right _ hbig
      _ = C ^ (140*C+1) := by rw [pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)
  calc
    _ ≤ C ^ (112*C) * C ^ (141*C) := Nat.mul_le_mul_left _ hq
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem mixed_geometry_bound {C b : ℕ} (hC : 596750 ≤ C)
    (hb : b ≤ C ^ 73) (hb2 : 2 ≤ b) :
    Compiler.Size.sparseGeometryCap (Size.horizontalCap b) (C ^ (253*C)) ≤ C ^ (1772*C) := by
  let M := C ^ (253*C)
  have hbig : 596750 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1 ≤ C := by omega
  have hH : Size.horizontalCap b ≤ C ^ 15403 := by
    calc
      _ ≤ b ^ 211 := horizontalCap_degree_211 b hb2
      _ ≤ (C ^ 73)^211 := Nat.pow_le_pow_left hb _
      _ = _ := by rw [← pow_mul]
  have hHM : Size.horizontalCap b ≤ M := hH.trans (Nat.pow_le_pow_right h1 (by omega))
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ h1
  have hH1 : 1 ≤ Size.horizontalCap b := (by omega : 1 ≤ b).trans (Size.le_horizontalCap b)
  let S := Compiler.Size.latticeSide (Size.horizontalCap b) M
  have hS : S ≤ 8003*M := by dsimp [S,Compiler.Size.latticeSide,Compiler.Size.latticeRadius]; omega
  have hS1 : 1 ≤ S := by dsimp [S,Compiler.Size.latticeSide]; omega
  have hinside : 18*S^2+6 ≤ 24*S^2 := by nlinarith
  have hside : (2*Size.horizontalCap b+1)^2 ≤ 9*(Size.horizontalCap b)^2 := by nlinarith
  have hconst : 9*2^24*24^3*8003^6 ≤ C ^ 7 := by
    apply (by norm_num : 9*2^24*24^3*8003^6 ≤ (2^19)^7).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ ≤ (2^24*(9*(Size.horizontalCap b)^2*M)) * (24*(8003*M)^2)^3 := by
      unfold Compiler.Size.sparseGeometryCap
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hside))
        (Nat.pow_le_pow_left (hinside.trans (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hS 2))) 3)
    _ = (9*2^24*24^3*8003^6) * (Size.horizontalCap b)^2 * M^7 := by ring
    _ ≤ C^7 * (C^15403)^2 * M^7 := Nat.mul_le_mul
      (Nat.mul_le_mul hconst (Nat.pow_le_pow_left hH 2)) le_rfl
    _ = C ^ (1771*C+30813) := by dsimp [M]; simp only [← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

end
end TranslationTiling.FiniteCompiler.MixedSize
