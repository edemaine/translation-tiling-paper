import TranslationTiling.FiniteCompiler.SharpBounds
import TranslationTiling.Compiler.TightPrimeCounting

namespace TranslationTiling.FiniteCompiler.TightSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {T : System} (E : EncodingParameters T)

def TightPrimes : Prop :=
  (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
  (∀ i j, E.digitPrime i j≤channelCount T^3) ∧
  ∀ i, (E.a i*E.b i)^3≤channelCount T^8

theorem tightPrimes_sharp (hp : TightPrimes E) : SharpSize.SmallPrimes E := by
  refine ⟨hp.1,fun i j => (hp.2.1 i j).trans ?_⟩
  exact Nat.pow_le_pow_right (by unfold channelCount; omega) (by decide)

theorem tight_r_le (hB : T.alphabet=3) (hp : TightPrimes E) (i : Channel T) :
    E.r i≤channelCount T^9 := by
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T i, channelCount T^3 := Finset.prod_le_prod (fun j _ => hp.2.1 i j)
    _ = channelCount T^(3*Fintype.card (Label T i)) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by unfold channelCount; omega)
      (by have := SharpSize.sharp_label_card hB i; omega)

theorem tight_cyclicOrder_le (hB : T.alphabet=3) (hp : TightPrimes E)
    (hC : 12*Sudoku.Width+2≤channelCount T) :
    E.cyclicOrder≤channelCount T^(21*channelCount T) := by
  let C := channelCount T
  have h1 : 1≤C := by unfold C channelCount; omega
  have hc : 596750≤C := by simpa [C,Sudoku.Width,Sudoku.q] using hC
  have hblock (i : Channel T) : E.blockModulus i^3≤C^62 := by
    calc
      _ = (E.r i)^6*(E.a i*E.b i)^3 := by unfold EncodingParameters.blockModulus; ring
      _ ≤ (C^9)^6*C^8 := Nat.mul_le_mul (Nat.pow_le_pow_left (tight_r_le E hB hp i) 6) (hp.2.2 i)
      _ = _ := by ring
  have hN : residueModulus≤C := MixedSize.seedModulus_le_channels hC
  apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
  calc
    _ = residueModulus^6*∏ i : Channel T, E.blockModulus i^3 := by
      unfold EncodingParameters.cyclicOrder
      rw [mul_pow,Finset.prod_pow]
      ring
    _ ≤ C^6*∏ _i : Channel T, C^62 := Nat.mul_le_mul (Nat.pow_le_pow_left hN 6)
      (Finset.prod_le_prod (fun i _ => hblock i))
    _ = C^(62*C+6) := by simp only [Finset.prod_const,Finset.card_univ,channel_card,← pow_mul,← pow_add]; congr 1; ring
    _ ≤ C^(63*C) := Nat.pow_le_pow_right h1 (by omega)
    _ = _ := by ring

def pairCap (C : ℕ) : ℕ := Nat.nthRoot 3 (C^8)
def cycleBudget (C : ℕ) : ℕ := pairCap C*C^3

theorem cycleBudget_bounds {C : ℕ} (hC : 596750≤C) :
    C^3≤cycleBudget C ∧ 6*cycleBudget C≤C^6 := by
  have h1 : 1≤C := by omega
  have hP : 1≤pairCap C := (Nat.le_nthRoot_iff (by decide : 3≠0)).mpr (by simpa using Nat.one_le_pow _ _ h1)
  have hP3 : pairCap C^3≤C^8 := Nat.pow_nthRoot_le (Or.inl (by decide))
  constructor
  · unfold cycleBudget
    simpa only [one_mul] using Nat.mul_le_mul_right (C^3) hP
  · apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
    calc
      _ = 216*(pairCap C)^3*C^9 := by unfold cycleBudget; ring
      _ ≤ 216*C^8*C^9 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP3)
      _ = 216*C^17 := by ring
      _ ≤ C*C^17 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring

theorem tight_cycleTiles_card_le (hp : TightPrimes E) (hC : 12*Sudoku.Width+2≤channelCount T)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    (sparseCycleTiles E cycle labels).card≤cycleBudget (channelCount T)^channelCount T := by
  let C := channelCount T
  have hc : 596750≤C := by simpa [C,Sudoku.Width,Sudoku.q] using hC
  have ht : t≤C := by simpa only [ZMod.card,channel_card] using Fintype.card_le_of_injective cycle cycle.injective
  have hP (i : Channel T) : Fintype.card (P E i)≤pairCap C := by
    apply (Nat.le_nthRoot_iff (by decide : 3≠0)).mpr
    simpa only [P,Fintype.card_prod,ZMod.card] using hp.2.2 i
  calc
    _ ≤ ∏ j : ZMod t, Fintype.card (P E (cycle (j-1)))*Fintype.card (digitSubgroup E (cycle j) (labels j)) := sparseCycleTiles_card_le E cycle labels
    _ ≤ ∏ _j : ZMod t, cycleBudget C := Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hP _)
      ((digitSubgroup_card_le_prime E _ _).trans (hp.2.1 _ _)))
    _ = cycleBudget C^t := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by
      exact (Nat.one_le_pow _ _ (by omega : 1≤C)).trans (cycleBudget_bounds hc).1) ht

private theorem six_mul_le_three_pow {C : ℕ} (hC : 4≤C) : 6*C≤3^C := by
  induction C, hC using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; nlinarith

theorem tight_testTiles_card_le (hB : T.alphabet=3) (hp : TightPrimes E)
    (hC : 12*Sudoku.Width+2≤channelCount T) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (testTiles E).card≤channelCount T^(6*channelCount T) := by
  let C := channelCount T
  let B := cycleBudget C
  let L := (3*B)^C
  have hc : 596750≤C := by simpa [C,Sudoku.Width,Sudoku.q] using hC
  have h1 : 1≤C := by omega
  have hB3 : C^3≤B := (cycleBudget_bounds hc).1
  have hb := SharpSize.smallPrimes_budget E hB (tightPrimes_sharp E hp) hC hS
  have hself : C≤C^73 := Nat.le_self_pow (by decide) _
  have hdep : (dependenceTiles E).card≤L := by
    apply (dependenceTiles_card_le hb hself).trans
    calc
      _ = C^292 := by rw [← pow_mul]
      _ ≤ C^(3*C) := Nat.pow_le_pow_right h1 (by omega)
      _ = (C^3)^C := by rw [← pow_mul]
      _ ≤ B^C := Nat.pow_le_pow_left hB3 C
      _ ≤ _ := Nat.pow_le_pow_left (by omega : B≤3*B) C
  have hword : (wordConstraintTiles E).card≤L := by
    have hw : Fintype.card (Word T)≤3^C := by
      simp only [Word,Symbol,Fintype.card_fun,Fintype.card_fin,hB]
      exact Nat.pow_le_pow_right (by decide) (by unfold C channelCount; omega)
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w∉allowedWords T)), B^C :=
        Finset.sum_le_sum (fun _ _ => tight_cycleTiles_card_le E hp hC _ _)
      _ ≤ Fintype.card (Word T)*B^C := by
        simp only [Finset.sum_const,smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ ≤ 3^C*B^C := Nat.mul_le_mul_right _ hw
      _ = _ := by unfold L; rw [mul_pow]
  have hseed : (seedConstraintTiles E).card≤L := by
    have hi : Fintype.card (Fin 2×Column T×Symbol T)≤3^C := by
      have hh : Fintype.card (Fin 2×Column T×Symbol T)≤6*C := by
        simp only [Fintype.card_prod,Fintype.card_fin,Column,Symbol,hB]
        unfold C channelCount
        omega
      exact hh.trans (six_mul_le_three_pow (by omega))
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Fin 2×Column T×Symbol T => ¬SeedSet T w.1 w.2.2)), B^C :=
        Finset.sum_le_sum (fun _ _ => tight_cycleTiles_card_le E hp hC _ _)
      _ ≤ Fintype.card (Fin 2×Column T×Symbol T)*B^C := by
        simp only [Finset.sum_const,smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ ≤ 3^C*B^C := Nat.mul_le_mul_right _ hi
      _ = _ := by unfold L; rw [mul_pow]
  have hsmall : C≤L := by
    apply (Nat.le_self_pow (by decide : (3:ℕ)≠0) C).trans
    apply hB3.trans
    apply (Nat.le_self_pow (by omega : C≠0) B).trans
    exact Nat.pow_le_pow_left (by omega : B≤3*B) C
  have hsingle : 1≤L := (by omega : 1≤C).trans hsmall
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤L := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hh : Fintype.card (Column T)≤C := by
      simp only [Column,Fintype.card_fin]
      unfold C channelCount
      omega
    exact hh.trans hsmall
  have hseeds : (Finset.univ.image (seedActivationTile E)).card≤L := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ,Fintype.card_fin]
    exact (by omega : 2≤C).trans hsmall
  have hsum : (testTiles E).card≤6*L := by
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
    _ ≤ 6*L := hsum
    _ ≤ (2^C*3^C)*B^C := by
      unfold L
      rw [mul_pow]
      have hh : 6≤2^C := (by norm_num : 6≤2^3).trans (Nat.pow_le_pow_right (by decide) (by omega))
      nlinarith [Nat.mul_le_mul_right (3^C*B^C) hh]
    _ = (6*B)^C := by rw [← mul_pow,← mul_pow]; norm_num
    _ ≤ (C^6)^C := Nat.pow_le_pow_left (cycleBudget_bounds hc).2 C
    _ = _ := by rw [← pow_mul]

theorem cyclicOrder_primeBound (hB : T.alphabet=3) (hp : TightPrimes E)
    (hC : 12*Sudoku.Width+2 ≤ channelCount T) :
    Effective.PrimeBound E.cyclicOrder (channelCount T^3) := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q ∣ E.cyclicOrder
    · right
      by_contra hl
      have hlarge : channelCount T^3 < q := by omega
      have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤channelCount T^3) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (by rw [residueModulus_eq]; decide)
        ((MixedSize.seedModulus_le_channels hC).trans (Nat.le_self_pow (by decide) _))
      have hi (i : Channel T) : Nat.Coprime q (E.blockModulus i) := by
        have hr : Nat.Coprime q (E.r i) := by
          rw [E.r_eq_prod]
          apply Nat.coprime_fintype_prod_right_iff.mpr
          intro j
          exact hcop _ (E.prime_isPrime (.inr (.inr ⟨i,j⟩))).pos (hp.2.1 i j)
        exact ((hr.pow_right 2).mul_right (hcop _ (E.prime_isPrime (.inl i)).pos
          ((hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide))))).mul_right
          (hcop _ (E.prime_isPrime (.inr (.inl i))).pos ((hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide))))
      have ht : Nat.Coprime q E.cyclicOrder :=
        (hR.pow_right 2).mul_right (Nat.coprime_fintype_prod_right_iff.mpr hi)
      exact (hprime.coprime_iff_not_dvd.mp ht) hd
    · exact Or.inl hd
  · exact Or.inl hprime

theorem differenceLog_channel_le {C : ℕ} (hC : 596750≤C) :
    Stacking.differenceLog (C^(6*C))≤C^2 := by
  apply le_trans (b:=Stacking.differenceLog (C^(11*C)))
  · unfold Stacking.differenceLog
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (by omega : 1≤C) (by omega)))) 1
  · exact SharpSize.differenceLog_channel_le hC

theorem freshCap_channel_le {C : ℕ} (hC : 12*Sudoku.Width+2 ≤ C) :
    Effective.freshCap (C^(6*C)) (C^3) ≤ C^(13*C) := by
  have hc : 596750 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1 ≤ C := by omega
  have hL := differenceLog_channel_le hc
  have hLp : 1 ≤ Stacking.differenceLog (C^(6*C)) := by unfold Stacking.differenceLog; omega
  have hP : C^3 ≤ (C^(6*C))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hX : 3 ≤ (C^(6*C))^2 := by
    apply (show 3 ≤ C by omega).trans
    rw [← pow_mul]
    exact Nat.le_self_pow (by omega) _
  have hXL : (C^(6*C))^2 ≤ (C^(6*C))^2*Stacking.differenceLog (C^(6*C)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ 132*(C^(6*C))^2*Stacking.differenceLog (C^(6*C)) := by
      unfold Effective.freshCap Stacking.logPartitionThreshold
      nlinarith
    _ ≤ 132*(C^(6*C))^2*C^2 := Nat.mul_le_mul_left _ hL
    _ = 132*C^(12*C+2) := by rw [← pow_mul,mul_assoc,← pow_add]; congr 2; ring
    _ ≤ C*C^(12*C+2) := Nat.mul_le_mul_right _ (by omega)
    _ = C^(12*C+3) := by simpa only [Nat.add_assoc] using (pow_succ' C (12*C+2)).symm
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

theorem sharp_geometry_bound {C b : ℕ} (hC : 12 * Sudoku.Width + 2 ≤ C)
    (hb : b ≤ C ^ 73) (hb2 : 2 ≤ b) :
    Compiler.Size.sparseGeometryCap (Size.horizontalCap b) (C ^ (34*C)) ≤ C ^ (239*C) := by
  let M := C ^ (34*C)
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
    _ = C ^ (238*C+30813) := by dsimp [M]; simp only [← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

end
end TranslationTiling.FiniteCompiler.TightSize
