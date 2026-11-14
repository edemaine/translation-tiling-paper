import TranslationTiling.FiniteCompiler.BitSystem
import TranslationTiling.FiniteCompiler.GeometryBound

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler.Size

open Compiler.Size
noncomputable section

theorem bit_alphabet_le : BitSystem.alphabet ≤ 10 ^ 5 := by
  have hinj : Function.Injective (fun z : BitSystem.Gamma => (z.1.val, z.2.1.val, z.2.2)) := by
    intro a b h
    refine Prod.ext (Units.ext (congrArg (fun z : ZMod Sudoku.p × (ZMod Sudoku.q × Bool) => z.1) h))
      (Prod.ext (Units.ext (congrArg (fun z : ZMod Sudoku.p × (ZMod Sudoku.q × Bool) => z.2.1) h))
        (congrArg (fun z : ZMod Sudoku.p × (ZMod Sudoku.q × Bool) => z.2.2) h))
  have h := Fintype.card_le_of_injective _ hinj
  rw [BitSystem.alphabet_eq]
  apply h.trans
  norm_num [Fintype.card_prod, ZMod.card, Sudoku.p, Sudoku.q]

theorem usefulPrimeCap_explicit_degree : PowerBoundAt (10 ^ 22) usefulPrimeCap := by
  have hstart : usefulStart ≤ 10 ^ 20 := by
    norm_num [usefulStart, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have h := (((PowerBoundAt.const 8).mul
    (((PowerBoundAt.const_le hstart).add ((PowerBoundAt.const 2).mul PowerBoundAt.id)).add
      (PowerBoundAt.const 1))).pow 2)
  exact h.mono (by norm_num)

theorem digitPrimeCap_explicit_degree (B : ℕ) (hB : B ≤ 10 ^ 5) :
    PowerBoundAt (10 ^ 24) (digitPrimeCap B) := by
  have hU := usefulPrimeCap_explicit_degree
  have hthreshold := ((((hU.pow 2).add ((PowerBoundAt.const 2).mul hU)).add
    (PowerBoundAt.const Sudoku.p)).add (PowerBoundAt.const Sudoku.q)).add (PowerBoundAt.const 3)
  have hthreshold' : PowerBoundAt (10 ^ 23) (fun C => primeThreshold (usefulPrimeCap C)) :=
    hthreshold.mono (by norm_num [Sudoku.p, Sudoku.q])
  have hB' : B + 1 ≤ 10 ^ 6 := by omega
  have h := ((PowerBoundAt.const 8).mul
    ((hthreshold'.add (PowerBoundAt.id.mul (PowerBoundAt.const_le hB'))).add
      (PowerBoundAt.const 1))).pow 2
  exact h.mono (by norm_num)

theorem bit_parameterBase_explicit_degree :
    PowerBoundAt (10 ^ 32) (parameterBase BitSystem.alphabet Sudoku.Width) := by
  have hB := bit_alphabet_le
  have hB' : BitSystem.alphabet + 1 ≤ 10 ^ 6 := by omega
  have hR : PowerBoundAt (10 ^ 30)
      (fun C => digitPrimeCap BitSystem.alphabet C ^ (BitSystem.alphabet + 1)) :=
    ((digitPrimeCap_explicit_degree _ hB).pow _).mono (by nlinarith)
  have hN : residueModulus ≤ 10 ^ 10 := by
    norm_num [residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hS : Sudoku.Width ≤ 10 ^ 10 := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
  have h := ((((((hR.add usefulPrimeCap_explicit_degree).add
    (PowerBoundAt.const_le hN)).add PowerBoundAt.id).add
      (PowerBoundAt.const_le hB')).add (PowerBoundAt.const_le hS)).add (PowerBoundAt.const 2))
  exact h.mono (by norm_num)

theorem geometryPolynomial_explicit_degree : PowerBoundAt (10 ^ 6) geometryPolynomial := by
  have hpair {d : ℕ} {f : ℕ → ℕ} (hf : PowerBoundAt d f) :
      PowerBoundAt (3 * d + 3) (fun x => pairCap (f x)) := by
    have h := (hf.mul hf).add ((PowerBoundAt.const 2).mul hf)
    convert h using 1
    · ring
    · rfl
  have hJ := hpair (hpair (hpair (hpair PowerBoundAt.id)))
  have hH := PowerBoundAt.id.mul
    (((PowerBoundAt.id.pow 5).mul (hJ.add (PowerBoundAt.const 1))).add (PowerBoundAt.const 1))
  have hM := PowerBoundAt.id.mul ((PowerBoundAt.const 2).mul
    ((((PowerBoundAt.const 8).mul (PowerBoundAt.id.pow 5)).add PowerBoundAt.id).add
      (PowerBoundAt.const 3)))
  have hS := ((PowerBoundAt.const 2).mul ((PowerBoundAt.const 1000).mul
    ((((PowerBoundAt.const 2).mul hH).add hM).add (PowerBoundAt.const 1)))).add (PowerBoundAt.const 3)
  have h := (hS.pow 3).mul
    ((((PowerBoundAt.const 3).mul (hS.pow 3)).add (PowerBoundAt.const 6)).pow 3)
  exact h.mono (by norm_num)

/-! Retained estimates for large channel counts. `TernaryBounds` gives sharper
estimates on the smaller range used by the current ternary compiler. -/

theorem usefulPrimeCap_le_of_width {C : ℕ} (hC : 2 ^ 31 ≤ C) :
    usefulPrimeCap C ≤ 256 * C ^ 4 := by
  have hN : residueModulus ≤ C := by
    have : Sudoku.SeedModulus ≤ 2 ^ 31 := by norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    rw [residueModulus_eq]
    omega
  have hbig : 1000 ≤ C := by norm_num at hC; omega
  have hs : usefulStart + 2 * C + 1 ≤ 2 * C ^ 2 := by
    have hN2 := Nat.pow_le_pow_left hN 2
    have hmul := Nat.mul_le_mul_left C hbig
    unfold usefulStart
    norm_num [Sudoku.p, Sudoku.q] at *
    nlinarith
  calc
    _ ≤ (8 * (2 * C ^ 2)) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hs) 2
    _ = _ := by ring

theorem digitPrimeCap_le_of_width {B C : ℕ} (hB : B ≤ 10 ^ 5)
    (hC : 2 ^ 31 ≤ C) : digitPrimeCap B C ≤ C ^ 18 := by
  have hbig : 2 ^ 31 ≤ C := hC
  have hC2 : 2 ≤ C := by omega
  have hB' : B + 1 ≤ C := by norm_num at hB hbig; omega
  have hU := usefulPrimeCap_le_of_width hC
  have hU2 := Nat.pow_le_pow_left hU 2
  have h4 : C ^ 4 ≤ C ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : C ^ 2 ≤ C ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ C ^ 8 := Nat.one_le_pow _ _ (by omega)
  have ht : primeThreshold (usefulPrimeCap C) + C * (B + 1) + 1 ≤ 2 ^ 17 * C ^ 8 := by
    have hm := Nat.mul_le_mul_left C hB'
    unfold primeThreshold
    norm_num [Sudoku.p, Sudoku.q] at *
    nlinarith
  calc
    _ ≤ (8 * (2 ^ 17 * C ^ 8)) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 ht) 2
    _ = 2 ^ 40 * C ^ 16 := by ring
    _ ≤ C ^ 2 * C ^ 16 := Nat.mul_le_mul_right _ (by nlinarith [Nat.pow_le_pow_left hbig 2])
    _ = _ := by ring

/-- A modest degree suffices on the actual range of bit-channel counts. -/
theorem bit_parameterBase_le_of_width {C : ℕ} (hC : 2 ^ 31 ≤ C) :
    parameterBase BitSystem.alphabet Sudoku.Width C ≤ C ^ 2000000 := by
  have hbig : 256 ≤ C := by
    have : 256 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  have hC1 : 1 ≤ C := by omega
  have hB := bit_alphabet_le
  have hQ := digitPrimeCap_le_of_width hB hC
  have hU : usefulPrimeCap C ≤ C ^ 5 := by
    calc
      _ ≤ 256 * C ^ 4 := usefulPrimeCap_le_of_width hC
      _ ≤ C * C ^ 4 := Nat.mul_le_mul_right _ hbig
      _ = _ := by ring
  have hDigits : digitPrimeCap BitSystem.alphabet C ^ (BitSystem.alphabet + 1) ≤ C ^ 1800018 := by
    calc
      _ ≤ (C ^ 18) ^ (BitSystem.alphabet + 1) := Nat.pow_le_pow_left hQ _
      _ = C ^ (18 * (BitSystem.alphabet + 1)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num at hB; omega)
  have hpow {k : ℕ} (hk : k ≤ 1800018) : C ^ k ≤ C ^ 1800018 :=
    Nat.pow_le_pow_right hC1 hk
  have hN : Sudoku.Width ≤ C := by norm_num [Sudoku.Width,Sudoku.q] at *; omega
  have hSeed : Sudoku.SeedModulus ≤ C := by norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q] at *; omega
  have hB' : BitSystem.alphabet + 1 ≤ C := by
    norm_num at hB hC
    omega
  have hsum : parameterBase BitSystem.alphabet Sudoku.Width C ≤ 7 * C ^ 1800018 := by
    have h1 := hpow (k := 1) (by omega)
    have h5 := hpow (k := 5) (by omega)
    have h2 : 2 ≤ C ^ 1800018 := (by omega : 2 ≤ C).trans (by simpa using h1)
    unfold parameterBase
    rw [residueModulus_eq]
    simp only [pow_one] at h1
    calc
      _ ≤ C ^ 1800018 + C ^ 1800018 + C ^ 1800018 + C ^ 1800018 +
          C ^ 1800018 + C ^ 1800018 + C ^ 1800018 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hDigits (hU.trans h5)) (hSeed.trans h1)) h1)
          (hB'.trans h1)) (hN.trans h1)) h2
      _ = _ := by generalize C ^ 1800018 = z; ring
  calc
    _ ≤ 7 * C ^ 1800018 := hsum
    _ ≤ C * C ^ 1800018 := Nat.mul_le_mul_right _ (by omega)
    _ = C ^ 1800019 := by rw [← pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

/-- A coarse bound for horizontal coordinates is already negligible beside
the common stacking cap. -/
theorem horizontalCap_degree_211 : PowerBoundAt 211 horizontalCap := by
  have hpair {d : ℕ} {f : ℕ → ℕ} (hf : PowerBoundAt d f) :
      PowerBoundAt (3 * d + 3) (fun x => pairCap (f x)) := by
    convert (hf.mul hf).add ((PowerBoundAt.const 2).mul hf) using 1
    · ring
    · rfl
  have hJ := hpair (hpair (hpair (hpair PowerBoundAt.id)))
  exact PowerBoundAt.id.mul
    (((PowerBoundAt.id.pow 5).mul (hJ.add (PowerBoundAt.const 1))).add (PowerBoundAt.const 1))

/-- Keep the horizontal bound at `b`, rather than enlarging it to the stacking
cap `b^(12*C)`. This gives a geometric degree of at most one hundred. -/
theorem geometryCap_commonCap_le {b C : ℕ} (hb : 2 ≤ b) (hC : 18 ≤ C) :
    Compiler.Size.geometryCap (horizontalCap b) (stackPolynomial (commonCap b C)) ≤
      commonCap b C ^ 100 := by
  let x := commonCap b C
  have hx : 8003 ≤ x := by
    calc
      _ ≤ 2 ^ (12 * 18) := by norm_num
      _ ≤ b ^ (12 * 18) := Nat.pow_le_pow_left hb _
      _ ≤ x := Nat.pow_le_pow_right (by omega) (by omega)
  have hx1 : 1 ≤ x := by omega
  have hH : horizontalCap b ≤ x :=
    (horizontalCap_degree_211 b hb).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h15 : x ≤ x ^ 5 := Nat.le_self_pow (by decide) x
  have h16 : x ≤ x ^ 6 := Nat.le_self_pow (by decide) x
  have h17 : x ≤ x ^ 7 := Nat.le_self_pow (by decide) x
  have h56 : x ^ 5 ≤ x ^ 6 := Nat.pow_le_pow_right hx1 (by omega)
  have hM : stackPolynomial x ≤ x ^ 7 := by
    have hmul := Nat.mul_le_mul_left (x ^ 6) (show 22 ≤ x by omega)
    have hsq : x ^ 2 ≤ x ^ 6 := Nat.pow_le_pow_right hx1 (by omega)
    unfold stackPolynomial
    nlinarith [show x * x ^ 5 = x ^ 6 by ring, show x * x ^ 6 = x ^ 7 by ring]
  have hS : Compiler.Size.latticeSide (horizontalCap b) (stackPolynomial x) ≤ x ^ 8 := by
    have hmul := Nat.mul_le_mul_left (x ^ 7) hx
    have hpow : 1 ≤ x ^ 7 := Nat.one_le_pow _ _ hx1
    unfold Compiler.Size.latticeSide Compiler.Size.latticeRadius
    nlinarith [show x * x ^ 7 = x ^ 8 by ring]
  have hS3 : Compiler.Size.latticeSide (horizontalCap b) (stackPolynomial x) ^ 3 ≤ x ^ 24 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hS 3
  have hinside : 3 * Compiler.Size.latticeSide (horizontalCap b) (stackPolynomial x) ^ 3 + 6 ≤ x ^ 25 := by
    have hp : 1 ≤ x ^ 24 := Nat.one_le_pow _ _ hx1
    have hm := Nat.mul_le_mul_left (x ^ 24) (show 9 ≤ x by omega)
    nlinarith [show x * x ^ 24 = x ^ 25 by ring]
  calc
    _ ≤ x ^ 24 * (x ^ 25) ^ 3 := Nat.mul_le_mul hS3 (Nat.pow_le_pow_left hinside 3)
    _ = x ^ 99 := by ring
    _ ≤ x ^ 100 := Nat.pow_le_pow_right hx1 (by omega)

/-- The numerical channel estimate shared by the existence and effective proofs. -/
theorem bit_geometry_channel_bound {C : ℕ} (hC : 2 ^ 31 ≤ C) :
    Compiler.Size.geometryCap (horizontalCap (parameterBase BitSystem.alphabet Sudoku.Width C))
        (stackPolynomial (commonCap (parameterBase BitSystem.alphabet Sudoku.Width C) C)) ≤
      C ^ ((12 * 2000000 * 100) * C) := by
  have hbase := bit_parameterBase_le_of_width hC
  have hb : 2 ≤ parameterBase BitSystem.alphabet Sudoku.Width C := by unfold parameterBase; omega
  have h18 : 18 ≤ C := by
    have : 18 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  calc
    _ ≤ commonCap (parameterBase BitSystem.alphabet Sudoku.Width C) C ^ 100 :=
      geometryCap_commonCap_le hb h18
    _ = parameterBase BitSystem.alphabet Sudoku.Width C ^ (12 * C * 100) := by
      rw [commonCap, ← pow_mul]
    _ ≤ (C ^ 2000000) ^ (12 * C * 100) := Nat.pow_le_pow_left hbase _
    _ = _ := by rw [← pow_mul]; congr 1; ring

end
end TranslationTiling.FiniteCompiler.Size
