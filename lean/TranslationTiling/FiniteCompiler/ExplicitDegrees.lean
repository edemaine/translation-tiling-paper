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

end
end TranslationTiling.FiniteCompiler.Size
