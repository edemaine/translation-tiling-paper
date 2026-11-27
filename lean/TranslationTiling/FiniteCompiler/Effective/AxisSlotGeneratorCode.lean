import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalRows
import TranslationTiling.Compiler.EffectiveResidues

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open Compiler.Effective

/-- The unit generator on one axis has residue zero on the other axis. -/
def axisGeneratorCode (p q : ℕ) (a : Bool) : ℕ :=
  residueSearch (p*q) [(p,if a then 0 else 1),(q,if a then 1 else 0)]

@[fun_prop] theorem axisGeneratorCode_primrec :
    Primrec (fun v : ℕ × ℕ × Bool => axisGeneratorCode v.1 v.2.1 v.2.2) := by
  unfold axisGeneratorCode
  apply residueSearch_primrec.comp (g := fun v : ℕ × ℕ × Bool =>
    (v.1*v.2.1,[(v.1,if v.2.2 then 0 else 1),(v.2.1,if v.2.2 then 1 else 0)]))
  have hl : Primrec (fun v : ℕ × ℕ × Bool => if v.2.2 then (0:ℕ) else 1) :=
    (Primrec.dom_bool (fun a => if a then (0:ℕ) else 1)).comp (by fun_prop)
  have hr : Primrec (fun v : ℕ × ℕ × Bool => if v.2.2 then (1:ℕ) else 0) :=
    (Primrec.dom_bool (fun a => if a then (1:ℕ) else 0)).comp (by fun_prop)
  fun_prop

theorem axisGeneratorCode_correct {k m : ℕ} (s : AxisParameters k m)
    (i : WangSlot k m) (a : Bool) :
    axisGeneratorCode (s.lowAxis i false) (s.lowAxis i true) a =
      (AxisSlot.axisGenerator (s.lowAxis_coprime i) a).val.val := by
  let p := s.lowAxis i false
  let q := s.lowAxis i true
  have : NeZero (s.low i) := ⟨(Nat.mul_pos (NeZero.pos p) (NeZero.pos q)).ne'⟩
  let e := s.lowEquiv i
  let cp : ℕ := if a then 0 else 1
  let cq : ℕ := if a then 1 else 0
  apply (residueSearch_of_equiv e.toEquiv ((cp : ZMod p),(cq : ZMod q)) [(p,cp),(q,cq)] ?_).trans
  · cases a <;> simp [e,lowEquiv,AxisSlot.axisGenerator,AxisSlot.axisEmbed,cp,cq] <;> rfl
  · intro n
    have h := map_natCast e n
    change e (n : ZMod (s.low i)) = ((n : ZMod p),(n : ZMod q)) at h
    rw [show e.toEquiv (n : ZMod (s.low i)) = _ from h,Prod.mk.injEq]
    simp only [Congruences,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,
      forall_eq,← (ZMod.val_injective p).eq_iff,← (ZMod.val_injective q).eq_iff,ZMod.val_natCast]

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
