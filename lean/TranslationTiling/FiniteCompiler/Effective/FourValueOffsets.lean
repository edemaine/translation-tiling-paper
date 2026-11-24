import TranslationTiling.FiniteCompiler.FourValueShift

namespace TranslationTiling.FiniteCompiler.Packed

open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000

private abbrev J := FourValueShift.Index

variable {m : J → ℕ}

def shiftDifference (z : FourValueShift.Shift m) : FourValueShift.Shift m :=
  z - FourValueShift.shift z


/-- A record is recoverable from the horizontal offset and the useful
shift together. Off the binary cube the useful shift is the index itself. -/
theorem activation_record_injective {r M : ℕ} [NeZero M]
    (e : ZMod M ≃ ZMod r × FourValueShift.Shift m) :
    Function.Injective (fun v : ZMod r × FourValueShift.Shift m =>
      ((e.symm (v.1,shiftDifference v.2)).val,FourValueShift.shift v.2)) := by
  intro u v huv
  have hh := congrArg Prod.fst huv
  have hs := congrArg Prod.snd huv
  have he := e.symm.injective (ZMod.val_injective M hh)
  have hlow := congrArg Prod.fst he
  change u.1 = v.1 at hlow
  refine Prod.ext hlow ?_
  have hd := congrArg Prod.snd he
  change u.2 - FourValueShift.shift u.2 = v.2 - FourValueShift.shift v.2 at hd
  change FourValueShift.shift u.2 = FourValueShift.shift v.2 at hs
  rwa [hs,sub_left_inj] at hd


end
end TranslationTiling.FiniteCompiler.Packed
