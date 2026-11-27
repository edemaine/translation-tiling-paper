import TranslationTiling.FiniteCompiler.Effective.AxisSlotArithmetic

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical BigOperators
noncomputable section

variable {k m : ℕ} (s : AxisParameters k m)

instance firstSize_neZero (i : AxisRow k m) : NeZero (s.layout.firstSize i) := by
  rcases i with i | i
  · exact inferInstanceAs (NeZero ((fourValueLayout 0).firstSize i))
  · exact ⟨Nat.one_ne_zero⟩

instance secondSize_neZero (i : AxisRow k m) : NeZero (s.layout.secondSize i) := by
  rcases i with i | i | i
  · exact inferInstanceAs (NeZero ((fourValueLayout 0).secondSize i))
  · refine ⟨?_⟩
    change (∏ j : Fin 3, s.marker i j) ≠ 0
    exact (Finset.prod_pos (fun j _ => (s.prime_isPrime (.inl (i,.inr j))).pos)).ne'
  · exact ⟨(s.prime_isPrime (.inr i)).ne_zero⟩

theorem positive_order : 0 < order s.layout := by
  unfold order rowModulus
  exact Nat.mul_pos (by decide) (Finset.prod_pos fun i _ =>
    Nat.mul_pos (Nat.mul_pos (pow_pos (s.layout.lowSize_pos i) _) (NeZero.pos _)) (NeZero.pos _))

instance order_neZero : NeZero (order s.layout) := ⟨s.positive_order.ne'⟩

instance finiteFactor : Fintype (Factor s.layout) := by
  unfold Factor Private Square
  haveI (i : AxisRow k m) : NeZero ((s.layout.lowSize i)^2) :=
    ⟨(pow_pos (s.layout.lowSize_pos i) _).ne'⟩
  infer_instance

instance finiteExtra : Fintype s.Extra := by
  unfold Extra Private Square
  haveI (i : AxisAddedRow k m) : NeZero ((s.layout.lowSize (.inr i))^2) :=
    ⟨(pow_pos (s.layout.lowSize_pos (.inr i)) _).ne'⟩
  infer_instance

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
