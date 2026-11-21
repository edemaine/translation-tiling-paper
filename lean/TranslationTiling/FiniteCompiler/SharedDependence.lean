import TranslationTiling.FiniteCompiler.SharedCoordinates
import TranslationTiling.FiniteCompiler.Dependence

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

section

variable {I Y : Type*} [Fintype I] [DecidableEq I] (L : Layout I)

def lowStep (i : I) : Base L := (0,Function.update 0 i 1)

private theorem periodic_of_sub {X : Type*} [AddGroup X] (f : X → Y) (v : X)
    (h : ∀ x, f (x-v) = f x) : Function.Periodic f v := by
  intro x
  simpa using (h (x+v)).symm

/-- Invariance under the other low generators leaves dependence only
on the selected low input. -/
theorem factor_own_low (f : Base L → Y) (i : I)
    (h : ∀ j, j ≠ i → ∀ v, f (v - lowStep L j) = f v)
    (x : Plane) (k : ∀ i, Low L i) :
    f (x,k) = f (x,Function.update 0 i (k i)) := by
  apply eq_of_update_invariant_off (fun k => f (x,k)) i
  · intro j hji z w
    obtain ⟨a,ha⟩ := ZMod.intCast_surjective (z j - w)
    have he : (x, Function.update z j w) = (x,z) - a • lowStep L j := by
      apply Prod.ext
      · simp [lowStep]
      · funext b
        by_cases hb : b = j
        · subst b
          simp [lowStep,zsmul_eq_mul,ha]
        · simp [lowStep,hb]
    change f (x, Function.update z j w) = f (x,z)
    rw [he]
    exact (periodic_of_sub f (lowStep L j) (h j hji)).sub_zsmul_eq a
  · simp

omit [Fintype I] [DecidableEq I] in
/-- The shared first output factors through the line while keeping the
entire low vector. The private output can additionally use `factor_own_low`. -/
theorem factor_line (f : Base L → Y) (s : ℤ)
    (h : ∀ v, f (v - (((1,-s) : Plane),0)) = f v)
    (x : Plane) (k : ∀ i, Low L i) :
    f (x,k) = f ((0,x.2+s*x.1),k) := by
  have he : (x,k) - x.1 • (((1,-s) : Plane), (0 : ∀ i, Low L i)) =
      ((0,x.2+s*x.1),k) := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [zsmul_eq_mul]
        ring
    · simp
  have hp := (periodic_of_sub f (((1,-s) : Plane),0) h).sub_zsmul_eq (x := (x,k)) x.1
  rwa [he,eq_comm] at hp

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
