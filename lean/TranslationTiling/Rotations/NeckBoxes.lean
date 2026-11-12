import TranslationTiling.Rotations.Motions
import TranslationTiling.Rotations.LocalGeometry

namespace TranslationTiling.Rotations.SixKeys

def NeckBox (lo : ℤ) (d a b : ℕ) : Set Point := {x |
  (lo ≤ x 0 ∧ x 0 ≤ 4 ∧ x 1 = 0 ∧ x 2 = 0) ∨
  (5 ≤ x 0 ∧ x 0 < 5+d ∧ 0 ≤ x 1 ∧ x 1 < a ∧ 0 ≤ x 2 ∧ x 2 < b)}

theorem neckBox_connected (lo : ℤ) (hl : 0 ≤ lo ∧ lo ≤ 1) (d a b : ℕ)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) : Connected (NeckBox lo d a b) := by
  have path (x : Point) (hx : x ∈ NeckBox lo d a b) :
      FacePath (· ∈ NeckBox lo d a b) x ![lo,0,0] := by
    have bounds : lo ≤ x 0 ∧ x 0 < 5+d ∧ 0 ≤ x 1 ∧ x 1 < a ∧ 0 ≤ x 2 ∧ x 2 < b := by
      rcases hx with hs | hc <;> omega
    have shrink₁ (z : Point) (hz : z ∈ NeckBox lo d a b) (t : ℤ)
        (ht : 0 ≤ t ∧ t ≤ z 1) : Function.update z 1 t ∈ NeckBox lo d a b := by
      rcases hz with hs | hc
      · left; simp; omega
      · right; simp; omega
    have shrink₂ (z : Point) (hz : z ∈ NeckBox lo d a b) (t : ℤ)
        (ht : 0 ≤ t ∧ t ≤ z 2) : Function.update z 2 t ∈ NeckBox lo d a b := by
      rcases hz with hs | hc
      · left; simp; omega
      · right; simp; omega
    have p₁ : FacePath (· ∈ NeckBox lo d a b) x (Function.update x 1 0) := by
      apply FacePath.axis
      intro t ht hu
      apply shrink₁ x hx t
      rw [min_eq_right bounds.2.2.1] at ht
      rw [max_eq_left bounds.2.2.1] at hu
      exact ⟨ht, hu⟩
    have h₁ := shrink₁ x hx 0 ⟨le_rfl, bounds.2.2.1⟩
    have p₂ : FacePath (· ∈ NeckBox lo d a b) (Function.update x 1 0)
        (Function.update (Function.update x 1 0) 2 0) := by
      apply FacePath.axis
      intro t ht hu
      apply shrink₂ _ h₁ t
      have hnonneg : 0 ≤ (Function.update x 1 0) 2 := by simpa using bounds.2.2.2.2.1
      rw [min_eq_right hnonneg] at ht
      rw [max_eq_left hnonneg] at hu
      exact ⟨ht, hu⟩
    have hend : Function.update (Function.update x 1 0) 2 0 = ![x 0,0,0] := by
      ext i; fin_cases i <;> simp
    rw [hend] at p₂
    have p₃ : FacePath (· ∈ NeckBox lo d a b) (![x 0,0,0]) ![lo,0,0] := by
      have he : Function.update (![x 0,0,0] : Point) 0 lo = ![lo,0,0] := by
        ext i; fin_cases i <;> simp
      rw [← he]
      apply FacePath.axis
      intro t ht hu
      simp only [Matrix.cons_val_zero] at ht hu
      rw [min_eq_right bounds.1] at ht
      rw [max_eq_left bounds.1] at hu
      by_cases hs : t ≤ 4
      · left; simp; omega
      · right; simp; omega
    exact (p₁.trans p₂).trans p₃
  intro x hx y hy
  exact (path x hx).trans (path y hy).reverse

def frameOrientation (i : Face) : Orientation where
  axes := if axis i = 0 then Equiv.refl _ else
    if axis i = 1 then Equiv.swap 0 1 else (Equiv.swap 0 1).trans (Equiv.swap 0 2)
  flip j := decide (j = axis i) && !negative i

def frameMotion (i : Face) : Motion := ⟨frameOrientation i, gate i⟩

theorem frame_localPoint (i : Face) (k u v : ℕ) :
    (frameMotion i).apply ![(k : ℤ),(u : ℤ),(v : ℤ)] = localPoint i k u v := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [frameMotion, frameOrientation, Motion.apply, Orientation.sign,
      localPoint, gate, normal, axis, negative, tangent₁, tangent₂, Equiv.swap_apply_def] <;> ring

theorem frame_coordinates (i : Face) (x : Point) :
    (frameMotion i).apply (coordinates i x) = x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [frameMotion, frameOrientation, Motion.apply, Orientation.sign,
      coordinates, gate, normal, axis, negative, tangent₁, tangent₂, Equiv.swap_apply_def] <;> ring

end TranslationTiling.Rotations.SixKeys
