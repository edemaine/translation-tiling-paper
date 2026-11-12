import TranslationTiling.Rotations.Geometry

namespace TranslationTiling.Rotations.SixKeys

def coordinates (i : Face) (x : Point) : Point :=
  ![if negative i then x (axis i) else 39 - x (axis i),
    x (tangent₁ i) - (if negative i then 12 else 13),
    x (tangent₂ i) - (if negative i then 12 else 13)]

theorem coordinates_localPoint (i : Face) (k u v : ℕ) :
    coordinates i (localPoint i k u v) = ![(k : ℤ), (u : ℤ), (v : ℤ)] := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [coordinates, localPoint, normal, gate, tangent₁, tangent₂, axis, negative] <;> omega

theorem reconstruct (i : Face) (x : Point)
    (hk : 0 ≤ coordinates i x 0) (hu : 0 ≤ coordinates i x 1)
    (hv : 0 ≤ coordinates i x 2) :
    localPoint i (coordinates i x 0).toNat (coordinates i x 1).toNat
      (coordinates i x 2).toNat = x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [coordinates, localPoint, normal, gate, tangent₁, tangent₂, axis, negative] at * <;> omega

def inRecess (i : Face) (x : Point) : Bool :=
  let c := coordinates i x
  decide ((0 ≤ c 0 ∧ c 0 ≤ 4 ∧ c 1 = 0 ∧ c 2 = 0) ∨
    (5 ≤ c 0 ∧ c 0 < 5 + (dimensions i).1 ∧
      0 ≤ c 1 ∧ c 1 < (dimensions i).2.1 ∧ 0 ≤ c 2 ∧ c 2 < (dimensions i).2.2))

theorem mem_recess_iff (i : Face) (x : Point) : x ∈ recess i ↔ inRecess i x = true := by
  simp only [recess, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, u, hu, v, hv, rfl⟩)
    · simp [inRecess, coordinates_localPoint]; omega
    · simp [inRecess, coordinates_localPoint]; right; omega
  · intro h
    change decide _ = true at h
    rw [decide_eq_true_eq] at h
    rcases h with h | h
    · left
      refine ⟨(coordinates i x 0).toNat, by omega, ?_⟩
      have recon := reconstruct i x h.1 (by omega) (by omega)
      simpa [h.2.2.1, h.2.2.2] using recon
    · right
      refine ⟨(coordinates i x 0 - 5).toNat, by omega,
        (coordinates i x 1).toNat, by omega,
        (coordinates i x 2).toNat, by omega, ?_⟩
      have recon := reconstruct i x (by omega) h.2.2.1 h.2.2.2.2.1
      have he : 5 + (coordinates i x 0 - 5).toNat = (coordinates i x 0).toNat := by omega
      rw [he]
      exact recon

end TranslationTiling.Rotations.SixKeys
