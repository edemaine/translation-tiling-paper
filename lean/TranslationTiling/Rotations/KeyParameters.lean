import TranslationTiling.Rotations.LocalGeometry

namespace TranslationTiling.Rotations.SixKeys

/-- Enumerate the four neck voxels first, then the 360 box voxels. -/
def chamberVoxel (i : Face) (j : Fin 364) : Point :=
  if j.val < 4 then localPoint i (j.val + 1) 0 0 else
    let a := (dimensions i).2.1
    let b := (dimensions i).2.2
    localPoint i (5 + (j.val - 4) / (a*b))
      (((j.val - 4) / b) % a) ((j.val - 4) % b)

theorem chamberVoxel_ne_gate (i : Face) (j : Fin 364) : chamberVoxel i j ≠ gate i := by
  intro he
  have hh := congrFun (congrArg (coordinates i) he) 0
  have hg : coordinates i (gate i) = 0 := by
    ext k; fin_cases i <;> fin_cases k <;>
      simp [coordinates, gate, axis, negative, tangent₁, tangent₂]
  simp only [chamberVoxel] at hh
  split_ifs at hh <;> simp [coordinates_localPoint, hg] at hh
  all_goals fin_cases i <;> (try simp [dimensions] at hh) <;> omega

theorem chamberVoxel_mem (i : Face) (j : Fin 364) : chamberVoxel i j ∈ chamber i := by
  rw [chamber, Finset.mem_erase]
  refine ⟨chamberVoxel_ne_gate i j, (mem_recess_iff _ _).mpr ?_⟩
  unfold chamberVoxel
  split_ifs with hj
  · simp [inRecess, coordinates_localPoint]; omega
  · have hbound := j.isLt
    fin_cases i <;> simp [inRecess, coordinates_localPoint, dimensions] <;> omega

theorem chamberVoxel_injective (i : Face) : Function.Injective (chamberVoxel i) := by
  intro j k he
  have h0 := congrFun (congrArg (coordinates i) he) 0
  have h1 := congrFun (congrArg (coordinates i) he) 1
  have h2 := congrFun (congrArg (coordinates i) he) 2
  apply Fin.ext
  simp only [chamberVoxel] at h0 h1 h2
  split_ifs at h0 h1 h2 <;> simp [coordinates_localPoint] at h0 h1 h2
  all_goals fin_cases i <;> simp [dimensions] at * <;> omega

theorem chamberVoxel_surjective (i : Face) {x : Point} (hx : x ∈ chamber i) :
    ∃ j, chamberVoxel i j = x := by
  obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
  simp only [recess, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_range] at hx
  rcases hx with ⟨k, hk, rfl⟩ | ⟨k, hk, u, hu, v, hv, rfl⟩
  · have hpos : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      subst k
      exact hne (by simp [localPoint])
    refine ⟨⟨k-1, by omega⟩, ?_⟩
    have he : k - 1 + 1 = k := by omega
    simp [chamberVoxel, show k-1<4 by omega, he]
  · let n := 4 + k * ((dimensions i).2.1 * (dimensions i).2.2) + u * (dimensions i).2.2 + v
    have hn : n < 364 := by
      fin_cases i <;> simp [n, dimensions] at * <;> omega
    refine ⟨⟨n, hn⟩, ?_⟩
    have hn4 : ¬ n < 4 := by dsimp [n]; omega
    simp only [chamberVoxel, if_neg hn4]
    have he0 : (n-4) / ((dimensions i).2.1 * (dimensions i).2.2) = k := by
      fin_cases i <;> simp [n, dimensions] at * <;> omega
    have he1 : (n-4) / (dimensions i).2.2 % (dimensions i).2.1 = u := by
      fin_cases i <;> simp [n, dimensions] at * <;> omega
    have he2 : (n-4) % (dimensions i).2.2 = v := by
      fin_cases i <;> simp [n, dimensions] at * <;> omega
    rw [he0, he1, he2]

theorem chamber_eq_image (i : Face) :
    chamber i = Finset.univ.image (chamberVoxel i) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨chamberVoxel_surjective i, by rintro ⟨j, rfl⟩; exact chamberVoxel_mem i j⟩

theorem chamber_card (i : Face) : (chamber i).card = 364 := by
  rw [chamber_eq_image, Finset.card_image_of_injective _ (chamberVoxel_injective i)]
  simp

end TranslationTiling.Rotations.SixKeys
