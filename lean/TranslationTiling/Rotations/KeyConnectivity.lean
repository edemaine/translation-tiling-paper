import TranslationTiling.Rotations.NeckBoxes
import TranslationTiling.Rotations.Protrusions

namespace TranslationTiling.Rotations.SixKeys

theorem coordinates_frame (i : Face) (x : Point) :
    coordinates i ((frameMotion i).apply x) = x :=
  (frameMotion i).injective (frame_coordinates i ((frameMotion i).apply x))

theorem frame_zero (i : Face) : (frameMotion i).apply 0 = gate i := by
  simp [frameMotion, Motion.apply]

theorem frame_recess (i : Face) :
    (frameMotion i).apply '' NeckBox 0 (dimensions i).1 (dimensions i).2.1 (dimensions i).2.2 =
      {x | x ∈ recess i} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    apply (mem_recess_iff _ _).mpr
    simpa [inRecess, coordinates_frame, NeckBox] using hu
  · intro hx
    refine ⟨coordinates i x, ?_, frame_coordinates i x⟩
    have h := (mem_recess_iff _ _).mp hx
    simpa [inRecess, NeckBox] using h

theorem frame_chamber (i : Face) :
    (frameMotion i).apply '' NeckBox 1 (dimensions i).1 (dimensions i).2.1 (dimensions i).2.2 =
      {x | x ∈ chamber i} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro he
      have hu0 : u = 0 := (frameMotion i).injective (he.trans (frame_zero i).symm)
      have hz := congrFun hu0 0
      rcases hu with hs | hb <;> simp at hz <;> omega
    · apply (mem_recess_iff _ _).mpr
      simp only [inRecess, coordinates_frame, decide_eq_true_eq]
      rcases hu with hs | hb
      · left; omega
      · right; exact hb
  · intro hx
    obtain ⟨hg, hr⟩ := Finset.mem_erase.mp hx
    refine ⟨coordinates i x, ?_, frame_coordinates i x⟩
    have hu0 : coordinates i x ≠ 0 := by
      intro he
      have hx' := frame_coordinates i x
      rw [he, frame_zero] at hx'
      exact hg hx'.symm
    have h := (mem_recess_iff _ _).mp hr
    simp only [inRecess, decide_eq_true_eq] at h
    rcases h with hs | hb
    · left
      have hn : coordinates i x 0 ≠ 0 := by
        intro he
        apply hu0
        ext a
        fin_cases a <;> simp_all
      omega
    · right; exact hb

theorem dimensions_pos (i : Face) :
    0 < (dimensions i).1 ∧ 0 < (dimensions i).2.1 ∧ 0 < (dimensions i).2.2 := by
  fin_cases i <;> decide

theorem recess_connected (i : Face) : Connected {x | x ∈ recess i} := by
  rw [← frame_recess]
  obtain ⟨hd, ha, hb⟩ := dimensions_pos i
  exact (frameMotion i).connected (neckBox_connected 0 (by omega) _ _ _ hd ha hb)

theorem chamber_connected (i : Face) : Connected {x | x ∈ chamber i} := by
  rw [← frame_chamber]
  obtain ⟨hd, ha, hb⟩ := dimensions_pos i
  exact (frameMotion i).connected (neckBox_connected 1 (by omega) _ _ _ hd ha hb)

theorem protrusion_connected (i : Face) : Connected {x | x ∈ protrusion i} := by
  let m : Motion := ⟨Orientation.ident, shift i⟩
  have h := m.connected (recess_connected i)
  have he : m.apply = (shift i + ·) := by
    funext x
    simp [m, Motion.apply]
  rw [he] at h
  have hs : ({x : Point | x ∈ recess i} : Set Point) = (recess i : Set Point) := by
    ext x; simp
  rw [hs] at h
  change Connected ((protrusion i : Finset Point) : Set Point)
  simpa only [protrusion, Finset.coe_image] using h

theorem key_core_eq (i : Face) :
    {x | x ∈ protrusion i} \ {shift i + gate i} =
      {x | x ∈ (chamber i).image (shift i + ·)} := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, rfl⟩
    intro he
    exact hn (by simp [he])
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Finset.mem_image.mpr ⟨u, Finset.mem_of_mem_erase hu, rfl⟩,
      fun he => (Finset.mem_erase.mp hu).1 (add_left_cancel he)⟩

end TranslationTiling.Rotations.SixKeys
