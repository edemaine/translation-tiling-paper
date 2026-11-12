import TranslationTiling.Rotations.General.ProtrusionGeometry
import TranslationTiling.Rotations.General.FullKeys

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def keyGate (f : Face d) : Lattice d := shift f + gate f

def attachment (f : Face d) : Lattice d := keyGate f - normal f

theorem attachment_axis (f : Face d) :
    attachment f (faceAxis f) = if negative f then (cubeSide d : ℤ)-1 else 0 := by
  simp [attachment,keyGate,Pi.sub_apply,Pi.add_apply,shift_axis,gate,normal]
  cases h : negative f <;> simp [h] <;> ring

theorem attachment_tangent (f : Face d) (j : Fin d) (hj : j ≠ faceAxis f) :
    attachment f j = 3*(margin d : ℤ)+(if negative f then 0 else 1) := by
  simp [attachment,keyGate,Pi.sub_apply,Pi.add_apply,shift_tangent f j hj,gate,hj,
    normal,Pi.single_eq_of_ne hj]

theorem recess_gate (f : Face d) {x : Lattice d} (hx : x ∈ recess f)
    (hn : x (faceAxis f) = gate f (faceAxis f)) : x = gate f := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  have hz : u 0 = 0 := by
    rw [frame_normal_apply] at hn
    simp only [gate,ite_true] at hn
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hn
    all_goals omega
  have he : u = 0 := by
    rw [← Finset.mem_coe,fullKeyFinset_set] at hu
    rcases hu with (hb | hs) | he
    · have hn := (hb 0).1
      simp only [keyLo,ite_true] at hn
      have hp : 0 < neckLength d := by unfold neckLength; omega
      omega
    · have := hs.1
      omega
    · exact he
  subst u
  simp [frameMotion,Motion.apply]

theorem attachment_inCube (f : Face d) : InCube (attachment f) := by
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  intro j
  by_cases hj : j = faceAxis f
  · subst j
    rw [attachment_axis]
    simp only [Pi.zero_apply]
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_false,ite_true]
    all_goals omega
  · rw [attachment_tangent f j hj]
    simp only [Pi.zero_apply]
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_false,ite_true]
    all_goals omega

/-- The one-voxel stagger between opposite faces keeps every key's attachment
voxel out of the recess on the opposite face. -/
theorem attachment_body (hd : 2 ≤ d) (f : Face d) : attachment f ∈ body := by
  apply (body_iff _).mpr
  refine ⟨attachment_inCube f,fun g hg => ?_⟩
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have ha : faceAxis g = faceAxis f := by
    by_contra hn
    have hh := recess_tangent_central g hg (faceAxis f) (Ne.symm hn)
    rw [attachment_axis] at hh
    dsimp [Central] at hh
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hh
    all_goals omega
  have hn : negative g = !negative f := by
    have hh := (recess_bounds g hg).1
    rw [ha,attachment_axis] at hh
    cases h1 : negative g <;> cases h2 : negative f
    all_goals simp only [h1,h2,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true] at hh ⊢
    all_goals first | rfl | omega
  have hgate : attachment f = gate g := by
    apply recess_gate g hg
    simp only [ha,attachment_axis,gate,ite_true,hn]
    cases h : negative f <;> simp [h]
  obtain ⟨j,hj⟩ := exists_other hd (faceAxis f)
  have hjg : j ≠ faceAxis g := by simpa [ha] using hj
  have he := congrFun hgate j
  rw [attachment_tangent f j hj] at he
  simp only [gate,ite_eq_right hjg,hn] at he
  cases h : negative f <;> simp [h] at he

theorem gate_attachment_adjacent (f : Face d) : FaceAdjacent (keyGate f) (attachment f) := by
  have he : attachment f = keyGate f - normal f := rfl
  unfold normal at he
  cases hn : negative f
  · refine ⟨faceAxis f,Or.inl ?_⟩
    rw [he]
    simp only [hn,Bool.false_eq_true,ite_false]
    ext j
    simp only [Pi.sub_apply,Pi.add_apply,Pi.single_apply]
    split_ifs <;> ring
  · refine ⟨faceAxis f,Or.inr ?_⟩
    rw [he]
    simp only [hn,ite_true]
    abel

end TranslationTiling.Rotations.General
