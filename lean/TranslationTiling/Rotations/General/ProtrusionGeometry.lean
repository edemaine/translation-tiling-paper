import TranslationTiling.Rotations.General.BodyGeometry

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def shift (f : Face d) : Lattice d := scale (cubeSide d) (normal f)

@[simp] theorem shift_axis (f : Face d) :
    shift f (faceAxis f) = if negative f then (cubeSide d : ℤ) else -(cubeSide d : ℤ) := by
  simp [shift,scale,normal]

@[simp] theorem shift_tangent (f : Face d) (j : Fin d) (hj : j ≠ faceAxis f) : shift f j = 0 := by
  simp [shift,scale,normal,Pi.single_eq_of_ne hj]

def ProtrusionBounds (f : Face d) (x : Lattice d) : Prop :=
  (if negative f then (cubeSide d : ℤ) ≤ x (faceAxis f) ∧ x (faceAxis f) < (cubeSide d : ℤ)+(margin d : ℤ)
   else -(margin d : ℤ) < x (faceAxis f) ∧ x (faceAxis f) < 0) ∧
  ∀ j, j ≠ faceAxis f → 3*(margin d : ℤ) ≤ x j ∧ x j ≤ 4*(margin d : ℤ)

theorem protrusion_bounds (f : Face d) {x : Lattice d} (hx : x ∈ protrusion f) : ProtrusionBounds f x := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hb := recess_bounds f hy
  change ProtrusionBounds f (shift f + y)
  constructor
  · have hn := hb.1
    simp only [Pi.add_apply,shift_axis]
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false] at hn ⊢
    all_goals omega
  · intro j hj
    change 3*(margin d : ℤ) ≤ shift f j+y j ∧ shift f j+y j ≤ 4*(margin d : ℤ)
    simpa [shift_tangent f j hj] using hb.2 j hj

theorem protrusion_outside (f : Face d) {x : Lattice d} (hx : x ∈ protrusion f) : ¬ InCube x := by
  have hn := (protrusion_bounds f hx).1
  intro hc
  have hcn := hc (faceAxis f)
  dsimp at hcn
  cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false] at hn
  all_goals omega

theorem protrusion_disjoint_body (f : Face d) : Disjoint (protrusion f) body := by
  apply Finset.disjoint_left.mpr
  intro x hx hb
  exact protrusion_outside f hx ((body_iff x).mp hb).1

theorem adjacent_coordinate {x y : Lattice d} (h : FaceAdjacent x y) (i : Fin d) : |x i-y i| ≤ 1 := by
  obtain ⟨k,he | he⟩ := h
  all_goals have hi := congrFun he i
  all_goals by_cases hik : i = k
  all_goals simp only [Pi.add_apply] at hi
  all_goals first
    | subst i; simp only [Pi.single_eq_same] at hi; rw [abs_le]; omega
    | simp only [Pi.single_eq_of_ne hik] at hi; rw [abs_le]; omega

/-- Distinct protrusions are separated by more than a voxel, including at corners. -/
theorem protrusions_separated {f g : Face d} (hfg : f ≠ g) {x y : Lattice d}
    (hx : x ∈ protrusion f) (hy : y ∈ protrusion g) : ¬ FaceAdjacent x y := by
  intro hxy
  have hbf := protrusion_bounds f hx
  have hbg := protrusion_bounds g hy
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have hcoord := abs_le.mp (adjacent_coordinate hxy (faceAxis f))
  by_cases ha : faceAxis f = faceAxis g
  · have hn : negative f ≠ negative g := fun he => hfg (face_ext ha he)
    have hfn := hbf.1
    have hgn := hbg.1
    rw [← ha] at hgn
    cases h1 : negative f <;> cases h2 : negative g
    all_goals simp [h1,h2] at hfn hgn hn
    all_goals omega
  · have hfn := hbf.1
    have hgt := hbg.2 (faceAxis f) ha
    cases h1 : negative f <;> simp only [h1,Bool.false_eq_true,ite_false,ite_true] at hfn
    all_goals omega

end TranslationTiling.Rotations.General
