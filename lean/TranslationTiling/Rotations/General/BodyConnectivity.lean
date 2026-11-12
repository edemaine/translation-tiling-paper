import TranslationTiling.Rotations.General.BodyPaths
import TranslationTiling.Rotations.General.ClearLines

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

/-- The replacement's body remains face connected after deleting any one voxel. -/
theorem body_punctured (hd : 3 ≤ d) (v : Lattice d) :
    Connected ((↑(body : Finset (Lattice d)) : Set (Lattice d)) \ {v}) := by
  classical
  have reach (x : Lattice d) (hx : x ∈ body) (hxv : x ≠ v) :
      ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => z ∈ body ∧ z ≠ v) x y := by
    by_cases ho : ∀ i, Outer (d := d) (x i)
    · exact outer_corner_path hd hx hxv ho
    · push_neg at ho
      obtain ⟨i,hi⟩ := ho
      have hcen : Central (d := d) (x i) := by dsimp [Outer,Central] at *; omega
      obtain ⟨j,hj,hclear⟩ := exists_clear_line hd hx i hcen
      exact clear_line_path hx hxv j hj hclear
  intro x hx y hy
  obtain ⟨a,ha,hav,p1⟩ := reach x hx.1 hx.2
  obtain ⟨b,hb,hbv,p2⟩ := reach y hy.1 hy.2
  have p3 := skeleton_punctured hd v a ⟨ha,hav⟩ b ⟨hb,hbv⟩
  have p3' : FacePath (fun z => z ∈ body ∧ z ≠ v) a b :=
    p3.mono (fun _ hz => ⟨skeleton_body hz.1,hz.2⟩)
  exact (p1.trans p3').trans p2.reverse

theorem zero_body (hd : 2 ≤ d) : (0 : Lattice d) ∈ body := by
  obtain ⟨j,hj⟩ := exists_other hd (0 : Fin d)
  refine two_outer_body ?_ 0 j (Ne.symm hj) ?_ ?_
  · intro i
    have hp := cubeSide_pos (d := d)
    dsimp
    omega
  · left; change (0 : ℤ) ≤ (margin d : ℤ); omega
  · left; change (0 : ℤ) ≤ (margin d : ℤ); omega

/-- Face connectivity of the body follows by deleting a point outside the cube. -/
theorem body_connected (hd : 3 ≤ d) : Connected (↑(body : Finset (Lattice d)) : Set (Lattice d)) := by
  let v : Lattice d := fun _ => -1
  have hn (x : Lattice d) (hx : x ∈ body) : x ≠ v := by
    have h0 := ((body_iff x).mp hx).1 0
    intro he
    rw [he] at h0
    change 0 ≤ (-1 : ℤ) ∧ _ at h0
    omega
  intro x hx y hy
  exact (body_punctured hd v x ⟨hx,hn x hx⟩ y ⟨hy,hn y hy⟩).mono (fun _ hz => hz.1)

end TranslationTiling.Rotations.General
