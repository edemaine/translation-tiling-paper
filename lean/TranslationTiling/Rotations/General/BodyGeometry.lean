import TranslationTiling.Rotations.General.Decomposition

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def InCube (x : Lattice d) : Prop := x ∈ Box 0 (fun _ => (cubeSide d : ℤ)-1)

def Central (t : ℤ) : Prop := (margin d : ℤ) < t ∧ t < (cubeSide d : ℤ)-(margin d : ℤ)

def Outer (t : ℤ) : Prop := t ≤ (margin d : ℤ) ∨ (cubeSide d : ℤ)-(margin d : ℤ) ≤ t

def Skeleton (x : Lattice d) : Prop := InCube x ∧
  ∃ i, x i = (margin d : ℤ) ∨ x i = (cubeSide d : ℤ)-(margin d : ℤ)

theorem body_iff (x : Lattice d) : x ∈ body ↔ InCube x ∧ ∀ f : Face d, x ∉ recess f := by
  simp [body,removed,cell,InCube,Finset.mem_biUnion]

theorem inCube_update {x : Lattice d} (hx : InCube x) (i : Fin d) (t : ℤ)
    (ht : 0 ≤ t ∧ t < cubeSide d) : InCube (Function.update x i t) := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self,Pi.zero_apply]
    exact ⟨ht.1,by omega⟩
  · simpa [Function.update_of_ne hj] using hx j

theorem recess_normal_outer (f : Face d) {x : Lattice d} (hx : x ∈ recess f) :
    Outer (d := d) (x (faceAxis f)) := by
  have hb := (recess_bounds f hx).1
  dsimp [Outer]
  cases hn : negative f <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at hb
  all_goals omega

theorem recess_normal_not_closed (f : Face d) {x : Lattice d} (hx : x ∈ recess f) :
    ¬ ((margin d : ℤ) ≤ x (faceAxis f) ∧ x (faceAxis f) ≤ (cubeSide d : ℤ)-(margin d : ℤ)) := by
  have hb := (recess_bounds f hx).1
  cases hn : negative f <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at hb
  all_goals omega

theorem recess_tangent_central (f : Face d) {x : Lattice d} (hx : x ∈ recess f)
    (j : Fin d) (hj : j ≠ faceAxis f) : Central (d := d) (x j) := by
  have hb := (recess_bounds f hx).2 j hj
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  dsimp [Central]
  omega

theorem two_outer_body {x : Lattice d} (hx : InCube x) (i j : Fin d) (hij : i ≠ j)
    (hi : Outer (d := d) (x i)) (hj : Outer (d := d) (x j)) : x ∈ body := by
  apply (body_iff x).mpr
  refine ⟨hx,fun f hf => ?_⟩
  have hai : i = faceAxis f := by
    by_contra hn
    have := recess_tangent_central f hf i hn
    dsimp [Central,Outer] at *
    omega
  have haj : j = faceAxis f := by
    by_contra hn
    have := recess_tangent_central f hf j hn
    dsimp [Central,Outer] at *
    omega
  exact hij (hai.trans haj.symm)

theorem skeleton_body {x : Lattice d} (hx : Skeleton x) : x ∈ body := by
  apply (body_iff x).mpr
  refine ⟨hx.1,fun f hf => ?_⟩
  obtain ⟨i,hi⟩ := hx.2
  by_cases hai : i = faceAxis f
  · subst i
    have := recess_normal_not_closed f hf
    have hL := margin_five_lt_cubeSide (d := d)
    have hp := margin_pos (d := d)
    rcases hi with hi | hi <;> omega
  · have hb := recess_tangent_central f hf i hai
    dsimp [Central] at hb
    rcases hi with hi | hi <;> omega

theorem exists_other (hd : 2 ≤ d) (a : Fin d) : ∃ b : Fin d, b ≠ a := by
  by_cases h : a.val = 0
  · exact ⟨⟨1,by omega⟩,by intro he; have := congrArg Fin.val he; dsimp at this; omega⟩
  · exact ⟨⟨0,by omega⟩,by intro he; have := congrArg Fin.val he; dsimp at this; omega⟩

theorem exists_third (hd : 3 ≤ d) (a b : Fin d) : ∃ c : Fin d, c ≠ a ∧ c ≠ b := by
  by_cases h0 : a.val = 0 ∨ b.val = 0
  · by_cases h1 : a.val = 1 ∨ b.val = 1
    · refine ⟨⟨2,by omega⟩,?_,?_⟩
      all_goals intro he; have := congrArg Fin.val he; dsimp at this; omega
    · refine ⟨⟨1,by omega⟩,?_,?_⟩
      all_goals intro he; have := congrArg Fin.val he; dsimp at this; omega
  · refine ⟨⟨0,by omega⟩,?_,?_⟩
    all_goals intro he; have := congrArg Fin.val he; dsimp at this; omega

end TranslationTiling.Rotations.General
