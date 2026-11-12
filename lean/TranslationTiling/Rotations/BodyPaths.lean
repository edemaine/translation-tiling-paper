import TranslationTiling.Rotations.LocalGeometry
import TranslationTiling.Rotations.Chambers

namespace TranslationTiling.Rotations.SixKeys

set_option maxHeartbeats 200000

def InCube (x : Point) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 39
def BodyPred (x : Point) : Prop := InCube x ∧
  ¬ (0 ≤ x 0 ∧ x 0 ≤ 4 ∧ x 1 = 12 ∧ x 2 = 12) ∧
  ¬ (5 ≤ x 0 ∧ x 0 ≤ 7 ∧ 12 ≤ x 1 ∧ x 1 ≤ 19 ∧ 12 ≤ x 2 ∧ x 2 ≤ 26) ∧
  ¬ (35 ≤ x 0 ∧ x 0 ≤ 39 ∧ x 1 = 13 ∧ x 2 = 13) ∧
  ¬ (32 ≤ x 0 ∧ x 0 ≤ 34 ∧ 13 ≤ x 1 ∧ x 1 ≤ 22 ∧ 13 ≤ x 2 ∧ x 2 ≤ 24) ∧
  ¬ (0 ≤ x 1 ∧ x 1 ≤ 4 ∧ x 0 = 12 ∧ x 2 = 12) ∧
  ¬ (5 ≤ x 1 ∧ x 1 ≤ 8 ∧ 12 ≤ x 0 ∧ x 0 ≤ 17 ∧ 12 ≤ x 2 ∧ x 2 ≤ 26) ∧
  ¬ (35 ≤ x 1 ∧ x 1 ≤ 39 ∧ x 0 = 13 ∧ x 2 = 13) ∧
  ¬ (31 ≤ x 1 ∧ x 1 ≤ 34 ∧ 13 ≤ x 0 ∧ x 0 ≤ 21 ∧ 13 ≤ x 2 ∧ x 2 ≤ 22) ∧
  ¬ (0 ≤ x 2 ∧ x 2 ≤ 4 ∧ x 0 = 12 ∧ x 1 = 12) ∧
  ¬ (5 ≤ x 2 ∧ x 2 ≤ 9 ∧ 12 ≤ x 0 ∧ x 0 ≤ 17 ∧ 12 ≤ x 1 ∧ x 1 ≤ 23) ∧
  ¬ (35 ≤ x 2 ∧ x 2 ≤ 39 ∧ x 0 = 13 ∧ x 1 = 13) ∧
  ¬ (30 ≤ x 2 ∧ x 2 ≤ 34 ∧ 13 ≤ x 0 ∧ x 0 ≤ 20 ∧ 13 ≤ x 1 ∧ x 1 ≤ 21)

def HolePred (i : Face) (x : Point) : Prop :=
  ![(0 ≤ x 0 ∧ x 0 ≤ 4 ∧ x 1 = 12 ∧ x 2 = 12) ∨
      (5 ≤ x 0 ∧ x 0 ≤ 7 ∧ 12 ≤ x 1 ∧ x 1 ≤ 19 ∧ 12 ≤ x 2 ∧ x 2 ≤ 26),
    (35 ≤ x 0 ∧ x 0 ≤ 39 ∧ x 1 = 13 ∧ x 2 = 13) ∨
      (32 ≤ x 0 ∧ x 0 ≤ 34 ∧ 13 ≤ x 1 ∧ x 1 ≤ 22 ∧ 13 ≤ x 2 ∧ x 2 ≤ 24),
    (0 ≤ x 1 ∧ x 1 ≤ 4 ∧ x 0 = 12 ∧ x 2 = 12) ∨
      (5 ≤ x 1 ∧ x 1 ≤ 8 ∧ 12 ≤ x 0 ∧ x 0 ≤ 17 ∧ 12 ≤ x 2 ∧ x 2 ≤ 26),
    (35 ≤ x 1 ∧ x 1 ≤ 39 ∧ x 0 = 13 ∧ x 2 = 13) ∨
      (31 ≤ x 1 ∧ x 1 ≤ 34 ∧ 13 ≤ x 0 ∧ x 0 ≤ 21 ∧ 13 ≤ x 2 ∧ x 2 ≤ 22),
    (0 ≤ x 2 ∧ x 2 ≤ 4 ∧ x 0 = 12 ∧ x 1 = 12) ∨
      (5 ≤ x 2 ∧ x 2 ≤ 9 ∧ 12 ≤ x 0 ∧ x 0 ≤ 17 ∧ 12 ≤ x 1 ∧ x 1 ≤ 23),
    (35 ≤ x 2 ∧ x 2 ≤ 39 ∧ x 0 = 13 ∧ x 1 = 13) ∨
      (30 ≤ x 2 ∧ x 2 ≤ 34 ∧ 13 ≤ x 0 ∧ x 0 ≤ 20 ∧ 13 ≤ x 1 ∧ x 1 ≤ 21)] i

theorem inRecess_iff_hole (i : Face) (x : Point) : inRecess i x = true ↔ HolePred i x := by
  fin_cases i <;>
    simp [inRecess, HolePred, coordinates, dimensions, axis, negative, tangent₁, tangent₂] <;> omega

theorem mem_body_iff (x : Point) : x ∈ body ↔ BodyPred x := by
  simp only [body, Finset.mem_sdiff, cube, Fintype.mem_piFinset, Finset.mem_Icc,
    removed, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_recess_iff, inRecess_iff_hole]
  simp [BodyPred, InCube, HolePred, Fin.exists_fin_succ, and_assoc]

def Skeleton (x : Point) : Prop := InCube x ∧ ∃ i, x i = 10 ∨ x i = 29

theorem skeleton_body {x : Point} (hx : Skeleton x) : BodyPred x := by
  obtain ⟨bounds, i, hi⟩ := hx
  fin_cases i <;> dsimp at hi <;> simp_all [BodyPred] <;> omega

theorem two_outside_body {x : Point} (hx : InCube x) (i j : Fin 3) (hne : i ≠ j)
    (hi : x i ≤ 10 ∨ 29 ≤ x i) (hj : x j ≤ 10 ∨ 29 ≤ x j) : BodyPred x := by
  fin_cases i <;> fin_cases j <;> dsimp at hne hi hj <;> simp_all
  all_goals simp only [BodyPred]; exact ⟨hx, by omega⟩

theorem inCube_update {x : Point} (hx : InCube x) (i : Fin 3) (t : ℤ)
    (ht : 0 ≤ t ∧ t ≤ 39) : InCube (Function.update x i t) := by
  intro j
  by_cases he : j = i
  · subst j; simpa using ht
  · simpa [he] using hx j

private theorem crossed_01 {x : Point} (hx : BodyPred x)
    (ci : 10 < x 0 ∧ x 0 < 29) (cj : 10 < x 1 ∧ x 1 < 29)
    (t u : ℤ) (ht : 10 ≤ t ∧ t ≤ 29) (hu : 10 ≤ u ∧ u ≤ 29)
    (bt : ¬ BodyPred (Function.update x 0 t))
    (bu : ¬ BodyPred (Function.update x 1 u)) : False := by
  simp [BodyPred, InCube, Fin.forall_fin_succ] at hx bt bu
  omega

private theorem crossed_02 {x : Point} (hx : BodyPred x)
    (ci : 10 < x 0 ∧ x 0 < 29) (cj : 10 < x 2 ∧ x 2 < 29)
    (t u : ℤ) (ht : 10 ≤ t ∧ t ≤ 29) (hu : 10 ≤ u ∧ u ≤ 29)
    (bt : ¬ BodyPred (Function.update x 0 t))
    (bu : ¬ BodyPred (Function.update x 2 u)) : False := by
  simp [BodyPred, InCube, Fin.forall_fin_succ] at hx bt bu
  omega

private theorem bad_with_two_central {x : Point} (hq : InCube x)
    (h1 : 10 ≤ x 1 ∧ x 1 ≤ 29) (h2 : 10 ≤ x 2 ∧ x 2 ≤ 29)
    (hb : ¬ BodyPred x) : HolePred 0 x ∨ HolePred 1 x := by
  by_contra h
  obtain ⟨h0, h1'⟩ := not_or.mp h
  dsimp [HolePred] at h0 h1'
  obtain ⟨a, b⟩ := not_or.mp h0
  obtain ⟨c, d⟩ := not_or.mp h1'
  apply hb
  refine ⟨hq, a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem crossed_12 {x : Point} (hx : BodyPred x)
    (ci : 10 < x 1 ∧ x 1 < 29) (cj : 10 < x 2 ∧ x 2 < 29)
    (t u : ℤ) (ht : 10 ≤ t ∧ t ≤ 29) (hu : 10 ≤ u ∧ u ≤ 29)
    (bt : ¬ BodyPred (Function.update x 1 t))
    (bu : ¬ BodyPred (Function.update x 2 u)) : False := by
  have bt' := bad_with_two_central (inCube_update hx.1 1 t (by omega))
    (by simpa using ht) (by simpa using (show 10 ≤ x 2 ∧ x 2 ≤ 29 by omega)) bt
  have bu' := bad_with_two_central (inCube_update hx.1 2 u (by omega))
    (by simpa using (show 10 ≤ x 1 ∧ x 1 ≤ 29 by omega)) (by simpa using hu) bu
  have a := hx.2.1
  have b := hx.2.2.1
  have c := hx.2.2.2.1
  have d := hx.2.2.2.2.1
  clear hx bt bu
  simp [HolePred] at bt' bu'
  omega

/-- A whole coordinate segment through a surviving voxel reaches both intact planes. -/
theorem clear_line {x : Point} (hx : BodyPred x)
    (central : ∃ i, 10 < x i ∧ x i < 29) :
    ∃ i, 10 < x i ∧ x i < 29 ∧
      ∀ t : ℤ, 10 ≤ t → t ≤ 29 → BodyPred (Function.update x i t) := by
  by_contra! bad
  by_cases c0 : 10 < x 0 ∧ x 0 < 29 <;>
    by_cases c1 : 10 < x 1 ∧ x 1 < 29 <;>
      by_cases c2 : 10 < x 2 ∧ x 2 < 29
  · obtain ⟨t0, ht0, hu0, hb0⟩ := bad 0 c0.1 c0.2
    obtain ⟨t1, ht1, hu1, hb1⟩ := bad 1 c1.1 c1.2
    exact crossed_01 hx c0 c1 t0 t1 ⟨ht0, hu0⟩ ⟨ht1, hu1⟩ hb0 hb1
  · obtain ⟨t0, ht0, hu0, hb0⟩ := bad 0 c0.1 c0.2
    obtain ⟨t1, ht1, hu1, hb1⟩ := bad 1 c1.1 c1.2
    exact crossed_01 hx c0 c1 t0 t1 ⟨ht0, hu0⟩ ⟨ht1, hu1⟩ hb0 hb1
  · obtain ⟨t0, ht0, hu0, hb0⟩ := bad 0 c0.1 c0.2
    obtain ⟨t2, ht2, hu2, hb2⟩ := bad 2 c2.1 c2.2
    exact crossed_02 hx c0 c2 t0 t2 ⟨ht0, hu0⟩ ⟨ht2, hu2⟩ hb0 hb2
  · obtain ⟨t, ht, hu, hb⟩ := bad 0 c0.1 c0.2
    have oj : x 1 ≤ 10 ∨ 29 ≤ x 1 := by omega
    have ok : x 2 ≤ 10 ∨ 29 ≤ x 2 := by omega
    apply hb
    apply two_outside_body (inCube_update hx.1 0 t (by omega)) 1 2 (by decide)
    · simpa using oj
    · simpa using ok
  · obtain ⟨t1, ht1, hu1, hb1⟩ := bad 1 c1.1 c1.2
    obtain ⟨t2, ht2, hu2, hb2⟩ := bad 2 c2.1 c2.2
    exact crossed_12 hx c1 c2 t1 t2 ⟨ht1, hu1⟩ ⟨ht2, hu2⟩ hb1 hb2
  · obtain ⟨t, ht, hu, hb⟩ := bad 1 c1.1 c1.2
    have oj : x 0 ≤ 10 ∨ 29 ≤ x 0 := by omega
    have ok : x 2 ≤ 10 ∨ 29 ≤ x 2 := by omega
    apply hb
    apply two_outside_body (inCube_update hx.1 1 t (by omega)) 0 2 (by decide)
    · simpa using oj
    · simpa using ok
  · obtain ⟨t, ht, hu, hb⟩ := bad 2 c2.1 c2.2
    have oj : x 0 ≤ 10 ∨ 29 ≤ x 0 := by omega
    have ok : x 1 ≤ 10 ∨ 29 ≤ x 1 := by omega
    apply hb
    apply two_outside_body (inCube_update hx.1 2 t (by omega)) 0 1 (by decide)
    · simpa using oj
    · simpa using ok
  · simp [Fin.exists_fin_succ] at central
    tauto

end TranslationTiling.Rotations.SixKeys
