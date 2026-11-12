import TranslationTiling.Rotations.KeyGeometry
import TranslationTiling.Proofs.Basic
import Mathlib.Algebra.Module.Pi

namespace TranslationTiling.Rotations.SixKeys

def grid (x : Point) : Point := (40 : ℤ) • x

theorem grid_injective : Function.Injective grid := by
  intro x y he
  ext i
  have hi := congrFun he i
  change 40 * x i = 40 * y i at hi
  omega

theorem cube_grid_unique {z w q r : Point} (hq : q ∈ cube) (hr : r ∈ cube)
    (he : grid z + q = grid w + r) : z = w ∧ q = r := by
  have hz : z = w := by
    ext i
    have hqi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq i)
    have hri := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr i)
    have hi := congrFun he i
    change 40 * z i + q i = 40 * w i + r i at hi
    omega
  subst w
  exact ⟨rfl, add_left_cancel he⟩

theorem exists_cube_grid (x : Point) :
    ∃ z q : Point, q ∈ cube ∧ grid z + q = x := by
  refine ⟨(fun i => x i / 40), (fun i => x i % 40), ?_, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hl := Int.emod_nonneg (x i) (by decide : (40 : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (x i) (by decide : (0 : ℤ) < 40)
    omega
  · ext i
    have h := Int.emod_add_mul_ediv (x i) 40
    change 40 * (x i / 40) + x i % 40 = x i
    omega

def Home (q j : Point) : Prop :=
  (j = 0 ∧ q ∈ body) ∨ ∃ i, j = normal i ∧ q ∈ recess i

theorem home_unique {q j k : Point} (hj : Home q j) (hk : Home q k) : j = k := by
  rcases hj with ⟨rfl, hB⟩ | ⟨i, rfl, hi⟩ <;>
    rcases hk with ⟨rfl, hB'⟩ | ⟨l, rfl, hl⟩
  · rfl
  · exact ((Finset.mem_sdiff.mp hB).2
      (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hl⟩)).elim
  · exact ((Finset.mem_sdiff.mp hB').2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)).elim
  · by_cases he : i = l
    · rw [he]
    · exact (Finset.disjoint_left.mp (recesses_disjoint he) hi hl).elim

theorem gadget_home {t : Point} (ht : t ∈ gadget) :
    ∃ q ∈ cube, ∃ j, Home q j ∧ t = grid j + q := by
  rcases Finset.mem_union.mp ht with hB | hp
  · exact ⟨t, (Finset.mem_sdiff.mp hB).1, 0, Or.inl ⟨rfl, hB⟩, by simp [grid]⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨q, recess_subset_cube i hq, normal i, Or.inr ⟨i, rfl, hq⟩, rfl⟩

theorem cube_home {q : Point} (hq : q ∈ cube) :
    ∃ j t, t ∈ gadget ∧ Home q j ∧ t = grid j + q := by
  by_cases hr : q ∈ removed
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hr
    refine ⟨normal i, shift i + q, ?_, Or.inr ⟨i, rfl, hi⟩, rfl⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨q, hi, rfl⟩⟩)
  · have hb : q ∈ body := Finset.mem_sdiff.mpr ⟨hq, hr⟩
    exact ⟨0, q, Finset.mem_union_left _ hb, Or.inl ⟨rfl, hb⟩, by simp [grid]⟩

/-- Moving each recess by an entire grid step preserves the fundamental domain. -/
theorem fundamental_domain : ExactTiling (Set.range grid) {t | t ∈ gadget} := by
  constructor
  · rintro ⟨a, t⟩ ⟨b, u⟩ he
    obtain ⟨z, hz⟩ := a.property
    obtain ⟨w, hw⟩ := b.property
    obtain ⟨q, hq, j, hj, ht⟩ := gadget_home t.property
    obtain ⟨r, hr, k, hk, hu⟩ := gadget_home u.property
    have hgrid : grid (z+j) + q = grid (w+k) + r := by
      change a.val + t.val = b.val + u.val at he
      rw [← hz, ← hw, ht, hu] at he
      simpa [grid, smul_add, add_assoc] using he
    obtain ⟨_, hqr⟩ := cube_grid_unique hq hr hgrid
    subst r
    have hjk := home_unique hj hk
    have htu : t.val = u.val := by rw [ht, hu, hjk]
    have hab : a.val = b.val := by
      change a.val + t.val = b.val + u.val at he
      rw [htu] at he
      exact add_right_cancel he
    exact Prod.ext (Subtype.ext hab) (Subtype.ext htu)
  · intro x
    obtain ⟨z, q, hq, hx⟩ := exists_cube_grid x
    obtain ⟨j, t, ht, _, he⟩ := cube_home hq
    refine ⟨(⟨grid (z-j), z-j, rfl⟩, ⟨t, ht⟩), ?_⟩
    change grid (z-j) + t = x
    rw [he, ← hx]
    simp only [grid, smul_sub]
    abel

theorem grid_unique {z w t u : Point} (ht : t ∈ gadget) (hu : u ∈ gadget)
    (he : grid z + t = grid w + u) : z = w ∧ t = u := by
  have hp := fundamental_domain.1
    (a₁ := (⟨grid z, z, rfl⟩, ⟨t, ht⟩))
    (a₂ := (⟨grid w, w, rfl⟩, ⟨u, hu⟩)) he
  exact ⟨grid_injective (congrArg (fun p => p.1.val) hp),
    congrArg (fun p => p.2.val) hp⟩

end TranslationTiling.Rotations.SixKeys
