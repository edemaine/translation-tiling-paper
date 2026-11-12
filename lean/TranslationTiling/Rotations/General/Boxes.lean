import TranslationTiling.Rotations.General.Motions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

namespace TranslationTiling.Rotations.General

variable {d : ℕ}

/-- Closed lattice rectangle, with independently specified coordinate intervals. -/
def Box (lo hi : Lattice d) : Set (Lattice d) := {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i}

/-- Effective enumeration of the rectangle's lattice points. -/
def boxFinset (lo hi : Lattice d) : Finset (Lattice d) :=
  Fintype.piFinset (fun i => Finset.Icc (lo i) (hi i))

@[simp] theorem mem_boxFinset (lo hi x : Lattice d) :
    x ∈ boxFinset lo hi ↔ x ∈ Box lo hi := by
  simp [boxFinset,Fintype.mem_piFinset,Box]

theorem box_finite (lo hi : Lattice d) : (Box lo hi).Finite := by
  have he : (boxFinset lo hi : Set (Lattice d)) = Box lo hi := by ext; simp
  rw [← he]
  exact Finset.finite_toSet _

theorem box_ncard (lo hi : Lattice d) :
    (Box lo hi).ncard = ∏ i, (hi i + 1 - lo i).toNat := by
  have he : (boxFinset lo hi : Set (Lattice d)) = Box lo hi := by ext; simp
  rw [← he,Set.ncard_coe_finset]
  simp [boxFinset,Fintype.card_piFinset,Int.card_Icc]

theorem box_path (lo hi x y : Lattice d) (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) :
    FacePath (· ∈ Box lo hi) x y := by
  classical
  let fill (s : Finset (Fin d)) : Lattice d := fun j => if j ∈ s then y j else x j
  have bounds (s : Finset (Fin d)) : fill s ∈ Box lo hi := by
    intro j
    dsimp [fill]
    split_ifs <;> first | exact hy j | exact hx j
  have path (s : Finset (Fin d)) : FacePath (· ∈ Box lo hi) x (fill s) := by
    induction s using Finset.induction_on with
    | empty => simpa [fill] using (Relation.ReflTransGen.refl : FacePath (· ∈ Box lo hi) x x)
    | @insert i s his ih =>
      have hu : fill (insert i s) = Function.update (fill s) i (y i) := by
        ext j
        by_cases h : j = i <;> simp [fill,h]
      rw [hu]
      apply ih.trans
      apply FacePath.axis
      intro t ht ht'
      intro j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
        have h := bounds s i
        have h' := hy i
        exact ⟨le_trans (le_min h.1 h'.1) ht, le_trans ht' (max_le h.2 h'.2)⟩
      · simpa [Function.update_of_ne hj] using bounds s j
  simpa [fill] using path Finset.univ

theorem box_connected (lo hi : Lattice d) : Connected (Box lo hi) :=
  fun x hx y hy => box_path lo hi x y hx hy

/-- Coordinates attaining both endpoints suffice to recover a rectangle from its set. -/
theorem box_bounds_eq {lo hi lo' hi' : Lattice d}
    (h : ∀ i, lo i ≤ hi i) (h' : ∀ i, lo' i ≤ hi' i)
    (he : Box lo hi = Box lo' hi') : lo = lo' ∧ hi = hi' := by
  have hlo : lo ∈ Box lo hi := fun i => ⟨le_rfl,h i⟩
  have hhi : hi ∈ Box lo hi := fun i => ⟨h i,le_rfl⟩
  have hlo' : lo' ∈ Box lo' hi' := fun i => ⟨le_rfl,h' i⟩
  have hhi' : hi' ∈ Box lo' hi' := fun i => ⟨h' i,le_rfl⟩
  rw [he] at hlo hhi
  rw [← he] at hlo' hhi'
  exact ⟨funext (fun i => le_antisymm (hlo' i).1 (hlo i).1),
    funext (fun i => le_antisymm (hhi i).2 (hhi' i).2)⟩

def Motion.boxLo (m : Motion d) (lo hi : Lattice d) : Lattice d := fun i =>
  m.offset i + if m.orientation.flip i then -hi (m.orientation.axes i) else lo (m.orientation.axes i)

def Motion.boxHi (m : Motion d) (lo hi : Lattice d) : Lattice d := fun i =>
  m.offset i + if m.orientation.flip i then -lo (m.orientation.axes i) else hi (m.orientation.axes i)

theorem Motion.image_box (m : Motion d) (lo hi : Lattice d) :
    m.apply '' Box lo hi = Box (m.boxLo lo hi) (m.boxHi lo hi) := by
  have mem (x : Lattice d) : m.apply x ∈ Box (m.boxLo lo hi) (m.boxHi lo hi) ↔ x ∈ Box lo hi := by
    constructor
    · intro h j
      have hj := h (m.orientation.axes.symm j)
      simp only [Motion.apply,Pi.add_apply,Orientation.linear_apply,Equiv.apply_symm_apply,
        Motion.boxLo,Motion.boxHi,Orientation.sign] at hj
      split_ifs at hj <;> omega
    · intro h i
      have hi := h (m.orientation.axes i)
      simp only [Motion.apply,Pi.add_apply,Orientation.linear_apply,
        Motion.boxLo,Motion.boxHi,Orientation.sign]
      split_ifs <;> omega
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem x).mpr hx
  · intro hy
    refine ⟨m.inverse.apply y,?_,m.apply_inverse_apply y⟩
    apply (mem _).mp
    simpa using hy

/-- A grid motion preserves each side length up to its coordinate permutation. -/
theorem Motion.box_width {lo hi lo' hi' : Lattice d} (m : Motion d)
    (h : ∀ i, lo i ≤ hi i) (h' : ∀ i, lo' i ≤ hi' i)
    (he : m.apply '' Box lo hi = Box lo' hi') (i : Fin d) :
    hi' i - lo' i = hi (m.orientation.axes i) - lo (m.orientation.axes i) := by
  rw [m.image_box] at he
  have hb : ∀ j, m.boxLo lo hi j ≤ m.boxHi lo hi j := by
    intro j
    have hj := h (m.orientation.axes j)
    dsimp [Motion.boxLo,Motion.boxHi]
    split_ifs <;> omega
  obtain ⟨hl,hh⟩ := box_bounds_eq hb h' he
  rw [← hl,← hh]
  dsimp [Motion.boxHi,Motion.boxLo]
  split_ifs <;> omega

end TranslationTiling.Rotations.General
