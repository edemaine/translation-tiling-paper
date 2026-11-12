import TranslationTiling.Rotations.Euclidean.Definitions
import TranslationTiling.Proofs.FacePaths
import Mathlib.Algebra.Order.Floor.Ring

namespace TranslationTiling.Rotations.Euclidean

noncomputable section

open Set

def block (lo hi : Lattice 3) : Finset (Lattice 3) :=
  Fintype.piFinset fun i => Finset.Icc (lo i) (hi i)

theorem mem_block (lo hi p : Lattice 3) : p ∈ block lo hi ↔ ∀ i, lo i ≤ p i ∧ p i ≤ hi i := by
  simp [block, Fintype.mem_piFinset]

/-- A rectangular block of lattice voxels fills its entire closed box. -/
theorem solid_block (lo hi : Lattice 3) (hlohi : ∀ i, lo i ≤ hi i) (x : EPoint) :
    x ∈ solid (block lo hi) ↔
      ∀ i, (lo i : ℝ)-(1:ℝ)/2 ≤ x i ∧ x i ≤ (hi i : ℝ)+(1:ℝ)/2 := by
  constructor
  · rintro ⟨p, hp, hx⟩ i
    have hb := (mem_block _ _ _).mp hp i
    have hv := abs_le.mp (hx i)
    have h₁ : (lo i : ℝ) ≤ (p i : ℝ) := by exact_mod_cast hb.1
    have h₂ : (p i : ℝ) ≤ (hi i : ℝ) := by exact_mod_cast hb.2
    constructor <;> linarith
  · intro hx
    let p : Lattice 3 := fun i => min (hi i) ⌊x i + (1:ℝ)/2⌋
    have hp : p ∈ block lo hi := by
      apply (mem_block _ _ _).mpr
      intro i
      have hlow : lo i ≤ ⌊x i + (1:ℝ)/2⌋ := Int.le_floor.mpr (by have := hx i; linarith)
      dsimp [p]
      exact ⟨le_min (hlohi i) hlow, min_le_left _ _⟩
    refine ⟨p, hp, ?_⟩
    intro i
    apply abs_le.mpr
    have hf := Int.floor_le (x i + (1:ℝ)/2)
    have hff := Int.lt_floor_add_one (x i + (1:ℝ)/2)
    have hib := hx i
    by_cases hh : ⌊x i + (1:ℝ)/2⌋ ≤ hi i
    · dsimp [p]
      rw [min_eq_right hh]
      constructor <;> linarith
    · have hcast : (hi i : ℝ) < (⌊x i + (1:ℝ)/2⌋ : ℝ) := by exact_mod_cast (by omega : hi i < ⌊x i+(1:ℝ)/2⌋)
      dsimp [p]
      rw [min_eq_left (by omega : hi i ≤ ⌊x i+(1:ℝ)/2⌋)]
      constructor <;> linarith

def openBox (lo hi : Fin 3 → ℝ) : Set EPoint := {x | ∀ i, lo i < x i ∧ x i < hi i}

theorem isOpen_openBox (lo hi : Fin 3 → ℝ) : IsOpen (openBox lo hi) := by
  have he : openBox lo hi = ⋂ i : Fin 3, {x : EPoint | lo i < x i ∧ x i < hi i} := by
    ext x; simp [openBox]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)).inter
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i) continuous_const)

theorem openBox_subset_interior_block (lo hi : Lattice 3) (hlohi : ∀ i, lo i ≤ hi i) :
    openBox (fun i => (lo i : ℝ)-(1:ℝ)/2) (fun i => (hi i : ℝ)+(1:ℝ)/2) ⊆
      interior (solid (block lo hi)) := by
  apply (isOpen_openBox _ _).subset_interior_iff.mpr
  intro x hx
  apply (solid_block lo hi hlohi x).mpr
  intro i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

def starLo (x : EPoint) : Lattice 3 := fun i => ⌈x i-(1:ℝ)/2⌉
def starHi (x : EPoint) : Lattice 3 := fun i => ⌊x i+(1:ℝ)/2⌋
def star (x : EPoint) : Finset (Lattice 3) := block (starLo x) (starHi x)

theorem mem_star (x : EPoint) (p : Lattice 3) : p ∈ star x ↔ x ∈ voxel p := by
  rw [star, mem_block]
  constructor
  · intro h i
    have hh := h i
    have hlo := Int.ceil_le.mp hh.1
    have hhi := Int.le_floor.mp hh.2
    apply abs_le.mpr
    constructor <;> linarith
  · intro h i
    have hh := abs_le.mp (h i)
    exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

theorem star_bounds (x : EPoint) (i : Fin 3) : starLo x i ≤ starHi x i := by
  apply Int.le_floor.mpr
  have h := Int.ceil_lt_add_one (x i-(1:ℝ)/2)
  change (⌈x i-(1:ℝ)/2⌉ : ℝ) ≤ x i+(1:ℝ)/2
  linarith

/-- If every voxel incident to a point is present, the point is interior.
This includes points on voxel faces, edges, and corners. -/
theorem star_interior (x : EPoint) {F : Finset (Lattice 3)} (h : star x ⊆ F) :
    x ∈ interior (solid F) := by
  have hx : x ∈ openBox (fun i => (starLo x i : ℝ)-(1:ℝ)/2)
      (fun i => (starHi x i : ℝ)+(1:ℝ)/2) := by
    intro i
    have hlo := Int.ceil_lt_add_one (x i-(1:ℝ)/2)
    have hhi := Int.lt_floor_add_one (x i+(1:ℝ)/2)
    dsimp [starLo, starHi]
    constructor <;> linarith
  have hx' := openBox_subset_interior_block (starLo x) (starHi x) (star_bounds x) hx
  apply interior_mono (show solid (star x) ⊆ solid F from ?_) hx'
  rintro y ⟨p, hp, hy⟩
  exact ⟨p, h hp, hy⟩

/-- Every boundary point lies on a face crossing from a present to an absent
voxel. The two incident voxels both contain that boundary point. -/
theorem frontier_neighbor {F : Finset (Lattice 3)} {x : EPoint} (hx : x ∈ frontier (solid F)) :
    ∃ p ∈ F, ∃ q ∉ F, FaceAdjacent p q ∧ x ∈ voxel p ∧ x ∈ voxel q := by
  have hxS : x ∈ solid F := by
    have hh := hx.1
    rwa [(isClosed_solid F).closure_eq] at hh
  obtain ⟨p, hp, hxp⟩ := hxS
  have hpStar := (mem_star x p).mpr hxp
  obtain ⟨q, hqStar, hq⟩ : ∃ q ∈ star x, q ∉ F := by
    by_contra! hall
    exact hx.2 (star_interior x hall)
  have path := FacePath.box3 (fun z => z ∈ star x) (starLo x) (starHi x) p q
    ((mem_block _ _ _).mp hpStar) ((mem_block _ _ _).mp hqStar)
    (by intro z hz; exact (mem_block _ _ _).mpr hz)
  by_contra! none
  have stay (z : Lattice 3) (hpath : FacePath (fun z => z ∈ star x) p z) : z ∈ F := by
    induction hpath with
    | refl => exact hp
    | @tail a b _ hab ih =>
      by_contra hb
      exact none a ih b hb hab.2.2 ((mem_star x a).mp hab.1) ((mem_star x b).mp hab.2.1)
  exact hq (stay q path)

theorem frontier_single_entrance (K H : Finset (Lattice 3)) (g : Lattice 3)
    (boundary : ∀ p ∈ K, ∀ q, FaceAdjacent p q → q ∈ K ∨ q = g ∨ q ∈ H) :
    frontier (solid K) ⊆ solid H ∪ voxel g := by
  intro x hx
  obtain ⟨p, hp, q, hq, hpq, _, hxq⟩ := frontier_neighbor hx
  rcases boundary p hp q hpq with hqK | rfl | hqH
  · exact (hq hqK).elim
  · exact Or.inr hxq
  · exact Or.inl ⟨q, hqH, hxq⟩

end
end TranslationTiling.Rotations.Euclidean
