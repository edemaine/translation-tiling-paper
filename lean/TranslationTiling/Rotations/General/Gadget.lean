import TranslationTiling.Rotations.General.PlacedKeys
import TranslationTiling.Rotations.General.PeriodicCells

/-! The explicit dimension-dependent replacement cube. The volume and periodic
coverage theorems below do not yet assert orientation forcing for tilings. -/
namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def faceAxis (f : Face d) : Fin d := ⟨f.val / 2,by have := f.isLt; omega⟩

def negative (f : Face d) : Bool := f.val % 2 == 0

/-- Inward unit normal of the indicated face. -/
def normal (f : Face d) : Lattice d := Pi.single (faceAxis f) (if negative f then 1 else -1)

def gate (f : Face d) : Lattice d := fun j =>
  if j = faceAxis f then (if negative f then 0 else (cubeSide d : ℤ)-1)
  else 3*(margin d : ℤ) + if negative f then 0 else 1

def frameOrientation (f : Face d) : Orientation d where
  axes := Equiv.swap 0 (faceAxis f)
  flip j := decide (j = faceAxis f) && !negative f

def frameMotion (f : Face d) : Motion d := ⟨frameOrientation f,gate f⟩

/-- Add the gate voxel to the canonical key. -/
def fullKeyFinset (f : Face d) : Finset (Lattice d) :=
  boxFinset keyLo (keyHi f) ∪ boxFinset stemLo stemHi ∪ {0}

theorem fullKeyFinset_set (f : Face d) :
    (fullKeyFinset f : Set (Lattice d)) = Key f ∪ {0} := by
  ext x
  simp only [fullKeyFinset,Finset.mem_coe,Finset.mem_union,mem_boxFinset,
    Finset.mem_singleton,Key,KeyBox,Set.mem_union,Set.mem_singleton_iff,stem_eq_box]

def recess (f : Face d) : Finset (Lattice d) := (fullKeyFinset f).image (frameMotion f).apply

/-- Select the face whose recess contains this voxel, if any. The ordered finite
search keeps the construction effective without making geometric assumptions. -/
def home (q : Lattice d) : Lattice d :=
  match (List.finRange (2*d)).find? (fun f => q ∈ recess f) with
  | none => 0
  | some f => normal f

def gadget : Finset (Lattice d) := periodicCell (cubeSide d) home

theorem cubeSide_pos : 0 < cubeSide d := by
  unfold cubeSide margin neckLength
  positivity

/-- The replacement has exactly one voxel for each residue class modulo its period. -/
theorem gadget_card : (gadget : Finset (Lattice d)).card = (cubeSide d)^d :=
  periodicCell_card _ _

theorem gadget_exact :
    ∀ x : Lattice d, ∃! z : Lattice d,
      x ∈ (scale (cubeSide d) z + ·) '' (↑(gadget : Finset (Lattice d)) : Set (Lattice d)) :=
  periodicCell_exact _ cubeSide_pos _

/-- Each positioned chamber is rigid under grid rotations and reflections. -/
theorem recess_chamber_rigid (hd : 2 ≤ d) (f g : Face d) (m : Motion d)
    (he : m.apply '' placedKey frameMotion f = placedKey frameMotion g) :
    f = g ∧ ∀ x, m.apply x = x :=
  placed_key_rigid hd frameMotion f g m he

end TranslationTiling.Rotations.General
