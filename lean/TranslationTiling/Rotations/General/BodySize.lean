import TranslationTiling.Rotations.General.BodyConnectivity
import TranslationTiling.Rotations.General.FullKeys

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def interiorShift (x : Lattice d) : Lattice d := fun j => 2*(margin d : ℤ)+x j

theorem interiorShift_injective : Function.Injective (interiorShift (d := d)) := by
  intro x y he
  ext i
  have hi := congrFun he i
  dsimp [interiorShift] at hi
  omega

/-- A translated copy of every complete key fits strictly inside the intact body. -/
theorem interiorShift_body (f : Face d) {x : Lattice d} (hx : x ∈ fullKeyFinset f) :
    interiorShift x ∈ body := by
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have bounds (j : Fin d) := fullKey_bounds f hx j
  apply (body_iff _).mpr
  constructor
  · intro j
    have hj := bounds j
    dsimp [interiorShift]
    omega
  · intro g hg
    have hn := recess_normal_not_closed g hg
    have hb := bounds (faceAxis g)
    apply hn
    dsimp [interiorShift]
    omega

/-- The body's cardinality exceeds a complete key's cardinality. An embedded key
and the additional body voxel at the origin suffice; no volume formula is needed. -/
theorem body_large (hd : 3 ≤ d) :
    boxVolume d + neckLength d < (body : Finset (Lattice d)).card := by
  let f : Face d := ⟨0,by omega⟩
  let S : Set (Lattice d) := interiorShift '' (fullKeyFinset f : Set (Lattice d))
  have sub : S ⊆ (↑(body : Finset (Lattice d)) : Set (Lattice d)) := by
    rintro _ ⟨x,hx,rfl⟩
    exact interiorShift_body f hx
  have hn : (0 : Lattice d) ∉ S := by
    rintro ⟨x,hx,he⟩
    have hb := fullKey_bounds f hx 0
    have hp := margin_pos (d := d)
    have hh := congrFun he 0
    change 2*(margin d : ℤ)+x 0 = 0 at hh
    omega
  have hstrict : S ⊂ (↑(body : Finset (Lattice d)) : Set (Lattice d)) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨sub,?_⟩
    intro he
    apply hn
    rw [he]
    exact zero_body (by omega : 2 ≤ d)
  have h := Set.ncard_lt_ncard hstrict (Finset.finite_toSet _)
  dsimp [S] at h
  rw [Set.ncard_image_of_injective _ interiorShift_injective,Set.ncard_coe_finset,
    Set.ncard_coe_finset,fullKey_card (by omega : 2 ≤ d) f] at h
  exact h

end TranslationTiling.Rotations.General
