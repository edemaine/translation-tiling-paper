import TranslationTiling.Proofs.KimPieceConnectivity
import TranslationTiling.Proofs.KimBoundaryConnectivity
import TranslationTiling.Proofs.KimShellGeometry

/-! Connectivity of Kim's explicit shell, without a rigidity hypothesis. -/

namespace TranslationTiling.Kim

theorem shell_piece_path (l i : ℕ) (hi : i < (boundary l).length)
    (a b : Lattice 3) (ha : a ∈ piece (boundary l).length (i + 1))
    (hb : b ∈ piece (boundary l).length (i + 1)) :
    FacePath (fun z => z ∈ shell l)
      ((scale (boundary l).length : ℤ) • (boundary l)[i] + a)
      ((scale (boundary l).length : ℤ) • (boundary l)[i] + b) := by
  apply Relation.ReflTransGen.lift (fun z =>
    (scale (boundary l).length : ℤ) • (boundary l)[i] + z) _
    (piece_connected (boundary l).length (i + 1) (by omega) (by omega) a ha b hb)
  intro x y hxy
  exact ⟨(mem_shell_iff _ _).mpr ⟨i, hi, x, hxy.1, rfl⟩,
    (mem_shell_iff _ _).mpr ⟨i, hi, y, hxy.2.1, rfl⟩,
    adjacent_add_left _ hxy.2.2⟩

theorem shell_connected (l : ℕ) (hl : 0 < l) : FaceConnected (shell l) := by
  let m := (boundary l).length
  let s : ℤ := scale m
  let P := fun z => z ∈ shell l
  let At := fun q z => ∃ (i : ℕ) (hi : i < m), (boundary l)[i] = q ∧
    ∃ a ∈ piece m (i + 1), z = s • q + a
  have at_mem (q z : Lattice 3) (hz : At q z) : P z := by
    obtain ⟨i, hi, hq, a, ha, rfl⟩ := hz
    exact (mem_shell_iff _ _).mpr ⟨i, hi, a, ha, by rw [hq]⟩
  have within (q : Lattice 3) (i : ℕ) (hi : i < m) (hq : (boundary l)[i] = q)
      (a b : Lattice 3) (ha : a ∈ piece m (i + 1)) (hb : b ∈ piece m (i + 1)) :
      FacePath P (s • q + a) (s • q + b) := by
    simpa only [hq] using shell_piece_path l i hi a b ha hb
  have same (q x y : Lattice 3) (hx : At q x) (hy : At q y) : FacePath P x y := by
    obtain ⟨i, hi, hqi, a, ha, rfl⟩ := hx
    obtain ⟨j, hj, hqj, b, hb, rfl⟩ := hy
    obtain ⟨c, hc, d, hd, hcd⟩ := pieces_adjacent m (i + 1) (j + 1)
      (by omega) (by omega) (by omega) (by omega)
    exact ((within q i hi hqi a c ha hc).tail
      ⟨at_mem q _ ⟨i, hi, hqi, c, hc, rfl⟩,
        at_mem q _ ⟨j, hj, hqj, d, hd, rfl⟩, adjacent_add_left _ hcd⟩).trans
      (within q j hj hqj d b hd hb)
  have forward (q r x y : Lattice 3) (k : Fin 3) (he : r = q + Pi.single k 1)
      (hx : At q x) (hy : At r y) : FacePath P x y := by
    obtain ⟨i, hi, hqi, a, ha, rfl⟩ := hx
    obtain ⟨j, hj, hrj, b, hb, rfl⟩ := hy
    obtain ⟨c, hc, d, hd, hcd⟩ := pieces_external_adjacent m (i + 1) (j + 1)
      (by omega) (by omega) (by omega) (by omega) k
    have hsum : s • r + d = s • q + (s • Pi.single k 1 + d) := by
      rw [he, smul_add]; abel
    have contact : FaceAdjacent (s • q + c) (s • r + d) := by
      rw [hsum]; exact adjacent_add_left _ hcd
    exact ((within q i hi hqi a c ha hc).tail
      ⟨at_mem q _ ⟨i, hi, hqi, c, hc, rfl⟩,
        at_mem r _ ⟨j, hj, hrj, d, hd, rfl⟩, contact⟩).trans
      (within r j hj hrj d b hd hb)
  have edge (q r x y : Lattice 3) (he : FaceAdjacent q r)
      (hx : At q x) (hy : At r y) : FacePath P x y := by
    obtain ⟨k, hk | hk⟩ := he
    · exact forward q r x y k hk hx hy
    · exact FacePath.reverse (forward r q y x k hk hy hx)
  have inhabited (q : Lattice 3) (hq : q ∈ boundary l) : ∃ z, At q z := by
    obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil (piece m (i + 1))
      (piece_nonempty m (i + 1) (by omega) (by omega))
    exact ⟨s • q + a, i, hi, hqi, a, ha, rfl⟩
  have route (q r : Lattice 3) (hp : FacePath (fun z => z ∈ boundary l) q r) :
      ∀ x y, At q x → At r y → FacePath P x y := by
    induction hp with
    | refl => exact same q
    | @tail r t hp hrt ih =>
      intro x y hx hy
      obtain ⟨z, hz⟩ := inhabited r hrt.1
      exact (ih x z hx hz).trans (edge r t z y hrt.2.2 hz hy)
  intro x hx y hy
  obtain ⟨i, hi, a, ha, rfl⟩ := (mem_shell_iff _ _).mp hx
  obtain ⟨j, hj, b, hb, rfl⟩ := (mem_shell_iff _ _).mp hy
  exact route _ _ (boundary_connected l hl _ (List.getElem_mem hi) _ (List.getElem_mem hj))
    _ _ ⟨i, hi, rfl, a, ha, rfl⟩ ⟨j, hj, rfl, b, hb, rfl⟩

/-- Arbitrary-tiling coset rigidity is the only remaining Kim input. -/
theorem rigidity_of_cosets
    (cosets : CosetRigidity) : Rigidity :=
  rigidity_of_connected_cosets (fun l hl => shell_connected l (by omega)) cosets

end TranslationTiling.Kim
