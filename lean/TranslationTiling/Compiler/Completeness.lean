import TranslationTiling.Compiler.CommonSolution
import TranslationTiling.Compiler.Soundness

namespace TranslationTiling.Compiler

noncomputable section

private theorem digit_of_seed_residue {T : LeanWang.TileSet} (r : ℕ) (hr : r.Prime)
    (hwidth : r ∣ residueModulus) (hproduct : r ∣ Sudoku.p * Sudoku.q)
    (n : Column T) (x : Plane) (k t : ℕ) (ht : (t : ZMod r) ≠ 0)
    (hx : SharedSeed.residue T x =
      (((Sudoku.p * Sudoku.q * k : ℕ) : ZMod residueModulus), (t : ZMod residueModulus))) :
    (Sudoku.lastDigit r hr (lineValue n x)).val = (t : ZMod r) := by
  let f : ZMod residueModulus →+* ZMod r := ZMod.castHom hwidth (ZMod r)
  have hprodcast : ((Sudoku.p * Sudoku.q : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hproduct
  have hmul : (Sudoku.p : ZMod r) * (Sudoku.q : ZMod r) = 0 := by
    simpa only [Nat.cast_mul] using hprodcast
  have hx₁ : (x.1 : ZMod r) = 0 := by
    have h := congrArg (fun s : SharedSeed.Residues T => f s.1) hx
    simpa only [SharedSeed.residue, map_intCast, map_mul, map_natCast,
      Nat.cast_mul, hmul, zero_mul] using h
  have hx₂ : (x.2 : ZMod r) = (t : ZMod r) := by
    have h := congrArg (fun s : SharedSeed.Residues T => f s.2) hx
    simpa only [SharedSeed.residue, map_intCast, map_natCast] using h
  have hval : (lineValue n x : ZMod r) = (t : ZMod r) := by
    simp [lineValue, hx₁, hx₂]
  have hnot : ¬ (r : ℤ) ∣ lineValue n x := by
    intro hd
    exact ht (hval.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))
  exact (Sudoku.lastDigit_eq_of_not_dvd r hr hnot).trans hval

/-- The canonical decorated array meets both seed regions. The decoration is
unrestricted in these regions, exactly as in the paper. -/
theorem canonical_seed_regions {T : LeanWang.TileSet}
    (τ : ℕ × ℕ → LeanWang.TileIn T) :
    ∀ t n x, SharedSeed.residue T x ∈ seedActiveRegion T t →
      SeedSet t (Sudoku.canonical τ (τ (0, 0)) n (lineValue n x)) := by
  intro t n x hx
  fin_cases t
  · obtain ⟨y, hy⟩ : SharedSeed.residue T x ∈ SharedSeed.firstRegion T := by
      simpa [seedActiveRegion] using hx
    have hs : SharedSeed.residue T x =
        (((Sudoku.p * Sudoku.q * y.val : ℕ) : ZMod residueModulus), 1) := hy.symm
    constructor
    · exact digit_of_seed_residue (T := T) Sudoku.p (by decide) (by rw [residueModulus_eq]; decide) (by decide)
        n x y.val 1 (by decide) (by simpa only [Nat.cast_one] using hs)
    · exact digit_of_seed_residue (T := T) Sudoku.q (by decide) (by rw [residueModulus_eq]; decide) (by decide)
        n x y.val 1 (by decide) (by simpa only [Nat.cast_one] using hs)
  · obtain ⟨u, hu⟩ : SharedSeed.residue T x ∈ SharedSeed.secondRegion T := by
      simpa [seedActiveRegion] using hx
    have hs : SharedSeed.residue T x =
        (((Sudoku.p * Sudoku.q * (2 * u.1.val + u.2.val) : ℕ) : ZMod residueModulus), 2) :=
      hu.symm
    constructor
    · exact digit_of_seed_residue (T := T) Sudoku.p (by decide) (by rw [residueModulus_eq]; decide) (by decide)
        n x _ 2 (by decide) hs
    · exact digit_of_seed_residue (T := T) Sudoku.q (by decide) (by rw [residueModulus_eq]; decide) (by decide)
        n x _ 2 (by decide) hs

theorem exists_solution_of_wang {T : LeanWang.TileSet} (E : EncodingParameters T)
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ, hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  exact ⟨CommonModel.commonGraph E (Sudoku.canonical τ),
    CommonModel.common_solution E (Sudoku.canonical τ)
      (Sudoku.canonical_lineRule τ hτ) (canonical_seed_regions τ)⟩

theorem finite_system_iff_wang (sound : Sudoku.Soundness) {T : LeanWang.TileSet}
    (E : EncodingParameters T) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A :=
  ⟨exists_solution_of_wang E, fun ⟨_, hA⟩ => wang_of_solves E sound hA⟩

end

end TranslationTiling.Compiler
