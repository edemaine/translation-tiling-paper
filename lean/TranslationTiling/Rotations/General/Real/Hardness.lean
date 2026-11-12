import TranslationTiling.Rotations.General.Real.Protect
import TranslationTiling.Rotations.General.Padding
import TranslationTiling.FiniteCompiler.Effective.SizeBound
import TranslationTiling.Proofs.Complexity

namespace TranslationTiling.Rotations.General.Real
noncomputable section
variable {d : ℕ} [NeZero d]

/-- Treat the existing optimized translation compiler as a black box: pad it
with zero coordinates, then apply the dimension-preserving rotation wrapper. -/
def rotationCompile (hd : 3 ≤ d) (T : LeanWang.TileSet) : Tile d :=
  General.protect ((FiniteCompiler.Effective.optimizedCompile T).map (pad hd))

theorem rotationCompile_computable (hd : 3 ≤ d) : Computable (rotationCompile hd) := by
  exact General.protect_primrec.to_comp.comp
    ((padTile_computable hd).comp FiniteCompiler.Effective.optimizedCompile_computable)

theorem rotationCompile_nonempty (hd : 3 ≤ d) (T : LeanWang.TileSet) : rotationCompile hd T ≠ [] := by
  dsimp only [rotationCompile]
  apply General.protect_nonempty hd
  have hn := (FiniteCompiler.Effective.optimizedCompile_channel_bound T).1
  intro hmap
  exact hn (List.map_eq_nil_iff.mp hmap)

theorem rotationCompile_connected (hd : 3 ≤ d) (T : LeanWang.TileSet) :
    FaceConnected (rotationCompile hd T) := by
  apply General.protect_connected hd
  exact pad_connected hd _ (FiniteCompiler.Effective.optimizedCompile_channel_bound T).2.1

theorem rotationCompile_correct (hd : 3 ≤ d) (allowed : Set (Rotation d))
    (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ProtectedEuclideanTileable allowed (rotationCompile hd T) := by
  obtain ⟨hne,_,hopt,_⟩ := FiniteCompiler.Effective.optimizedCompile_channel_bound T
  have hn : (FiniteCompiler.Effective.optimizedCompile T).map (pad hd) ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have h := hopt.trans ((tiles_pad_iff hd _).symm.trans (protect_correct hd _ hn allowed hid))
  exact ⟨fun ht => ⟨rotationCompile_connected hd T,h.mp ht⟩,fun ht => h.mpr ht.2⟩

/-- Exact size before applying the existing optimized compiler's size bound. -/
theorem rotationCompile_length (hd : 3 ≤ d) (T : LeanWang.TileSet) :
    (rotationCompile hd T).length=(cubeSide d)^d*(FiniteCompiler.Effective.optimizedCompile T).length := by
  rw [rotationCompile,General.protect_length,List.length_map]

/-- The general wrapper changes only the dimension-dependent multiplicative
constant in the optimized compiler's closed-form size estimate. -/
theorem rotationCompile_length_bound (hd : 3 ≤ d) (T : LeanWang.TileSet) :
    ((rotationCompile hd T).length : ℝ) ≤ (2 : ℝ)^(10*(d+1)^2)*
      ((T.length : ℝ)+4)^(10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  have hb := General.protect_length_bound ((FiniteCompiler.Effective.optimizedCompile T).map (pad hd))
  simp only [List.length_map] at hb
  have hb' : ((rotationCompile hd T).length : ℝ) ≤
      (2 : ℝ)^(10*(d+1)^2)*(FiniteCompiler.Effective.optimizedCompile T).length := by
    exact_mod_cast hb
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (FiniteCompiler.Effective.optimizedCompile_real_bound T) (by positivity))

/-- Hardness in every fixed dimension at least three, for any allowed rotation
set containing the identity. Reflections may be included or excluded. -/
theorem rotation_coRE_hard (hd : 3 ≤ d) (allowed : Set (Rotation d))
    (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed) :
    LeanWang.CoREHard (ProtectedEuclideanTileable allowed) := by
  intro α _ P hP
  exact (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨rotationCompile hd,rotationCompile_computable hd,rotationCompile_correct hd allowed hid⟩

theorem rotation_undecidable (hd : 3 ≤ d) (allowed : Set (Rotation d))
    (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed) :
    ¬ ComputablePred (ProtectedEuclideanTileable allowed) := by
  intro h
  exact LeanWang.Kari.domino_problem_undecidable
    (ComputablePred.computable_of_manyOneReducible
      ⟨rotationCompile hd,rotationCompile_computable hd,rotationCompile_correct hd allowed hid⟩ h)

end

/-- Proper arbitrary Euclidean rotations and all arbitrary Euclidean rotations
and reflections both give co-RE-hard problems in every dimension d ≥ 3. -/
theorem dimension_hardness (d : ℕ) (hd : 3 ≤ d) :
    LeanWang.CoREHard (ProtectedEuclideanTileable (d := d) {r | Proper r}) ∧
    ¬ ComputablePred (ProtectedEuclideanTileable (d := d) {r | Proper r}) ∧
    LeanWang.CoREHard (ProtectedEuclideanTileable (d := d) Set.univ) ∧
    ¬ ComputablePred (ProtectedEuclideanTileable (d := d) Set.univ) := by
  letI : NeZero d := ⟨by omega⟩
  exact ⟨rotation_coRE_hard hd _ proper_ident,rotation_undecidable hd _ proper_ident,
    rotation_coRE_hard hd _ (Set.mem_univ _),rotation_undecidable hd _ (Set.mem_univ _)⟩

end TranslationTiling.Rotations.General.Real
