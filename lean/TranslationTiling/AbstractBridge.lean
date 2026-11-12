import TranslationTiling.Statements
import TranslationTiling.FiniteCompiler.Effective.SizeBound
import TranslationTiling.Rotations.Euclidean.Main
import TranslationTiling.Rotations.General.Real.Hardness
import TranslationTiling.EuclideanMembership.EffectiveSystem
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Projection

/-!
# Bridge to `Abstract.lean`

`Abstract.lean` states tiling problems with points of `Fin d → ℤ`, the same
model of `ℤᵈ` as the rest of the development (`Tile d = List (Lattice d)`). This
file shows that the predicates written there agree with the ones proved about in the
project. Its statements spell out the predicates of `Abstract.lean` explicitly,
so that `Abstract.lean` can cite them by definitional unfolding.

All mathematical inputs are proved, as in `Statements.lean`.
-/

namespace TranslationTiling.AbstractBridge

open TranslationTiling

variable {d : ℕ}

/-- The predicate of `Abstract.Tiles`, spelled out. -/
def AbsTiles (P : List (Fin d → ℤ)) : Prop :=
  ∃ T : Set (Fin d → ℤ), ∀ x : Fin d → ℤ, ∃! t : Fin d → ℤ, t ∈ T ∧ x - t ∈ P

theorem exactTiling_iff {G : Type*} [Add G] (A S : Set G) :
    ExactTiling A S ↔ ∀ x : G, ∃! t : G × G, t.1 ∈ A ∧ t.2 ∈ S ∧ t.1 + t.2 = x := by
  unfold ExactTiling
  rw [Function.bijective_iff_existsUnique]
  refine forall_congr' fun x => ?_
  constructor
  · rintro ⟨a, ha, hx⟩
    refine ⟨(a.1.1, a.2.1), ⟨a.1.2, a.2.2, ha⟩, ?_⟩
    rintro ⟨u, v⟩ ⟨hu, hv, huv⟩
    have := hx ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ huv
    rw [← this]
  · rintro ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, hx⟩
    refine ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, huv, ?_⟩
    rintro ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
    have := hx (u', v') ⟨hu', hv', h⟩
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-- In a group, exact coverage says each point lies in exactly one translate. -/
theorem exactTiling_iff' {G : Type*} [AddCommGroup G] (A S : Set G) :
    ExactTiling A S ↔ ∀ x : G, ∃! t : G, t ∈ A ∧ x - t ∈ S := by
  rw [exactTiling_iff]
  refine forall_congr' fun x => ?_
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, hx⟩
    refine ⟨u, ⟨hu, ?_⟩, ?_⟩
    · rw [← huv]; simpa using hv
    · rintro t ⟨ht, hts⟩
      have := hx (t, x - t) ⟨ht, hts, by simp⟩
      exact congrArg Prod.fst this
  · rintro ⟨u, ⟨hu, hv⟩, hx⟩
    refine ⟨(u, x - u), ⟨hu, hv, by simp⟩, ?_⟩
    rintro ⟨t, s⟩ ⟨ht, hs, hts⟩
    have : t = u := hx t ⟨ht, by rw [← hts]; simpa using hs⟩
    subst this
    have : s = x - t := by rw [← hts]; simp
    rw [this]

theorem tiles_iff (F : Tile d) : Tiles F ↔ AbsTiles F := by
  simp only [Tiles, AbsTiles, exactTiling_iff', Set.mem_setOf_eq]

/-! ### Connected prototiles -/

/-- Face adjacency: the points are at `ℓ¹` distance one. -/
def AbsAdjacent (a b : Fin d → ℤ) : Prop :=
  ∑ i, |a i - b i| = 1

/-- The predicate of `Abstract.Connected`, spelled out. -/
def AbsConnected (P : List (Fin d → ℤ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ AbsAdjacent a b) p q

theorem faceAdjacent_iff (a b : Lattice d) : FaceAdjacent a b ↔ AbsAdjacent a b := by
  constructor
  · rintro ⟨i,h | h⟩
    all_goals unfold AbsAdjacent
    all_goals apply Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) (show (∑ j : Fin d, if j=i then (1 : ℤ) else 0)=1 by simp)
    all_goals have hj := congrFun h j
    all_goals by_cases hji : j=i
    all_goals simp only [Pi.add_apply] at hj
    all_goals first
      | subst j; simp only [Pi.single_eq_same] at hj; simp only [ite_true]; rw [abs_eq] <;> omega
      | simp only [Pi.single_eq_of_ne hji,add_zero] at hj; simp only [ite_eq_right hji]; rw [abs_eq_zero]; omega
  · intro hs
    change ∑ j, |a j-b j|=1 at hs
    have hex : ∃ i : Fin d, 0 < |a i-b i| := by
      by_contra! hn
      have hz (j : Fin d) : |a j-b j|=0 := le_antisymm (hn j) (abs_nonneg _)
      simp only [hz,Finset.sum_const_zero] at hs
      omega
    obtain ⟨i,hi⟩ := hex
    have hu : |a i-b i| ≤ 1 := by
      rw [← hs]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (a j-b j)) (Finset.mem_univ i)
    have hi1 : |a i-b i|=1 := by omega
    have off (j : Fin d) (hj : j ≠ i) : a j=b j := by
      have ht := Finset.sum_le_sum_of_subset_of_nonneg
        (show ({i,j} : Finset (Fin d)) ⊆ Finset.univ from Finset.subset_univ _)
        (fun k _ _ => abs_nonneg (a k-b k))
      rw [Finset.sum_pair (Ne.symm hj),hi1,hs] at ht
      have hz : |a j-b j|=0 := by have := abs_nonneg (a j-b j); omega
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    have hsign : a i-b i=1 ∨ a i-b i= -1 := by rw [abs_eq] at hi1 <;> omega
    rcases hsign with hp | hn
    · refine ⟨i,Or.inr ?_⟩
      ext j
      by_cases hj : j=i
      · subst j; simp only [Pi.add_apply,Pi.single_eq_same]; omega
      · simp [Pi.add_apply,Pi.single_eq_of_ne hj,off j hj]
    · refine ⟨i,Or.inl ?_⟩
      ext j
      by_cases hj : j=i
      · subst j; simp only [Pi.add_apply,Pi.single_eq_same]; omega
      · simp [Pi.add_apply,Pi.single_eq_of_ne hj,off j hj]

theorem faceConnected_iff (F : Tile d) : FaceConnected F ↔ AbsConnected F := by
  simp only [FaceConnected, AbsConnected, faceAdjacent_iff]

/-! ### Real translations -/

/-- The solid body of a prototile: the union of its unit cubes. -/
private def CoordinateSolid (P : List (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  {x | ∃ p ∈ P, ∀ i, (p i : ℝ) ≤ x i ∧ x i ≤ p i + 1}

/-- The predicate of `Abstract.RealTiles`, spelled out. -/
private def CoordinateRealTiles (P : List (Fin d → ℤ)) : Prop :=
  ∃ T : Set (Fin d → ℝ), ∀ᵐ x ∂MeasureTheory.volume,
    ∃! t : Fin d → ℝ, t ∈ T ∧ x - t ∈ CoordinateSolid P

theorem existsUnique_subtype_iff {α : Type*} (T : Set α) (p : α → Prop) :
    (∃! t : T, p t.val) ↔ ∃! t : α, t ∈ T ∧ p t := by
  constructor
  · rintro ⟨⟨t, ht⟩, hp, hu⟩
    exact ⟨t, ⟨ht, hp⟩, fun s ⟨hs, hps⟩ => congrArg Subtype.val (hu ⟨s, hs⟩ hps)⟩
  · rintro ⟨t, ⟨ht, hp⟩, hu⟩
    exact ⟨⟨t, ht⟩, hp, fun s hps => Subtype.ext (hu s.val ⟨s.property, hps⟩)⟩

private theorem coordinate_realTiles_iff (F : Tile d) : RealTiles F ↔ CoordinateRealTiles F := by
  exact exists_congr fun T => Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    existsUnique_subtype_iff T (fun t => x - t ∈ CubeUnion F))

private abbrev EPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The public solid, expressed directly in Euclidean coordinates. -/
def AbsSolid (P : List (Fin d → ℤ)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ p ∈ P, ∀ i, (p i : ℝ) ≤ x i ∧ x i ≤ p i + 1}

def AbsRealTiles (P : List (Fin d → ℤ)) : Prop :=
  ∃ T : Set (EuclideanSpace ℝ (Fin d)), ∀ᵐ x ∂MeasureTheory.volume,
    ∃! t : EuclideanSpace ℝ (Fin d), t ∈ T ∧ x - t ∈ AbsSolid P

/-- Mathlib's coordinate equivalence preserves Lebesgue measure. -/
theorem realTiles_iff (F : Tile d) : RealTiles F ↔ AbsRealTiles F := by
  apply (coordinate_realTiles_iff F).trans
  unfold CoordinateRealTiles AbsRealTiles
  let e := (WithLp.equiv 2 (Fin d → ℝ)).symm
  apply e.setCongr.exists_congr
  intro T
  have pointwise (x : Fin d → ℝ) :
      (∃! t : Fin d → ℝ, t ∈ T ∧ x - t ∈ CoordinateSolid F) ↔
      ∃! t : (EPoint d), t ∈ e '' T ∧ e x - t ∈ AbsSolid F := by
    apply e.existsUnique_congr
    intro t
    simp [e, CoordinateSolid, AbsSolid]
  constructor
  · intro h
    have h' := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae h
    filter_upwards [h'] with x hx
    exact (pointwise x.ofLp).mp hx
  · intro h
    have h' := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae h
    filter_upwards [h'] with x hx
    exact (pointwise x).mpr hx

/-! ### Main statements -/

private theorem connected_complete_in_dimension (d : ℕ) (hd : 3 ≤ d) :
    LeanWang.CoREComplete (@ConnectedTiles d) := by
  refine ⟨connectedTiles_coRE d,?_⟩
  intro α _ P hP
  refine (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨fun T => (Compiler.connectedCompile T).map (pad hd),
      (padTile_computable hd).comp Compiler.connectedCompile_computable,?_⟩
  intro T
  constructor
  · intro ht
    exact ⟨Rotations.General.pad_connected hd _ (Compiler.connectedCompile_connected T),
      (tiles_pad_iff hd _).mpr ((Compiler.connectedCompile_correct T).mp ht)⟩
  · intro ht
    exact (Compiler.connectedCompile_correct T).mpr ((tiles_pad_iff hd _).mp ht.2)

theorem connected_coRE_complete (d : ℕ) (hd : 3 ≤ d) :
    LeanWang.CoREComplete fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsTiles P := by
  have : (fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsTiles P) = @ConnectedTiles d :=
    funext fun F => propext (and_congr (faceConnected_iff F).symm (tiles_iff F).symm)
  rw [this]
  exact connected_complete_in_dimension d hd

theorem connected_real_coRE_complete (d : ℕ) (hd : 3 ≤ d) :
    LeanWang.CoREComplete fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRealTiles P := by
  have : (fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRealTiles P) = @ConnectedTiles d :=
    funext fun F => propext (and_congr (faceConnected_iff F).symm
      ((realTiles_iff F).symm.trans (realTiles_iff_tiles F)))
  rw [this]
  exact connected_complete_in_dimension d hd

/-- Co-r.e.-completeness implies undecidability (Mathlib's halting problem). -/
theorem undecidable_of_coRE_complete {α : Type} [Primcodable α] {p : α → Prop}
    (h : LeanWang.CoREComplete p) : ¬ ComputablePred p := by
  intro hc
  have hre : LeanWang.CoREPred fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    (Partrec.dom_re (Nat.Partrec.Code.eval_part.comp Computable.id (Computable.const 0))).of_eq
      fun _ => by simp
  have hcomp := ComputablePred.computable_of_manyOneReducible (h.2 _ hre) hc
  exact ComputablePred.halting_problem 0 (by simpa using hcomp.not)

theorem connected_undecidable (d : ℕ) (hd : 3 ≤ d) : ¬ ComputablePred fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsTiles P :=
  undecidable_of_coRE_complete (connected_coRE_complete d hd)

private theorem simulation_bound_mono {n m : ℕ} (h : n ≤ m) :
    ((n : ℝ) + 4) ^ (10 ^ 61 * Real.logb 2 (Real.logb 2 ((n : ℝ) + 4))) ≤
      ((m : ℝ) + 4) ^ (10 ^ 61 * Real.logb 2 (Real.logb 2 ((m : ℝ) + 4))) := by
  have hbase : (n : ℝ) + 4 ≤ (m : ℝ) + 4 := by exact_mod_cast Nat.add_le_add_right h 4
  have hinner : 1 ≤ Real.logb 2 ((n : ℝ) + 4) := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 4) hbase
  have hloglog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by linarith : 0 < Real.logb 2 ((n : ℝ) + 4)) hlog
  have hnonneg := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hinner
  exact (Real.rpow_le_rpow (by positivity) hbase (mul_nonneg (by positivity) hnonneg)).trans
    (Real.rpow_le_rpow_of_exponent_le
      (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
      (mul_le_mul_of_nonneg_left hloglog (by positivity)))

/-- The optimized compiler is uniform, total, and satisfies the closed cube bound. -/
theorem tiling_reduction (d : ℕ) (hd : 3 ≤ d) : ∃ f : LeanWang.TileSet → List (Fin d → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := by
  refine ⟨fun T => (FiniteCompiler.Effective.optimizedCompile T).map (pad hd),
    (padTile_computable hd).comp FiniteCompiler.Effective.optimizedCompile_computable,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hb⟩ := FiniteCompiler.Effective.optimizedCompile_channel_bound T
  refine ⟨?_,(faceConnected_iff _).mp (Rotations.General.pad_connected hd _ hc),
    ht.trans ((tiles_pad_iff hd _).symm.trans (tiles_iff _)),?_⟩
  · intro hm
    exact hn (List.map_eq_nil_iff.mp hm)
  · rw [List.length_map]
    exact FiniteCompiler.Effective.optimizedCompile_real_bound T

/-- The same bounded computable compiler permits arbitrary real translations. -/
theorem real_tiling_reduction (d : ℕ) (hd : 3 ≤ d) : ∃ f : LeanWang.TileSet → List (Fin d → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsRealTiles (f T)) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := by
  obtain ⟨f,hf,hs⟩ := tiling_reduction d hd
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hb⟩ := hs T
  exact ⟨hn,hc,ht.trans ((tiles_iff _).symm.trans
    ((realTiles_iff_tiles _).symm.trans (realTiles_iff _))),hb⟩

theorem connected_real_undecidable (d : ℕ) (hd : 3 ≤ d) : ¬ ComputablePred fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRealTiles P :=
  undecidable_of_coRE_complete (connected_real_coRE_complete d hd)

/-! ### Arbitrary Euclidean motions -/

noncomputable section

private abbrev Motion (d : ℕ) := EPoint d ≃ᵃⁱ[ℝ] EPoint d

/-- The predicate of `Abstract.RigidTiles`, spelled out using Mathlib motions. -/
def AbsRigidTiles (P : List (Fin d → ℤ)) (allowReflections : Bool) : Prop :=
  ∃ T : Set (EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)),
    (∀ f ∈ T, allowReflections = true ∨ LinearMap.det f.linear.toLinearMap = 1) ∧
    ∀ᵐ x ∂MeasureTheory.volume, ∃! f, f ∈ T ∧ x ∈ f '' (AbsSolid P)

private def halfCube : (EPoint d) := WithLp.toLp 2 fun _ => (1 : ℝ) / 2

/-- Shift the lower-corner solid to the centered solid, inside each motion. -/
private def motionEquiv : Rotations.General.Real.RigidMotion d ≃ (Motion d) where
  toFun m := AffineIsometryEquiv.mk' (fun x => m.apply (x - halfCube)) m.rotation 0 (by
    intro x
    simp only [vsub_eq_sub, sub_zero, vadd_eq_add, Rotations.General.Real.RigidMotion.apply,
      map_sub, map_zero]
    abel)
  invFun f := ⟨f.linearIsometryEquiv, f halfCube⟩
  left_inv m := by
    cases m
    simp [Rotations.General.Real.RigidMotion.apply]
  right_inv f := by
    apply AffineIsometryEquiv.ext
    intro x
    change f halfCube + f.linearIsometryEquiv (x - halfCube) = f x
    have he := f.map_vadd halfCube (x - halfCube)
    simp only [vadd_eq_add, sub_add_cancel] at he
    simpa only [add_comm] using he.symm

private theorem promoted_solid (P : List (Fin d → ℤ)) :
    AbsSolid P =
      (fun x : (EPoint d) => x + halfCube) '' Rotations.General.Real.solid P.toFinset := by
  ext x
  constructor
  · rintro ⟨p,hp,hy⟩
    refine ⟨x - halfCube,⟨p,by simpa using hp,?_⟩,by simp⟩
    intro i
    change |x i - (1 : ℝ) / 2 - (p i : ℝ)| ≤ (1 : ℝ) / 2
    apply abs_le.mpr
    have hh := hy i
    constructor <;> linarith
  · rintro ⟨y,⟨p,hp,hy⟩,rfl⟩
    refine ⟨p,by simpa using hp,?_⟩
    intro i
    change (p i : ℝ) ≤ y i + (1 : ℝ) / 2 ∧ y i + (1 : ℝ) / 2 ≤ (p i : ℝ) + 1
    have hh := abs_le.mp (hy i)
    constructor <;> linarith

private theorem motion_image (P : List (Fin d → ℤ)) (m : Rotations.General.Real.RigidMotion d) :
    motionEquiv m '' (AbsSolid P) = Rotations.General.Real.Placed P.toFinset m := by
  rw [promoted_solid, Set.image_image]
  have he : (fun x : (EPoint d) => motionEquiv m (x + halfCube)) = m.apply := by
    funext x
    change m.apply (x + halfCube - halfCube) = m.apply x
    simp
  exact congrArg (fun f => f '' Rotations.General.Real.solid P.toFinset) he

private theorem motion_proper (m : Rotations.General.Real.RigidMotion d) :
    LinearMap.det (motionEquiv m).linear.toLinearMap = 1 ↔ Rotations.General.Real.Proper m.rotation := by
  simp only [AffineIsometryEquiv.linear_eq_linear_isometry, motionEquiv, Equiv.coe_fn_mk,
    AffineIsometryEquiv.linearIsometryEquiv_mk', Rotations.General.Real.Proper]

theorem rigidTiles_iff (P : List (Fin d → ℤ)) (allowReflections : Bool) :
    Rotations.General.Real.AllowedEuclideanTiles
      {r | allowReflections = true ∨ Rotations.General.Real.Proper r} P.toFinset ↔
      AbsRigidTiles P allowReflections := by
  unfold Rotations.General.Real.AllowedEuclideanTiles AbsRigidTiles
  apply motionEquiv.setCongr.exists_congr
  intro T
  apply and_congr
  · apply motionEquiv.forall_congr
    intro m
    simp only [Equiv.setCongr_apply, Set.mem_image_equiv, Equiv.symm_apply_apply,
      Set.mem_setOf_eq, motion_proper]
  · apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun x => by
      apply (existsUnique_subtype_iff T
        (fun m => x ∈ Rotations.General.Real.Placed P.toFinset m)).trans
      apply motionEquiv.existsUnique_congr
      intro m
      simp only [Equiv.setCongr_apply, Set.mem_image_equiv, Equiv.symm_apply_apply, motion_image]

private theorem rigid_predicate_eq (allowReflections : Bool) :
    (fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRigidTiles P allowReflections) =
      Rotations.General.Real.ProtectedEuclideanTileable
        {r | allowReflections = true ∨ Rotations.General.Real.Proper r} := by
  funext P
  exact propext (and_congr (faceConnected_iff P).symm (rigidTiles_iff P allowReflections).symm)

theorem connected_rigid_coRE_hard (d : ℕ) (hd : 3 ≤ d) (allowReflections : Bool) :
    LeanWang.CoREHard fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRigidTiles P allowReflections := by
  letI : NeZero d := ⟨by omega⟩
  rw [rigid_predicate_eq]
  intro α _ P hP
  exact Rotations.General.Real.rotation_coRE_hard hd
    {r | allowReflections=true ∨ Rotations.General.Real.Proper r}
    (Or.inr (Rotations.General.Real.proper_ident (d := d))) P hP

theorem connected_rigid_undecidable (d : ℕ) (hd : 3 ≤ d) (allowReflections : Bool) :
    ¬ ComputablePred fun P : List (Fin d → ℤ) => AbsConnected P ∧ AbsRigidTiles P allowReflections := by
  letI : NeZero d := ⟨by omega⟩
  rw [rigid_predicate_eq]
  exact Rotations.General.Real.rotation_undecidable hd
    {r | allowReflections=true ∨ Rotations.General.Real.Proper r}
    (Or.inr (Rotations.General.Real.proper_ident (d := d)))


/-- Restricting grid motions to the identity orientation is translation-only tiling. -/
private theorem grid_identity_iff (P : Tile d) :
    Rotations.General.AllowedGridTiles {Rotations.General.Orientation.ident} P.toFinset ↔ AbsTiles P := by
  let M (a : Lattice d) : (Rotations.General.Motion d) := ⟨Rotations.General.Orientation.ident,a⟩
  have placed (m : (Rotations.General.Motion d)) (hm : m.orientation = Rotations.General.Orientation.ident)
      (x : Lattice d) : x ∈ Rotations.General.Placed P.toFinset m ↔ x - m.offset ∈ P := by
    simp only [Rotations.General.Placed,Set.mem_image,Finset.mem_coe,List.mem_toFinset,
      Rotations.General.Motion.apply,hm,Rotations.General.Orientation.ident_apply]
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [add_sub_cancel_left] using hp
    · intro hx; exact ⟨x-m.offset,hx,by abel⟩
  constructor
  · rintro ⟨C,hC,hcover⟩
    have hor (m : C) : m.val.orientation = Rotations.General.Orientation.ident := hC m.val m.property
    refine ⟨Rotations.General.Motion.offset '' C,fun x => ?_⟩
    obtain ⟨m,hm,hu⟩ := hcover x
    refine ⟨m.val.offset,⟨⟨m.val,m.property,rfl⟩,(placed m.val (hor m) x).mp hm⟩,?_⟩
    rintro a ⟨⟨n,hn,rfl⟩,hxn⟩
    have he := hu ⟨n,hn⟩ ((placed n (hor ⟨n,hn⟩) x).mpr hxn)
    exact congrArg (fun k : C => k.val.offset) he
  · rintro ⟨A,hA⟩
    refine ⟨M '' A,?_,fun x => ?_⟩
    · rintro m ⟨a,ha,rfl⟩; exact rfl
    · obtain ⟨a,⟨ha,hxa⟩,hu⟩ := hA x
      refine ⟨⟨M a,a,ha,rfl⟩,(placed (M a) rfl x).mpr hxa,?_⟩
      intro n hxn
      obtain ⟨b,hb,he⟩ := n.property
      have hxb : x-b ∈ P := by
        simpa only [M] using (placed (M b) rfl x).mp (he.symm ▸ hxn)
      have hba : b = a := hu b ⟨hb,hxb⟩
      apply Subtype.ext
      exact he.symm.trans (congrArg M hba)


/-- One computable output has the same tilability in all motion models. -/
theorem rigid_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
    ∃ f : LeanWang.TileSet → List (Fin d → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (AbsTiles (f T) ↔ AbsRealTiles (f T)) ∧
      (∀ b : Bool, AbsRealTiles (f T) ↔ AbsRigidTiles (f T) b) ∧
      ((f T).length : ℝ) ≤ (2 : ℝ)^(10*(d+1)^2)*(((T.length : ℝ)+4)^
        (10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))) := by
  letI : NeZero d := ⟨by omega⟩
  let f := Rotations.General.Real.rotationCompile hd
  refine ⟨f,Rotations.General.Real.rotationCompile_computable hd,fun T => ?_⟩
  obtain ⟨hn,hc,ht,_⟩ := FiniteCompiler.Effective.optimizedCompile_channel_bound T
  let E := (FiniteCompiler.Effective.optimizedCompile T).map (pad hd)
  have hE : E ≠ [] := by intro he; exact hn (List.map_eq_nil_iff.mp he)
  have hW : LeanWang.TilesPlane T ↔ Tiles E := ht.trans (tiles_pad_iff hd _).symm
  have htile : LeanWang.TilesPlane T ↔ AbsTiles (f T) := hW.trans
    ((Rotations.General.protect_correct hd E hE {Rotations.General.Orientation.ident} rfl).trans
      (grid_identity_iff _))
  have hreal : AbsTiles (f T) ↔ AbsRealTiles (f T) :=
    (tiles_iff _).symm.trans ((realTiles_iff_tiles _).symm.trans (realTiles_iff _))
  refine ⟨Rotations.General.Real.rotationCompile_nonempty hd T,
    (faceConnected_iff _).mp (Rotations.General.Real.rotationCompile_connected hd T),
    htile,hreal,?_,Rotations.General.Real.rotationCompile_length_bound hd T⟩
  intro b
  have hr : LeanWang.TilesPlane T ↔ AbsRigidTiles (f T) b := hW.trans
    ((Rotations.General.Real.protect_correct hd E hE
      {r | b=true ∨ Rotations.General.Real.Proper r}
      (Or.inr (Rotations.General.Real.proper_ident (d := d)))).trans (rigidTiles_iff _ b))
  exact hreal.symm.trans (htile.symm.trans hr)

/-- The smaller three-dimensional construction uses the same solid and motion
conventions; only its internal motion record has a different type. -/
private def legacyMotionEquiv : Rotations.Euclidean.RigidMotion ≃ Rotations.General.Real.RigidMotion 3 where
  toFun m := ⟨m.rotation,m.offset⟩
  invFun m := ⟨m.rotation,m.offset⟩
  left_inv m := by cases m; rfl
  right_inv m := by cases m; rfl

private theorem legacy_allowed_iff (P : Tile 3) (allowed : Set Rotations.Euclidean.Rotation) :
    Rotations.Euclidean.AllowedEuclideanTiles allowed P.toFinset ↔
      Rotations.General.Real.AllowedEuclideanTiles allowed P.toFinset := by
  unfold Rotations.Euclidean.AllowedEuclideanTiles Rotations.General.Real.AllowedEuclideanTiles
  apply legacyMotionEquiv.setCongr.exists_congr
  intro T
  apply and_congr
  · apply legacyMotionEquiv.forall_congr
    intro m
    simp only [Equiv.setCongr_apply,Set.mem_image_equiv,Equiv.symm_apply_apply]
    rfl
  · unfold Rotations.Euclidean.AECover Rotations.General.Real.AECover
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun x => by
      apply (legacyMotionEquiv.image T).existsUnique_congr
      intro m
      rfl

private theorem legacy_rigidTiles_iff (P : Tile 3) (b : Bool) :
    Rotations.Euclidean.AllowedEuclideanTiles
      {r | b=true ∨ Rotations.Euclidean.Proper r} P.toFinset ↔ AbsRigidTiles P b :=
  (legacy_allowed_iff P _).trans (rigidTiles_iff P b)

/-- Restricting grid motions to the identity orientation is translation-only tiling. -/
private theorem grid_identity_iff_three (P : Tile 3) :
    Rotations.SixKeys.AllowedGridTiles {Rotations.Orientation.ident} P.toFinset ↔ AbsTiles P := by
  let M (a : Lattice 3) : Rotations.Motion := ⟨Rotations.Orientation.ident,a⟩
  have placed (m : Rotations.Motion) (hm : m.orientation = Rotations.Orientation.ident)
      (x : Lattice 3) : x ∈ Rotations.SixKeys.Placed P.toFinset m ↔ x - m.offset ∈ P := by
    simp only [Rotations.SixKeys.Placed,Set.mem_image,Finset.mem_coe,List.mem_toFinset,
      Rotations.Motion.apply,hm,Rotations.Orientation.ident_apply]
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [add_sub_cancel_left] using hp
    · intro hx; exact ⟨x-m.offset,hx,by abel⟩
  constructor
  · rintro ⟨C,hC,hcover⟩
    have hor (m : C) : m.val.orientation = Rotations.Orientation.ident := hC m.val m.property
    refine ⟨Rotations.Motion.offset '' C,fun x => ?_⟩
    obtain ⟨m,hm,hu⟩ := hcover x
    refine ⟨m.val.offset,⟨⟨m.val,m.property,rfl⟩,(placed m.val (hor m) x).mp hm⟩,?_⟩
    rintro a ⟨⟨n,hn,rfl⟩,hxn⟩
    have he := hu ⟨n,hn⟩ ((placed n (hor ⟨n,hn⟩) x).mpr hxn)
    exact congrArg (fun k : C => k.val.offset) he
  · rintro ⟨A,hA⟩
    refine ⟨M '' A,?_,fun x => ?_⟩
    · rintro m ⟨a,ha,rfl⟩; exact rfl
    · obtain ⟨a,⟨ha,hxa⟩,hu⟩ := hA x
      refine ⟨⟨M a,a,ha,rfl⟩,(placed (M a) rfl x).mpr hxa,?_⟩
      intro n hxn
      obtain ⟨b,hb,he⟩ := n.property
      have hxb : x-b ∈ P := by
        simpa only [M] using (placed (M b) rfl x).mp (he.symm ▸ hxn)
      have hba : b = a := hu b ⟨hb,hxb⟩
      apply Subtype.ext
      exact he.symm.trans (congrArg M hba)

/-- Protect the same optimized computable output against all Euclidean motions. -/
theorem rigid_tiling_reduction_three : ∃ f : LeanWang.TileSet → List (Fin 3 → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (AbsTiles (f T) ↔ AbsRealTiles (f T)) ∧
      (∀ allowReflections : Bool, AbsRealTiles (f T) ↔ AbsRigidTiles (f T) allowReflections) ∧
      ((f T).length : ℝ) ≤ 64000 * (((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)))) := by
  obtain ⟨f,hf,hs⟩ := tiling_reduction 3 (by decide)
  refine ⟨fun T => Rotations.SixKeys.protect (f T),
    Rotations.SixKeys.protect_primrec.to_comp.comp hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hb⟩ := hs T
  have hprot : AbsTiles (f T) ↔ AbsTiles (Rotations.SixKeys.protect (f T)) :=
    (tiles_iff _).symm.trans
      ((Rotations.SixKeys.protect_correct _ hn {Rotations.Orientation.ident} rfl).trans
        (grid_identity_iff_three _))
  have hreal : AbsTiles (Rotations.SixKeys.protect (f T)) ↔
      AbsRealTiles (Rotations.SixKeys.protect (f T)) :=
    (tiles_iff _).symm.trans ((realTiles_iff_tiles _).symm.trans (realTiles_iff _))
  refine ⟨Rotations.SixKeys.protect_nonempty _ hn,
    (faceConnected_iff _).mp
      (Rotations.SixKeys.protect_connected _ ((faceConnected_iff _).mpr hc)),
    ht.trans hprot,hreal,?_,?_⟩
  · intro allowReflections
    exact hreal.symm.trans (hprot.symm.trans ((tiles_iff _).symm.trans
      ((Rotations.Euclidean.protect_correct _ hn
        {r | allowReflections = true ∨ Rotations.Euclidean.Proper r}
        (Or.inr Rotations.Euclidean.proper_ident)).trans (legacy_rigidTiles_iff _ _))))
  · have hlen : (Rotations.SixKeys.protect (f T)).length = 64000 * (f T).length := by
      simp [Rotations.SixKeys.protect,List.length_flatMap,List.map_const',
        List.sum_replicate,Rotations.SixKeys.gadget_card,Nat.mul_comm]
    rw [hlen,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)


/-! ### Optional rotations and reflections -/

/-- The permitted linear parts, including arbitrary hyperplane reflections. -/
def AbsAllowedLinear (allowRotations allowReflections : Bool)
    (r : Rotations.General.Rotation d) : Prop :=
  if allowRotations then
    allowReflections = true ∨ LinearMap.det r.toLinearMap = 1
  else
    r = LinearIsometryEquiv.refl ℝ (EPoint d) ∨
      (allowReflections = true ∧ ∃ v : EPoint d, v ≠ 0 ∧
        r = (Submodule.span ℝ {v}).orthogonal.reflection)

/-- The public tiling predicate, parameterized by its permitted linear parts. -/
def AbsMotionTiles (P : List (Fin d → ℤ)) (allowed : Set (Rotations.General.Rotation d)) : Prop :=
  ∃ T : Set (Motion d), (∀ f ∈ T, f.linearIsometryEquiv ∈ allowed) ∧
    ∀ᵐ x ∂MeasureTheory.volume, ∃! f : Motion d, f ∈ T ∧ x ∈ f '' AbsSolid P

private theorem motion_linear (m : Rotations.General.Real.RigidMotion d) :
    (motionEquiv m).linearIsometryEquiv = m.rotation := by
  simp [motionEquiv]

theorem allowedMotionTiles_iff (P : List (Fin d → ℤ))
    (allowed : Set (Rotations.General.Rotation d)) :
    Rotations.General.Real.AllowedEuclideanTiles allowed P.toFinset ↔ AbsMotionTiles P allowed := by
  unfold Rotations.General.Real.AllowedEuclideanTiles AbsMotionTiles
  apply motionEquiv.setCongr.exists_congr
  intro T
  apply and_congr
  · apply motionEquiv.forall_congr
    intro m
    simp only [Equiv.setCongr_apply, Set.mem_image_equiv, Equiv.symm_apply_apply, motion_linear]
  · apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun x => by
      apply (existsUnique_subtype_iff T
        (fun m => x ∈ Rotations.General.Real.Placed P.toFinset m)).trans
      apply motionEquiv.existsUnique_congr
      intro m
      simp only [Equiv.setCongr_apply, Set.mem_image_equiv, Equiv.symm_apply_apply, motion_image]

private theorem allowed_ident (allowRotations allowReflections : Bool) :
    AbsAllowedLinear (d := d) allowRotations allowReflections
      (LinearIsometryEquiv.refl ℝ (EPoint d)) := by
  cases allowRotations <;> simp [AbsAllowedLinear]

private theorem translate_linear (a : EPoint d) :
    (AffineIsometryEquiv.constVAdd ℝ (EPoint d) a).linearIsometryEquiv =
      LinearIsometryEquiv.refl ℝ (EPoint d) := by
  ext x
  rfl

private theorem apply_of_linear_identity (f : Motion d)
    (hf : f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d)) (x : EPoint d) :
    f x = f 0 + x := by
  simpa [hf, add_comm] using f.map_vadd 0 x

private theorem image_of_linear_identity (f : Motion d)
    (hf : f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d))
    (P : List (Fin d → ℤ)) (x : EPoint d) :
    x ∈ f '' AbsSolid P ↔ x - f 0 ∈ AbsSolid P := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa [apply_of_linear_identity f hf y] using hy
  · intro hx
    exact ⟨x-f 0,hx,by rw [apply_of_linear_identity f hf]; abel⟩

theorem motionTiles_translation_iff (P : List (Fin d → ℤ)) :
    AbsMotionTiles P {r | AbsAllowedLinear false false r} ↔ AbsRealTiles P := by
  constructor
  · rintro ⟨T,hT,hcover⟩
    have hlin (f : Motion d) (hf : f ∈ T) :
        f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d) := by
      simpa [AbsAllowedLinear] using hT f hf
    refine ⟨(fun f : Motion d => f 0) '' T, ?_⟩
    filter_upwards [hcover] with x hx
    obtain ⟨f,⟨hf,hfx⟩,hu⟩ := hx
    refine ⟨f 0,⟨⟨f,hf,rfl⟩,(image_of_linear_identity f (hlin f hf) P x).mp hfx⟩,?_⟩
    rintro a ⟨⟨g,hg,rfl⟩,hga⟩
    exact congrArg (fun m : Motion d => m 0)
      (hu g ⟨hg,(image_of_linear_identity g (hlin g hg) P x).mpr hga⟩)
  · rintro ⟨A,hA⟩
    let M := AffineIsometryEquiv.constVAdd ℝ (EPoint d)
    refine ⟨M '' A,?_,?_⟩
    · rintro f ⟨a,ha,rfl⟩
      exact Or.inl (translate_linear a)
    · filter_upwards [hA] with x hx
      obtain ⟨a,⟨ha,hxa⟩,hu⟩ := hx
      have hzero (a : EPoint d) : M a 0 = a := by simp [M]
      refine ⟨M a,⟨⟨a,ha,rfl⟩,?_⟩,?_⟩
      · apply (image_of_linear_identity (M a) (translate_linear a) P x).mpr
        simpa only [hzero] using hxa
      · rintro g ⟨⟨b,hb,rfl⟩,hgb⟩
        have hxb := (image_of_linear_identity (M b) (translate_linear b) P x).mp hgb
        rw [hzero] at hxb
        exact congrArg M (hu b ⟨hb,hxb⟩)

private theorem motion_predicate_eq (allowRotations allowReflections : Bool) :
    (fun P : List (Fin d → ℤ) =>
      AbsConnected P ∧ AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r}) =
      Rotations.General.Real.ProtectedEuclideanTileable
        {r | AbsAllowedLinear allowRotations allowReflections r} := by
  funext P
  exact propext (and_congr (faceConnected_iff P).symm (allowedMotionTiles_iff P _).symm)

theorem connected_motion_coRE_hard (d : ℕ) (hd : 3 ≤ d)
    (allowRotations allowReflections : Bool) :
    LeanWang.CoREHard fun P : List (Fin d → ℤ) =>
      AbsConnected P ∧ AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r} := by
  letI : NeZero d := ⟨by omega⟩
  rw [motion_predicate_eq]
  intro α _ Q hQ
  exact Rotations.General.Real.rotation_coRE_hard hd _ (allowed_ident _ _) Q hQ

theorem connected_motion_undecidable (d : ℕ) (hd : 3 ≤ d)
    (allowRotations allowReflections : Bool) :
    ¬ ComputablePred fun P : List (Fin d → ℤ) =>
      AbsConnected P ∧ AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r} := by
  letI : NeZero d := ⟨by omega⟩
  rw [motion_predicate_eq]
  exact Rotations.General.Real.rotation_undecidable hd _ (allowed_ident _ _)

theorem connected_motion_coRE_complete (d : ℕ) (hd : 3 ≤ d)
    (allowRotations allowReflections : Bool) :
    LeanWang.CoREComplete fun P : List (Fin d → ℤ) =>
      AbsConnected P ∧ AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r} := by
  letI : NeZero d := ⟨by omega⟩
  refine ⟨?_,connected_motion_coRE_hard d hd allowRotations allowReflections⟩
  have h := EuclideanMembership.connectedMotionTiles_coRE (d := d) allowRotations allowReflections
  have he : (fun P : Tile d => FaceConnected P ∧
      EuclideanMembership.MotionTiles P allowRotations allowReflections) =
      (fun P : Tile d => AbsConnected P ∧
        AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r}) := by
    funext P
    apply propext
    apply and_congr (faceConnected_iff P)
    simpa only [EuclideanMembership.MotionTiles,EuclideanMembership.AllowedLinear,
      Rotations.General.Real.AllowedEuclideanTiles,AbsAllowedLinear,Set.mem_setOf_eq]
      using (allowedMotionTiles_iff P {r | AbsAllowedLinear allowRotations allowReflections r})
  rwa [he] at h


private theorem motion_models_iff (P : List (Fin d → ℤ))
    (hreal : AbsTiles P ↔ AbsRealTiles P)
    (hrigid : AbsRealTiles P ↔ AbsRigidTiles P true)
    (allowRotations allowReflections : Bool) :
    AbsTiles P ↔ AbsMotionTiles P {r | AbsAllowedLinear allowRotations allowReflections r} := by
  constructor
  · intro h
    obtain ⟨T,hT,hcover⟩ := (motionTiles_translation_iff P).mpr (hreal.mp h)
    refine ⟨T,?_,hcover⟩
    intro f hf
    have he : f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d) := by
      simpa [AbsAllowedLinear] using hT f hf
    rw [he]
    exact allowed_ident _ _
  · rintro ⟨T,hT,hcover⟩
    exact hreal.mpr (hrigid.mpr ⟨T,fun _ _ => Or.inl rfl,hcover⟩)

theorem motion_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
    ∃ f : LeanWang.TileSet → List (Fin d → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (∀ allowRotations allowReflections : Bool, AbsTiles (f T) ↔
        AbsMotionTiles (f T) {r | AbsAllowedLinear allowRotations allowReflections r}) ∧
      ((f T).length : ℝ) ≤ (2 : ℝ)^(10*(d+1)^2)*(((T.length : ℝ)+4)^
        (10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))) := by
  obtain ⟨f,hf,hs⟩ := rigid_tiling_reduction d hd
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hreal,hrigid,hb⟩ := hs T
  exact ⟨hn,hc,ht,motion_models_iff _ hreal (hrigid true),hb⟩

theorem motion_tiling_reduction_three :
    ∃ f : LeanWang.TileSet → List (Fin 3 → ℤ),
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (∀ allowRotations allowReflections : Bool, AbsTiles (f T) ↔
        AbsMotionTiles (f T) {r | AbsAllowedLinear allowRotations allowReflections r}) ∧
      ((f T).length : ℝ) ≤ 64000 * (((T.length : ℝ)+4)^
        (10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))) := by
  obtain ⟨f,hf,hs⟩ := rigid_tiling_reduction_three
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hreal,hrigid,hb⟩ := hs T
  exact ⟨hn,hc,ht,motion_models_iff _ hreal (hrigid true),hb⟩

/-! ### Explicit sets of Euclidean motions -/

def AbsTranslations : Set (Motion d) :=
  {f | f.linear = 1}

def AbsTranslationsAndRotations : Set (Motion d) :=
  {f | f.linear.det = 1}

def AbsTranslationsAndReflections : Set (Motion d) :=
  {f | ∃ t ∈ AbsTranslations, ∃ p q : EPoint d,
    f = t * EuclideanGeometry.reflection (AffineSubspace.perpBisector p q)}

def AbsAllMotions : Set (Motion d) := Set.univ

def AbsSetMotionTiles (P : Tile d) (motions : Set (Motion d)) : Prop :=
  ∃ T : Set (Motion d), T ⊆ motions ∧
    ∀ᵐ x ∂MeasureTheory.volume, ∃! f : Motion d, f ∈ T ∧ x ∈ f '' AbsSolid P

private theorem setMotionTiles_flags_iff (P : Tile d) (ar af : Bool) :
    AbsSetMotionTiles P {f | AbsAllowedLinear ar af f.linearIsometryEquiv} ↔
      AbsMotionTiles P {r | AbsAllowedLinear ar af r} := Iff.rfl

private theorem translations_flags :
    AbsTranslations (d := d) = {f | AbsAllowedLinear false false f.linearIsometryEquiv} := by
  ext f
  have h : (f.linear = 1) ↔
      f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d) := by
    rw [AffineIsometryEquiv.linear_eq_linear_isometry]
    exact LinearIsometryEquiv.toLinearEquiv_inj
      (f := f.linearIsometryEquiv) (g := LinearIsometryEquiv.refl ℝ (EPoint d))
  simpa [AbsTranslations,AbsAllowedLinear] using h

private theorem translationsAndRotations_flags :
    AbsTranslationsAndRotations (d := d) = {f | AbsAllowedLinear true false f.linearIsometryEquiv} := by
  ext f
  have h : (f.linear.det = 1) ↔ LinearMap.det f.linearIsometryEquiv.toLinearMap = 1 := by
    rw [← Units.val_inj,LinearEquiv.coe_det]
    rfl
  simpa [AbsTranslationsAndRotations,AbsAllowedLinear] using h

private theorem zero_normal_reflection :
    (Submodule.span ℝ {(0 : EPoint d)}).orthogonal.reflection =
      LinearIsometryEquiv.refl ℝ (EPoint d) := by
  ext x
  simp [Submodule.reflection_apply,Submodule.starProjection_top,two_smul]

-- Affine perpendicular-bisector reflections have the normal-vector linear part
-- used by the tiling proofs. Translating after them leaves that part unchanged.
private theorem bisector_linear (p q : EPoint d) :
    (EuclideanGeometry.reflection (AffineSubspace.perpBisector p q)).linearIsometryEquiv =
      (Submodule.span ℝ {q - p}).orthogonal.reflection := by
  change (AffineSubspace.perpBisector p q).direction.reflection = _
  simp only [AffineSubspace.direction_perpBisector, vsub_eq_sub]

private theorem translationsAndReflections_iff_normal (f : Motion d) :
    f ∈ AbsTranslationsAndReflections ↔ ∃ v : EPoint d,
      f.linearIsometryEquiv = (Submodule.span ℝ {v}).orthogonal.reflection := by
  constructor
  · rintro ⟨t,ht,p,q,rfl⟩
    refine ⟨q-p,?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    change t.linear ((EuclideanGeometry.reflection
      (AffineSubspace.perpBisector p q)).linearIsometryEquiv x) = _
    rw [show t.linear = 1 from ht, bisector_linear]
    rfl
  · rintro ⟨v,hv⟩
    let r := EuclideanGeometry.reflection (AffineSubspace.perpBisector (0 : EPoint d) v)
    let t := f * r⁻¹
    refine ⟨t,?_,0,v,?_⟩
    · change t.linear = 1
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext
      intro x
      change f.linearIsometryEquiv (r.symm.linearIsometryEquiv x) = x
      have hr : r.linearIsometryEquiv = (Submodule.span ℝ {v}).orthogonal.reflection := by
        simpa [r] using bisector_linear (0 : EPoint d) v
      rw [hv, ← hr]
      change r.linearIsometryEquiv (r.linearIsometryEquiv.symm x) = x
      exact r.linearIsometryEquiv.apply_symm_apply x
    · change f = (f * r⁻¹) * r
      simp

private theorem translationsAndReflections_flags :
    AbsTranslationsAndReflections (d := d) = {f | AbsAllowedLinear false true f.linearIsometryEquiv} := by
  ext f
  rw [translationsAndReflections_iff_normal]
  change (∃ v : EPoint d, f.linearIsometryEquiv =
    (Submodule.span ℝ {v}).orthogonal.reflection) ↔
      AbsAllowedLinear false true f.linearIsometryEquiv
  have hi : AbsAllowedLinear false true f.linearIsometryEquiv ↔
      f.linearIsometryEquiv = LinearIsometryEquiv.refl ℝ (EPoint d) ∨
      ∃ v : EPoint d, v ≠ 0 ∧ f.linearIsometryEquiv =
        (Submodule.span ℝ {v}).orthogonal.reflection := by simp [AbsAllowedLinear]
  rw [hi]
  constructor
  · rintro ⟨v,hv⟩
    by_cases hz : v = 0
    · exact Or.inl (by simpa only [hz,zero_normal_reflection] using hv)
    · exact Or.inr ⟨v,hz,hv⟩
  · rintro (hf | ⟨v,hv,hf⟩)
    · exact ⟨0,hf.trans zero_normal_reflection.symm⟩
    · exact ⟨v,hf⟩

private theorem allMotions_flags :
    AbsAllMotions (d := d) = {f | AbsAllowedLinear true true f.linearIsometryEquiv} := by
  ext f
  simp [AbsAllMotions,AbsAllowedLinear]

private theorem setMotionTiles_mono {P : Tile d} {S T : Set (Motion d)} (hst : S ⊆ T) :
    AbsSetMotionTiles P S → AbsSetMotionTiles P T := by
  rintro ⟨C,hC,hcover⟩
  exact ⟨C,hC.trans hst,hcover⟩

theorem setMotionTiles_translation_iff (P : Tile d) :
    AbsSetMotionTiles P AbsTranslations ↔ AbsRealTiles P := by
  rw [translations_flags,setMotionTiles_flags_iff,motionTiles_translation_iff]

theorem set_real_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
    ∃ f : LeanWang.TileSet → Tile d,
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (AbsTiles (f T) ↔ AbsSetMotionTiles (f T) AbsTranslations) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := by
  obtain ⟨f,hf,hs⟩ := tiling_reduction d hd
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hb⟩ := hs T
  exact ⟨hn,hc,ht,((tiles_iff _).symm.trans
    ((realTiles_iff_tiles _).symm.trans (realTiles_iff _))).trans
      (setMotionTiles_translation_iff _).symm,hb⟩

private theorem set_motion_models_iff (P : Tile d)
    (h : ∀ ar af : Bool, AbsTiles P ↔ AbsMotionTiles P {r | AbsAllowedLinear ar af r})
    (motions : Set (Motion d)) (hm : AbsTranslations ⊆ motions) :
    AbsTiles P ↔ AbsSetMotionTiles P motions := by
  constructor
  · intro ht
    apply setMotionTiles_mono hm
    rw [translations_flags,setMotionTiles_flags_iff]
    exact (h false false).mp ht
  · intro ht
    apply (h true true).mpr
    rw [← setMotionTiles_flags_iff,← allMotions_flags]
    exact setMotionTiles_mono (Set.subset_univ motions) ht

theorem set_motion_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
    ∃ f : LeanWang.TileSet → Tile d,
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (∀ motions : Set (Motion d), AbsTranslations ⊆ motions →
        (AbsTiles (f T) ↔ AbsSetMotionTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ (2 : ℝ)^(10*(d+1)^2)*(((T.length : ℝ)+4)^
        (10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))) := by
  obtain ⟨f,hf,hs⟩ := motion_tiling_reduction d hd
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hm,hb⟩ := hs T
  exact ⟨hn,hc,ht,set_motion_models_iff _ hm,hb⟩

theorem set_motion_tiling_reduction_three :
    ∃ f : LeanWang.TileSet → Tile 3,
    Computable f ∧ ∀ T, f T ≠ [] ∧ AbsConnected (f T) ∧
      (LeanWang.TilesPlane T ↔ AbsTiles (f T)) ∧
      (∀ motions : Set (Motion 3), AbsTranslations ⊆ motions →
        (AbsTiles (f T) ↔ AbsSetMotionTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ 64000 * (((T.length : ℝ)+4)^
        (10^61*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4)))) := by
  obtain ⟨f,hf,hs⟩ := motion_tiling_reduction_three
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hm,hb⟩ := hs T
  exact ⟨hn,hc,ht,set_motion_models_iff _ hm,hb⟩

private theorem set_motion_reduction (d : ℕ) (hd : 3 ≤ d)
    (motions : Set (Motion d)) (hm : AbsTranslations ⊆ motions) :
    LeanWang.TilesPlane ≤₀ (fun P : Tile d => AbsConnected P ∧ AbsSetMotionTiles P motions) := by
  obtain ⟨f,hf,hs⟩ := set_motion_tiling_reduction d hd
  refine ⟨f,hf,fun T => ?_⟩
  obtain ⟨hn,hc,ht,hM,hb⟩ := hs T
  exact ⟨fun h => ⟨hc,(hM motions hm).mp (ht.mp h)⟩,
    fun h => ht.mpr ((hM motions hm).mpr h.2)⟩

theorem connected_set_motion_coRE_hard (d : ℕ) (hd : 3 ≤ d)
    (motions : Set (Motion d)) (hm : AbsTranslations ⊆ motions) :
    LeanWang.CoREHard (fun P : Tile d => AbsConnected P ∧ AbsSetMotionTiles P motions) := by
  intro α _ Q hQ
  exact (LeanWang.Kari.domino_problem_coRE_hard Q hQ).trans (set_motion_reduction d hd motions hm)

theorem connected_set_motion_undecidable (d : ℕ) (hd : 3 ≤ d)
    (motions : Set (Motion d)) (hm : AbsTranslations ⊆ motions) :
    ¬ ComputablePred (fun P : Tile d => AbsConnected P ∧ AbsSetMotionTiles P motions) := by
  intro h
  exact LeanWang.Kari.domino_problem_undecidable
    (ComputablePred.computable_of_manyOneReducible (set_motion_reduction d hd motions hm) h)

theorem connected_set_motion_coRE_complete (d : ℕ) (hd : 3 ≤ d)
    (motions : Set (Motion d))
    (hm : motions ∈ ({AbsAllMotions,AbsTranslations,AbsTranslationsAndRotations,
      AbsTranslationsAndReflections} : Set (Set (Motion d)))) :
    LeanWang.CoREComplete (fun P : Tile d => AbsConnected P ∧ AbsSetMotionTiles P motions) := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    first
    | simp_rw [translations_flags,setMotionTiles_flags_iff]
      exact connected_motion_coRE_complete d hd false false
    | simp_rw [translationsAndRotations_flags,setMotionTiles_flags_iff]
      exact connected_motion_coRE_complete d hd true false
    | simp_rw [translationsAndReflections_flags,setMotionTiles_flags_iff]
      exact connected_motion_coRE_complete d hd false true
    | simp_rw [allMotions_flags,setMotionTiles_flags_iff]
      exact connected_motion_coRE_complete d hd true true

end

end TranslationTiling.AbstractBridge
