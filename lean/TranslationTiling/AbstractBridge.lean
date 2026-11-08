import TranslationTiling.Statements
import TranslationTiling.Compiler.CleanQuasipolynomialBound

/-!
# Bridge to `Abstract.lean`

`Abstract.lean` states the 3D tiling problem with points of `Fin 3 → ℤ`, the same
model of `ℤ³` as the rest of the development (`Tile 3 = List (Lattice 3)`). This
file shows that the predicates written there agree with the ones proved about in the
project. Its statements spell out the predicates of `Abstract.lean` explicitly,
so that `Abstract.lean` can cite them by definitional unfolding.

All mathematical inputs are proved, as in `Statements.lean`.
-/

namespace TranslationTiling.AbstractBridge

open TranslationTiling

/-- The predicate of `Abstract.Tiles`, spelled out. -/
def AbsTiles (P : List (Fin 3 → ℤ)) : Prop :=
  ∃ T : Set (Fin 3 → ℤ), ∀ x : Fin 3 → ℤ, ∃! t : Fin 3 → ℤ, t ∈ T ∧ x - t ∈ P

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

theorem tiles_iff (F : Tile 3) : Tiles F ↔ AbsTiles F := by
  simp only [Tiles, AbsTiles, exactTiling_iff', Set.mem_setOf_eq]

/-! ### Connected prototiles -/

/-- Face adjacency: the points are at `ℓ¹` distance one. -/
def AbsAdjacent (a b : Fin 3 → ℤ) : Prop :=
  ∑ i, |a i - b i| = 1

/-- The predicate of `Abstract.Connected`, spelled out. -/
def AbsConnected (P : List (Fin 3 → ℤ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ AbsAdjacent a b) p q

theorem faceAdjacent_iff (a b : Lattice 3) : FaceAdjacent a b ↔ AbsAdjacent a b := by
  constructor
  · rintro ⟨i, h | h⟩ <;> subst h <;> fin_cases i <;>
      simp [AbsAdjacent, Fin.sum_univ_three]
  · intro h
    simp only [AbsAdjacent, Fin.sum_univ_three, abs_eq_max_neg] at h
    have h' : (b 0 = a 0 + 1 ∧ b 1 = a 1 ∧ b 2 = a 2) ∨ (b 0 = a 0 ∧ b 1 = a 1 + 1 ∧ b 2 = a 2) ∨
        (b 0 = a 0 ∧ b 1 = a 1 ∧ b 2 = a 2 + 1) ∨ (a 0 = b 0 + 1 ∧ a 1 = b 1 ∧ a 2 = b 2) ∨
        (a 0 = b 0 ∧ a 1 = b 1 + 1 ∧ a 2 = b 2) ∨ (a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 + 1) := by
      omega
    rcases h' with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩
    · exact ⟨0, Or.inl (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩
    · exact ⟨1, Or.inl (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩
    · exact ⟨2, Or.inl (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩
    · exact ⟨0, Or.inr (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩
    · exact ⟨1, Or.inr (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩
    · exact ⟨2, Or.inr (by ext j; fin_cases j <;> simp [h0, h1, h2, add_comm])⟩

theorem faceConnected_iff (F : Tile 3) : FaceConnected F ↔ AbsConnected F := by
  simp only [FaceConnected, AbsConnected, faceAdjacent_iff]

/-! ### Real translations -/

/-- The solid body of a prototile: the union of its unit cubes. -/
def AbsSolid (P : List (Fin 3 → ℤ)) : Set (Fin 3 → ℝ) :=
  {x | ∃ p ∈ P, ∀ i, (p i : ℝ) ≤ x i ∧ x i ≤ p i + 1}

/-- The predicate of `Abstract.RealTiles`, spelled out. -/
def AbsRealTiles (P : List (Fin 3 → ℤ)) : Prop :=
  ∃ T : Set (Fin 3 → ℝ), ∀ᵐ x ∂MeasureTheory.volume,
    ∃! t : Fin 3 → ℝ, t ∈ T ∧ x - t ∈ AbsSolid P

theorem existsUnique_subtype_iff {α : Type*} (T : Set α) (p : α → Prop) :
    (∃! t : T, p t.val) ↔ ∃! t : α, t ∈ T ∧ p t := by
  constructor
  · rintro ⟨⟨t, ht⟩, hp, hu⟩
    exact ⟨t, ⟨ht, hp⟩, fun s ⟨hs, hps⟩ => congrArg Subtype.val (hu ⟨s, hs⟩ hps)⟩
  · rintro ⟨t, ⟨ht, hp⟩, hu⟩
    exact ⟨⟨t, ht⟩, hp, fun s hps => Subtype.ext (hu s.val ⟨s.property, hps⟩)⟩

theorem realTiles_iff (F : Tile 3) : RealTiles F ↔ AbsRealTiles F := by
  exact exists_congr fun T => Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    existsUnique_subtype_iff T (fun t => x - t ∈ CubeUnion F))

/-! ### Main statements -/

theorem connected_coRE_complete :
    LeanWang.CoREComplete fun P => AbsConnected P ∧ AbsTiles P := by
  have : (fun P : List (Fin 3 → ℤ) => AbsConnected P ∧ AbsTiles P) = @ConnectedTiles 3 :=
    funext fun F => propext (and_congr (faceConnected_iff F).symm (tiles_iff F).symm)
  rw [this]
  exact TranslationTiling.connected_completeness

theorem connected_real_coRE_complete :
    LeanWang.CoREComplete fun P => AbsConnected P ∧ AbsRealTiles P := by
  have : (fun P : List (Fin 3 → ℤ) => AbsConnected P ∧ AbsRealTiles P) = @ConnectedTiles 3 :=
    funext fun F => propext (and_congr (faceConnected_iff F).symm
      ((realTiles_iff F).symm.trans (realTiles_iff_tiles F)))
  rw [this]
  exact TranslationTiling.connected_completeness

/-- Co-r.e.-completeness implies undecidability (Mathlib's halting problem). -/
theorem undecidable_of_coRE_complete {α : Type} [Primcodable α] {p : α → Prop}
    (h : LeanWang.CoREComplete p) : ¬ ComputablePred p := by
  intro hc
  have hre : LeanWang.CoREPred fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    (Partrec.dom_re (Nat.Partrec.Code.eval_part.comp Computable.id (Computable.const 0))).of_eq
      fun _ => by simp
  have hcomp := ComputablePred.computable_of_manyOneReducible (h.2 _ hre) hc
  exact ComputablePred.halting_problem 0 (by simpa using hcomp.not)

theorem connected_undecidable : ¬ ComputablePred fun P => AbsConnected P ∧ AbsTiles P :=
  undecidable_of_coRE_complete connected_coRE_complete

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

/-- Remove duplicate cubes and bound the simulation by the input list length. -/
theorem tiling_simulates_wang (T : LeanWang.TileSet) :
    ∃ P : List (Fin 3 → ℤ), P ≠ [] ∧ AbsConnected P ∧
      (LeanWang.TilesPlane T ↔ AbsTiles P) ∧
      (P.length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := by
  obtain ⟨P, hP, hconn, hiff, hbound⟩ :=
    Compiler.Size.exists_connected_tile_clean_quasipolynomial_bound T
  refine ⟨P.dedup, (List.dedup_eq_nil P).not.mpr hP, ?_, ?_, ?_⟩
  · simpa only [AbsConnected, List.mem_dedup] using (faceConnected_iff P).mp hconn
  · simpa only [AbsTiles, List.mem_dedup] using hiff.trans (tiles_iff P)
  · simpa only [Compiler.Size.cubeCount, List.card_toFinset] using
      hbound.trans (simulation_bound_mono T.toFinset_card_le)

/-- The discrete witness also works for arbitrary real translations. -/
theorem real_tiling_simulates_wang (T : LeanWang.TileSet) :
    ∃ P : List (Fin 3 → ℤ), P ≠ [] ∧ AbsConnected P ∧
      (LeanWang.TilesPlane T ↔ AbsRealTiles P) ∧
      (P.length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := by
  obtain ⟨P, hP, hconn, hiff, hbound⟩ := tiling_simulates_wang T
  exact ⟨P, hP, hconn,
    hiff.trans ((tiles_iff P).symm.trans
      ((realTiles_iff_tiles P).symm.trans (realTiles_iff P))), hbound⟩

theorem connected_real_undecidable : ¬ ComputablePred fun P => AbsConnected P ∧ AbsRealTiles P :=
  undecidable_of_coRE_complete connected_real_coRE_complete

end TranslationTiling.AbstractBridge
