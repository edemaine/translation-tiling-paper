import TranslationTiling.Statements

/-!
# Bridge to `Abstract.lean`

`Abstract.lean` states the 3D tiling problem with points of `ℤ × ℤ × ℤ`. The rest
of the development works with `Tile 3 = List (Fin 3 → ℤ)`. This file transports
tilings and co-r.e.-completeness along the computable identification of the two
encodings. Its statements spell out the predicate of `Abstract.Tiles` explicitly,
so that `Abstract.lean` can cite them by definitional unfolding.

All mathematical inputs are proved, as in `Statements.lean`.
-/

namespace TranslationTiling.AbstractBridge

open TranslationTiling

/-- The predicate of `Abstract.Tiles`, spelled out. -/
def AbsTiles (P : List (ℤ × ℤ × ℤ)) : Prop :=
  ∃ A : Set (ℤ × ℤ × ℤ), ∀ x : ℤ × ℤ × ℤ,
    ∃! t : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ), t.1 ∈ A ∧ t.2 ∈ P ∧ t.1 + t.2 = x

def toPoint (f : Lattice 3) : ℤ × ℤ × ℤ := (f 0, f 1, f 2)

def ofPoint (p : ℤ × ℤ × ℤ) : Lattice 3 := ![p.1, p.2.1, p.2.2]

theorem ofPoint_toPoint (f : Lattice 3) : ofPoint (toPoint f) = f := by
  ext i; fin_cases i <;> rfl

theorem toPoint_ofPoint (p : ℤ × ℤ × ℤ) : toPoint (ofPoint p) = p := rfl

theorem toPoint_injective : Function.Injective toPoint :=
  Function.LeftInverse.injective ofPoint_toPoint

theorem toPoint_add (f g : Lattice 3) : toPoint (f + g) = toPoint f + toPoint g := rfl

/-- The identification of the two models of `ℤ³`. -/
def equiv : Lattice 3 ≃+ ℤ × ℤ × ℤ where
  toFun := toPoint
  invFun := ofPoint
  left_inv := ofPoint_toPoint
  right_inv := toPoint_ofPoint
  map_add' := toPoint_add

theorem toPoint_primrec : Primrec toPoint := by
  unfold toPoint
  have h : ∀ i : Fin 3, Primrec (fun f : Lattice 3 => f i) := fun i =>
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  exact (h 0).pair ((h 1).pair (h 2))

theorem ofPoint_primrec : Primrec ofPoint := by
  have h : ∀ i : Fin 3, Primrec (fun p : ℤ × ℤ × ℤ => ofPoint p i) := by
    intro i
    fin_cases i
    · exact Primrec.fst
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap

def toProto (F : Tile 3) : List (ℤ × ℤ × ℤ) := F.map toPoint

def ofProto (P : List (ℤ × ℤ × ℤ)) : Tile 3 := P.map ofPoint

theorem toProto_computable : Computable toProto :=
  (Primrec.list_map Primrec.id (toPoint_primrec.comp₂ Primrec₂.right)).to_comp

theorem ofProto_computable : Computable ofProto :=
  (Primrec.list_map Primrec.id (ofPoint_primrec.comp₂ Primrec₂.right)).to_comp

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

/-- The elementary predicate agrees with exact coverage by subtype pairs. -/
theorem absTiles_iff_exactTiling (P : List (ℤ × ℤ × ℤ)) :
    AbsTiles P ↔ ∃ A, ExactTiling A {p | p ∈ P} := by
  simp only [AbsTiles, exactTiling_iff, Set.mem_setOf_eq]

theorem tiles_iff (F : Tile 3) : Tiles F ↔ AbsTiles (toProto F) := by
  have hmap : equiv '' {f | f ∈ F} = {p | p ∈ toProto F} := by
    ext p
    exact List.mem_map.symm
  have hback : equiv.symm '' {p | p ∈ toProto F} = {f | f ∈ F} := by
    rw [← hmap, Set.image_image]
    simp
  rw [absTiles_iff_exactTiling]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨equiv '' A, by simpa only [hmap] using exactTiling_transport equiv hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨equiv.symm '' A, by simpa only [hback] using exactTiling_transport equiv.symm hA⟩

@[simp] theorem toProto_ofProto (P : List (ℤ × ℤ × ℤ)) : toProto (ofProto P) = P := by
  simp [toProto, ofProto, List.map_map, Function.comp_def, toPoint_ofPoint]

@[simp] theorem ofProto_toProto (F : Tile 3) : ofProto (toProto F) = F := by
  simp [toProto, ofProto, List.map_map, Function.comp_def, ofPoint_toPoint]

/-! ### Connected prototiles -/

/-- Face adjacency: the points are at `ℓ¹` distance one. -/
def AbsAdjacent (a b : ℤ × ℤ × ℤ) : Prop :=
  |a.1 - b.1| + |a.2.1 - b.2.1| + |a.2.2 - b.2.2| = 1

/-- The predicate of `Abstract.Connected`, spelled out. -/
def AbsConnected (P : List (ℤ × ℤ × ℤ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ AbsAdjacent a b) p q

theorem faceAdjacent_iff (a b : Lattice 3) :
    FaceAdjacent a b ↔ AbsAdjacent (toPoint a) (toPoint b) := by
  constructor
  · rintro ⟨i, h | h⟩ <;> subst h <;> fin_cases i <;> simp [AbsAdjacent, toPoint]
  · intro h
    simp only [AbsAdjacent, toPoint, abs_eq_max_neg] at h
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

theorem faceConnected_iff (F : Tile 3) : FaceConnected F ↔ AbsConnected (toProto F) := by
  constructor
  · intro h p hp q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    refine Relation.ReflTransGen.lift toPoint ?_ (h x hx y hy)
    rintro a b ⟨ha, hb, hab⟩
    exact ⟨List.mem_map_of_mem ha, List.mem_map_of_mem hb, (faceAdjacent_iff a b).mp hab⟩
  · intro h x hx y hy
    have := h _ (List.mem_map_of_mem (f := toPoint) hx) _ (List.mem_map_of_mem (f := toPoint) hy)
    have key : ∀ a b : ℤ × ℤ × ℤ, (a ∈ toProto F ∧ b ∈ toProto F ∧ AbsAdjacent a b) →
        (ofPoint a ∈ F ∧ ofPoint b ∈ F ∧ FaceAdjacent (ofPoint a) (ofPoint b)) := by
      rintro a b ⟨ha, hb, hab⟩
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      simp only [ofPoint_toPoint]
      exact ⟨ha', hb', (faceAdjacent_iff a' b').mpr hab⟩
    simpa [ofPoint_toPoint] using Relation.ReflTransGen.lift ofPoint key this

/-! ### Real translations -/

/-- The solid body of a prototile: the union of its unit cubes. -/
def AbsSolid (P : List (ℤ × ℤ × ℤ)) : Set (Fin 3 → ℝ) :=
  {x | ∃ p ∈ P, x - ![(p.1 : ℝ), p.2.1, p.2.2] ∈ Set.Icc 0 1}

/-- The predicate of `Abstract.RealTiles`, spelled out. -/
def AbsRealTiles (P : List (ℤ × ℤ × ℤ)) : Prop :=
  ∃ A : Set (Fin 3 → ℝ), ∀ᵐ x ∂MeasureTheory.volume, ∃! a : A, x - a.val ∈ AbsSolid P

theorem realTiles_iff (F : Tile 3) : RealTiles F ↔ AbsRealTiles (toProto F) := by
  have hc : ∀ y : Fin 3 → ℝ, y ∈ CubeUnion F ↔ y ∈ AbsSolid (toProto F) := by
    intro y
    simp only [CubeUnion, AbsSolid, toProto, List.mem_map, Set.mem_setOf_eq,
      exists_exists_and_eq_and]
    refine exists_congr fun f => and_congr_right fun _ => ?_
    simp only [toPoint, Set.mem_Icc, Pi.le_def]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp [(h _).1, (h _).2] <;> linarith [(h 0).1, (h 0).2, (h 1).1, (h 1).2, (h 2).1, (h 2).2]
    · rintro ⟨h0, h1⟩ i
      have a := h0 i
      have b := h1 i
      fin_cases i <;> simp at a b ⊢ <;> constructor <;> linarith
  unfold RealTiles AbsRealTiles
  simp only [hc]

/-! ### Transfer -/

theorem transfer {q : Tile 3 → Prop} {q' : List (ℤ × ℤ × ℤ) → Prop}
    (h : LeanWang.CoREComplete q) (hiff : ∀ F, q F ↔ q' (toProto F)) :
    LeanWang.CoREComplete q' := by
  refine ⟨?_, ?_⟩
  · refine _root_.REPred.of_eq (LeanWang.REPred.comp h.1 ofProto_computable) fun P => ?_
    exact not_congr (by simpa only [toProto_ofProto] using hiff (ofProto P))
  · intro α _ p hp
    exact (h.2 p hp).trans ⟨toProto, toProto_computable, hiff⟩

theorem connected_coRE_complete :
    LeanWang.CoREComplete fun P => AbsConnected P ∧ AbsTiles P :=
  transfer TranslationTiling.connected_completeness fun F => by
    rw [← faceConnected_iff, ← tiles_iff]; rfl

theorem connected_real_coRE_complete :
    LeanWang.CoREComplete fun P => AbsConnected P ∧ AbsRealTiles P :=
  transfer TranslationTiling.connected_completeness fun F => by
    rw [← faceConnected_iff, ← realTiles_iff, realTiles_iff_tiles]; rfl

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

theorem connected_real_undecidable : ¬ ComputablePred fun P => AbsConnected P ∧ AbsRealTiles P :=
  undecidable_of_coRE_complete connected_real_coRE_complete

end TranslationTiling.AbstractBridge
