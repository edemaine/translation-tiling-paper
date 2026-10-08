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

theorem coREComplete_transfer (h : LeanWang.CoREComplete (@Tiles 3)) :
    LeanWang.CoREComplete AbsTiles := by
  refine ⟨?_, ?_⟩
  · refine _root_.REPred.of_eq (LeanWang.REPred.comp h.1 ofProto_computable) fun P => ?_
    exact not_congr (by simpa only [toProto_ofProto] using tiles_iff (ofProto P))
  · intro α _ p hp
    exact (h.2 p hp).trans ⟨toProto, toProto_computable, tiles_iff⟩

/-- Main theorem in the form used by `Abstract.lean`. -/
theorem coRE_complete : LeanWang.CoREComplete AbsTiles :=
  coREComplete_transfer TranslationTiling.completeness

/-- Transfer undecidability from the lattice model using co-r.e.-hardness. -/
theorem undecidable_of_coRE_complete (h : LeanWang.CoREComplete AbsTiles) :
    ¬ ComputablePred AbsTiles := by
  intro hc
  exact TranslationTiling.undecidability
    (ComputablePred.computable_of_manyOneReducible (h.2 _ (membership 3)) hc)

theorem undecidable : ¬ ComputablePred AbsTiles :=
  undecidable_of_coRE_complete coRE_complete

end TranslationTiling.AbstractBridge
