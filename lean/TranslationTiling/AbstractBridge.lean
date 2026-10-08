import TranslationTiling.Statements

/-!
# Bridge to `Abstract.lean`

`Abstract.lean` states the 3D tiling problem with points of `ℤ × ℤ × ℤ`. The rest
of the development works with `Tile 3 = List (Fin 3 → ℤ)`. This file transports
tilings and co-r.e.-completeness along the computable identification of the two
encodings. Its statements spell out the predicate of `Abstract.Tiles` explicitly,
so that `Abstract.lean` can cite them by definitional unfolding.

The mathematical inputs are explicit, as in `Statements.lean`.
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
def equiv : Lattice 3 ≃ ℤ × ℤ × ℤ where
  toFun := toPoint
  invFun := ofPoint
  left_inv := ofPoint_toPoint
  right_inv := toPoint_ofPoint

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

theorem tiles_iff (F : Tile 3) : Tiles F ↔ AbsTiles (toProto F) := by
  unfold Tiles AbsTiles
  simp only [exactTiling_iff]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨equiv.symm ⁻¹' A, fun y => ?_⟩
    obtain ⟨t, ht, hu⟩ := hA (equiv.symm y)
    refine ⟨(toPoint t.1, toPoint t.2), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [equiv, ofPoint_toPoint] using ht.1
      · exact List.mem_map.mpr ⟨t.2, ht.2.1, rfl⟩
      · show toPoint (t.1 + t.2) = y
        rw [show t.1 + t.2 = equiv.symm y from ht.2.2]; exact toPoint_ofPoint y
    · rintro ⟨u, v⟩ ⟨h1, h2, h3⟩
      obtain ⟨v', hv', rfl⟩ := List.mem_map.mp h2
      have := hu (ofPoint u, v') ⟨h1, hv', ?_⟩
      · rw [← this]; simp [toPoint_ofPoint]
      · apply equiv.injective
        show toPoint (ofPoint u + v') = toPoint (equiv.symm y)
        rw [toPoint_add, toPoint_ofPoint]; exact h3.trans (toPoint_ofPoint y).symm
  · rintro ⟨A, hA⟩
    refine ⟨equiv ⁻¹' A, fun x => ?_⟩
    obtain ⟨t, ht, hu⟩ := hA (equiv x)
    obtain ⟨v', hv', hv⟩ := List.mem_map.mp ht.2.1
    refine ⟨(ofPoint t.1, v'), ⟨?_, hv', ?_⟩, ?_⟩
    · simpa [equiv, toPoint_ofPoint] using ht.1
    · apply equiv.injective
      show toPoint (ofPoint t.1 + v') = toPoint x
      rw [toPoint_add, toPoint_ofPoint, hv]; exact ht.2.2
    · rintro ⟨u, v⟩ ⟨h1, h2, h3⟩
      have := hu (toPoint u, toPoint v) ⟨h1, List.mem_map.mpr ⟨v, h2, rfl⟩, ?_⟩
      · have h1' : toPoint u = t.1 := congrArg Prod.fst this
        have h2' : toPoint v = t.2 := congrArg Prod.snd this
        refine Prod.ext ?_ (toPoint_injective (h2'.trans hv.symm))
        show u = ofPoint t.1
        rw [← h1', ofPoint_toPoint]
      · show toPoint u + toPoint v = equiv x
        rw [← toPoint_add]; exact congrArg toPoint h3

theorem coREComplete_transfer (h : LeanWang.CoREComplete (@Tiles 3)) :
    LeanWang.CoREComplete AbsTiles := by
  refine ⟨?_, ?_⟩
  · refine (h.1.comp ofProto_computable).of_eq fun P => ?_
    have hP : toProto (ofProto P) = P := by
      simp [toProto, ofProto, List.map_map, Function.comp_def, toPoint_ofPoint]
    have e : Tiles (ofProto P) ↔ AbsTiles P := by
      rw [tiles_iff, hP]
    exact Part.ext'
      ⟨fun ⟨h, _⟩ => ⟨(not_congr e).1 h, trivial⟩, fun ⟨h, _⟩ => ⟨(not_congr e).2 h, trivial⟩⟩
      (fun _ _ => rfl)
  · intro α _ p hp
    exact (h.2 p hp).trans ⟨toProto, toProto_computable, tiles_iff⟩

/-- Main theorem in the form used by `Abstract.lean`. -/
theorem coRE_complete : LeanWang.CoREComplete AbsTiles :=
  coREComplete_transfer TranslationTiling.completeness

/-- Co-r.e.-completeness implies undecidability (Mathlib's halting problem). -/
theorem undecidable_of_coRE_complete (h : LeanWang.CoREComplete AbsTiles) :
    ¬ ComputablePred AbsTiles := by
  intro hc
  have hre : LeanWang.CoREPred fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    (Partrec.dom_re (Nat.Partrec.Code.eval_part.comp Computable.id (Computable.const 0))).of_eq
      fun _ => by simp
  have hcomp := ComputablePred.computable_of_manyOneReducible (h.2 _ hre) hc
  exact ComputablePred.halting_problem 0 (by simpa using hcomp.not)

theorem undecidable (h : ReductionInputs) : ¬ ComputablePred AbsTiles :=
  undecidable_of_coRE_complete (coRE_complete h)

end TranslationTiling.AbstractBridge
