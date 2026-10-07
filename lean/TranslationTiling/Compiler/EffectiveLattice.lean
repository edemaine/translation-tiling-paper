import TranslationTiling.Compiler.EffectiveConnected

namespace TranslationTiling.Compiler

open Effective
open scoped Classical
noncomputable section

/-- Coordinates in a finite cyclic factor are stored as natural numbers. -/
abbrev CyclicPoint := Plane × ℕ
abbrev CyclicTile := List CyclicPoint
abbrev CyclicTileData := ℕ × CyclicTile

def cyclicPoint (Q : ℕ) (f : CyclicPoint) : Plane × ZMod Q := (f.1, (f.2 : ZMod Q))

def cyclicTileSet (Q : ℕ) (F : CyclicTile) : Finset (Plane × ZMod Q) :=
  F.toFinset.image (cyclicPoint Q)

/-- Normalize at the first tile point and choose the canonical quotient representatives. -/
def latticeRepresentatives (Q : ℕ) (F : CyclicTile) : Tile 3 :=
  let f₀ := F.headD ((0, 0), 0)
  F.map fun f => ![f.1.1 - f₀.1.1, f.1.2 - f₀.1.2,
    ((f.2 : ℤ) - (f₀.2 : ℤ)) % (Q : ℤ)]

def componentList (Q j : ℕ) : Tile 3 :=
  (MSS.baseShape \ (MSS.frame j).image (MSS.marker j + ·)).toList ++
    (MSS.frame j).toList.map fun v => MSS.scale • MSS.kernelStep Q + MSS.marker j + v

theorem mem_componentList (Q j : ℕ) (x : Lattice 3) :
    x ∈ componentList Q j ↔ x ∈ MSS.component Q j := by
  simp only [componentList, MSS.component, List.mem_append, Finset.mem_toList,
    List.mem_map, Finset.mem_union, Finset.mem_image]

/-- Numerical MSS assembly, with component five marking the normalized origin. -/
def integerTile (d : CyclicTileData) : Tile 3 :=
  (latticeRepresentatives d.1 d.2).flatMap fun u =>
    (componentList d.1 (if u = 0 then 5 else 4)).map fun v => MSS.scale • u + v

@[fun_prop] theorem latticeRepresentatives_primrec :
    Primrec (fun d : CyclicTileData => latticeRepresentatives d.1 d.2) := by
  have hh : Primrec (fun d : CyclicTileData => d.2.headD ((0, 0), 0)) :=
    by simpa only [List.headD_eq_head?_getD] using
      (Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.snd)
        (Primrec.const ((0, 0), 0)))
  unfold latticeRepresentatives
  apply mapList Primrec.snd
  have hh' : Primrec (fun z : CyclicTileData × CyclicPoint =>
      z.1.2.headD ((0, 0), 0)) := hh.comp Primrec.fst
  fun_prop

@[fun_prop] theorem kernelStep_primrec : Primrec MSS.kernelStep := by
  apply piValue
  intro i
  fin_cases i <;> simp only [MSS.kernelStep] <;> fun_prop

theorem componentList_primrec (j : ℕ) : Primrec (fun Q => componentList Q j) := by
  unfold componentList
  fun_prop

theorem integerTile_primrec : Primrec integerTile := by
  unfold integerTile
  apply flatMapList latticeRepresentatives_primrec
  apply mapList
  · have h5 : Primrec (fun z : CyclicTileData × Lattice 3 => componentList z.1.1 5) :=
      (componentList_primrec 5).comp (Primrec.fst.comp Primrec.fst)
    have h4 : Primrec (fun z : CyclicTileData × Lattice 3 => componentList z.1.1 4) :=
      (componentList_primrec 4).comp (Primrec.fst.comp Primrec.fst)
    apply (iteValue (p := fun z : CyclicTileData × Lattice 3 => z.2 = 0)
      (by fun_prop) h5 h4).of_eq
    intro z
    by_cases h : z.2 = 0
    · simp only [if_pos h]
    · simp only [if_neg h]
  · fun_prop

/-- The normalized origin contributes a nonempty marked component. -/
theorem integerTile_nonempty (d : CyclicTileData) (hF : d.2 ≠ []) : integerTile d ≠ [] := by
  obtain ⟨Q, F⟩ := d
  cases F with
  | nil => exact False.elim (hF rfl)
  | cons f fs =>
    have hrep : (0 : Lattice 3) ∈ latticeRepresentatives Q (f :: fs) := by
      apply List.mem_map.mpr
      refine ⟨f, List.mem_cons_self, ?_⟩
      funext i
      fin_cases i <;> simp [latticeRepresentatives, List.headD]
    have hc : (0 : Lattice 3) ∈ componentList Q 5 :=
      (mem_componentList Q 5 0).mpr (LatticeGeometry.zero_mem_component Q 5 (by decide))
    have hz : (0 : Lattice 3) ∈ integerTile (Q, f :: fs) := by
      apply List.mem_flatMap.mpr
      refine ⟨0, hrep, ?_⟩
      simp only [ite_true]
      exact List.mem_map.mpr ⟨0, hc, by simp⟩
    intro he
    simp only [he, List.not_mem_nil] at hz

theorem integerTile_computable : Computable integerTile := integerTile_primrec.to_comp

theorem latticeRepresentatives_toFinset (Q : ℕ) (hQ : 0 < Q) (F : CyclicTile) :
    (latticeRepresentatives Q F).toFinset = CyclicQuotient.representatives Q
      ((cyclicTileSet Q F).image (fun f => f - cyclicPoint Q (F.headD ((0, 0), 0)))) := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hpoint (f : CyclicPoint) :
      ![f.1.1 - (F.headD ((0, 0), 0)).1.1, f.1.2 - (F.headD ((0, 0), 0)).1.2,
        ((f.2 : ℤ) - ((F.headD ((0, 0), 0)).2 : ℤ)) % (Q : ℤ)] =
      CyclicQuotient.lift Q (cyclicPoint Q f - cyclicPoint Q (F.headD ((0, 0), 0))) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · simp only [CyclicQuotient.lift, cyclicPoint, Prod.fst_sub, Prod.snd_sub, Matrix.cons_val]
      rw [← ZMod.val_intCast, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  ext x
  simp only [List.mem_toFinset, latticeRepresentatives, List.mem_map,
    CyclicQuotient.representatives, Finset.mem_image, cyclicTileSet]
  constructor
  · rintro ⟨f, hf, he⟩
    exact ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, (hpoint f).symm.trans he⟩
  · rintro ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, he⟩
    exact ⟨f, hf, (hpoint f).trans he⟩

theorem integerTile_toFinset (d : CyclicTileData) :
    (integerTile d).toFinset =
      LatticeGeometry.assembled d.1 (latticeRepresentatives d.1 d.2).toFinset := by
  ext x
  simp only [integerTile, List.mem_toFinset, List.mem_flatMap, List.mem_map,
    LatticeGeometry.assembled, Finset.mem_biUnion, Finset.mem_image,
    LatticeGeometry.part, LatticeGeometry.scaleHom]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨u, hu, v, ?_, he⟩
    by_cases h : u = 0
    · simpa only [if_pos h, mem_componentList] using hv
    · simpa only [if_neg h, mem_componentList] using hv
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨u, hu, v, ?_, he⟩
    by_cases h : u = 0
    · simpa only [if_pos h, mem_componentList] using hv
    · simpa only [if_neg h, mem_componentList] using hv

/-- The primitive-recursive lattice assembly realizes arbitrary cyclic input tiles. -/
theorem integerTile_correct (rigid : MSS.Rigidity) (d : CyclicTileData)
    (hQ : 0 < d.1) (hF : d.2 ≠ []) :
    (∃ A : Set (Plane × ZMod d.1), Tiles (cyclicTileSet d.1 d.2) A) ↔
      TranslationTiling.Tiles (integerTile d) := by
  have hhead : d.2.headD ((0, 0), 0) ∈ d.2 := by
    cases he : d.2 with
    | nil => exact False.elim (hF he)
    | cons f fs => simp
  let F := cyclicTileSet d.1 d.2
  let f₀ := cyclicPoint d.1 (d.2.headD ((0, 0), 0))
  let F₀ := F.image (fun f => f - f₀)
  have h0 : 0 ∈ F₀ := Finset.mem_image.mpr
    ⟨f₀, Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr hhead, rfl⟩, sub_self _⟩
  have hshift : (∃ A, Tiles F A) ↔ ∃ A, Tiles F₀ A := by
    simpa only [F₀, sub_eq_add_neg] using exists_covers_shift_iff F (-f₀)
  have he := integerTile_toFinset d
  rw [latticeRepresentatives_toFinset d.1 hQ d.2] at he
  have ht : (∃ B : Set (Lattice 3), Tiles (integerTile d).toFinset B) ↔
      TranslationTiling.Tiles (integerTile d) := by
    simp only [Tiles, Stacking.covers_iff_exactTiling, TranslationTiling.Tiles]
    have hs : ((integerTile d).toFinset : Set (Lattice 3)) =
        {f | f ∈ integerTile d} := by ext f; exact List.mem_toFinset
    rw [hs]
  exact (hshift.trans (LatticeGeometry.assembled_iff_quotient rigid d.1 hQ F₀ h0)).trans
    (he ▸ ht)

end
end TranslationTiling.Compiler
