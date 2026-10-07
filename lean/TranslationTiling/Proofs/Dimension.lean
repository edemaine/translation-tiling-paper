import TranslationTiling.Proofs.Basic

namespace TranslationTiling

/-- Embed a tile into a higher dimension by appending zero coordinates. -/
def pad {d e : ℕ} (_h : d ≤ e) : Lattice d →+ Lattice e where
  toFun x i := if hi : i.val < d then x ⟨i.val, hi⟩ else 0
  map_zero' := by ext i; dsimp; split <;> rfl
  map_add' x y := by ext i; dsimp; split <;> simp

def project {d e : ℕ} (h : d ≤ e) : Lattice e →+ Lattice d where
  toFun x i := x (Fin.castLE h i)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem project_pad {d e : ℕ} (h : d ≤ e) (x : Lattice d) :
    project h (pad h x) = x := by
  funext i
  simp [project, pad, i.isLt]

theorem pad_injective {d e : ℕ} (h : d ≤ e) : Function.Injective (pad h) :=
  Function.LeftInverse.injective (project_pad h)

/-- Higher-dimensional tilings can be sliced; lower-dimensional tilings extend independently. -/
theorem tiles_pad_iff {d e : ℕ} (h : d ≤ e) (F : Tile d) :
    Tiles (F.map (pad h)) ↔ Tiles F := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨{a | pad h a ∈ A}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    obtain ⟨f', hf', hu⟩ := (exactTiling_iff A _).mp hA (pad h x)
    obtain ⟨f, hf, he⟩ := List.mem_map.mp f'.property
    refine ⟨⟨f, hf⟩, ?_, ?_⟩
    · change pad h (x - f) ∈ A
      simpa only [map_sub, he] using hf'
    · intro g hg
      have hg' : pad h x - pad h g.val ∈ A := by
        change pad h (x - g.val) ∈ A at hg
        simpa only [map_sub] using hg
      have hgf := hu ⟨pad h g.val, List.mem_map.mpr ⟨g.val, g.property, rfl⟩⟩ hg'
      apply Subtype.ext
      apply pad_injective h
      exact (congrArg Subtype.val hgf).trans he.symm
  · rintro ⟨A, hA⟩
    refine ⟨{a | project h a ∈ A}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    obtain ⟨f, hf, hu⟩ := (exactTiling_iff A _).mp hA (project h x)
    refine ⟨⟨pad h f.val, List.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩, ?_, ?_⟩
    · change project h (x - pad h f.val) ∈ A
      simpa only [map_sub, project_pad] using hf
    · intro g hg
      obtain ⟨g', hg', he⟩ := List.mem_map.mp g.property
      have ha : project h x - g' ∈ A := by
        change project h (x - g.val) ∈ A at hg
        simpa only [← he, map_sub, project_pad] using hg
      have hgf := hu ⟨g', hg'⟩ ha
      apply Subtype.ext
      rw [← he]
      exact congrArg (pad h) (congrArg Subtype.val hgf)

theorem pad_primrec {d e : ℕ} (h : d ≤ e) : Primrec (pad h) := by
  have hc : ∀ i : Fin e, Primrec (fun x : Lattice d => pad h x i) := by
    intro i
    by_cases hi : i.val < d
    · exact (Primrec.fin_app.comp (Primrec.id : Primrec (fun x : Lattice d => x))
        (Primrec.const (⟨i.val, hi⟩ : Fin d))).of_eq (by intro x; simp [pad, hi])
    · exact (Primrec.const (0 : ℤ) : Primrec (fun _ : Lattice d => (0 : ℤ))).of_eq
        (g := fun x : Lattice d => pad h x i) (by intro x; simp [pad, hi])
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr hc).swap

/-- The dimensional embedding is itself computable under the finite-tile encoding. -/
theorem padTile_computable {d e : ℕ} (h : d ≤ e) :
    Computable (fun F : Tile d => F.map (pad h)) :=
  (Primrec.list_map Primrec.id ((pad_primrec h).comp₂ Primrec₂.right)).to_comp

end TranslationTiling
