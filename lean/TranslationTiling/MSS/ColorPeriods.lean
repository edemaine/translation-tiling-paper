import TranslationTiling.MSS.GridCenters
import TranslationTiling.MSS.Cells

/-! The two special frames force the periods of the individual tile types. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem placement_radius_ge {Q C₁ C₂} (a : Placement Q C₁ C₂) : 4 ≤ a.radius := by
  cases a <;> simp only [Placement.radius] <;> omega

theorem grid_add_step {c : Lattice 3}
    (hc : c ∈ Set.range (fun x : Lattice 3 => scale • x)) (v : Lattice 3) :
    c + scale • v ∈ Set.range (fun x : Lattice 3 => scale • x) := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨w + v, smul_add _ _ _⟩

theorem grid_sub_step {c : Lattice 3}
    (hc : c ∈ Set.range (fun x : Lattice 3 => scale • x)) (v : Lattice 3) :
    c - scale • v ∈ Set.range (fun x : Lattice 3 => scale • x) := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨w - v, smul_sub _ _ _⟩

theorem mixed_special_same_radius {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    (hQ : 0 < Q) (h0 : 0 ∈ C₁ ∪ C₂) (a : Placement Q C₁ C₂) :
    ∃ b : Placement Q C₁ C₂,
      b.center = a.center + scale • kernelStep Q ∧ b.radius = a.radius := by
  have hgrid := mixed_grid_centers h h0
  have ha : a.center ∈ Set.range (fun x : Lattice 3 => scale • x) := hgrid ▸ a.center_mem
  have hc : a.center + scale • kernelStep Q ∈ C₁ ∪ C₂ :=
    hgrid ▸ grid_add_step ha (kernelStep Q)
  obtain ⟨b, hb⟩ := placement_at_center (Q := Q) hc
  refine ⟨b, hb, ?_⟩
  by_contra hne
  let r : Lattice 3 := marker a.radius + Pi.single 0 (a.radius : ℤ)
  have hr : r ∈ cell a.radius :=
    Finset.mem_image.mpr ⟨_, axis_frame_vertex a.radius a.radius_pos, rfl⟩
  have hbody := other_special_cell_in_body a.radius b.radius (placement_radius_ge a)
    a.radius_le (placement_radius_ge b) b.radius_le (Ne.symm hne) hr
  have hneq : a.center ≠ b.center := by
    intro he
    have hh := congrFun (he.trans hb) 2
    change a.center 2 = a.center 2 + 201 * (Q : ℤ) at hh
    omega
  apply mixed_copies_no_overlap h a b hneq (special_cell_mem_component Q a.radius hr)
    (body_subset_component Q b.radius hbody)
  rw [hb]
  abel

theorem mixed_color_periods {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    (hQ : 0 < Q) (h0 : 0 ∈ C₁ ∪ C₂) :
    Period C₁ (scale • kernelStep Q) ∧ Period C₂ (scale • kernelStep Q) := by
  have forward₁ {c : Lattice 3} (hc : c ∈ C₁) : c + scale • kernelStep Q ∈ C₁ := by
    let a : Placement Q C₁ C₂ := .inl (⟨c, hc⟩, ⟨0, zero_mem_component Q 4 (by omega)⟩)
    obtain ⟨b, hb, hr⟩ := mixed_special_same_radius h hQ h0 a
    cases b with
    | inl z => exact hb ▸ z.1.property
    | inr z => change 5 = 4 at hr; omega
  have forward₂ {c : Lattice 3} (hc : c ∈ C₂) : c + scale • kernelStep Q ∈ C₂ := by
    let a : Placement Q C₁ C₂ := .inr (⟨c, hc⟩, ⟨0, zero_mem_component Q 5 (by omega)⟩)
    obtain ⟨b, hb, hr⟩ := mixed_special_same_radius h hQ h0 a
    cases b with
    | inl z => change 4 = 5 at hr; omega
    | inr z => exact hb ▸ z.1.property
  have hd := Set.disjoint_left.mp (mixed_centers_disjoint h)
  have grid := mixed_grid_centers h h0
  have backward {c : Lattice 3} (hc : c + scale • kernelStep Q ∈ C₁ ∪ C₂) : c ∈ C₁ ∪ C₂ := by
    have hh := grid_sub_step (grid ▸ hc) (kernelStep Q)
    simpa only [add_sub_cancel_right, ← grid] using hh
  constructor
  · intro c
    constructor
    · intro hc
      rcases backward (Or.inl hc) with hc' | hc'
      · exact hc'
      · exact (hd hc (forward₂ hc')).elim
    · exact forward₁
  · intro c
    constructor
    · intro hc
      rcases backward (Or.inr hc) with hc' | hc'
      · exact (hd (forward₁ hc') hc).elim
      · exact hc'
    · exact forward₂

theorem mixed_rigidity_necessary {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    (hQ : 0 < Q) (h0 : 0 ∈ C₁ ∪ C₂) :
    Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x) ∧
      Period C₁ (scale • kernelStep Q) ∧ Period C₂ (scale • kernelStep Q) :=
  ⟨mixed_centers_disjoint h, mixed_grid_centers h h0, mixed_color_periods h hQ h0⟩

end
end TranslationTiling.MSS
