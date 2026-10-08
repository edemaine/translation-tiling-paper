import TranslationTiling.MSS.ColorPeriods

/-! Reassembling moved cells gives a mixed tiling of the entire lattice. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

def colorSet (C₁ C₂ : Set (Lattice 3)) (j : ℕ) : Set (Lattice 3) :=
  if j = 4 then C₁ else C₂

namespace Placement

theorem color_mem {Q C₁ C₂} (a : Placement Q C₁ C₂) :
    a.center ∈ colorSet C₁ C₂ a.radius := by
  cases a with
  | inl z => exact z.1.property
  | inr z => exact z.1.property

def withCenter {Q C₁ C₂} (a : Placement Q C₁ C₂) (c : Lattice 3)
    (hc : c ∈ colorSet C₁ C₂ a.radius) : Placement Q C₁ C₂ := match a with
  | .inl z => .inl (⟨c, hc⟩, z.2)
  | .inr z => .inr (⟨c, hc⟩, z.2)

@[simp] theorem center_withCenter {Q C₁ C₂} (a : Placement Q C₁ C₂) (c) (hc) :
    (a.withCenter c hc).center = c := by cases a <;> rfl

@[simp] theorem radius_withCenter {Q C₁ C₂} (a : Placement Q C₁ C₂) (c) (hc) :
    (a.withCenter c hc).radius = a.radius := by cases a <;> rfl

theorem color_period {Q C₁ C₂} (a : Placement Q C₁ C₂)
    (hp₁ : Period C₁ (scale • kernelStep Q)) (hp₂ : Period C₂ (scale • kernelStep Q)) :
    Period (colorSet C₁ C₂ a.radius) (scale • kernelStep Q) := by
  cases a
  · exact hp₁
  · exact hp₂

end Placement

theorem same_radius_of_color {Q C₁ C₂} (hd : Disjoint C₁ C₂)
    (a b : Placement Q C₁ C₂) {c : Lattice 3}
    (ha : c ∈ colorSet C₁ C₂ a.radius) (hb : c ∈ colorSet C₁ C₂ b.radius) :
    a.radius = b.radius := by
  cases a <;> cases b
  · rfl
  · exact (Set.disjoint_left.mp hd ha hb).elim
  · exact (Set.disjoint_left.mp hd hb ha).elim
  · rfl

theorem placement_eq_of_center_vertex {Q C₁ C₂} (hd : Disjoint C₁ C₂)
    (a b : Placement Q C₁ C₂) (hc : a.center = b.center) (hv : a.vertex = b.vertex) :
    a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      exact Prod.ext (Subtype.ext hc) (Subtype.ext hv)
    | inr b =>
      change a.1.val = b.1.val at hc
      have hb' : a.1.val ∈ C₂ := by rw [hc]; exact b.1.property
      exact (Set.disjoint_left.mp hd a.1.property hb').elim
  | inr a =>
    cases b with
    | inl b =>
      change a.1.val = b.1.val at hc
      have hb' : a.1.val ∈ C₁ := by rw [hc]; exact b.1.property
      exact (Set.disjoint_left.mp hd hb' a.1.property).elim
    | inr b =>
      apply congrArg Sum.inr
      exact Prod.ext (Subtype.ext hc) (Subtype.ext hv)

theorem box_grid_unique {c d r s : Lattice 3}
    (hc : c ∈ Set.range (fun x : Lattice 3 => scale • x))
    (hd : d ∈ Set.range (fun x : Lattice 3 => scale • x))
    (hr : r ∈ box 100) (hs : s ∈ box 100) (he : c + r = d + s) : c = d ∧ r = s := by
  obtain ⟨z, rfl⟩ := hc
  obtain ⟨w, rfl⟩ := hd
  have hrb := (mem_box_iff 100 _).mp hr
  have hsb := (mem_box_iff 100 _).mp hs
  have hz : z = w := by
    ext i
    have hh := congrFun he i
    change 201 * z i + r i = 201 * w i + s i at hh
    have hri := hrb i
    have hsi := hsb i
    omega
  subst w
  exact ⟨rfl, add_left_cancel he⟩

theorem exists_box_grid (x : Lattice 3) :
    ∃ c r : Lattice 3, c ∈ Set.range (fun x : Lattice 3 => scale • x) ∧
      r ∈ box 100 ∧ c + r = x := by
  let c : Lattice 3 := fun i => 201 * ((x i + 100) / 201)
  let r : Lattice 3 := fun i => (x i + 100) % 201 - 100
  refine ⟨c, r, ⟨(fun i => (x i + 100) / 201), rfl⟩, ?_, ?_⟩
  · apply (mem_box_iff 100 _).mpr
    intro i
    have hl := Int.emod_nonneg (x i + 100) (by omega : (201 : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (x i + 100) (by omega : (0 : ℤ) < 201)
    dsimp [r]; omega
  · ext i
    have hh := Int.emod_add_mul_ediv (x i + 100) 201
    change 201 * ((x i + 100) / 201) + ((x i + 100) % 201 - 100) = x i
    omega

structure Home {Q C₁ C₂} (a : Placement Q C₁ C₂) where
  residue : Lattice 3
  residue_mem : residue ∈ box 100
  jump : Lattice 3
  vertex_eq : a.vertex = scale • jump + residue
  piece :
    (jump = 0 ∧ residue ∈ body a.radius) ∨
    (∃ i : Fin 3, jump = Pi.single i 1 ∧ residue ∈ cell (i.val + 1)) ∨
    (jump = kernelStep Q ∧ residue ∈ cell a.radius)

theorem exists_home {Q C₁ C₂} (a : Placement Q C₁ C₂) : Nonempty (Home a) := by
  rcases component_mem_pieces Q a.radius a.radius_pos a.radius_le a.vertex_mem with
    hv | hv | hv
  · exact ⟨⟨a.vertex, (Finset.mem_sdiff.mp hv).1, 0, by simp, Or.inl ⟨rfl, hv⟩⟩⟩
  · obtain ⟨i, u, hu, he⟩ := hv
    exact ⟨⟨u, cell_subset_box _ (by omega) (by have := i.isLt; omega) hu,
      Pi.single i 1, he, Or.inr (Or.inl ⟨i, rfl, hu⟩)⟩⟩
  · obtain ⟨u, hu, he⟩ := hv
    exact ⟨⟨u, cell_subset_box _ a.radius_pos a.radius_le hu, kernelStep Q, he,
      Or.inr (Or.inr ⟨rfl, hu⟩)⟩⟩

theorem home_common_of_removed {Q C₁ C₂} (a : Placement Q C₁ C₂) (f : Home a)
    (hr : f.residue ∈ removed) :
    ∃ i : Fin 3, f.jump = Pi.single i 1 ∧ f.residue ∈ cell (i.val + 1) := by
  rcases f.piece with hp | hp | hp
  · have hn := (Finset.mem_sdiff.mp hp.2).2
    exact (hn (Finset.mem_union_left _ hr)).elim
  · exact hp
  · obtain ⟨i, hi⟩ := (mem_removed_iff _).mp hr
    have he := cells_same_radius a.radius (i.val + 1) a.radius_pos (by omega) a.radius_le
      (by have := i.isLt; omega) hp.2 hi
    have ha := placement_radius_ge a
    have hi3 := i.isLt
    omega

theorem home_noncommon {Q C₁ C₂} (a : Placement Q C₁ C₂) (f : Home a)
    (hr : f.residue ∉ removed) :
    (f.jump = 0 ∧ f.residue ∈ body a.radius) ∨
      (f.jump = kernelStep Q ∧ f.residue ∈ cell a.radius) := by
  rcases f.piece with hp | hp | hp
  · exact Or.inl hp
  · obtain ⟨i, _, hi⟩ := hp
    exact (hr ((mem_removed_iff _).mpr ⟨i, hi⟩)).elim
  · exact Or.inr hp

theorem home_noncommon_color {Q C₁ C₂} (a : Placement Q C₁ C₂) (f : Home a)
    (hr : f.residue ∉ removed)
    (hp₁ : Period C₁ (scale • kernelStep Q)) (hp₂ : Period C₂ (scale • kernelStep Q)) :
    a.center + scale • f.jump ∈ colorSet C₁ C₂ a.radius := by
  rcases home_noncommon a f hr with hp | hp
  · simpa only [hp.1, smul_zero, add_zero] using a.color_mem
  · rw [hp.1]
    exact (a.color_period hp₁ hp₂ a.center).mpr a.color_mem

theorem mixed_grid_injective {Q C₁ C₂} (hd : Disjoint C₁ C₂)
    (hg : C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x))
    (hp₁ : Period C₁ (scale • kernelStep Q)) (hp₂ : Period C₂ (scale • kernelStep Q)) :
    Function.Injective (Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂)) := by
  intro a b hab
  obtain ⟨f⟩ := exists_home a
  obtain ⟨g⟩ := exists_home b
  have ha : a.center ∈ Set.range (fun x : Lattice 3 => scale • x) := hg ▸ a.center_mem
  have hb : b.center ∈ Set.range (fun x : Lattice 3 => scale • x) := hg ▸ b.center_mem
  have he : (a.center + scale • f.jump) + f.residue =
      (b.center + scale • g.jump) + g.residue := by
    rw [Placement.position, Placement.position, f.vertex_eq, g.vertex_eq] at hab
    simpa only [add_assoc] using hab
  obtain ⟨hc, hr⟩ := box_grid_unique (grid_add_step ha f.jump) (grid_add_step hb g.jump)
    f.residue_mem g.residue_mem he
  have hjump : f.jump = g.jump := by
    by_cases hrem : f.residue ∈ removed
    · obtain ⟨i, hfi, hfr⟩ := home_common_of_removed a f hrem
      obtain ⟨j, hgj, hgr⟩ := home_common_of_removed b g (hr ▸ hrem)
      rw [← hr] at hgr
      have hij := cells_same_radius (i.val + 1) (j.val + 1) (by omega) (by omega)
        (by have := i.isLt; omega) (by have := j.isLt; omega) hfr hgr
      have hij' : i = j := Fin.ext (by omega)
      rw [hfi, hgj, hij']
    · have hgrem : g.residue ∉ removed := by rwa [← hr]
      have hfcolor := home_noncommon_color a f hrem hp₁ hp₂
      have hgcolor := home_noncommon_color b g hgrem hp₁ hp₂
      rw [← hc] at hgcolor
      have hrad := same_radius_of_color hd a b hfcolor hgcolor
      rcases home_noncommon a f hrem with hf | hf <;>
        rcases home_noncommon b g hgrem with hg' | hg'
      · exact hf.1.trans hg'.1.symm
      · have hn := (Finset.mem_sdiff.mp hf.2).2
        have hh : f.residue ∈ cell a.radius := by simpa only [← hr, ← hrad] using hg'.2
        exact (hn (Finset.mem_union_right _ hh)).elim
      · have hn := (Finset.mem_sdiff.mp hg'.2).2
        have hh : g.residue ∈ cell b.radius := by simpa only [hr, hrad] using hf.2
        exact (hn (Finset.mem_union_right _ hh)).elim
      · exact hf.1.trans hg'.1.symm
  have hcenters : a.center = b.center := by
    rw [hjump] at hc
    exact add_right_cancel hc
  have hvertices : a.vertex = b.vertex := by
    rw [f.vertex_eq, g.vertex_eq, hjump, hr]
  exact placement_eq_of_center_vertex hd a b hcenters hvertices

theorem mixed_grid_surjective {Q C₁ C₂}
    (hg : C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x))
    (hp₁ : Period C₁ (scale • kernelStep Q)) (hp₂ : Period C₂ (scale • kernelStep Q)) :
    Function.Surjective (Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂)) := by
  intro x
  obtain ⟨c, r, hc, hr, hx⟩ := exists_box_grid x
  obtain ⟨a, ha⟩ := placement_at_center (Q := Q) (hg ▸ hc)
  by_cases hrem : r ∈ removed
  · obtain ⟨i, hi⟩ := (mem_removed_iff r).mp hrem
    obtain ⟨b, hb⟩ := placement_at_center (Q := Q)
      (hg ▸ grid_sub_step hc (Pi.single i 1))
    let v := scale • Pi.single i 1 + r
    have hv := common_cell_mem_component Q b.radius b.radius_pos b.radius_le i hi
    refine ⟨b.withVertex v hv, ?_⟩
    simp only [Placement.position, Placement.center_withVertex, Placement.vertex_withVertex, hb]
    dsimp [v]
    calc
      _ = c + r := by abel
      _ = x := hx
  · by_cases hs : r ∈ cell a.radius
    · have hcolor : c - scale • kernelStep Q ∈ colorSet C₁ C₂ a.radius := by
        have hh := a.color_period hp₁ hp₂ (c - scale • kernelStep Q)
        have hc' : c ∈ colorSet C₁ C₂ a.radius := ha ▸ a.color_mem
        exact hh.mp (by simpa only [sub_add_cancel] using hc')
      let b := a.withCenter (c - scale • kernelStep Q) hcolor
      let v := scale • kernelStep Q + r
      have hv : v ∈ component Q b.radius := by
        simp only [b, Placement.radius_withCenter]
        exact special_cell_mem_component Q a.radius hs
      refine ⟨b.withVertex v hv, ?_⟩
      simp only [Placement.position, Placement.center_withVertex, Placement.vertex_withVertex,
        b, Placement.center_withCenter]
      dsimp [v]
      calc
        _ = c + r := by abel
        _ = x := hx
    · have hv : r ∈ body a.radius := Finset.mem_sdiff.mpr ⟨hr, by
        simpa only [holes, Finset.mem_union, not_or] using ⟨hrem, hs⟩⟩
      refine ⟨a.withVertex r (body_subset_component Q a.radius hv), ?_⟩
      simpa only [Placement.position, Placement.center_withVertex, Placement.vertex_withVertex, ha]
        using hx

theorem mixed_rigidity_sufficient {Q C₁ C₂} (hd : Disjoint C₁ C₂)
    (hg : C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x))
    (hp₁ : Period C₁ (scale • kernelStep Q)) (hp₂ : Period C₂ (scale • kernelStep Q)) :
    MixedTiling Q C₁ C₂ := by
  have hb : Function.Bijective (Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂)) :=
    ⟨mixed_grid_injective hd hg hp₁ hp₂, mixed_grid_surjective hg hp₁ hp₂⟩
  have he : Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂) =
      Sum.elim (fun z : C₁ × ↥(component Q 4) => z.1.val + z.2.val)
        (fun z : C₂ × ↥(component Q 5) => z.1.val + z.2.val) := by
    funext a; cases a <;> rfl
  rwa [he] at hb

/-- MSS's rigid-component input, with no additional mathematical hypothesis. -/
theorem rigidity : Rigidity := by
  intro Q hQ C₁ C₂ h0
  constructor
  · exact fun h => mixed_rigidity_necessary h hQ h0
  · rintro ⟨hd, hg, hp₁, hp₂⟩
    exact mixed_rigidity_sufficient hd hg hp₁ hp₂

end
end TranslationTiling.MSS
