import TranslationTiling.Rotations.GlobalRigidity

namespace TranslationTiling.Rotations.SixKeys

def assembly (E : Finset Point) : Finset Point :=
  E.biUnion fun e => gadget.image (grid e + ·)

theorem mem_assembly (E : Finset Point) (x : Point) :
    x ∈ assembly E ↔ ∃ e ∈ E, ∃ u ∈ gadget, x = grid e + u := by
  constructor
  · intro hx
    obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
    exact ⟨e, he, u, hu, heq.symm⟩
  · rintro ⟨e, he, u, hu, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

abbrev Placed (F : Finset Point) (m : Motion) : Set Point := m.apply '' (F : Set Point)

/-- All signed coordinate permutations are allowed, including reflections. -/
def GridTiles (F : Finset Point) : Prop :=
  ∃ C : Set Motion, ExactCover (fun m : C => Placed F m.val)

def AllowedGridTiles (allowed : Set Orientation) (F : Finset Point) : Prop :=
  ∃ C : Set Motion, (∀ m ∈ C, m.orientation ∈ allowed) ∧
    ExactCover (fun m : C => Placed F m.val)

def FiniteTiles (F : Finset Point) : Prop := ∃ A, ExactTiling A (F : Set Point)

theorem finiteTiles_iff (F : Finset Point) : FiniteTiles F ↔ TranslationTiling.Tiles F.toList := by
  simp [FiniteTiles, TranslationTiling.Tiles]

theorem cover_range {ι : Type*} {F : Finset Point} (M : ι → Motion)
    (cover : ExactCover (fun i => Placed F (M i))) :
    ExactCover (fun m : Set.range M => Placed F m.val) := by
  intro x
  obtain ⟨i, hi, unique⟩ := cover x
  refine ⟨⟨M i, i, rfl⟩, hi, ?_⟩
  intro m hm
  obtain ⟨j, hj⟩ := m.property
  have hji : j = i := unique j (by simpa only [hj] using hm)
  apply Subtype.ext
  exact hj.symm.trans (congrArg M hji)

theorem gridTiles_of_cover {ι : Type*} {F : Finset Point} (M : ι → Motion)
    (cover : ExactCover (fun i => Placed F (M i))) : GridTiles F :=
  ⟨Set.range M, cover_range M cover⟩

theorem allowedGridTiles_of_cover {ι : Type*} {F : Finset Point}
    (allowed : Set Orientation) (M : ι → Motion) (hM : ∀ i, (M i).orientation ∈ allowed)
    (cover : ExactCover (fun i => Placed F (M i))) : AllowedGridTiles allowed F := by
  refine ⟨Set.range M, ?_, cover_range M cover⟩
  rintro m ⟨i, rfl⟩
  exact hM i

theorem assembly_forward_allowed (allowed : Set Orientation)
    (hid : Orientation.ident ∈ allowed) (E : Finset Point) (hE : FiniteTiles E) :
    AllowedGridTiles allowed (assembly E) := by
  obtain ⟨A, coverE⟩ := hE
  let M : A → Motion := fun a => ⟨Orientation.ident, grid a.val⟩
  have applyM (a : A) (x : Point) : (M a).apply x = grid a.val + x := by simp [M, Motion.apply]
  apply allowedGridTiles_of_cover allowed M (by intro a; simpa [M] using hid)
  intro x
  obtain ⟨⟨z, u⟩, hx⟩ := fundamental_domain.2 x
  obtain ⟨z₀, hz₀⟩ := z.property
  obtain ⟨⟨a, e⟩, he⟩ := coverE.2 z₀
  change a.val + e.val = z₀ at he
  have hp : grid e.val + u.val ∈ assembly E :=
    (mem_assembly _ _).mpr ⟨e.val, e.property, u.val, u.property, rfl⟩
  have hax : (M a).apply (grid e.val + u.val) = x := by
    calc
      _ = grid (a.val + e.val) + u.val := by simp [applyM, grid, smul_add, add_assoc]
      _ = x := by rw [he, hz₀]; exact hx
  refine ⟨a, ⟨grid e.val + u.val, hp, hax⟩, ?_⟩
  rintro b ⟨p, hp, hb⟩
  obtain ⟨f, hf, v, hv, rfl⟩ := (mem_assembly _ _).mp hp
  have hEq : grid (b.val + f) + v = grid (a.val + e.val) + u.val := by
    calc
      _ = (M b).apply (grid f + v) := by simp [applyM, grid, smul_add, add_assoc]
      _ = x := hb
      _ = grid (a.val + e.val) + u.val := by
        rw [← hax]; simp [applyM, grid, smul_add, add_assoc]
  have hm := (grid_unique hv u.property hEq).1
  have hpair := coverE.1 (a₁ := (b, ⟨f, hf⟩)) (a₂ := (a, e)) hm
  exact congrArg Prod.fst hpair

theorem assembly_forward (E : Finset Point) (hE : FiniteTiles E) : GridTiles (assembly E) := by
  obtain ⟨C, _, hC⟩ := assembly_forward_allowed Set.univ (Set.mem_univ _) E hE
  exact ⟨C, hC⟩

def submotion (m : Motion) (e : Point) : Motion :=
  ⟨m.orientation, m.apply (grid e)⟩

@[simp] theorem submotion_apply (m : Motion) (e x : Point) :
    (submotion m e).apply x = m.apply (grid e + x) := by
  simp [submotion, Motion.apply, map_add, add_assoc]

theorem expand_cover {ι : Type*} (E : Finset Point) (M : ι → Motion)
    (cover : ExactCover (fun i => Placed (assembly E) (M i))) :
    ExactCover (fun p : ι × ↥E => Footprint (submotion (M p.1) p.2.val)) := by
  intro x
  obtain ⟨i, ⟨p, hp, hpx⟩, unique⟩ := cover x
  obtain ⟨e, he, u, hu, hpu⟩ := (mem_assembly _ _).mp hp
  refine ⟨(i, ⟨e, he⟩), ⟨u, hu, ?_⟩, ?_⟩
  · rw [submotion_apply, ← hpu]
    exact hpx
  · rintro ⟨j, f⟩ ⟨v, hv, hfv⟩
    have hj : j = i := unique j ⟨grid f.val + v,
      (mem_assembly _ _).mpr ⟨f.val, f.property, v, hv, rfl⟩,
      by simpa only [submotion_apply] using hfv⟩
    subst j
    have hEq : grid f.val + v = grid e + u := by
      apply (M i).injective
      rw [← hpu, hpx]
      simpa only [submotion_apply] using hfv
    exact Prod.ext rfl (Subtype.ext (grid_unique hv hu hEq).1)

theorem assembly_backward {ι : Type*} (E : Finset Point) (hE : E.Nonempty) (M : ι → Motion)
    (cover : ExactCover (fun i => Placed (assembly E) (M i))) : FiniteTiles E := by
  have expanded := expand_cover E M cover
  obtain ⟨r, rigid⟩ := rigidity (fun p : ι × ↥E => submotion (M p.1) p.2.val) expanded
  obtain ⟨e₀, he₀⟩ := hE
  choose z hz using fun i => rigid (i, ⟨e₀, he₀⟩)
  let a : ι → Point := fun i => z i - e₀
  have parent (i : ι) (y : Point) : (M i).apply y = r.apply (grid (a i) + y) := by
    have h := hz i (y - grid e₀)
    rw [submotion_apply] at h
    have hleft : grid e₀ + (y-grid e₀) = y := by abel
    have hright : grid (z i) + (y-grid e₀) = grid (a i) + y := by
      simp only [a, grid, smul_sub]
      abel
    rwa [hleft, hright] at h
  refine ⟨Set.range a, ?_, ?_⟩
  · rintro ⟨b, e⟩ ⟨c, f⟩ heq
    obtain ⟨i, hi⟩ := b.property
    obtain ⟨j, hj⟩ := c.property
    have hpoint (k : ι) (g : E) : r.apply (grid (a k + g.val)) ∈ Placed (assembly E) (M k) := by
      refine ⟨grid g.val, (mem_assembly _ _).mpr
        ⟨g.val, g.property, 0, body_subset_gadget zero_body, by simp⟩, ?_⟩
      rw [parent]
      simp [grid, smul_add]
    have hsame : r.apply (grid (a i + e.val)) = r.apply (grid (a j + f.val)) := by
      rw [hi, hj]
      exact congrArg (fun y => r.apply (grid y)) heq
    have hij := cover.same (hpoint i e) (by rw [hsame]; exact hpoint j f)
    subst j
    have hbc : b.val = c.val := hi.symm.trans hj
    have hef : e.val = f.val := by
      change b.val + e.val = c.val + f.val at heq
      rw [hbc] at heq
      exact add_left_cancel heq
    exact Prod.ext (Subtype.ext hbc) (Subtype.ext hef)
  · intro x
    obtain ⟨i, ⟨p, hp, hx⟩, _⟩ := cover (r.apply (grid x))
    obtain ⟨e, he, u, hu, hpu⟩ := (mem_assembly _ _).mp hp
    have hEq : grid (a i + e) + u = grid x + 0 := by
      have hh := r.injective ((parent i p).symm.trans hx)
      rw [hpu] at hh
      simpa [grid, smul_add, add_assoc] using hh
    have macroEq := (grid_unique hu (body_subset_gadget zero_body) hEq).1
    exact ⟨(⟨a i, i, rfl⟩, ⟨e, he⟩), macroEq⟩

/-- The rotation-resistant replacement preserves both tilability directions. -/
theorem assembly_tiles_iff (E : Finset Point) (hE : E.Nonempty) :
    FiniteTiles E ↔ GridTiles (assembly E) := by
  refine ⟨assembly_forward E, ?_⟩
  rintro ⟨C, hC⟩
  exact assembly_backward E hE (fun m : C => m.val) hC

/-- Restricting the allowed orientations to any set containing the identity
preserves the equivalence; in particular this applies to the 24 proper rotations. -/
theorem assembly_allowed_iff (E : Finset Point) (hE : E.Nonempty)
    (allowed : Set Orientation) (hid : Orientation.ident ∈ allowed) :
    FiniteTiles E ↔ AllowedGridTiles allowed (assembly E) := by
  refine ⟨assembly_forward_allowed allowed hid E, ?_⟩
  rintro ⟨C, _, hC⟩
  exact assembly_backward E hE (fun m : C => m.val) hC

end TranslationTiling.Rotations.SixKeys
