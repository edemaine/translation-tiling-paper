import TranslationTiling.Compiler.LatticeGeometry

namespace TranslationTiling.Compiler.LatticeGeometry

noncomputable section
open scoped Classical

def nonzeroCenters (B : Set (Lattice 3)) (U : Finset (Lattice 3)) : Set (Lattice 3) :=
  {c | ∃ a ∈ B, ∃ u ∈ U, u ≠ 0 ∧ c = a + scaleHom u}

def allCenters (B : Set (Lattice 3)) (U : Finset (Lattice 3)) : Set (Lattice 3) :=
  {c | ∃ a ∈ B, ∃ u ∈ U, c = a + scaleHom u}

theorem center_union (B : Set (Lattice 3)) (U : Finset (Lattice 3)) (h0 : 0 ∈ U) :
    nonzeroCenters B U ∪ B = allCenters B U := by
  ext c
  constructor
  · rintro (⟨a, ha, u, hu, _, rfl⟩ | hc)
    · exact ⟨a, ha, u, hu, rfl⟩
    · exact ⟨c, hc, 0, h0, by simp⟩
  · rintro ⟨a, ha, u, hu, rfl⟩
    by_cases hu0 : u = 0
    · exact Or.inr (by simpa [hu0] using ha)
    · exact Or.inl ⟨a, ha, u, hu, hu0, rfl⟩

variable {Q : ℕ} {U : Finset (Lattice 3)}

private theorem representations_unique
    (hparts : ∀ {u u' v v' : Lattice 3}, u ∈ U → u' ∈ U →
      v ∈ part Q u → v' ∈ part Q u' →
      scaleHom u + v = scaleHom u' + v' → u = u' ∧ v = v')
    {B : Set (Lattice 3)} (hB : Tiles (assembled Q U) B)
    {a a' u u' v v' : Lattice 3} (ha : a ∈ B) (ha' : a' ∈ B)
    (hu : u ∈ U) (hu' : u' ∈ U) (hv : v ∈ part Q u) (hv' : v' ∈ part Q u')
    (he : a + scaleHom u + v = a' + scaleHom u' + v') :
    a = a' ∧ u = u' ∧ v = v' := by
  let f : ↥(assembled Q U) :=
    ⟨scaleHom u + v, (mem_assembled Q U _).mpr ⟨u, hu, v, hv, rfl⟩⟩
  let f' : ↥(assembled Q U) :=
    ⟨scaleHom u' + v', (mem_assembled Q U _).mpr ⟨u', hu', v', hv', rfl⟩⟩
  have hp : (f, (⟨a, ha⟩ : B)) = (f', (⟨a', ha'⟩ : B)) := by
    apply hB.1
    change (scaleHom u + v) + a = (scaleHom u' + v') + a'
    convert he using 1 <;> abel
  have hf : scaleHom u + v = scaleHom u' + v' := congrArg (fun q => q.1.val) hp
  exact ⟨congrArg (fun q => q.2.val) hp, hparts hu hu' hv hv' hf⟩

theorem centers_injective_of_assembled
    (hparts : ∀ {u u' v v' : Lattice 3}, u ∈ U → u' ∈ U →
      v ∈ part Q u → v' ∈ part Q u' →
      scaleHom u + v = scaleHom u' + v' → u = u' ∧ v = v')
    {B : Set (Lattice 3)} (hB : Tiles (assembled Q U) B)
    {a a' u u' : Lattice 3} (ha : a ∈ B) (ha' : a' ∈ B)
    (hu : u ∈ U) (hu' : u' ∈ U)
    (he : a + scaleHom u = a' + scaleHom u') : a = a' ∧ u = u' := by
  have hr := representations_unique hparts hB ha ha' hu hu'
    (zero_mem_part Q u) (zero_mem_part Q u')
    (by simpa only [add_zero] using he)
  exact ⟨hr.1, hr.2.1⟩

/-- Every tiling of the assembled tile refines into the two MSS component
types, retaining unique representations even when centers are initially arbitrary. -/
theorem mixed_of_assembled
    (h0 : 0 ∈ U)
    (hparts : ∀ {u u' v v' : Lattice 3}, u ∈ U → u' ∈ U →
      v ∈ part Q u → v' ∈ part Q u' →
      scaleHom u + v = scaleHom u' + v' → u = u' ∧ v = v')
    {B : Set (Lattice 3)} (hB : Tiles (assembled Q U) B) :
    MSS.MixedTiling Q (nonzeroCenters B U) B := by
  let I := (nonzeroCenters B U × ↥(MSS.component Q 4)) ⊕
    (B × ↥(MSS.component Q 5))
  let center : I → Lattice 3 := Sum.elim (fun z => z.1.val) (fun z => z.1.val)
  let vertex : I → Lattice 3 := Sum.elim (fun z => z.2.val) (fun z => z.2.val)
  let tag : I → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  have repr (i : I) : ∃ a ∈ B, ∃ u ∈ U, ∃ v ∈ part Q u,
      center i = a + scaleHom u ∧ vertex i = v ∧ tag i = if u = 0 then 1 else 0 := by
    cases i with
    | inl z =>
      obtain ⟨a, ha, u, hu, hn, hc⟩ := z.1.property
      refine ⟨a, ha, u, hu, z.2.val, ?_, hc, rfl, ?_⟩
      · simpa [part, hn] using z.2.property
      · simp [tag, hn]
    | inr z =>
      exact ⟨z.1.val, z.1.property, 0, h0, z.2.val,
        by simpa [part] using z.2.property, by simp [center], rfl, by simp [tag]⟩
  have hvalue : (Sum.elim
      (fun z : nonzeroCenters B U × ↥(MSS.component Q 4) => z.1.val + z.2.val)
      (fun z : B × ↥(MSS.component Q 5) => z.1.val + z.2.val)) =
      fun i : I => center i + vertex i := by
    funext i
    cases i <;> rfl
  change Function.Bijective _
  rw [hvalue]
  constructor
  · intro i j he
    obtain ⟨a, ha, u, hu, v, hv, hc, hp, ht⟩ := repr i
    obtain ⟨a', ha', u', hu', v', hv', hc', hp', ht'⟩ := repr j
    have he' : a + scaleHom u + v = a' + scaleHom u' + v' := by
      simpa only [hc, hp, hc', hp', add_assoc] using he
    obtain ⟨haa, huu, hvv⟩ := representations_unique hparts hB ha ha' hu hu' hv hv' he'
    have hcent : center i = center j := by rw [hc, hc', haa, huu]
    have hpoint : vertex i = vertex j := by rw [hp, hp', hvv]
    have htag : tag i = tag j := by rw [ht, ht', huu]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        apply congrArg Sum.inl
        exact Prod.ext (Subtype.ext hcent) (Subtype.ext hpoint)
      | inr j => simp [tag] at htag
    | inr i =>
      cases j with
      | inl j => simp [tag] at htag
      | inr j =>
        apply congrArg Sum.inr
        exact Prod.ext (Subtype.ext hcent) (Subtype.ext hpoint)
  · intro x
    obtain ⟨⟨f, a⟩, hx⟩ := hB.2 x
    obtain ⟨u, hu, v, hv, hf⟩ := (mem_assembled Q U f.val).mp f.property
    have hx' : a.val + scaleHom u + v = x := by
      change f.val + a.val = x at hx
      rw [hf] at hx
      simpa only [add_assoc, add_comm, add_left_comm] using hx
    by_cases hu0 : u = 0
    · have hv' : v ∈ MSS.component Q 5 := by simpa [part, hu0] using hv
      refine ⟨Sum.inr (a, ⟨v, hv'⟩), ?_⟩
      simpa [center, vertex, hu0] using hx'
    · have hc : a.val + scaleHom u ∈ nonzeroCenters B U :=
        ⟨a.val, a.property, u, hu, hu0, rfl⟩
      have hv' : v ∈ MSS.component Q 4 := by simpa [part, hu0] using hv
      exact ⟨Sum.inl (⟨a.val + scaleHom u, hc⟩, ⟨v, hv'⟩), hx'⟩

end

end TranslationTiling.Compiler.LatticeGeometry
