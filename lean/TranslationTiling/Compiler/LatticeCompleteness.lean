import TranslationTiling.Compiler.LatticeDescent

namespace TranslationTiling.Compiler.LatticeGeometry

noncomputable section
open scoped Classical

private theorem assembled_of_mixed {Q : ℕ} {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    {B : Set (Lattice 3)}
    (hc : ∀ {a a' u u'}, a ∈ B → a' ∈ B → u ∈ U → u' ∈ U →
      a + scaleHom u = a' + scaleHom u' → a = a' ∧ u = u')
    (hm : MSS.MixedTiling Q (nonzeroCenters B U) B) : Tiles (assembled Q U) B := by
  let I := (nonzeroCenters B U × ↥(MSS.component Q 4)) ⊕
    (B × ↥(MSS.component Q 5))
  let center : I → Lattice 3 := Sum.elim (fun z => z.1.val) (fun z => z.1.val)
  let vertex : I → Lattice 3 := Sum.elim (fun z => z.2.val) (fun z => z.2.val)
  have hvalue : (Sum.elim
      (fun z : nonzeroCenters B U × ↥(MSS.component Q 4) => z.1.val + z.2.val)
      (fun z : B × ↥(MSS.component Q 5) => z.1.val + z.2.val)) =
      fun i : I => center i + vertex i := by
    funext i
    cases i <;> rfl
  have mk (a : Lattice 3) (ha : a ∈ B) (u : Lattice 3) (hu : u ∈ U)
      (v : Lattice 3) (hv : v ∈ part Q u) :
      ∃ i : I, center i = a + scaleHom u ∧ vertex i = v := by
    by_cases hu0 : u = 0
    · have hp : v ∈ MSS.component Q 5 := by simpa [part, hu0] using hv
      exact ⟨Sum.inr (⟨a, ha⟩, ⟨v, hp⟩), by simp [center, hu0], rfl⟩
    · have hcenter : a + scaleHom u ∈ nonzeroCenters B U := ⟨a, ha, u, hu, hu0, rfl⟩
      have hp : v ∈ MSS.component Q 4 := by simpa [part, hu0] using hv
      exact ⟨Sum.inl (⟨a + scaleHom u, hcenter⟩, ⟨v, hp⟩), rfl, rfl⟩
  constructor
  · rintro ⟨f, a⟩ ⟨g, b⟩ he
    obtain ⟨u, hu, v, hv, hf⟩ := (mem_assembled Q U _).mp f.property
    obtain ⟨u', hu', v', hv', hg⟩ := (mem_assembled Q U _).mp g.property
    obtain ⟨i, hi, hp⟩ := mk a a.property u hu v hv
    obtain ⟨j, hj, hp'⟩ := mk b b.property u' hu' v' hv'
    have hij : i = j := by
      apply hm.1
      rw [hvalue]
      change center i + vertex i = center j + vertex j
      rw [hi, hj, hp, hp']
      change f.val + a.val = g.val + b.val at he
      rw [hf, hg] at he
      simpa only [add_assoc, add_comm, add_left_comm] using he
    have hcent : a.val + scaleHom u = b.val + scaleHom u' :=
      hi.symm.trans ((congrArg center hij).trans hj)
    obtain ⟨hab, huu⟩ := hc a.property b.property hu hu' hcent
    have hvv : v = v' := hp.symm.trans ((congrArg vertex hij).trans hp')
    exact Prod.ext (Subtype.ext (by rw [hf, hg, huu, hvv])) (Subtype.ext hab)
  · intro x
    obtain ⟨i, hi⟩ := hm.2 x
    cases i with
    | inl z =>
      obtain ⟨a, ha, u, hu, hn, hc⟩ := z.1.property
      have hv : z.2.val ∈ part Q u := by simpa [part, hn] using z.2.property
      let f : ↥(assembled Q U) :=
        ⟨scaleHom u + z.2.val, (mem_assembled Q U _).mpr ⟨u, hu, _, hv, rfl⟩⟩
      refine ⟨(f, ⟨a, ha⟩), ?_⟩
      change z.1.val + z.2.val = x at hi
      change (scaleHom u + z.2.val) + a = x
      rw [hc] at hi
      simpa only [add_assoc, add_comm, add_left_comm] using hi
    | inr z =>
      have hv : z.2.val ∈ part Q 0 := by simpa [part] using z.2.property
      let f : ↥(assembled Q U) :=
        ⟨z.2.val, (mem_assembled Q U _).mpr ⟨0, h0, _, hv, by simp⟩⟩
      refine ⟨(f, z.1), ?_⟩
      change z.1.val + z.2.val = x at hi
      change z.2.val + z.1.val = x
      simpa only [add_comm] using hi

private theorem period_image {A : Set (Lattice 3)} {w : Lattice 3} (hp : Period A w) :
    Period (scaleHom '' A) (scaleHom w) := by
  intro x
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a - w, (hp (a - w)).mp (by simpa using ha), ?_⟩
    rw [map_sub, he, add_sub_cancel_right]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a + w, (hp a).mpr ha, map_add scaleHom a w⟩

private theorem nonzeroCenters_period {B : Set (Lattice 3)} {U : Finset (Lattice 3)}
    {w : Lattice 3} (hp : Period B w) : Period (nonzeroCenters B U) w := by
  intro c
  constructor
  · rintro ⟨a, ha, u, hu, hn, he⟩
    refine ⟨a - w, (hp (a - w)).mp (by simpa using ha), u, hu, hn, ?_⟩
    calc
      c = (c + w) - w := by abel
      _ = a - w + scaleHom u := by rw [he]; abel
  · rintro ⟨a, ha, u, hu, hn, rfl⟩
    refine ⟨a + w, (hp a).mpr ha, u, hu, hn, ?_⟩
    abel

theorem assembled_of_periodic_lattice_complement (rigid : MSS.Rigidity)
    (Q : ℕ) (hQ : 0 < Q) (U : Finset (Lattice 3)) (h0 : 0 ∈ U)
    {A : Set (Lattice 3)} (hA : Tiles U A) (hp : Period A (MSS.kernelStep Q)) :
    Tiles (assembled Q U) (scaleHom '' A) := by
  let B := scaleHom '' A
  have hcent : ∀ {a a' u u'}, a ∈ B → a' ∈ B → u ∈ U → u' ∈ U →
      a + scaleHom u = a' + scaleHom u' → a = a' ∧ u = u' := by
    intro a a' u u' ha ha' hu hu' he
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := ha'
    have he' : u + b = u' + b' := by
      apply scaleHom_injective
      simp only [map_add]
      simpa only [add_comm] using he
    have h := hA.1 (a₁ := (⟨u, hu⟩, ⟨b, hb⟩)) (a₂ := (⟨u', hu'⟩, ⟨b', hb'⟩)) he'
    exact ⟨congrArg scaleHom (congrArg (fun z => z.2.val) h),
      congrArg (fun z => z.1.val) h⟩
  have hdisj : Disjoint (nonzeroCenters B U) B := by
    apply Set.disjoint_left.mpr
    rintro c ⟨a, ha, u, hu, hn, he⟩ hc
    have h := hcent ha hc hu h0 (by simpa only [map_zero, add_zero] using he.symm)
    exact hn h.2
  have hgrid : allCenters B U = Set.range scaleHom := by
    ext c
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, u, hu, rfl⟩
      exact ⟨b + u, map_add scaleHom b u⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨⟨u, a⟩, hx⟩ := hA.2 x
      refine ⟨scaleHom a.val, ⟨a.val, a.property, rfl⟩, u.val, u.property, ?_⟩
      rw [← hx, map_add, add_comm]
  have hnormal : 0 ∈ nonzeroCenters B U ∪ B := by
    rw [center_union B U h0, hgrid]
    exact ⟨0, map_zero scaleHom⟩
  have hpB : Period B (scaleHom (MSS.kernelStep Q)) := period_image hp
  have hm : MSS.MixedTiling Q (nonzeroCenters B U) B :=
    (rigid Q hQ _ _ hnormal).mpr
      ⟨hdisj, (center_union B U h0).trans hgrid, nonzeroCenters_period hpB, hpB⟩
  exact assembled_of_mixed h0 hcent hm

theorem assembled_of_quotient_tiling (rigid : MSS.Rigidity) (Q : ℕ) (hQ : 0 < Q)
    (F : Finset (CyclicQuotient.Group Q)) (h0 : 0 ∈ F)
    (hF : ∃ A : Set (CyclicQuotient.Group Q), Tiles F A) :
    ∃ B : Set (Lattice 3), Tiles (assembled Q (CyclicQuotient.representatives Q F)) B := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  obtain ⟨A, hA⟩ := hF
  have hp : Period ((CyclicQuotient.projection Q) ⁻¹' A) (MSS.kernelStep Q) := by
    have he : CyclicQuotient.kernelStep Q = MSS.kernelStep Q := by
      funext i
      fin_cases i <;> simp [CyclicQuotient.kernelStep, MSS.kernelStep]
    rw [← he]
    exact CyclicQuotient.period_preimage_kernelStep Q A
  exact ⟨_, assembled_of_periodic_lattice_complement rigid Q hQ _
    (CyclicQuotient.zero_mem_representatives Q h0) (CyclicQuotient.preimage_tiles Q hA) hp⟩

theorem assembled_iff_quotient (rigid : MSS.Rigidity) (Q : ℕ) (hQ : 0 < Q)
    (F : Finset (CyclicQuotient.Group Q)) (h0 : 0 ∈ F) :
    (∃ A : Set (CyclicQuotient.Group Q), Tiles F A) ↔
      ∃ B : Set (Lattice 3), Tiles (assembled Q (CyclicQuotient.representatives Q F)) B :=
  ⟨assembled_of_quotient_tiling rigid Q hQ F h0,
    quotient_tiling_of_assembled rigid Q hQ F h0⟩

end

end TranslationTiling.Compiler.LatticeGeometry
