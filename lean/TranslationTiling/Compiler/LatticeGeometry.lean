import TranslationTiling.Compiler.CyclicQuotient
import TranslationTiling.Compiler.QuotientTiling
import Mathlib.Tactic.Abel

namespace TranslationTiling.Compiler.LatticeGeometry

noncomputable section
open scoped Classical

def scaleHom : Lattice 3 →+ Lattice 3 where
  toFun x := MSS.scale • x
  map_zero' := smul_zero _
  map_add' := smul_add _

theorem scaleHom_injective : Function.Injective scaleHom := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (201 : ℤ) * x i = 201 * y i at hi
  exact mul_left_cancel₀ (by decide : (201 : ℤ) ≠ 0) hi

def part (Q : ℕ) (u : Lattice 3) : Finset (Lattice 3) :=
  if u = 0 then MSS.component Q 5 else MSS.component Q 4

def assembled (Q : ℕ) (U : Finset (Lattice 3)) : Finset (Lattice 3) :=
  U.biUnion fun u => (part Q u).image (fun v => scaleHom u + v)

private theorem zero_not_marker_frame (j : ℕ) (hj : 0 < j) :
    (0 : Lattice 3) ∉ (MSS.frame j).image (MSS.marker j + ·) := by
  intro h
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
  have hbox := (Finset.mem_sdiff.mp hv).1
  have hlo : -(j : ℤ) ≤ v 0 :=
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hbox 0)).1
  have he₀ := congrFun he 0
  have hj₀ : (0 : ℤ) < j := by exact_mod_cast hj
  change 12 * (j : ℤ) + v 0 = 0 at he₀
  omega

theorem zero_mem_component (Q j : ℕ) (hj : 0 < j) :
    (0 : Lattice 3) ∈ MSS.component Q j := by
  have hbox : (0 : Lattice 3) ∈ MSS.box 100 := by
    simp [MSS.box, Fintype.mem_piFinset]
  have hremoved : (0 : Lattice 3) ∉ MSS.removed := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
    exact zero_not_marker_frame (k.val + 1) (by omega) hk
  have hbase : (0 : Lattice 3) ∈ MSS.baseShape :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbox, hremoved⟩)
  exact Finset.mem_union_left _
    (Finset.mem_sdiff.mpr ⟨hbase, zero_not_marker_frame j hj⟩)

theorem zero_mem_part (Q : ℕ) (u : Lattice 3) : (0 : Lattice 3) ∈ part Q u := by
  by_cases hu : u = 0 <;> simp only [part, hu, if_pos, if_neg]
  · exact zero_mem_component Q 5 (by decide)
  · exact zero_mem_component Q 4 (by decide)

theorem mem_assembled (Q : ℕ) (U : Finset (Lattice 3)) (x : Lattice 3) :
    x ∈ assembled Q U ↔ ∃ u ∈ U, ∃ v ∈ part Q u, x = scaleHom u + v := by
  simp only [assembled, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩

private theorem projection_step (Q : ℕ) :
    CyclicQuotient.projection Q (MSS.kernelStep Q) = 0 := by
  have he : MSS.kernelStep Q = CyclicQuotient.kernelStep Q := by
    funext i
    fin_cases i <;> simp [MSS.kernelStep, CyclicQuotient.kernelStep]
  rw [he]
  exact CyclicQuotient.projection_kernelStep Q

private def coloredGrid (Q : ℕ) (zeroColor : Bool) : Set (Lattice 3) :=
  {c | ∃ z, c = scaleHom z ∧
    (if zeroColor then CyclicQuotient.projection Q z = 0
      else CyclicQuotient.projection Q z ≠ 0)}

private theorem coloredGrid_period (Q : ℕ) (b : Bool) :
    Period (coloredGrid Q b) (scaleHom (MSS.kernelStep Q)) := by
  intro c
  constructor
  · rintro ⟨z, hz, hc⟩
    refine ⟨z - MSS.kernelStep Q, ?_, ?_⟩
    · rw [map_sub, ← hz]
      abel
    · simpa only [map_sub, projection_step, sub_zero] using hc
  · rintro ⟨z, rfl, hc⟩
    refine ⟨z + MSS.kernelStep Q, (map_add scaleHom _ _).symm, ?_⟩
    simpa only [map_add, projection_step, add_zero] using hc

/-- MSS also certifies that the finitely many constituents of one output tile
are disjoint. The coloring separates their distinct quotient representatives. -/
theorem parts_unique (rigid : MSS.Rigidity) (Q : ℕ) (hQ : 0 < Q)
    (U : Finset (Lattice 3)) (h0 : 0 ∈ U)
    (hinj : Set.InjOn (CyclicQuotient.projection Q) (U : Set (Lattice 3)))
    {u u' v v' : Lattice 3} (hu : u ∈ U) (hu' : u' ∈ U)
    (hv : v ∈ part Q u) (hv' : v' ∈ part Q u')
    (he : scaleHom u + v = scaleHom u' + v') : u = u' ∧ v = v' := by
  let C₁ := coloredGrid Q false
  let C₂ := coloredGrid Q true
  have hd : Disjoint C₁ C₂ := by
    apply Set.disjoint_left.mpr
    rintro c ⟨z, hz, hn⟩ ⟨w, hw, hzero⟩
    have hzw := scaleHom_injective (hz.symm.trans hw)
    exact hn (hzw ▸ hzero)
  have hgrid : C₁ ∪ C₂ = Set.range scaleHom := by
    ext c
    constructor
    · rintro (⟨z, rfl, _⟩ | ⟨z, rfl, _⟩) <;> exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      by_cases hz : CyclicQuotient.projection Q z = 0
      · exact Or.inr ⟨z, rfl, hz⟩
      · exact Or.inl ⟨z, rfl, hz⟩
  have hnormal : 0 ∈ C₁ ∪ C₂ := by
    rw [hgrid]
    exact ⟨0, map_zero scaleHom⟩
  have hmix : MSS.MixedTiling Q C₁ C₂ :=
    (rigid Q hQ C₁ C₂ hnormal).mpr
      ⟨hd, hgrid, coloredGrid_period Q false, coloredGrid_period Q true⟩
  let Index := (C₁ × ↥(MSS.component Q 4)) ⊕ (C₂ × ↥(MSS.component Q 5))
  let center : Index → Lattice 3 := Sum.elim (fun z => z.1.val) (fun z => z.1.val)
  let vertex : Index → Lattice 3 := Sum.elim (fun z => z.2.val) (fun z => z.2.val)
  have mk (w : Lattice 3) (hw : w ∈ U) (p : Lattice 3) (hp : p ∈ part Q w) :
      ∃ i : Index, center i = scaleHom w ∧ vertex i = p := by
    by_cases hw0 : w = 0
    · have hC : scaleHom w ∈ C₂ := ⟨w, rfl, by simp [hw0]⟩
      have hp' : p ∈ MSS.component Q 5 := by simpa [part, hw0] using hp
      exact ⟨Sum.inr (⟨scaleHom w, hC⟩, ⟨p, hp'⟩), rfl, rfl⟩
    · have hproj : CyclicQuotient.projection Q w ≠ 0 := by
        intro hz
        exact hw0 (hinj hw h0 (by simpa only [map_zero] using hz))
      have hC : scaleHom w ∈ C₁ := ⟨w, rfl, hproj⟩
      have hp' : p ∈ MSS.component Q 4 := by simpa [part, hw0] using hp
      exact ⟨Sum.inl (⟨scaleHom w, hC⟩, ⟨p, hp'⟩), rfl, rfl⟩
  obtain ⟨i, hi, hv₁⟩ := mk u hu v hv
  obtain ⟨j, hj, hv₂⟩ := mk u' hu' v' hv'
  have hsum : (Sum.elim (fun z : C₁ × ↥(MSS.component Q 4) => z.1.val + z.2.val)
      (fun z : C₂ × ↥(MSS.component Q 5) => z.1.val + z.2.val)) =
      fun i : Index => center i + vertex i := by
    funext i
    cases i <;> rfl
  have hij : i = j := by
    apply hmix.1
    rw [hsum]
    change center i + vertex i = center j + vertex j
    rwa [hi, hj, hv₁, hv₂]
  exact ⟨scaleHom_injective (hi.symm.trans ((congrArg center hij).trans hj)),
    hv₁.symm.trans ((congrArg vertex hij).trans hv₂)⟩

end

end TranslationTiling.Compiler.LatticeGeometry
