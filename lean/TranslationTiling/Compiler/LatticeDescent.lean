import TranslationTiling.Compiler.LatticeAssembly
import Mathlib.Algebra.Ring.Periodic

namespace TranslationTiling.Compiler.LatticeGeometry

noncomputable section
open scoped Classical

private theorem period_zsmul {B : Set (Lattice 3)} {w : Lattice 3}
    (h : Period B w) (n : ℤ) : Period B (n • w) := by
  have hp : Function.Periodic (fun x => x ∈ B) w := fun x => propext (h x)
  intro x
  exact Iff.of_eq (hp.zsmul n x)

private theorem normalize_complement {F : Finset (Lattice 3)}
    {B : Set (Lattice 3)} (hB : Tiles F B) :
    ∃ C : Set (Lattice 3), Tiles F C ∧ 0 ∈ C := by
  obtain ⟨⟨_, a⟩, _⟩ := hB.2 0
  let C := {c : Lattice 3 | c + a.val ∈ B}
  refine ⟨C, Stacking.covers_iff_unique_tile.mpr ?_, by simpa [C] using a.property⟩
  intro x
  obtain ⟨f, hf, hu⟩ := Stacking.covers_iff_unique_tile.mp hB (x + a.val)
  refine ⟨f, ?_, ?_⟩
  · change x - f.val + a.val ∈ B
    convert hf using 1 <;> abel
  · intro g hg
    apply hu
    change x - g.val + a.val ∈ B at hg
    convert hg using 1 <;> abel

theorem lattice_complement_of_normalized_assembled
    (rigid : MSS.Rigidity) (Q : ℕ) (hQ : 0 < Q)
    (U : Finset (Lattice 3)) (h0 : 0 ∈ U)
    (hinj : Set.InjOn (CyclicQuotient.projection Q) (U : Set (Lattice 3)))
    {B : Set (Lattice 3)} (hB : Tiles (assembled Q U) B) (hB0 : 0 ∈ B) :
    ∃ A : Set (Lattice 3), Tiles U A ∧ Period A (MSS.kernelStep Q) := by
  have hparts : ∀ {u u' v v' : Lattice 3}, u ∈ U → u' ∈ U →
      v ∈ part Q u → v' ∈ part Q u' →
      scaleHom u + v = scaleHom u' + v' → u = u' ∧ v = v' := by
    intro u u' v v' hu hu' hv hv' he
    exact parts_unique rigid Q hQ U h0 hinj hu hu' hv hv' he
  have hmixed := mixed_of_assembled h0 hparts hB
  have hrigid := (rigid Q hQ (nonzeroCenters B U) B (Or.inr hB0)).mp hmixed
  have hgrid : allCenters B U = Set.range scaleHom := by
    rw [← center_union B U h0]
    exact hrigid.2.1
  have hBgrid {a : Lattice 3} (ha : a ∈ B) : ∃ b, scaleHom b = a := by
    have hc : a ∈ allCenters B U := ⟨a, ha, 0, h0, by simp⟩
    rw [hgrid] at hc
    exact hc
  let A := {a : Lattice 3 | scaleHom a ∈ B}
  have hA : Tiles U A := by
    constructor
    · rintro ⟨u, a⟩ ⟨v, b⟩ he
      have hscaled : scaleHom a.val + scaleHom u.val =
          scaleHom b.val + scaleHom v.val := by
        have h := congrArg scaleHom he
        simpa only [map_add, add_comm] using h
      obtain ⟨hab, huv⟩ := centers_injective_of_assembled hparts hB
        a.property b.property u.property v.property hscaled
      exact Prod.ext (Subtype.ext huv) (Subtype.ext (scaleHom_injective hab))
    · intro x
      have hx : scaleHom x ∈ allCenters B U := by rw [hgrid]; exact ⟨x, rfl⟩
      obtain ⟨a, ha, u, hu, he⟩ := hx
      obtain ⟨b, hb⟩ := hBgrid ha
      have hbu : u + b = x := by
        apply scaleHom_injective
        rw [map_add, hb]
        exact (add_comm _ _).trans he.symm
      exact ⟨(⟨u, hu⟩, ⟨b, by change scaleHom b ∈ B; rw [hb]; exact ha⟩), hbu⟩
  refine ⟨A, hA, ?_⟩
  intro a
  change scaleHom (a + MSS.kernelStep Q) ∈ B ↔ scaleHom a ∈ B
  rw [map_add]
  exact hrigid.2.2.2 (scaleHom a)

/-- Arbitrary assembled-tile complements descend through the cyclic quotient;
MSS supplies the missing grid and kernel-period conclusions. -/
theorem quotient_tiling_of_assembled (rigid : MSS.Rigidity) (Q : ℕ) (hQ : 0 < Q)
    (F : Finset (CyclicQuotient.Group Q)) (h0 : 0 ∈ F)
    (hF : ∃ B : Set (Lattice 3), Tiles (assembled Q (CyclicQuotient.representatives Q F)) B) :
    ∃ A : Set (CyclicQuotient.Group Q), Tiles F A := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  obtain ⟨B, hB⟩ := hF
  obtain ⟨C, hC, hC0⟩ := normalize_complement hB
  obtain ⟨A, hA, hp⟩ := lattice_complement_of_normalized_assembled rigid Q hQ
    (CyclicQuotient.representatives Q F) (CyclicQuotient.zero_mem_representatives Q h0)
    (CyclicQuotient.projection_injOn_representatives Q F) hC hC0
  have hk : ∀ k ∈ (CyclicQuotient.projection Q).ker, Period A k := by
    intro k hk
    obtain ⟨n, rfl⟩ := (CyclicQuotient.mem_ker_iff_zsmul_kernelStep Q k).mp hk
    have he : CyclicQuotient.kernelStep Q = MSS.kernelStep Q := by
      funext i
      fin_cases i <;> simp [CyclicQuotient.kernelStep, MSS.kernelStep]
    rw [he]
    exact period_zsmul hp n
  have ht := tiles_image_of_kernel_periods (CyclicQuotient.projection Q)
    (CyclicQuotient.projection_surjective Q) hA hk
  rw [CyclicQuotient.projection_image_representatives Q F] at ht
  exact ⟨_, ht⟩

end

end TranslationTiling.Compiler.LatticeGeometry
