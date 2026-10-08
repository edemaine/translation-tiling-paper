import TranslationTiling.MSS.TransverseCoverage
import TranslationTiling.MSS.FrameMatching
import Mathlib.Algebra.Ring.Periodic

/-! Matching the larger common frames forces the remaining coordinate steps. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem holes_bounds (j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5) {v : Lattice 3}
    (hv : v ∈ holes j) :
    (11 ≤ v 0 ∧ v 0 ≤ 65) ∧ (-5 ≤ v 1 ∧ v 1 ≤ 5) ∧ (-5 ≤ v 2 ∧ v 2 ≤ 5) := by
  obtain ⟨r, hr, hr5, hf, _⟩ := mem_holes_witness j hj hj5 hv
  have hh := ((mem_frame_iff r hr _).mp hf).1
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  simp only [Pi.sub_apply, marker] at h0 h1 h2
  simp only [if_neg (by decide : (1 : Fin 3) ≠ 0)] at h1
  simp only [if_neg (by decide : (2 : Fin 3) ≠ 0)] at h2
  push_cast at h0
  omega

theorem box_not_body_mem_holes (j : ℕ) {v : Lattice 3}
    (hv : v ∈ box 100) (hn : v ∉ body j) : v ∈ holes j := by
  by_contra hh
  exact hn (Finset.mem_sdiff.mpr ⟨hv, hh⟩)

theorem mixed_first_shift {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (t : ℤ) :
    c + (201 * t) • Pi.single 0 1 ∈ C₁ ∪ C₂ := by
  have hp : Function.Periodic (fun c => c ∈ C₁ ∪ C₂) (scale • Pi.single 0 1) :=
    fun c => propext (mixed_first_period h c)
  have hh := (Iff.of_eq (hp.zsmul t c)).mpr hc
  convert hh using 1
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, scale]
  ring

theorem placement_at_center {Q C₁ C₂} {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) :
    ∃ a : Placement Q C₁ C₂, a.center = c := by
  rcases hc with hc | hc
  · exact ⟨.inl (⟨c, hc⟩, ⟨0, zero_mem_component Q 4 (by omega)⟩), rfl⟩
  · exact ⟨.inr (⟨c, hc⟩, ⟨0, zero_mem_component Q 5 (by omega)⟩), rfl⟩

theorem mixed_copies_no_overlap {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    (a b : Placement Q C₁ C₂) (hne : a.center ≠ b.center)
    {u v : Lattice 3} (hu : u ∈ component Q a.radius) (hv : v ∈ component Q b.radius)
    (he : a.center + u = b.center + v) : False := by
  have he' : (a.withVertex u hu).position = (b.withVertex v hv).position := by
    simpa only [Placement.position, Placement.center_withVertex, Placement.vertex_withVertex]
      using he
  have hh := (mixed_placement_bijective h).1 he'
  apply hne
  simpa only [Placement.center_withVertex] using congrArg Placement.center hh

theorem mixed_common_forward {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (i : Fin 3) (hi : i ≠ 0) :
    c + scale • Pi.single i 1 ∈ C₁ ∪ C₂ := by
  let k := i.val + 1
  have hk : 0 < k := by dsimp [k]; omega
  have hk3 : k ≤ 3 := by have := i.isLt; dsimp [k]; omega
  let p := c + (scale • Pi.single i 1 + marker k)
  obtain ⟨d, hd, hdbox⟩ := mixed_transverse_cover h (p 1) (p 2)
  let t : ℤ := (p 0 - d 0 + 100) / 201
  let d' : Lattice 3 := d + (201 * t) • Pi.single 0 1
  have hd' : d' ∈ C₁ ∪ C₂ := mixed_first_shift h hd t
  obtain ⟨a, ha⟩ := placement_at_center (Q := Q) hc
  obtain ⟨b, hb⟩ := placement_at_center (Q := Q) hd'
  have d'_transverse (j : Fin 3) (hj : j ≠ 0) : d' j = d j := by
    simp only [d', Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
      smul_eq_mul, mul_zero, add_zero]
  have hdiff : p 0 - d' 0 = (p 0 - d 0 + 100) % 201 - 100 := by
    have hh := Int.emod_add_mul_ediv (p 0 - d 0 + 100) 201
    change p 0 - (d 0 + 201 * t * 1) = _
    dsimp [t]; omega
  have hx : -100 ≤ p 0 - d' 0 ∧ p 0 - d' 0 ≤ 100 := by
    have hl := Int.emod_nonneg (p 0 - d 0 + 100) (by omega : (201 : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (p 0 - d 0 + 100) (by omega : (0 : ℤ) < 201)
    omega
  have hy : -100 ≤ p 1 - d' 1 ∧ p 1 - d' 1 ≤ 100 := by
    simpa only [d'_transverse 1 (by decide)] using ⟨hdbox.1, hdbox.2.1⟩
  have hz : -100 ≤ p 2 - d' 2 ∧ p 2 - d' 2 ≤ 100 := by
    simpa only [d'_transverse 2 (by decide)] using ⟨hdbox.2.2.1, hdbox.2.2.2⟩
  have hne : a.center ≠ b.center := by
    intro he
    have hd'c : d' = c := hb.symm.trans (he.symm.trans ha)
    have hnz : i = 1 ∨ i = 2 := by have := i.isLt; apply Or.imp (Fin.ext) (Fin.ext); omega
    rcases hnz with rfl | rfl
    · have hh : p 1 - c 1 = 201 := by
        dsimp [p]; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
          smul_eq_mul, mul_one, marker, if_neg (by decide : (1 : Fin 3) ≠ 0), add_zero,
          scale]
        omega
      rw [hd'c, hh] at hy
      omega
    · have hh : p 2 - c 2 = 201 := by
        dsimp [p]; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
          smul_eq_mul, mul_one, marker, if_neg (by decide : (2 : Fin 3) ≠ 0), add_zero,
          scale]
        omega
      rw [hd'c, hh] at hz
      omega
  let u₀ : Lattice 3 := Pi.single 0 (if 0 ≤ p 0 - d' 0 then -(k : ℤ) else (k : ℤ))
  have hu₀ : u₀ ∈ frame k := by
    apply (mem_frame_iff k hk u₀).mpr
    refine ⟨?_, 0, ?_⟩
    · intro j
      by_cases hj : j = 0
      · subst j; simp only [u₀, Pi.single_eq_same]; split_ifs <;> omega
      · simp only [u₀, Pi.single_eq_of_ne hj]; omega
    · simp only [u₀, Pi.single_eq_same]; split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  let q := p + u₀ - d'
  have hqbox : q ∈ box 100 := by
    apply (mem_box_iff 100 _).mpr
    intro j
    fin_cases j
    · change -100 ≤ p 0 + u₀ 0 - d' 0 ∧ p 0 + u₀ 0 - d' 0 ≤ 100
      simp only [u₀, Pi.single_eq_same]; split_ifs <;> omega
    · change -100 ≤ p 1 + u₀ 1 - d' 1 ∧ p 1 + u₀ 1 - d' 1 ≤ 100
      simp only [u₀, Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0)]
      omega
    · change -100 ≤ p 2 + u₀ 2 - d' 2 ∧ p 2 + u₀ 2 - d' 2 ≤ 100
      simp only [u₀, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      omega
  have avoid (v : Lattice 3) (hv : v ∈ frame k) : p + v - d' ∉ body b.radius := by
    intro hbody
    have ha' := common_bump_mem_component Q a.radius a.radius_pos a.radius_le i hv
    have hb' := body_subset_component Q b.radius hbody
    apply mixed_copies_no_overlap h a b hne ha' hb'
    rw [ha, hb]
    dsimp [p]
    abel
  have hqholes := box_not_body_mem_holes b.radius hqbox (avoid u₀ hu₀)
  have hqb := holes_bounds b.radius b.radius_pos b.radius_le hqholes
  have hqx : 11 ≤ p 0 + u₀ 0 - d' 0 ∧ p 0 + u₀ 0 - d' 0 ≤ 65 := hqb.1
  have hqy : -5 ≤ p 1 - d' 1 ∧ p 1 - d' 1 ≤ 5 := by
    have hh := hqb.2.1
    simpa only [q, Pi.sub_apply, Pi.add_apply, u₀,
      Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0), add_zero] using hh
  have hqz : -5 ≤ p 2 - d' 2 ∧ p 2 - d' 2 ≤ 5 := by
    have hh := hqb.2.2
    simpa only [q, Pi.sub_apply, Pi.add_apply, u₀,
      Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), add_zero] using hh
  have hpx : 8 ≤ p 0 - d' 0 ∧ p 0 - d' 0 ≤ 68 := by
    simp only [u₀, Pi.single_eq_same] at hqx
    split_ifs at hqx <;> omega
  have allholes (v : Lattice 3) (hv : v ∈ frame k) : (p - d') + v ∈ holes b.radius := by
    have hvb := ((mem_frame_iff k hk v).mp hv).1
    have hbox : p + v - d' ∈ box 100 := by
      apply (mem_box_iff 100 _).mpr
      intro j
      have hvj := hvb j
      fin_cases j
      · change -100 ≤ p 0 + v 0 - d' 0 ∧ p 0 + v 0 - d' 0 ≤ 100
        change -(k : ℤ) ≤ v 0 ∧ v 0 ≤ k at hvj
        omega
      · change -100 ≤ p 1 + v 1 - d' 1 ∧ p 1 + v 1 - d' 1 ≤ 100
        change -(k : ℤ) ≤ v 1 ∧ v 1 ≤ k at hvj
        omega
      · change -100 ≤ p 2 + v 2 - d' 2 ∧ p 2 + v 2 - d' 2 ≤ 100
        change -(k : ℤ) ≤ v 2 ∧ v 2 ≤ k at hvj
        omega
    have hh := box_not_body_mem_holes b.radius hbox (avoid v hv)
    convert hh using 1 <;> abel
  have hmatch := translated_frame_subset_holes b.radius k b.radius_pos b.radius_le hk
    (p - d') allholes
  have he : d' = c + scale • Pi.single i 1 := by
    have hh := sub_eq_iff_eq_add.mp hmatch
    dsimp [p] at hh
    have hh' : (c + scale • Pi.single i 1) + marker k = d' + marker k := by
      calc
        _ = c + (scale • Pi.single i 1 + marker k) := by abel
        _ = marker k + d' := hh
        _ = d' + marker k := add_comm _ _
    exact (add_right_cancel hh').symm
  exact he ▸ hd'

end
end TranslationTiling.MSS
