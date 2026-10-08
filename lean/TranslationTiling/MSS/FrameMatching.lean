import TranslationTiling.MSS.ComponentIsolation

/-! A whole closed frame can fit the separated holes only at its own marker. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem adjacent_coordinate_bound {x y : Lattice 3} (h : FaceAdjacent x y) (i : Fin 3) :
    -1 ≤ y i - x i ∧ y i - x i ≤ 1 := by
  obtain ⟨k, he | he⟩ := h
  · have hh := congrFun he i
    simp only [Pi.add_apply, Pi.single_apply] at hh
    split_ifs at hh <;> omega
  · have hh := congrFun he i
    simp only [Pi.add_apply, Pi.single_apply] at hh
    split_ifs at hh <;> omega

theorem adjacent_holes_same_radius (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hr5 : r ≤ 5) (hs5 : s ≤ 5) {x y : Lattice 3}
    (hx : x - marker r ∈ frame r) (hy : y - marker s ∈ frame s)
    (hxy : FaceAdjacent x y) : r = s := by
  have hxb := ((mem_frame_iff r hr _).mp hx).1 0
  have hyb := ((mem_frame_iff s hs _).mp hy).1 0
  have hbound := adjacent_coordinate_bound hxy 0
  simp only [Pi.sub_apply, marker] at hxb hyb
  push_cast at hxb hyb
  omega

theorem holes_path_same_frame (j r : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (hr : 0 < r) (hr5 : r ≤ 5) {x y : Lattice 3}
    (hx : x - marker r ∈ frame r) (hpath : FacePath (fun z => z ∈ holes j) x y) :
    y - marker r ∈ frame r := by
  induction hpath with
  | refl => exact hx
  | @tail y z hpath hyz ih =>
    obtain ⟨s, hs, hs5, hz, _⟩ := mem_holes_witness j hj hj5 hyz.2.1
    have he := adjacent_holes_same_radius r s hr hs hr5 hs5 ih hz hyz.2.2
    simpa only [← he] using hz

theorem translated_frame_subset_frame (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (c : Lattice 3) (hsub : ∀ u ∈ frame k, c + u ∈ frame r) : k = r ∧ c = 0 := by
  have corners (sgn : ℤ) (hsgn : sgn = 1 ∨ sgn = -1) :
      (fun _ : Fin 3 => sgn * (k : ℤ)) ∈ frame k := by
    apply (mem_frame_iff k hk _).mpr
    rcases hsgn with rfl | rfl
    · refine ⟨?_, 0, Or.inr (by simp)⟩
      intro i; simp only [one_mul]; omega
    · refine ⟨?_, 0, Or.inl (by simp)⟩
      intro i; simp only [neg_one_mul]; omega
  have hc (i : Fin 3) : -(r : ℤ) + k ≤ c i ∧ c i ≤ r - k := by
    have hp := ((mem_frame_iff r hr _).mp (hsub _ (corners 1 (Or.inl rfl)))).1 i
    have hn := ((mem_frame_iff r hr _).mp (hsub _ (corners (-1) (Or.inr rfl)))).1 i
    simp only [Pi.add_apply, one_mul, neg_one_mul] at hp hn
    omega
  have hkr : k ≤ r := by have hh := hc 0; omega
  have he : k = r := by
    by_contra hne
    have hlt : k < r := by omega
    let u : Lattice 3 := fun i => if c i ≤ 0 then (k : ℤ) else -(k : ℤ)
    have hu : u ∈ frame k := by
      apply (mem_frame_iff k hk u).mpr
      refine ⟨?_, 0, ?_⟩
      · intro i; dsimp [u]; split_ifs <;> omega
      · dsimp [u]; split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
    have strict (i : Fin 3) : -(r : ℤ) < (c + u) i ∧ (c + u) i < r := by
      have hh := hc i
      simp only [Pi.add_apply, u]
      split_ifs <;> omega
    obtain ⟨_, i, hi⟩ := (mem_frame_iff r hr _).mp (hsub u hu)
    have hh := strict i
    omega
  refine ⟨he, ?_⟩
  ext i
  have hh := hc i
  simp only [Pi.zero_apply]
  omega

theorem translated_frame_subset_holes (j k : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (hk : 0 < k) (c : Lattice 3) (hsub : ∀ u ∈ frame k, c + u ∈ holes j) :
    c = marker k := by
  let u₀ : Lattice 3 := fun _ => (k : ℤ)
  have hu₀ : u₀ ∈ frame k := by
    apply (mem_frame_iff k hk _).mpr
    refine ⟨?_, 0, Or.inr rfl⟩
    intro i; dsimp [u₀]; omega
  obtain ⟨r, hr, hr5, h₀, _⟩ := mem_holes_witness j hj hj5 (hsub u₀ hu₀)
  have hf (v : Lattice 3) (hv : v ∈ frame k) : (c - marker r) + v ∈ frame r := by
    have path : FacePath (fun z => z ∈ holes j) (c + u₀) (c + v) :=
      Relation.ReflTransGen.lift (c + ·)
        (fun a b hab => ⟨hsub a hab.1, hsub b hab.2.1, adjacent_add c hab.2.2⟩)
        (frame_path k hk u₀ v hu₀ hv)
    have hh := holes_path_same_frame j r hj hj5 hr hr5 h₀ path
    convert hh using 1 <;> abel
  obtain ⟨he, hc⟩ := translated_frame_subset_frame k r hk hr (c - marker r) hf
  have hh := sub_eq_zero.mp hc
  simpa only [← he] using hh

end
end TranslationTiling.MSS
