import TranslationTiling.MSS.FrameSeparation

/-! Connectivity of each closed frame, used to confine whole detached pieces. -/

namespace TranslationTiling.MSS

theorem frame_path_to_corner (k : ℕ) (hk : 0 < k) (x : Lattice 3) (hx : x ∈ frame k) :
    FacePath (fun z => z ∈ frame k) x (fun _ => (k : ℤ)) := by
  obtain ⟨hxb, j, hj⟩ := (mem_frame_iff k hk x).mp hx
  let lo : Lattice 3 := fun i => if i = j then x j else -(k : ℤ)
  let hi : Lattice 3 := fun i => if i = j then x j else (k : ℤ)
  have hxh : ∀ i, lo i ≤ x i ∧ x i ≤ hi i := by
    intro i
    by_cases he : i = j
    · subst i; simp [lo, hi]
    · simpa only [lo, hi, if_neg he] using hxb i
  have hhh : ∀ i, lo i ≤ hi i ∧ hi i ≤ hi i := by
    intro i
    by_cases he : i = j
    · simp only [lo, hi, if_pos he, le_refl, and_self]
    · simp only [lo, hi, if_neg he, le_refl, and_true]
      omega
  have hface : ∀ z : Lattice 3, (∀ i, lo i ≤ z i ∧ z i ≤ hi i) → z ∈ frame k := by
    intro z hz
    apply (mem_frame_iff k hk z).mpr
    have hzj : z j = x j := by
      have hh := hz j
      simp only [lo, hi, if_pos rfl] at hh
      omega
    refine ⟨?_, j, hzj ▸ hj⟩
    intro i
    by_cases he : i = j
    · subst i; rw [hzj]; exact hxb j
    · simpa only [lo, hi, if_neg he] using hz i
  have first := FacePath.box3 (fun z => z ∈ frame k) lo hi x hi hxh hhh hface
  obtain ⟨j', hj'⟩ : ∃ i : Fin 3, i ≠ j := by
    by_cases he : j = 0
    · exact ⟨1, by subst j; decide⟩
    · exact ⟨0, Ne.symm he⟩
  have last : FacePath (fun z => z ∈ frame k) hi (Function.update hi j (k : ℤ)) := by
    apply FacePath.axis
    intro t ht ht'
    have hjb := hxb j
    have hhij : hi j = x j := by simp only [hi, if_pos rfl]
    simp only [hhij, min_eq_left hjb.2, max_eq_right hjb.2] at ht ht'
    apply (mem_frame_iff k hk _).mpr
    refine ⟨?_, j', Or.inr ?_⟩
    · intro i
      by_cases he : i = j
      · subst i
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne he, hi, if_neg he]
        omega
    · simp only [Function.update_of_ne hj', hi, if_neg hj']
  have he : Function.update hi j (k : ℤ) = (fun _ => (k : ℤ)) := by
    funext i
    by_cases he : i = j
    · subst i; simp only [Function.update_self]
    · simp only [Function.update_of_ne he, hi, if_neg he]
  rw [he] at last
  exact first.trans last

theorem frame_path (k : ℕ) (hk : 0 < k) (x y : Lattice 3)
    (hx : x ∈ frame k) (hy : y ∈ frame k) : FacePath (fun z => z ∈ frame k) x y :=
  (frame_path_to_corner k hk x hx).trans (frame_path_to_corner k hk y hy).reverse

theorem frame_connected (k : ℕ) (hk : 0 < k) : FaceConnected (frame k).toList := by
  intro x hx y hy
  exact FacePath.mono (frame_path k hk x y (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy))
    fun z hz => Finset.mem_toList.mpr hz

theorem frame_has_neighbor (k : ℕ) (hk : 0 < k) (x : Lattice 3) (hx : x ∈ frame k) :
    ∃ y ∈ frame k, FaceAdjacent x y := by
  let pos : Lattice 3 := fun _ => k
  let neg : Lattice 3 := fun _ => -(k : ℤ)
  have hp : pos ∈ frame k := by
    apply (mem_frame_iff k hk pos).mpr
    refine ⟨?_, 0, Or.inr rfl⟩
    intro i; dsimp [pos]; omega
  have hn : neg ∈ frame k := by
    apply (mem_frame_iff k hk neg).mpr
    refine ⟨?_, 0, Or.inl rfl⟩
    intro i; dsimp [neg]; omega
  have targets : ∃ y ∈ frame k, x ≠ y := by
    by_cases he : x = pos
    · refine ⟨neg, hn, ?_⟩
      intro hh
      have hv := congrFun (he.symm.trans hh) 0
      dsimp [pos, neg] at hv
      omega
    · exact ⟨pos, hp, he⟩
  obtain ⟨y, hy, hxy⟩ := targets
  rcases (frame_path k hk x y hx hy).cases_head with he | ⟨z, hz, _⟩
  · exact (hxy he).elim
  · exact ⟨z, hz.2.1, hz.2.2⟩

end TranslationTiling.MSS
