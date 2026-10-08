import TranslationTiling.MSS.FrameConnectivity

/-! The only point trapped between two opposite frame points is the center
of a frame of radius one. -/

namespace TranslationTiling.MSS

theorem opposite_neighbors_in_frame (k : ℕ) (hk : 0 < k) (x : Lattice 3)
    (hplus : Function.update x (1 : Fin 3) (x 1 + 1) ∈ frame k)
    (hminus : Function.update x (1 : Fin 3) (x 1 - 1) ∈ frame k)
    (hx : x ∉ frame k) : k = 1 ∧ x = 0 := by
  obtain ⟨hp, ip, hip⟩ := (mem_frame_iff k hk _).mp hplus
  obtain ⟨hm, im, him⟩ := (mem_frame_iff k hk _).mp hminus
  have hxb : ∀ i, -(k : ℤ) ≤ x i ∧ x i ≤ k := by
    intro i
    by_cases hi : i = 1
    · subst i
      have hh := hp 1
      have hh' := hm 1
      simp only [Function.update_self] at hh hh'
      omega
    · simpa only [Function.update_of_ne hi] using hp i
  have hnob : ∀ i, x i ≠ -(k : ℤ) ∧ x i ≠ k := by
    intro i
    constructor <;> intro he
    · exact hx ((mem_frame_iff k hk x).mpr ⟨hxb, i, Or.inl he⟩)
    · exact hx ((mem_frame_iff k hk x).mpr ⟨hxb, i, Or.inr he⟩)
  have hip1 : ip = 1 := by
    by_contra hh
    simp only [Function.update_of_ne hh] at hip
    exact hip.elim (hnob ip).1 (hnob ip).2
  have him1 : im = 1 := by
    by_contra hh
    simp only [Function.update_of_ne hh] at him
    exact him.elim (hnob im).1 (hnob im).2
  subst ip
  subst im
  simp only [Function.update_self] at hip him
  have hk1 : k = 1 := by rcases hip with hip | hip <;> rcases him with him | him <;> omega
  refine ⟨hk1, ?_⟩
  funext i
  have hb := hxb i
  have hn := hnob i
  simp only [hk1, Nat.cast_one] at hb hn
  change x i = 0
  omega

end TranslationTiling.MSS
