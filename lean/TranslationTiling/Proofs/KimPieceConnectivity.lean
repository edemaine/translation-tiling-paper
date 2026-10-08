import TranslationTiling.Proofs.KimColorConnectivity
import TranslationTiling.Proofs.KimResidues

/-! Paths through inflated color classes, their dents, and attached bumps. -/

namespace TranslationTiling.Kim

def blockCenter (q : Lattice 3) : Lattice 3 := 3 • q + ![1, 1, 1]

theorem vector_eq_iff (v w : Lattice 3) :
    v = w ↔ v 0 = w 0 ∧ v 1 = w 1 ∧ v 2 = w 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩; funext k; fin_cases k <;> simpa using (by assumption)

theorem block_dent_iff (m : ℕ) (q c : Lattice 3) (hc : c ∈ cube 3) :
    3 • q + c ∈ dents m ↔
      (q = ![(m : ℤ) + 1, 0, 0] ∧ c = ![2, 1, 1]) ∨
      (q = ![0, (m : ℤ) + 1, 0] ∧ c = ![1, 2, 1]) ∨
      (q = ![0, 0, (m : ℤ) + 1] ∧ c = ![1, 1, 2]) := by
  have h0 := (mem_cube_iff _ _).mp hc 0
  have h1 := (mem_cube_iff _ _).mp hc 1
  have h2 := (mem_cube_iff _ _).mp hc 2
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false, vector_eq_iff]
  simp [scale]
  omega

/-- A small block remains connected after removing a positive-face midpoint. -/
theorem punctured_block_path (k : Fin 3) (c : Lattice 3) (hc : c ∈ cube 3)
    (hne : c ≠ (![1, 1, 1] : Lattice 3) + Pi.single k 1) :
    FacePath (fun z => z ∈ cube 3 ∧ z ≠ (![1, 1, 1] : Lattice 3) + Pi.single k 1)
      c ![1, 1, 1] := by
  let P := fun z => z ∈ cube 3 ∧ z ≠ (![1, 1, 1] : Lattice 3) + Pi.single k 1
  let d := Function.update c k 1
  have hd : d ∈ cube 3 := by
    apply (mem_cube_iff _ _).mpr
    intro j
    by_cases hj : j = k
    · subst j; simp [d]
    · simpa [d, hj] using (mem_cube_iff _ _).mp hc j
  have hdne : d ≠ (![1, 1, 1] : Lattice 3) + Pi.single k 1 := by
    intro he
    have he' := congrFun he k
    fin_cases k <;> simp [d] at he'
  have first : FacePath P c d := by
    have hk := (mem_cube_iff _ _).mp hc k
    have cases : c k = 0 ∨ c k = 1 ∨ c k = 2 := by omega
    rcases cases with hk | hk | hk
    · apply FacePath.step ⟨hc, hne⟩ ⟨hd, hdne⟩
      refine ⟨k, Or.inl ?_⟩
      funext j
      by_cases hj : j = k
      · subst j; simp [d, hk]
      · simp [d, hj]
    · have he : d = c := by simp [d, ← hk]
      exact he ▸ Relation.ReflTransGen.refl
    · apply FacePath.step ⟨hc, hne⟩ ⟨hd, hdne⟩
      refine ⟨k, Or.inr ?_⟩
      funext j
      by_cases hj : j = k
      · subst j; simp [d, hk]
      · simp [d, hj]
  have last : FacePath P d ![1, 1, 1] := by
    apply FacePath.box3 P (Function.update (0 : Lattice 3) k 1)
      (Function.update (fun _ => 2) k 1)
    · intro j
      by_cases hj : j = k
      · subst j; simp [d]
      · have := (mem_cube_iff _ _).mp hc j
        simp [d, hj]; omega
    · intro j
      by_cases hj : j = k
      · subst j; fin_cases k <;> simp
      · simp only [Function.update_of_ne hj]
        fin_cases j <;> simp
    · intro z hz
      constructor
      · apply (mem_cube_iff _ _).mpr
        intro j
        have := hz j
        by_cases hj : j = k
        · subst j; simp at this; omega
        · simp [hj] at this; omega
      · intro he
        have hzk := hz k
        simp at hzk
        have he' := congrFun he k
        have hzk' : z k = 1 := by omega
        rw [hzk'] at he'
        fin_cases k <;> simp at he'
  exact first.trans last

theorem block_path_to_center (m i : ℕ) (q c : Lattice 3)
    (hq : q ∈ cube (m + 2)) (hqi : color m q = i) (hc : c ∈ cube 3)
    (hnd : 3 • q + c ∉ dents m) :
    FacePath (fun z => z ∈ piece m i) (3 • q + c) (blockCenter q) := by
  let P := fun z => z ∈ cube 3 ∧ 3 • q + z ∉ dents m
  have small : FacePath P c ![1, 1, 1] := by
    by_cases hq0 : q = ![(m : ℤ) + 1, 0, 0]
    · have hne : c ≠ (![1, 1, 1] : Lattice 3) + Pi.single 0 1 := by
        intro he
        apply hnd
        apply (block_dent_iff _ _ _ hc).mpr
        exact Or.inl ⟨hq0, by simpa [vector_eq_iff] using he⟩
      apply FacePath.mono (punctured_block_path 0 c hc hne)
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [block_dent_iff _ _ _ hz.1]
      simp [hq0, vector_eq_iff] at hz ⊢
      omega
    · by_cases hq1 : q = ![0, (m : ℤ) + 1, 0]
      · have hne : c ≠ (![1, 1, 1] : Lattice 3) + Pi.single 1 1 := by
          intro he; apply hnd
          apply (block_dent_iff _ _ _ hc).mpr
          exact Or.inr (Or.inl ⟨hq1, by simpa [vector_eq_iff] using he⟩)
        apply FacePath.mono (punctured_block_path 1 c hc hne)
        intro z hz
        refine ⟨hz.1, ?_⟩
        rw [block_dent_iff _ _ _ hz.1]
        simp [hq1, vector_eq_iff] at hz ⊢
        omega
      · by_cases hq2 : q = ![0, 0, (m : ℤ) + 1]
        · have hne : c ≠ (![1, 1, 1] : Lattice 3) + Pi.single 2 1 := by
            intro he; apply hnd
            apply (block_dent_iff _ _ _ hc).mpr
            exact Or.inr (Or.inr ⟨hq2, by simpa [vector_eq_iff] using he⟩)
          apply FacePath.mono (punctured_block_path 2 c hc hne)
          intro z hz
          refine ⟨hz.1, ?_⟩
          rw [block_dent_iff _ _ _ hz.1]
          simp [hq2, vector_eq_iff] at hz ⊢
          omega
        · apply FacePath.box3 P 0 (fun _ => 2) c ![1, 1, 1]
          · intro j; have := (mem_cube_iff _ _).mp hc j; simp; omega
          · intro j; fin_cases j <;> simp
          · intro z hz
            have hzc : z ∈ cube 3 := by
              apply (mem_cube_iff _ _).mpr
              intro j; have := hz j; simp at this; omega
            refine ⟨hzc, ?_⟩
            rw [block_dent_iff _ _ _ hzc]
            simp [hq0, hq1, hq2]
  exact Relation.ReflTransGen.lift (fun z => 3 • q + z)
    (fun a b hab => ⟨mem_piece_of_block hq hqi hab.1.1 hab.1.2,
      mem_piece_of_block hq hqi hab.2.1.1 hab.2.1.2,
      by
        obtain ⟨k, hk | hk⟩ := hab.2.2
        · exact ⟨k, Or.inl (by rw [hk, add_assoc])⟩
        · exact ⟨k, Or.inr (by rw [hk, add_assoc])⟩⟩) small

theorem internal_not_dent (m : ℕ) (v : Lattice 3)
    (hv : ∀ k, v k ≤ (scale m : ℤ) - 2) : v ∉ dents m := by
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h)
  · have he := congrFun h 0; have := hv 0; simp at he; omega
  · have he := congrFun h 1; have := hv 1; simp at he; omega
  · have he := congrFun h 2; have := hv 2; simp at he; omega

theorem center_bounds (m : ℕ) (q : Lattice 3) (hq : q ∈ cube (m + 2)) :
    ∀ k, 1 ≤ blockCenter q k ∧ blockCenter q k ≤ (scale m : ℤ) - 2 := by
  intro k
  have := (mem_cube_iff _ _).mp hq k
  fin_cases k <;> simp [blockCenter, scale] at this ⊢ <;> omega

theorem center_mem_piece (m i : ℕ) (q : Lattice 3)
    (hq : q ∈ cube (m + 2)) (hqi : color m q = i) : blockCenter q ∈ piece m i :=
  mem_piece_of_block hq hqi (by decide)
    (internal_not_dent m _ (fun k => (center_bounds m q hq k).2))

theorem center_edge_forward (m i : ℕ) (q r : Lattice 3)
    (hq : q ∈ cube (m + 2)) (hr : r ∈ cube (m + 2))
    (hqi : color m q = i) (hri : color m r = i)
    (k : Fin 3) (he : r = q + Pi.single k 1) :
    FacePath (fun z => z ∈ piece m i) (blockCenter q) (blockCenter r) := by
  have endpoint : Function.update (blockCenter q) k (blockCenter r k) = blockCenter r := by
    funext j
    by_cases hj : j = k
    · subst j; simp
    · simp [blockCenter, he, hj]
  rw [← endpoint]
  apply FacePath.axis
  intro t ht hu
  have hqk := (mem_cube_iff _ _).mp hq k
  have hqbound := center_bounds m q hq
  have hrbound := center_bounds m r hr
  have hec : blockCenter r k = blockCenter q k + 3 := by
    fin_cases k <;> simp [blockCenter, he] <;> omega
  have ht' : blockCenter q k ≤ t ∧ t ≤ blockCenter r k := by
    rw [min_eq_left (by omega)] at ht
    rw [max_eq_right (by omega)] at hu
    exact ⟨ht, hu⟩
  have hnd : Function.update (blockCenter q) k t ∉ dents m := by
    apply internal_not_dent
    intro j
    by_cases hj : j = k
    · subst j; simp; have := hrbound k; omega
    · simpa [hj] using (hqbound j).2
  by_cases htq : t ≤ 3 * q k + 2
  · let c := Function.update (![1, 1, 1] : Lattice 3) k (t - 3 * q k)
    have hc : c ∈ cube 3 := by
      apply (mem_cube_iff _ _).mpr
      intro j
      by_cases hj : j = k
      · subst j
        simp [c]
        fin_cases k <;> simp [blockCenter] at ht' htq ⊢ <;> omega
      · simp only [c, Function.update_of_ne hj]
        fin_cases j <;> simp
    have hx : Function.update (blockCenter q) k t = 3 • q + c := by
      funext j
      by_cases hj : j = k
      · subst j; simp [c]
      · simp [c, blockCenter, hj]
    rw [hx] at hnd ⊢
    exact mem_piece_of_block hq hqi hc hnd
  · let c := Function.update (![1, 1, 1] : Lattice 3) k (t - 3 * r k)
    have hc : c ∈ cube 3 := by
      apply (mem_cube_iff _ _).mpr
      intro j
      by_cases hj : j = k
      · subst j
        simp [c]
        have herk : r k = q k + 1 := by simp [he]
        fin_cases k <;> simp [blockCenter] at ht' htq herk ⊢ <;> omega
      · simp only [c, Function.update_of_ne hj]
        fin_cases j <;> simp
    have hx : Function.update (blockCenter q) k t = 3 • r + c := by
      funext j
      by_cases hj : j = k
      · subst j; simp [c]
      · simp [c, blockCenter, he, hj]
    rw [hx] at hnd ⊢
    exact mem_piece_of_block hr hri hc hnd

theorem centers_connected (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (q r : Lattice 3) (hq : q ∈ cube (m + 2)) (hr : r ∈ cube (m + 2))
    (hqi : color m q = i) (hri : color m r = i) :
    FacePath (fun z => z ∈ piece m i) (blockCenter q) (blockCenter r) := by
  apply Relation.ReflTransGen.lift' blockCenter _ (color_connected m i hi him q r hq hr hqi hri)
  intro a b hab
  obtain ⟨k, hk | hk⟩ := hab.2.2
  · exact center_edge_forward m i a b hab.1.1 hab.2.1.1 hab.1.2 hab.2.1.2 k hk
  · exact FacePath.reverse
      (center_edge_forward m i b a hab.2.1.1 hab.1.1 hab.2.1.2 hab.1.2 k hk)

theorem piece_path_to_core (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (v : Lattice 3) (hv : v ∈ piece m i) :
    FacePath (fun z => z ∈ piece m i) v (blockCenter ![1, 1, (i : ℤ)]) := by
  have hroot : ![1, 1, (i : ℤ)] ∈ cube (m + 2) := by
    apply (mem_cube_iff _ _).mpr
    intro k; fin_cases k <;> simp <;> omega
  have raw_route (q c : Lattice 3) (hq : q ∈ cube (m + 2))
      (hqi : color m q = i) (hc : c ∈ cube 3) (hnd : 3 • q + c ∉ dents m) :
      FacePath (fun z => z ∈ piece m i) (3 • q + c)
        (blockCenter ![1, 1, (i : ℤ)]) :=
    (block_path_to_center m i q c hq hqi hc hnd).trans
      (centers_connected m i hi him q _ hq hroot hqi (color_core m i hi him))
  rcases mem_piece_cases hv with ⟨hr, hnd⟩ | ⟨rfl, hb⟩
  · obtain ⟨q, hq, hqi, c, hc, rfl⟩ := (mem_rawPiece _ _ _).mp hr
    exact raw_route q c hq hqi hc hnd
  · have hzero : (0 : Lattice 3) ∈ cube (m + 2) := by
      apply (mem_cube_iff _ _).mpr
      intro k; simp; omega
    have hcolor : color m 0 = 1 := by simp [color]
    have attach (c : Lattice 3) (hc : c ∈ cube 3)
        (ha : FaceAdjacent v c) :
        FacePath (fun z => z ∈ piece m 1) v (blockCenter ![1, 1, (1 : ℤ)]) := by
      have hnd : 3 • (0 : Lattice 3) + c ∉ dents m := by
        apply internal_not_dent
        intro k
        have := (mem_cube_iff _ _).mp hc k
        simp [scale]; omega
      have hc' : c ∈ piece m 1 := by simpa using mem_piece_of_block hzero hcolor hc hnd
      exact (FacePath.step hv hc' ha).trans (by simpa using raw_route 0 c hzero hcolor hc hnd)
    simp only [bumps, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · apply attach ![0, 1, 1] (by decide)
      refine ⟨0, Or.inl ?_⟩; funext k; fin_cases k <;> simp
    · apply attach ![1, 0, 1] (by decide)
      refine ⟨1, Or.inl ?_⟩; funext k; fin_cases k <;> simp
    · apply attach ![1, 1, 0] (by decide)
      refine ⟨2, Or.inl ?_⟩; funext k; fin_cases k <;> simp

theorem piece_connected (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    FaceConnected (piece m i) := by
  intro x hx y hy
  exact (piece_path_to_core m i hi him x hx).trans
    (FacePath.reverse (piece_path_to_core m i hi him y hy))

end TranslationTiling.Kim
