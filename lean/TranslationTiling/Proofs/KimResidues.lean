import TranslationTiling.Proofs.KimGeometry
import Mathlib.Data.List.Enum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators

/-! Residue representatives of Kim's pieces and shells. -/

namespace TranslationTiling.Kim

def residue (s : ℕ) (v : Lattice 3) : Lattice 3 := fun k => v k % (s : ℤ)

theorem scale_pos (m : ℕ) : 1 < scale m := by unfold scale; omega

theorem residue_mem_cube (s : ℕ) (hs : 0 < s) (v : Lattice 3) :
    residue s v ∈ cube s := by
  apply (mem_cube_iff _ _).mpr
  intro k
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

theorem residue_eq_self {s : ℕ} {v : Lattice 3} (hv : v ∈ cube s) :
    residue s v = v := by
  funext k
  exact Int.emod_eq_of_lt ((mem_cube_iff _ _).mp hv k).1
    ((mem_cube_iff _ _).mp hv k).2

theorem residue_scale_add (s : ℕ) (u v : Lattice 3) :
    residue s ((s : ℤ) • u + v) = residue s v := by
  funext k
  simp [residue, Int.add_emod]

private theorem neg_one_emod (s : ℕ) (hs : 1 < s) :
    (-1 : ℤ) % (s : ℤ) = (s : ℤ) - 1 := by
  have he : (-1 : ℤ) ≡ (s : ℤ) - 1 [ZMOD (s : ℤ)] :=
    Int.modEq_of_dvd ⟨1, by omega⟩
  rw [show (-1 : ℤ) % (s : ℤ) = ((s : ℤ) - 1) % (s : ℤ) from he]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem dent_mem_rawPiece {m : ℕ} {v : Lattice 3} (hv : v ∈ dents m) :
    v ∈ rawPiece m 1 := by
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · apply (mem_rawPiece _ _ _).mpr
    refine ⟨![(m : ℤ) + 1, 0, 0], ?_, ?_, ![2, 1, 1], by decide, ?_⟩
    · apply (mem_cube_iff _ _).mpr
      intro k
      fin_cases k <;> simp <;> omega
    · unfold color
      dsimp
      split_ifs <;> omega
    · funext k
      fin_cases k <;> simp [scale]
      omega
  · apply (mem_rawPiece _ _ _).mpr
    refine ⟨![0, (m : ℤ) + 1, 0], ?_, ?_, ![1, 2, 1], by decide, ?_⟩
    · apply (mem_cube_iff _ _).mpr
      intro k
      fin_cases k <;> simp <;> omega
    · unfold color
      dsimp
      split_ifs <;> omega
    · funext k
      fin_cases k <;> simp [scale]
      omega
  · apply (mem_rawPiece _ _ _).mpr
    refine ⟨![0, 0, (m : ℤ) + 1], ?_, ?_, ![1, 1, 2], by decide, ?_⟩
    · apply (mem_cube_iff _ _).mpr
      intro k
      fin_cases k <;> simp <;> omega
    · simp [color]
    · funext k
      fin_cases k <;> simp [scale]
      omega

theorem rawPiece_mem_cube {m i : ℕ} {v : Lattice 3} (hv : v ∈ rawPiece m i) :
    v ∈ cube (scale m) := by
  obtain ⟨q, hq, _, c, hc, he⟩ := (mem_rawPiece _ _ _).mp hv
  have hs : scale m = 3 * (m + 2) := by unfold scale; omega
  rw [hs, cube_blocks]
  exact ⟨q, hq, c, hc, he⟩

theorem rawPiece_color_unique {m i j : ℕ} {v : Lattice 3}
    (hi : v ∈ rawPiece m i) (hj : v ∈ rawPiece m j) : i = j := by
  by_contra h
  exact (Set.disjoint_left.mp (rawPieces_disjoint m i j h)) hi hj

theorem bump_residue_mem_dents {m : ℕ} {v : Lattice 3} (hv : v ∈ bumps) :
    residue (scale m) v ∈ dents m := by
  have hs := scale_pos m
  have h1 : (1 : ℤ) % (scale m : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [bumps, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
  rcases hv with rfl | rfl | rfl
  · apply Or.inl
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]
  · apply Or.inr ∘ Or.inl
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]
  · apply Or.inr ∘ Or.inr
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]

theorem dent_has_bump {m : ℕ} {v : Lattice 3} (hv : v ∈ dents m) :
    ∃ b ∈ bumps, residue (scale m) b = v := by
  have hs := scale_pos m
  have h1 : (1 : ℤ) % (scale m : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · refine ⟨![-1, 1, 1], by simp [bumps], ?_⟩
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]
  · refine ⟨![1, -1, 1], by simp [bumps], ?_⟩
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]
  · refine ⟨![1, 1, -1], by simp [bumps], ?_⟩
    funext k
    fin_cases k <;> simp [residue, neg_one_emod _ hs, h1]

theorem bump_residue_injective {m : ℕ} {v w : Lattice 3}
    (hv : v ∈ bumps) (hw : w ∈ bumps)
    (he : residue (scale m) v = residue (scale m) w) : v = w := by
  have hs := scale_pos m
  have h1 : (1 : ℤ) % (scale m : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have hn : (scale m : ℤ) - 1 ≠ 1 := by unfold scale; omega
  simp only [bumps, List.mem_cons, List.not_mem_nil, or_false] at hv hw
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  all_goals try rfl
  all_goals
    have h0 := congrFun he 0
    have h2 := congrFun he 1
    simp [residue, neg_one_emod _ hs, h1] at h0 h2
    omega

theorem mem_piece_cases {m i : ℕ} {v : Lattice 3} (hv : v ∈ piece m i) :
    (v ∈ rawPiece m i ∧ v ∉ dents m) ∨ (i = 1 ∧ v ∈ bumps) := by
  rw [piece_eq] at hv
  by_cases hi : i = 1
  · rw [if_pos hi, List.mem_append] at hv
    rcases hv with hv | hv
    · exact Or.inl (by simpa using hv)
    · exact Or.inr ⟨hi, hv⟩
  · rw [if_neg hi] at hv
    refine Or.inl ⟨hv, ?_⟩
    intro hd
    exact hi (rawPiece_color_unique hv (dent_mem_rawPiece hd))

theorem piece_residue_mem_rawPiece {m i : ℕ} {v : Lattice 3}
    (hv : v ∈ piece m i) : residue (scale m) v ∈ rawPiece m i := by
  rcases mem_piece_cases hv with ⟨hr, _⟩ | ⟨rfl, hb⟩
  · rwa [residue_eq_self (rawPiece_mem_cube hr)]
  · exact dent_mem_rawPiece (bump_residue_mem_dents hb)

theorem pieces_residue_unique {m i j : ℕ} {v w : Lattice 3}
    (hv : v ∈ piece m i) (hw : w ∈ piece m j)
    (he : residue (scale m) v = residue (scale m) w) : i = j ∧ v = w := by
  have hi : i = j := rawPiece_color_unique (piece_residue_mem_rawPiece hv)
    (he ▸ piece_residue_mem_rawPiece hw)
  refine ⟨hi, ?_⟩
  rcases mem_piece_cases hv with ⟨hr, hnd⟩ | ⟨_, hb⟩ <;>
    rcases mem_piece_cases hw with ⟨hr', hnd'⟩ | ⟨_, hb'⟩
  · rwa [residue_eq_self (rawPiece_mem_cube hr),
      residue_eq_self (rawPiece_mem_cube hr')] at he
  · rw [residue_eq_self (rawPiece_mem_cube hr)] at he
    exact False.elim (hnd (he ▸ bump_residue_mem_dents hb'))
  · rw [residue_eq_self (rawPiece_mem_cube hr')] at he
    exact False.elim (hnd' (he.symm ▸ bump_residue_mem_dents hb))
  · exact bump_residue_injective hb hb' he

theorem pieces_residue_surjective {m : ℕ} (hm : 0 < m) {r : Lattice 3}
    (hr : r ∈ cube (scale m)) :
    ∃ i, 1 ≤ i ∧ i ≤ m ∧ ∃ v ∈ piece m i, residue (scale m) v = r := by
  obtain ⟨i, hi, him, hri⟩ := (rawPiece_partition m hm r).mp hr
  refine ⟨i, hi, him, ?_⟩
  by_cases hd : r ∈ dents m
  · have hi1 := rawPiece_color_unique hri (dent_mem_rawPiece hd)
    obtain ⟨b, hb, he⟩ := dent_has_bump hd
    refine ⟨b, ?_, he⟩
    rw [piece_eq, if_pos hi1]
    exact List.mem_append_right _ hb
  · refine ⟨r, ?_, residue_eq_self hr⟩
    rw [piece_eq]
    split_ifs
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hri, by simpa using hd⟩)
    · exact hri

theorem mem_shell_iff (l : ℕ) (v : Lattice 3) : v ∈ shell l ↔
    ∃ (i : ℕ) (hi : i < (boundary l).length), ∃ q ∈ piece (boundary l).length (i + 1),
      v = (scale (boundary l).length : ℤ) • (boundary l)[i] + q := by
  simp only [shell, List.mem_flatMap]
  rw [List.exists_mem_zipIdx']
  simp only [List.mem_map]
  exact exists_congr fun i => exists_congr fun hi =>
    exists_congr fun q => and_congr_right fun _ => eq_comm

theorem boundary_length_pos (l : ℕ) (hl : 0 < l) : 0 < (boundary l).length := by
  have hz := zero_mem_boundary l hl
  cases he : boundary l with
  | nil => simp [he] at hz
  | cons x xs => simp

theorem shell_residue_surjective (l : ℕ) (hl : 0 < l) {r : Lattice 3}
    (hr : r ∈ cube (scale (boundary l).length)) :
    ∃ a ∈ shell l, residue (scale (boundary l).length) a = r := by
  obtain ⟨i, hi, him, v, hv, he⟩ :=
    pieces_residue_surjective (boundary_length_pos l hl) hr
  have hslot : i - 1 < (boundary l).length := by omega
  refine ⟨(scale (boundary l).length : ℤ) • (boundary l)[i - 1] + v, ?_, ?_⟩
  · apply (mem_shell_iff _ _).mpr
    exact ⟨i - 1, hslot, v, by simpa [show i - 1 + 1 = i by omega] using hv, rfl⟩
  · rwa [residue_scale_add]

theorem shell_residue_injective {l : ℕ} {a b : Lattice 3}
    (ha : a ∈ shell l) (hb : b ∈ shell l)
    (he : residue (scale (boundary l).length) a =
      residue (scale (boundary l).length) b) : a = b := by
  obtain ⟨i, hi, q, hq, rfl⟩ := (mem_shell_iff _ _).mp ha
  obtain ⟨j, hj, r, hr, rfl⟩ := (mem_shell_iff _ _).mp hb
  rw [residue_scale_add, residue_scale_add] at he
  obtain ⟨hij, hqr⟩ := pieces_residue_unique hq hr he
  have hij' : i = j := by omega
  subst j
  rw [hqr]

theorem sub_mem_grid_iff (s : ℕ) (x f : Lattice 3) :
    x - f ∈ gridCoset s 0 ↔ residue s x = residue s f := by
  classical
  simp only [gridCoset, Set.mem_setOf_eq, zero_add]
  constructor
  · rintro ⟨z, he⟩
    funext k
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-z k, ?_⟩
    have hk := congrFun he k
    change x k - f k = (s : ℤ) * z k at hk
    change f k - x k = (s : ℤ) * -z k
    rw [mul_neg, ← hk]
    omega
  · intro he
    have hdiv (k : Fin 3) : ∃ z : ℤ, x k - f k = (s : ℤ) * z :=
      Int.modEq_iff_dvd.mp (congrFun he k).symm
    choose z hz using hdiv
    exact ⟨z, by funext k; exact hz k⟩

/-- Kim's shell is a fundamental domain for its scale grid. -/
theorem shell_exactTiling (l : ℕ) (hl : 0 < l) :
    ExactTiling (gridCoset (scale (boundary l).length) 0) {a | a ∈ shell l} := by
  rw [exactTiling_iff]
  intro x
  obtain ⟨a, ha, he⟩ := shell_residue_surjective l hl
    (residue_mem_cube _ (by have := scale_pos (boundary l).length; omega) x)
  refine ⟨⟨a, ha⟩, (sub_mem_grid_iff _ _ _).mpr he.symm, ?_⟩
  intro b hb
  exact Subtype.ext (shell_residue_injective b.property ha
    (((sub_mem_grid_iff _ _ _).mp hb).symm.trans he.symm))

/-- Distinct grid translates of a shell cannot share a lattice point. -/
theorem shell_translates_disjoint (l : ℕ) {u v : Lattice 3} (hne : u ≠ v) :
    Disjoint {x | ∃ a ∈ shell l, x = (scale (boundary l).length : ℤ) • u + a}
      {x | ∃ b ∈ shell l, x = (scale (boundary l).length : ℤ) • v + b} := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, he⟩ ⟨b, hb, hf⟩
  have hab : a = b := shell_residue_injective ha hb (by
    have hh := congrArg (residue (scale (boundary l).length)) (he.symm.trans hf)
    simpa only [residue_scale_add] using hh)
  have huv : u = v := by
    have hh := add_right_cancel (hab ▸ he.symm.trans hf)
    funext k
    have hk := congrFun hh k
    change (scale (boundary l).length : ℤ) * u k =
      (scale (boundary l).length : ℤ) * v k at hk
    exact mul_left_cancel₀ (by have := scale_pos (boundary l).length; omega) hk
  exact hne huv

theorem cube_toFinset (s : ℕ) : (cube s).toFinset =
    Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (0 : ℤ) ((s : ℤ) - 1)) := by
  ext v
  simp only [List.mem_toFinset, mem_cube_iff, Fintype.mem_piFinset, Finset.mem_Icc]
  exact forall_congr' fun k => by omega

theorem cube_card (s : ℕ) : (cube s).toFinset.card = s ^ 3 := by
  rw [cube_toFinset, Fintype.card_piFinset_const, Int.card_Icc]
  simp

/-- The shell has exactly one point per grid residue, hence the stated volume. -/
theorem shell_card (l : ℕ) (hl : 0 < l) :
    (shell l).toFinset.card = (scale (boundary l).length) ^ 3 := by
  have hcard : (shell l).toFinset.card = (cube (scale (boundary l).length)).toFinset.card := by
    apply Finset.card_bij (fun a _ => residue (scale (boundary l).length) a)
    · intro a _
      exact List.mem_toFinset.mpr (residue_mem_cube _
        (by have := scale_pos (boundary l).length; omega) a)
    · intro a ha b hb he
      exact shell_residue_injective (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) he
    · intro r hr
      obtain ⟨a, ha, he⟩ := shell_residue_surjective l hl (List.mem_toFinset.mp hr)
      exact ⟨a, List.mem_toFinset.mpr ha, he⟩
  rw [hcard, cube_card]

end TranslationTiling.Kim
