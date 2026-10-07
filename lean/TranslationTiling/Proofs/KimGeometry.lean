import TranslationTiling.External.Kim
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Elementary geometry of Kim's interlocking partition. -/

namespace TranslationTiling.Kim

theorem mem_cube_iff (l : ℕ) (x : Lattice 3) :
    x ∈ cube l ↔ ∀ i, 0 ≤ x i ∧ x i < (l : ℤ) := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, c, hc, he⟩ :=
      (by simpa only [cube, List.mem_flatMap, List.mem_map] using hx :
        ∃ a ∈ List.range l, ∃ b ∈ List.range l, ∃ c ∈ List.range l,
          ![(a : ℤ), (b : ℤ), (c : ℤ)] = x)
    subst x
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    have hc' := List.mem_range.mp hc
    intro i
    fin_cases i <;> simp <;> omega
  · intro hx
    have he : ![((x 0).toNat : ℤ), ((x 1).toNat : ℤ), ((x 2).toNat : ℤ)] = x := by
      funext i
      fin_cases i <;>
        exact Int.toNat_of_nonneg (hx _).1
    simp only [cube, List.mem_flatMap, List.mem_map]
    refine ⟨(x 0).toNat, List.mem_range.mpr ?_, (x 1).toNat,
      List.mem_range.mpr ?_, (x 2).toNat, List.mem_range.mpr ?_, he⟩
    · exact (Int.toNat_lt (hx 0).1).mpr (hx 0).2
    · exact (Int.toNat_lt (hx 1).1).mpr (hx 1).2
    · exact (Int.toNat_lt (hx 2).1).mpr (hx 2).2


theorem color_bounds (m : ℕ) (hm : 0 < m) (v : Lattice 3) :
    1 ≤ color m v ∧ color m v ≤ m := by
  unfold color
  dsimp
  split_ifs <;> omega

theorem color_core (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    color m ![1, 1, (i : ℤ)] = i := by
  simp only [color, Matrix.cons_val]
  simp only [show (i : ℤ) ≠ 0 by omega, and_false, if_false,
    show ¬ (i : ℤ) = (m : ℤ) + 1 by omega, one_ne_zero,
    false_and]
  rw [if_pos (by omega)]
  exact Int.toNat_natCast i

theorem piece_nonempty (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    piece m i ≠ [] := by
  have hq : ![1, 1, (i : ℤ)] ∈ cube (m + 2) := by
    apply (mem_cube_iff _ _).mpr
    intro j
    fin_cases j <;> simp <;> omega
  have hc : (![1, 1, 1] : Lattice 3) ∈ cube 3 := by decide
  have hr : 3 • ![1, 1, (i : ℤ)] + ![1, 1, 1] ∈
      ((cube (m + 2)).filter fun v => color m v == i).flatMap
        (fun q => (cube 3).map fun c => 3 • q + c) := by
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq]
    exact ⟨_, ⟨hq, color_core m i hi him⟩, _, hc, rfl⟩
  have hnd : 3 • ![1, 1, (i : ℤ)] + ![1, 1, 1] ∉ dents m := by
    simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · have := congrFun h 1
      norm_num at this
    · have := congrFun h 0
      norm_num at this
    · have := congrFun h 0
      norm_num at this
  have hp : 3 • ![1, 1, (i : ℤ)] + ![1, 1, 1] ∈ piece m i := by
    unfold piece
    split_ifs
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hr, by simpa using hnd⟩)
    · exact hr
  intro he
  simp [he] at hp

theorem cube_blocks (l : ℕ) (v : Lattice 3) :
    v ∈ cube (3 * l) ↔ ∃ q ∈ cube l, ∃ c ∈ cube 3, v = 3 • q + c := by
  constructor
  · intro hv
    have hv' := (mem_cube_iff _ _).mp hv
    refine ⟨(fun j => v j / 3), (mem_cube_iff _ _).mpr ?_,
      (fun j => v j % 3), (mem_cube_iff _ _).mpr ?_, ?_⟩
    · intro j
      have := hv' j
      push_cast at this
      omega
    · intro j
      omega
    · funext j
      change v j = 3 * (v j / 3) + v j % 3
      omega
  · rintro ⟨q, hq, c, hc, rfl⟩
    apply (mem_cube_iff _ _).mpr
    intro j
    have hq' := (mem_cube_iff _ _).mp hq j
    have hc' := (mem_cube_iff _ _).mp hc j
    change 0 ≤ 3 * q j + c j ∧ 3 * q j + c j < (3 * l : ℕ)
    push_cast
    omega
theorem blocks_unique {q r c d : Lattice 3} (hc : c ∈ cube 3) (hd : d ∈ cube 3)
    (he : 3 • q + c = 3 • r + d) : q = r ∧ c = d := by
  have hq : q = r := by
    funext j
    have hc' := (mem_cube_iff _ _).mp hc j
    have hd' := (mem_cube_iff _ _).mp hd j
    have he' := congrFun he j
    change 3 * q j + c j = 3 * r j + d j at he'
    omega
  refine ⟨hq, ?_⟩
  rw [hq] at he
  exact add_left_cancel he

def rawPiece (m i : ℕ) : Tile 3 :=
   ((cube (m + 2)).filter fun q => color m q == i).flatMap
     fun q => (cube 3).map fun c => 3 • q + c
theorem mem_rawPiece (m i : ℕ) (v : Lattice 3) :
    v ∈ rawPiece m i ↔ ∃ q ∈ cube (m + 2), color m q = i ∧
      ∃ c ∈ cube 3, v = 3 • q + c := by
  simp only [rawPiece, List.mem_flatMap, List.mem_filter, beq_iff_eq, List.mem_map]
  constructor
  · rintro ⟨q, ⟨hq, hi⟩, c, hc, he⟩
    exact ⟨q, hq, hi, c, hc, he.symm⟩
  · rintro ⟨q, hq, hi, c, hc, he⟩
    exact ⟨q, ⟨hq, hi⟩, c, hc, he.symm⟩
theorem rawPiece_partition (m : ℕ) (hm : 0 < m) (v : Lattice 3) :
    v ∈ cube (scale m) ↔ ∃ i, 1 ≤ i ∧ i ≤ m ∧ v ∈ rawPiece m i := by
  have hs : scale m = 3 * (m + 2) := by unfold scale; omega
  rw [hs, cube_blocks]
  constructor
  · rintro ⟨q, hq, c, hc, he⟩
    exact ⟨color m q, (color_bounds m hm q).1, (color_bounds m hm q).2,
      (mem_rawPiece m _ v).mpr ⟨q, hq, rfl, c, hc, he⟩⟩
  · rintro ⟨i, _, _, hi⟩
    obtain ⟨q, hq, _, c, hc, he⟩ := (mem_rawPiece m i v).mp hi
    exact ⟨q, hq, c, hc, he⟩
theorem rawPieces_disjoint (m i j : ℕ) (hne : i ≠ j) :
    Disjoint {v | v ∈ rawPiece m i} {v | v ∈ rawPiece m j} := by
  apply Set.disjoint_left.mpr
  intro v hi hj
  obtain ⟨q, _, hqi, c, hc, he⟩ := (mem_rawPiece m i v).mp hi
  obtain ⟨r, _, hrj, d, hd, hf⟩ := (mem_rawPiece m j v).mp hj
  obtain ⟨hqr, _⟩ := blocks_unique hc hd (he.symm.trans hf)
  exact hne (hqi.symm.trans (hqr ▸ hrj))
theorem piece_eq (m i : ℕ) : piece m i =
    if i = 1 then ((rawPiece m i).filter fun v => decide (v ∉ dents m)) ++ bumps
      else rawPiece m i := rfl

theorem color_side (m i j : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m) :
    color m ![0, (i : ℤ), (j : ℤ)] = i := by
  unfold color
  dsimp
  split_ifs <;> omega
theorem color_inside (m x y z : ℕ) (hx : 1 ≤ x) (hxm : x ≤ m + 1)
    (hy : 1 ≤ y) (hym : y ≤ m + 1) (hz : 1 ≤ z) (hzm : z ≤ m) :
    color m ![(x : ℤ), (y : ℤ), (z : ℤ)] = z := by
  simp only [color, Matrix.cons_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  exact Int.toNat_natCast z
theorem mem_piece_of_block {m i : ℕ} {q c : Lattice 3}
    (hq : q ∈ cube (m + 2)) (hi : color m q = i) (hc : c ∈ cube 3)
    (hnd : 3 • q + c ∉ dents m) : 3 • q + c ∈ piece m i := by
  have hr : 3 • q + c ∈ ((cube (m + 2)).filter fun v => color m v == i).flatMap
      (fun q => (cube 3).map fun c => 3 • q + c) := by
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq]
    exact ⟨q, ⟨hq, hi⟩, c, hc, rfl⟩
  unfold piece
  split_ifs
  · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hr, by simpa using hnd⟩)
  · exact hr
theorem pieces_adjacent (m i j : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m) :
    ∃ a ∈ piece m i, ∃ b ∈ piece m j, FaceAdjacent a b := by
  let a : Lattice 3 := 3 • ![0, (i : ℤ), (j : ℤ)] + ![2, 1, 1]
  let b : Lattice 3 := 3 • ![1, (i : ℤ), (j : ℤ)] + ![0, 1, 1]
  have hqa : ![0, (i : ℤ), (j : ℤ)] ∈ cube (m + 2) := by
    apply (mem_cube_iff _ _).mpr
    intro k
    fin_cases k <;> simp <;> omega
  have hqb : ![1, (i : ℤ), (j : ℤ)] ∈ cube (m + 2) := by
    apply (mem_cube_iff _ _).mpr
    intro k
    fin_cases k <;> simp <;> omega
  have hnda : a ∉ dents m := by
    simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · have := congrFun h 1
      change 3 * (i : ℤ) + 1 = 1 at this
      omega
    · have := congrFun h 0
      change 2 = 1 at this
      omega
    · have := congrFun h 0
      change 2 = 1 at this
      omega
  have hndb : b ∉ dents m := by
    simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · have := congrFun h 1
      change 3 * (i : ℤ) + 1 = 1 at this
      omega
    · have := congrFun h 0
      change 3 = 1 at this
      omega
    · have := congrFun h 0
      change 3 = 1 at this
      omega
  refine ⟨a, mem_piece_of_block hqa (color_side m i j hi him hj hjm)
    (by decide) hnda, b, mem_piece_of_block hqb
    (color_inside m 1 i j (by omega) (by omega) hi (by omega) hj hjm)
    (by decide) hndb, ?_⟩
  unfold FaceAdjacent
  refine ⟨0, Or.inl ?_⟩
  funext k
  fin_cases k <;> simp [a, b]

theorem color_floor (m x y : ℕ) (hx : 1 ≤ x) (hxm : x ≤ m)
    (hy : 1 ≤ y) (hym : y ≤ m) : color m ![(x : ℤ), (y : ℤ), 0] = y := by
  unfold color
  dsimp
  split_ifs <;> omega
theorem color_ceiling (m x y : ℕ) (hx : 1 ≤ x) (hxm : x ≤ m)
    (hy : 1 ≤ y) (hym : y ≤ m) : color m ![(x : ℤ), (y : ℤ), (m : ℤ) + 1] = x := by
  unfold color
  dsimp
  split_ifs <;> omega
theorem color_front (m x z : ℕ) (hx : 1 ≤ x) (hxm : x ≤ m)
    (hz : 1 ≤ z) (hzm : z ≤ m) : color m ![(x : ℤ), 0, (z : ℤ)] = x := by
  unfold color
  dsimp
  split_ifs <;> omega
theorem not_mem_dents_of_ne_one {m : ℕ} {v : Lattice 3}
    (hv : ∀ k, v k ≠ 1) : v ∉ dents m := by
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h)
  · exact hv 1 (congrFun h 1)
  · exact hv 0 (congrFun h 0)
  · exact hv 0 (congrFun h 0)
theorem pieces_external_adjacent (m i j : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m) (k : Fin 3) :
    ∃ a ∈ piece m i, ∃ b ∈ piece m j,
      FaceAdjacent a ((scale m : ℤ) • Pi.single k 1 + b) := by
  fin_cases k
  · let a : Lattice 3 := 3 • ![(m : ℤ) + 1, (j : ℤ), (i : ℤ)] + ![2, 1, 1]
    let b : Lattice 3 := 3 • ![0, (j : ℤ), (i : ℤ)] + ![0, 1, 1]
    have ha : a ∈ piece m i := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · simpa using color_inside m (m + 1) j i (by omega) (by omega) hj (by omega) hi him
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [a, scale] <;> omega
    have hb : b ∈ piece m j := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · exact color_side m j i hj hjm hi him
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [b, scale] <;> omega
    refine ⟨a, ha, b, hb, 0, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp [a, b, scale] <;> omega
  · let a : Lattice 3 := 3 • ![(j : ℤ), (m : ℤ) + 1, (i : ℤ)] + ![1, 2, 1]
    let b : Lattice 3 := 3 • ![(j : ℤ), 0, (i : ℤ)] + ![1, 0, 1]
    have ha : a ∈ piece m i := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · simpa using color_inside m j (m + 1) i hj (by omega) (by omega) (by omega) hi him
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [a, scale] <;> omega
    have hb : b ∈ piece m j := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · exact color_front m j i hj hjm hi him
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [b, scale] <;> omega
    refine ⟨a, ha, b, hb, 1, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp [a, b, scale] <;> omega
  · let a : Lattice 3 := 3 • ![(i : ℤ), (j : ℤ), (m : ℤ) + 1] + ![1, 1, 2]
    let b : Lattice 3 := 3 • ![(i : ℤ), (j : ℤ), 0] + ![1, 1, 0]
    have ha : a ∈ piece m i := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · simpa using color_ceiling m i j hi him hj hjm
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [a, scale] <;> omega
    have hb : b ∈ piece m j := by
      apply mem_piece_of_block
      · apply (mem_cube_iff _ _).mpr
        intro r
        fin_cases r <;> simp <;> omega
      · exact color_floor m i j hi him hj hjm
      · decide
      · apply not_mem_dents_of_ne_one
        intro r
        fin_cases r <;> norm_num [b, scale] <;> omega
    refine ⟨a, ha, b, hb, 2, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp [a, b, scale] <;> omega

theorem zero_mem_boundary (l : ℕ) (hl : 0 < l) : (0 : Lattice 3) ∈ boundary l := by
  apply List.mem_filter.mpr
  refine ⟨(mem_cube_iff l 0).mpr ?_, ?_⟩
  · intro k
    simp only [Pi.zero_apply]
    omega
  · simpa using (show ∃ k : Fin 3, (0 : Lattice 3) k = 0 ∨
        (0 : Lattice 3) k = (l : ℤ) - 1 from ⟨0, Or.inl rfl⟩)
theorem shell_nonempty (l : ℕ) (hl : 0 < l) : shell l ≠ [] := by
  have hz := zero_mem_boundary l hl
  cases he : boundary l with
  | nil => simp [he] at hz
  | cons x xs =>
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil (piece (xs.length + 1) 1)
      (piece_nonempty _ _ (by omega) (by omega))
    have hidx : (x, 0) ∈ (x :: xs).zipIdx := by simp
    have hmem : (scale (xs.length + 1) : ℤ) • x + p ∈ shell l := by
      simp only [shell, he, List.length_cons, List.mem_flatMap, List.mem_map]
      exact ⟨(x, 0), hidx, p, hp, rfl⟩
    intro hn
    simp [hn] at hmem

end TranslationTiling.Kim
