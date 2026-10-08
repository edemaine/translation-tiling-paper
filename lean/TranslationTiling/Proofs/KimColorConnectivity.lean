import TranslationTiling.Proofs.KimGeometry
import TranslationTiling.Proofs.FacePaths

/-! Connectivity of the coarse color classes in Kim's partition. -/

set_option maxHeartbeats 800000

namespace TranslationTiling.Kim

def regionLo (m i : ℕ) (j : Fin 15) : Lattice 3 :=
  match j.val with
  | 0 => ![1, 1, (i : ℤ)]
  | 1 => ![0, (i : ℤ), 1]
  | 2 => ![0, (i : ℤ), 0]
  | 3 => ![(i : ℤ), 0, 1]
  | 4 => ![(i : ℤ), 0, (m : ℤ) + 1]
  | 5 => ![0, 0, 0]
  | 6 => ![0, 0, 0]
  | 7 => ![(m : ℤ) + 1, 0, 0]
  | 8 => ![0, 0, (m : ℤ) + 1]
  | 9 => ![(m : ℤ) + 1, 0, 0]
  | 10 => ![(m : ℤ) + 1, 0, (m : ℤ) + 1]
  | 11 => ![0, (m : ℤ) + 1, 0]
  | 12 => ![(m : ℤ) + 1, (m : ℤ) + 1, 0]
  | 13 => ![0, (m : ℤ) + 1, 0]
  | _ => ![0, (m : ℤ) + 1, (m : ℤ) + 1]

def regionHi (m i : ℕ) (j : Fin 15) : Lattice 3 :=
  match j.val with
  | 0 => ![(m : ℤ) + 1, (m : ℤ) + 1, (i : ℤ)]
  | 1 => ![0, (i : ℤ), (m : ℤ)]
  | 2 => ![(m : ℤ), (i : ℤ), 0]
  | 3 => ![(i : ℤ), 0, (m : ℤ)]
  | 4 => ![(i : ℤ), (m : ℤ), (m : ℤ) + 1]
  | 5 => ![(m : ℤ) + 1, 0, 0]
  | 6 => ![0, 0, (m : ℤ) + 1]
  | 7 => ![(m : ℤ) + 1, 0, (m : ℤ) + 1]
  | 8 => ![0, (m : ℤ) + 1, (m : ℤ) + 1]
  | 9 => ![(m : ℤ) + 1, (m : ℤ) + 1, 0]
  | 10 => ![(m : ℤ) + 1, (m : ℤ) + 1, (m : ℤ) + 1]
  | 11 => ![0, (m : ℤ) + 1, (m : ℤ) + 1]
  | 12 => ![(m : ℤ) + 1, (m : ℤ) + 1, 0]
  | 13 => ![(m : ℤ) + 1, (m : ℤ) + 1, 0]
  | _ => ![(m : ℤ) + 1, (m : ℤ) + 1, (m : ℤ) + 1]

def InRegion (m i : ℕ) (j : Fin 15) (q : Lattice 3) : Prop :=
  ∀ k, regionLo m i j k ≤ q k ∧ q k ≤ regionHi m i j k

theorem inRegion_iff (m i : ℕ) (j : Fin 15) (q : Lattice 3) :
    InRegion m i j q ↔
      (regionLo m i j 0 ≤ q 0 ∧ q 0 ≤ regionHi m i j 0) ∧
      (regionLo m i j 1 ≤ q 1 ∧ q 1 ≤ regionHi m i j 1) ∧
      (regionLo m i j 2 ≤ q 2 ∧ q 2 ≤ regionHi m i j 2) := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ k
    fin_cases k <;> simpa using (by assumption)

def ActiveRegion (i : ℕ) (j : Fin 15) : Prop := j.val < 5 ∨ i = 1

def regionParent (_m _i : ℕ) (j : Fin 15) : Fin 15 :=
  ![0,
    0,
    1,
    0,
    3,
    2,
    5,
    5,
    6,
    5,
    7,
    8,
    9,
    9,
    10] j

def regionExit (m i : ℕ) (j : Fin 15) : Lattice 3 :=
  ![![1, 1, (i : ℤ)],
    ![0, (i : ℤ), (i : ℤ)],
    ![0, (i : ℤ), 0],
    ![(i : ℤ), 0, (i : ℤ)],
    ![(i : ℤ), 0, (m : ℤ) + 1],
    ![0, 0, 0],
    ![0, 0, 0],
    ![(m : ℤ) + 1, 0, 0],
    ![0, 0, (m : ℤ) + 1],
    ![(m : ℤ) + 1, 0, 0],
    ![(m : ℤ) + 1, 0, (m : ℤ) + 1],
    ![0, (m : ℤ) + 1, (m : ℤ) + 1],
    ![(m : ℤ) + 1, (m : ℤ) + 1, 0],
    ![(m : ℤ) + 1, (m : ℤ) + 1, 0],
    ![(m : ℤ) + 1, (m : ℤ) + 1, (m : ℤ) + 1]] j

def regionEntry (m i : ℕ) (j : Fin 15) : Lattice 3 :=
  ![![1, 1, (i : ℤ)],
    ![1, (i : ℤ), (i : ℤ)],
    ![0, (i : ℤ), 1],
    ![(i : ℤ), 1, (i : ℤ)],
    ![(i : ℤ), 0, (m : ℤ)],
    ![0, 1, 0],
    ![0, 0, 0],
    ![(m : ℤ) + 1, 0, 0],
    ![0, 0, (m : ℤ) + 1],
    ![(m : ℤ) + 1, 0, 0],
    ![(m : ℤ) + 1, 0, (m : ℤ) + 1],
    ![0, (m : ℤ) + 1, (m : ℤ) + 1],
    ![(m : ℤ) + 1, (m : ℤ) + 1, 0],
    ![(m : ℤ) + 1, (m : ℤ) + 1, 0],
    ![(m : ℤ) + 1, (m : ℤ) + 1, (m : ℤ) + 1]] j

theorem region_colored (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (j : Fin 15) (hj : ActiveRegion i j) (q : Lattice 3) (hq : InRegion m i j q) :
    q ∈ cube (m + 2) ∧ color m q = i := by
  have h0 := hq 0; have h1 := hq 1; have h2 := hq 2
  fin_cases j <;> simp [regionLo, regionHi] at h0 h1 h2 <;>
    simp [ActiveRegion] at hj
  all_goals constructor
  all_goals try { apply (mem_cube_iff _ _).mpr; intro k; fin_cases k <;> simp <;> omega }
  all_goals unfold color; dsimp; split_ifs <;> omega

theorem colored_in_region (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (q : Lattice 3) (hq : q ∈ cube (m + 2)) (hc : color m q = i) :
    ∃ j : Fin 15, ActiveRegion i j ∧ InRegion m i j q := by
  have h0 := (mem_cube_iff _ _).mp hq 0
  have h1 := (mem_cube_iff _ _).mp hq 1
  have h2 := (mem_cube_iff _ _).mp hq 2
  unfold color at hc
  dsimp at hc
  split_ifs at hc with hf ht hs hh hc'
  · refine ⟨2, Or.inl (by decide), ?_⟩
    intro k
    fin_cases k <;> simp [regionLo, regionHi] <;> omega
  · refine ⟨4, Or.inl (by decide), ?_⟩
    intro k
    fin_cases k <;> simp [regionLo, regionHi] <;> omega
  · refine ⟨1, Or.inl (by decide), ?_⟩
    intro k
    fin_cases k <;> simp [regionLo, regionHi] <;> omega
  · refine ⟨3, Or.inl (by decide), ?_⟩
    intro k
    fin_cases k <;> simp [regionLo, regionHi] <;> omega
  · refine ⟨0, Or.inl (by decide), ?_⟩
    intro k
    fin_cases k <;> simp [regionLo, regionHi] <;> omega
  · subst i
    by_cases hx0 : q 0 = 0 <;> by_cases hxM : q 0 = (m : ℤ) + 1 <;>
      by_cases hy0 : q 1 = 0 <;> by_cases hyM : q 1 = (m : ℤ) + 1 <;>
      by_cases hz0 : q 2 = 0 <;> by_cases hzM : q 2 = (m : ℤ) + 1
    all_goals first
      | (refine ⟨5, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨6, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨7, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨8, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨9, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨10, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨11, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨12, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨13, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)
      | (refine ⟨14, Or.inr rfl, ?_⟩; intro k;
          fin_cases k <;> simp [regionLo, regionHi] <;> omega)

theorem region_link (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (j : Fin 15) (hj : ActiveRegion i j) (hne : j ≠ 0) :
    (regionParent m i j).val < j.val ∧ ActiveRegion i (regionParent m i j) ∧
    InRegion m i j (regionExit m i j) ∧
    InRegion m i (regionParent m i j) (regionEntry m i j) ∧
    (regionExit m i j = regionEntry m i j ∨
      FaceAdjacent (regionExit m i j) (regionEntry m i j)) := by
  fin_cases j <;> simp [ActiveRegion] at hj <;> try contradiction
  all_goals simp only [regionParent, regionExit, regionEntry, Matrix.cons_val,
    Fin.reduceFinMk, Fin.val_zero]
  all_goals refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  all_goals try { simp [ActiveRegion] <;> omega }
  all_goals try { intro k; fin_cases k <;> simp [regionLo, regionHi] <;> omega }
  · right
    refine ⟨0, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp
  · right
    refine ⟨2, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp
  · right
    refine ⟨1, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp
  · right
    refine ⟨2, Or.inr ?_⟩
    funext r
    fin_cases r <;> simp
  · right
    refine ⟨1, Or.inl ?_⟩
    funext r
    fin_cases r <;> simp

theorem color_path_to_core (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (q : Lattice 3) (hq : q ∈ cube (m + 2)) (hc : color m q = i) :
    FacePath (fun z => z ∈ cube (m + 2) ∧ color m z = i) q ![1, 1, (i : ℤ)] := by
  let P := fun z => z ∈ cube (m + 2) ∧ color m z = i
  have within (j : Fin 15) (hj : ActiveRegion i j) (x y : Lattice 3)
      (hx : InRegion m i j x) (hy : InRegion m i j y) : FacePath P x y :=
    FacePath.box3 P (regionLo m i j) (regionHi m i j) x y hx hy
      (fun z hz => region_colored m i hi him j hj z hz)
  have route (n : ℕ) : ∀ j : Fin 15, j.val = n → ActiveRegion i j →
      ∀ x, InRegion m i j x → FacePath P x ![1, 1, (i : ℤ)] := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hjn hj x hx
      by_cases hj0 : j = 0
      · subst j
        apply within 0 hj x _ hx
        intro k; fin_cases k <;> simp [regionLo, regionHi]
      · obtain ⟨hp, ha, he, hn, hlink⟩ := region_link m i hi him j hj hj0
        have first := within j hj x _ hx he
        have last := ih (regionParent m i j).val (by omega) _ rfl ha _ hn
        rcases hlink with hlink | hlink
        · rw [hlink] at first
          exact first.trans last
        · exact (first.trans (FacePath.step
            (region_colored m i hi him j hj _ he)
            (region_colored m i hi him _ ha _ hn) hlink)).trans last
  obtain ⟨j, hj, hr⟩ := colored_in_region m i hi him q hq hc
  exact route j.val j rfl hj q hr

theorem color_connected (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (x y : Lattice 3) (hx : x ∈ cube (m + 2)) (hy : y ∈ cube (m + 2))
    (hxc : color m x = i) (hyc : color m y = i) :
    FacePath (fun z => z ∈ cube (m + 2) ∧ color m z = i) x y :=
  (color_path_to_core m i hi him x hx hxc).trans
    (FacePath.reverse (color_path_to_core m i hi him y hy hyc))

end TranslationTiling.Kim
