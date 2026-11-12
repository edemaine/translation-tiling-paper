import TranslationTiling.EuclideanMembership.IntegerTests
import Mathlib.Data.List.GetD

/-! Correctness of the finite integer tests as tests of real polynomial
inequalities on finite rational grids. -/
namespace TranslationTiling.EuclideanMembership

noncomputable section

/-- Interpret an integer vector as a rational point of the compact box. -/
def rationalPoint (D : ℕ) (z : List ℤ) : ℕ → ℝ := fun i => (z.getD i 0 : ℝ)/(D : ℝ)

theorem denominator_pos (fs : List Formula) (k : ℕ) : 0 < denominator fs k := by
  unfold denominator
  positivity

theorem mem_integerGrid (D : ℕ) (a : ℤ) :
    a ∈ integerGrid D ↔ -(D : ℤ) ≤ a ∧ a ≤ D := by
  unfold integerGrid
  simp only [List.mem_map,List.mem_range]
  constructor
  · rintro ⟨n,hn,rfl⟩
    constructor <;> omega
  · rintro ⟨hl,hu⟩
    refine ⟨(a+D).toNat,?_,?_⟩
    · omega
    · omega

private theorem length_le_degree {p : Polynomial} {t : ℤ × List ℕ} (ht : t ∈ p) :
    t.2.length ≤ degree p := by
  induction p with
  | nil => simp at ht
  | cons a p ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

private theorem monomial_rational (v : List ℕ) (D : ℕ) (z : List ℤ) :
    monomial v (rationalPoint D z) =
      ((v.map fun i => (z.getD i 0 : ℝ)).prod)/(D : ℝ)^v.length := by
  induction v with
  | nil => simp [monomial]
  | cons i v ih =>
    change (z.getD i 0 : ℝ)/(D : ℝ)*monomial v (rationalPoint D z) = _
    rw [ih]
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    ring

private theorem scaledMonomial_cast (D N : ℕ) (hD : 0 < D) (z : List ℤ)
    (t : ℤ × List ℕ) (ht : t.2.length ≤ N) :
    (scaledMonomial D N z t : ℝ) =
      (D : ℝ)^N*((t.1 : ℝ)*monomial t.2 (rationalPoint D z)) := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hp : (D : ℝ)^N=(D : ℝ)^t.2.length*(D : ℝ)^(N-t.2.length) := by
    rw [← pow_add,Nat.add_sub_of_le ht]
  rw [monomial_rational]
  simp only [scaledMonomial,Int.cast_mul,Int.cast_natCast,Nat.cast_pow,
    Int.cast_list_prod,Int.cast_pow,List.map_map,Function.comp_def]
  rw [hp]
  field_simp
  <;> ring

private theorem scaledEvaluate_cast_aux (D N : ℕ) (hD : 0 < D) (z : List ℤ)
    (p : Polynomial) (hp : ∀ t ∈ p, t.2.length ≤ N) :
    (scaledEvaluate D N z p : ℝ) = (D : ℝ)^N*evaluate p (rationalPoint D z) := by
  induction p with
  | nil => simp [scaledEvaluate,evaluate]
  | cons t p ih =>
    change ((scaledMonomial D N z t + scaledEvaluate D N z p : ℤ) : ℝ) = _
    rw [Int.cast_add,scaledMonomial_cast D N hD z t (hp t (by simp)),
      ih (fun s hs => hp s (by simp [hs]))]
    simp only [evaluate,List.map_cons,List.sum_cons]
    ring

theorem scaledEvaluate_cast (D : ℕ) (hD : 0 < D) (z : List ℤ) (p : Polynomial) :
    (scaledEvaluate D (degree p) z p : ℝ) =
      (D : ℝ)^degree p*evaluate p (rationalPoint D z) :=
  scaledEvaluate_cast_aux D (degree p) hD z p (fun _ ht => length_le_degree ht)

theorem integerHolds_iff (f : Formula) (k D : ℕ) (hD : 0 < D) (z : List ℤ) :
    integerHolds f k D z ↔ Holds f (error k) (rationalPoint D z) := by
  have he (p : Polynomial) :
      scaledEvaluate D (degree p) z p*(k+1 : ℕ) ≤ (D^degree p : ℕ) ↔
        evaluate p (rationalPoint D z) ≤ error k := by
    have hpow : 0 < (D : ℝ)^degree p := pow_pos (by exact_mod_cast hD) _
    have hk : 0 < (k : ℝ)+1 := by positivity
    rw [← Int.cast_le (R := ℝ)]
    simp only [Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_pow,Int.cast_natCast,
      Nat.cast_add,Nat.cast_one,Nat.cast_pow,
      scaledEvaluate_cast D hD z p]
    rw [mul_assoc]
    exact (mul_le_iff_le_one_right hpow).trans
      (show evaluate p (rationalPoint D z)*((k : ℝ)+1) ≤ 1 ↔
        evaluate p (rationalPoint D z) ≤ 1/((k : ℝ)+1) from (le_div_iff₀ hk).symm)
  unfold integerHolds Holds
  simp only [he]

private theorem getD_grid {D : ℕ} {z : List ℤ}
    (hz : ∀ a ∈ z, a ∈ integerGrid D) (i : ℕ) :
    -(D : ℤ) ≤ z.getD i 0 ∧ z.getD i 0 ≤ D := by
  by_cases hi : i < z.length
  · rw [List.getD_eq_getElem z 0 hi]
    exact (mem_integerGrid _ _).mp (hz z[i] (List.getElem_mem hi))
  · rw [List.getD_eq_default z 0 (by omega)]
    constructor <;> omega

theorem rationalPoint_abs_le {D : ℕ} (hD : 0 < D) {z : List ℤ}
    (hz : ∀ a ∈ z, a ∈ integerGrid D) (i : ℕ) : |rationalPoint D z i| ≤ 1 := by
  obtain ⟨hl,hu⟩ := getD_grid hz i
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  unfold rationalPoint
  rw [abs_div,abs_of_pos hd,div_le_one hd]
  exact abs_le.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩

/-- A successful integer test gives an approximate real solution. -/
theorem finiteTest_solution {fs : List Formula} {k : ℕ} (h : finiteTest fs k) :
    ∃ x : Assignment, ∀ f ∈ fs, Holds f (error k) (coordinates x) := by
  obtain ⟨z,hz,hf⟩ := h
  have hb := (Compiler.Effective.mem_strings _ _ _).mp hz
  let x : Assignment := fun i => ⟨rationalPoint (denominator fs k) z i,
    abs_le.mp (rationalPoint_abs_le (denominator_pos fs k) hb.2 i)⟩
  refine ⟨x,fun f hmem => ?_⟩
  exact (integerHolds_iff f k _ (denominator_pos fs k) z).mp (hf f hmem)

end
end TranslationTiling.EuclideanMembership
