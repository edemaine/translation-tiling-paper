import TranslationTiling.EuclideanMembership.RationalTests

/-! Every exact solution of a finite constraint system has a sufficiently
accurate representative in the explicitly enumerated rational grid. -/
namespace TranslationTiling.EuclideanMembership

noncomputable section

def roundedVector (x : Assignment) (M D : ℕ) : List ℤ :=
  (List.range M).map fun i => ⌊(x i : ℝ)*(D : ℝ)⌋

private theorem roundedVector_getD (x : Assignment) (M D i : ℕ) (hi : i < M) :
    (roundedVector x M D).getD i 0 = ⌊(x i : ℝ)*(D : ℝ)⌋ := by
  rw [List.getD_eq_getElem _ 0 (by simpa [roundedVector] using hi)]
  simp [roundedVector,hi]

private theorem roundedVector_mem (x : Assignment) (M D : ℕ) :
    ∀ a ∈ roundedVector x M D, a ∈ integerGrid D := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  apply (mem_integerGrid _ _).mpr
  have hl : ((-(D : ℤ) : ℤ) : ℝ) ≤ (x i : ℝ)*(D : ℝ) := by
    push_cast
    nlinarith [(x i).property.1, (show (0 : ℝ) ≤ D from Nat.cast_nonneg D)]
  have hu : (⌊(x i : ℝ)*(D : ℝ)⌋ : ℝ) ≤ (D : ℝ) :=
    (Int.floor_le _).trans (by nlinarith [(x i).property.2, (show (0 : ℝ) ≤ D from Nat.cast_nonneg D)])
  exact ⟨Int.le_floor.mpr hl,by exact_mod_cast hu⟩

private def truncated (x : Assignment) (M : ℕ) : ℕ → ℝ :=
  fun i => if i < M then (x i : ℝ) else 0

private theorem truncated_abs_le (x : Assignment) (M : ℕ) (i : ℕ) :
    |truncated x M i| ≤ 1 := by
  unfold truncated
  split_ifs with hi
  · exact abs_le.mpr (x i).property
  · norm_num

private theorem rounding_error (x : Assignment) (M D : ℕ) (hD : 0 < D) (i : ℕ) :
    |truncated x M i-rationalPoint D (roundedVector x M D) i| ≤ 1/(D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hi : i < M
  · simp only [truncated,if_pos hi,rationalPoint,roundedVector_getD x M D i hi]
    have hl := Int.floor_le ((x i : ℝ)*(D : ℝ))
    have hu := Int.lt_floor_add_one ((x i : ℝ)*(D : ℝ))
    have hcancel : ((⌊(x i : ℝ)*(D : ℝ)⌋ : ℝ)/(D : ℝ))*(D : ℝ) =
        (⌊(x i : ℝ)*(D : ℝ)⌋ : ℝ) := div_mul_cancel₀ _ hd.ne'
    have hnonneg : 0 ≤ (x i : ℝ)-(⌊(x i : ℝ)*(D : ℝ)⌋ : ℝ)/(D : ℝ) := by
      rw [sub_nonneg,div_le_iff₀ hd]
      exact hl
    rw [abs_of_nonneg hnonneg,le_div_iff₀ hd]
    nlinarith
  · simp only [truncated,if_neg hi,rationalPoint]
    rw [List.getD_eq_default _ 0 (by simpa [roundedVector] using Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero,zero_div,sub_self,abs_zero]
    positivity

private theorem weight_div_denominator (fs : List Formula) (k : ℕ) :
    ((totalWeight fs : ℝ)+1)/(denominator fs k : ℝ)=error k := by
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  have hw : (totalWeight fs : ℝ)+1 ≠ 0 := by positivity
  simp only [denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    TranslationTiling.EuclideanMembership.error]
  field_simp

/-- The finite search never rejects a genuinely satisfiable constraint family. -/
theorem finiteTest_of_solution (fs : List Formula) (k : ℕ) (x : Assignment)
    (hx : ∀ f ∈ fs, Holds f 0 (coordinates x)) : finiteTest fs k := by
  let D := denominator fs k
  let z := roundedVector x (arity fs) D
  have hD : 0 < D := denominator_pos fs k
  have hz : ∀ a ∈ z, a ∈ integerGrid D := roundedVector_mem x (arity fs) D
  refine ⟨z,(Compiler.Effective.mem_strings _ _ _).mpr ⟨by simp [z,roundedVector],hz⟩,?_⟩
  intro f hf
  apply (integerHolds_iff f k D hD z).mpr
  have ht : Holds f 0 (truncated x (arity fs)) :=
    (holds_congr hf 0 (coordinates x) (truncated x (arity fs))
      (fun i hi => by simp [coordinates,truncated,hi])).mp (hx f hf)
  obtain ⟨c,hc,hp⟩ := ht
  refine ⟨c,hc,fun p hp' => ?_⟩
  have he := evaluate_sub_le p (truncated x (arity fs)) (rationalPoint D z) (1/(D : ℝ))
    (truncated_abs_le x (arity fs)) (rationalPoint_abs_le hD hz)
    (rounding_error x (arity fs) D hD)
  have hw : (weight p : ℝ) ≤ (totalWeight fs : ℝ)+1 := by
    exact_mod_cast (weight_le_totalWeight hf hc hp').trans (Nat.le_succ _)
  calc
    evaluate p (rationalPoint D z) ≤ (weight p : ℝ)*(1/(D : ℝ)) := by
      have hl := (abs_le.mp he).1
      have hh := hp p hp'
      linarith
    _ = (weight p : ℝ)/(D : ℝ) := by ring
    _ ≤ ((totalWeight fs : ℝ)+1)/(D : ℝ) :=
      div_le_div_of_nonneg_right hw (Nat.cast_nonneg _)
    _ = error k := weight_div_denominator fs k

end
end TranslationTiling.EuclideanMembership
