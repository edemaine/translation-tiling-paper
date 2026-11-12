import TranslationTiling.EuclideanMembership.CompactConstraints

/-! Explicit moduli of continuity for the integer polynomials in a compact
constraint system. The moduli use only integer arithmetic. -/
namespace TranslationTiling.EuclideanMembership

/-- An integer Lipschitz bound on the unit box, in the coordinatewise metric. -/
def weight (p : Polynomial) : ℕ :=
  (p.map fun t => t.1.natAbs * t.2.length).sum

/-- All polynomials in a finite family of formulas. -/
def polynomials (fs : List Formula) : List Polynomial := fs.flatten.flatten

def variableIndices (fs : List Formula) : List ℕ :=
  (polynomials fs).flatMap fun p => p.flatMap fun t => t.2

def arity (fs : List Formula) : ℕ :=
  (variableIndices fs).foldr (fun i n => max (i + 1) n) 0

def totalWeight (fs : List Formula) : ℕ := ((polynomials fs).map weight).sum

private theorem monomial_abs_le (v : List ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : |monomial v x| ≤ 1 := by
  induction v with
  | nil => simp [monomial]
  | cons i v ih =>
    change |x i * monomial v x| ≤ 1
    rw [abs_mul]
    exact mul_le_one₀ (hx i) (abs_nonneg _) ih

/-- Products of `m` coordinates change by at most `m * e` on the unit box. -/
theorem monomial_sub_le (v : List ℕ) (x y : ℕ → ℝ) (e : ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (he : ∀ i, |x i-y i| ≤ e) :
    |monomial v x-monomial v y| ≤ (v.length : ℝ)*e := by
  induction v with
  | nil => simp [monomial]
  | cons i v ih =>
    have he0 : 0 ≤ e := (abs_nonneg _).trans (he i)
    change |x i*monomial v x-y i*monomial v y| ≤ ((v.length+1 : ℕ) : ℝ)*e
    have hid : x i*monomial v x-y i*monomial v y =
        (x i-y i)*monomial v x+y i*(monomial v x-monomial v y) := by ring
    rw [hid]
    calc
      _ ≤ |x i-y i| *|monomial v x|+|y i| *|monomial v x-monomial v y| := by
        simpa only [abs_mul] using abs_add_le ((x i-y i)*monomial v x)
          (y i*(monomial v x-monomial v y))
      _ ≤ e*1+1*((v.length : ℝ)*e) := add_le_add
        (mul_le_mul (he i) (monomial_abs_le v x hx) (abs_nonneg _) he0)
        (mul_le_mul (hy i) ih (abs_nonneg _) (by norm_num))
      _ = _ := by push_cast; ring

/-- The modulus is uniform over every pair of assignments in the unit box. -/
theorem evaluate_sub_le (p : Polynomial) (x y : ℕ → ℝ) (e : ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (he : ∀ i, |x i-y i| ≤ e) :
    |evaluate p x-evaluate p y| ≤ (weight p : ℝ)*e := by
  induction p with
  | nil => simp [evaluate,weight]
  | cons t p ih =>
    have ht := monomial_sub_le t.2 x y e hx hy he
    have ha : |(t.1 : ℝ)| = (t.1.natAbs : ℝ) := by simp
    have hid : evaluate (t::p) x-evaluate (t::p) y =
        (t.1 : ℝ)*(monomial t.2 x-monomial t.2 y)+(evaluate p x-evaluate p y) := by
      simp only [evaluate,List.map_cons,List.sum_cons]
      ring
    rw [hid]
    calc
      _ ≤ |(t.1 : ℝ)| *|monomial t.2 x-monomial t.2 y|+|evaluate p x-evaluate p y| := by
        simpa only [abs_mul] using abs_add_le
          ((t.1 : ℝ)*(monomial t.2 x-monomial t.2 y)) (evaluate p x-evaluate p y)
      _ ≤ (t.1.natAbs : ℝ)*((t.2.length : ℝ)*e)+(weight p : ℝ)*e := by
        rw [ha]
        exact add_le_add (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)) ih
      _ = _ := by simp only [weight,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul]; ring

private theorem le_variable_fold {v : List ℕ} {i : ℕ} (hi : i ∈ v) :
    i+1 ≤ v.foldr (fun j n => max (j+1) n) 0 := by
  induction v with
  | nil => simp at hi
  | cons j v ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact (ih hi).trans (le_max_right _ _)

theorem variable_lt_arity {fs : List Formula} {f : Formula} {c : List Polynomial}
    {p : Polynomial} {t : ℤ × List ℕ} {i : ℕ}
    (hf : f ∈ fs) (hc : c ∈ f) (hp : p ∈ c) (ht : t ∈ p) (hi : i ∈ t.2) :
    i < arity fs := by
  apply Nat.lt_of_succ_le
  apply le_variable_fold
  have hp' : p ∈ polynomials fs := List.mem_flatten.mpr
    ⟨c,List.mem_flatten.mpr ⟨f,hf,hc⟩,hp⟩
  exact List.mem_flatMap.mpr ⟨p,hp',List.mem_flatMap.mpr ⟨t,ht,hi⟩⟩

theorem weight_le_totalWeight {fs : List Formula} {f : Formula} {c : List Polynomial}
    {p : Polynomial} (hf : f ∈ fs) (hc : c ∈ f) (hp : p ∈ c) :
    weight p ≤ totalWeight fs := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  exact List.mem_map.mpr ⟨p,List.mem_flatten.mpr
    ⟨c,List.mem_flatten.mpr ⟨f,hf,hc⟩,hp⟩,rfl⟩

theorem evaluate_congr (p : Polynomial) (x y : ℕ → ℝ)
    (h : ∀ t ∈ p, ∀ i ∈ t.2, x i=y i) : evaluate p x=evaluate p y := by
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro t ht
  congr 1
  unfold monomial
  congr 1
  exact List.map_congr_left (h t ht)

theorem holds_congr {fs : List Formula} {f : Formula} (hf : f ∈ fs)
    (e : ℝ) (x y : ℕ → ℝ) (h : ∀ i < arity fs, x i=y i) :
    Holds f e x ↔ Holds f e y := by
  have he (c : List Polynomial) (hc : c ∈ f) (p : Polynomial) (hp : p ∈ c) :
      evaluate p x=evaluate p y := evaluate_congr p x y fun t ht i hi =>
    h i (variable_lt_arity hf hc hp ht hi)
  constructor <;> rintro ⟨c,hc,hp⟩ <;> refine ⟨c,hc,fun p hp' => ?_⟩
  · rw [← he c hc p hp']; exact hp p hp'
  · rw [he c hc p hp']; exact hp p hp'

end TranslationTiling.EuclideanMembership
