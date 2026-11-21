import TranslationTiling.FiniteCompiler.Activation
import TranslationTiling.FiniteCompiler.BlockActivationInverse

namespace TranslationTiling.FiniteCompiler

open scoped BigOperators

/-- If a histogram is supported on one private output and passes the two-coordinate
shift test, its mass is a multiple of the shared modulus. -/
theorem shared_histogram_mass_dvd {a b D : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (Q : ZMod a × ZMod b → ℕ) (z : ZMod b)
    (hsupport : ∀ x y, y ≠ z → Q (x, y) = 0)
    (hmass : (∑ c, Q c) = D)
    (hcoverage : ∀ c : ZMod a × ZMod b,
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = D) : a ∣ D := by
  let : Fact (1 < b) := ⟨hb⟩
  have hz : z - 1 ≠ z := by
    intro he
    exact one_ne_zero (sub_eq_self.mp he)
  obtain ⟨u, v, huv⟩ := histogram_separable Q
    (mixedDifferenceZero_of_shift_sum ha hb Q hmass hcoverage)
  have hu (x : ZMod a) : u x = 0 := by
    have h := huv x (z - 1)
    rw [hsupport _ _ hz] at h
    omega
  refine ⟨∑ y, v y, ?_⟩
  rw [← hmass, histogram_mass_eq Q u v huv]
  simp [hu]

/-- In an activation test the shared output may vary with the low input. The
private output must still vary if the shared modulus does not divide the low
input size. -/
theorem shared_activation_private_nonconstant {a b : ℕ} [NeZero a] [NeZero b]
    {K : Type*} [Fintype K] (ha : 2 ≤ a) (hb : 2 ≤ b) (hdvd : ¬ a ∣ Fintype.card K)
    (shared : K → ZMod a) (privateOutput : K → ZMod b)
    (high : K × ShiftIndex a b → K)
    (hcover : Function.Bijective fun j : K × ShiftIndex a b =>
      ((shared j.1, privateOutput j.1) + shift a b j.2, high j)) :
    ¬ ∃ z, ∀ l, privateOutput l = z := by
  classical
  rintro ⟨z, hz⟩
  let Q : ZMod a × ZMod b → ℕ :=
    fun c => ∑ l, if (shared l, z) = c then 1 else 0
  have hs (x : ZMod a) (y : ZMod b) (hy : y ≠ z) : Q (x, y) = 0 := by
    unfold Q
    apply Finset.sum_eq_zero
    intro l _
    apply ite_eq_right
    exact fun h => hy (congrArg Prod.snd h).symm
  have hm : (∑ c, Q c) = Fintype.card K := by
    unfold Q
    rw [Finset.sum_comm]
    simp
  have hc (c : ZMod a × ZMod b) :
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = Fintype.card K := by
    have h := sum_firstCoordinate_of_bijective _ hcover c
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h
    simpa only [Q, eq_sub_iff_add_eq, hz] using h
  exact hdvd (shared_histogram_mass_dvd ha hb Q z hs hm hc)

/-- A nonconstant private output on a product of digit coordinates has an
active digit. The codomain need only be the observed private coordinate. -/
theorem exists_active_private_digit {K Y I : Type*} [AddGroup K] [Fintype I]
    {D : I → Type*} (e : K ≃ (∀ i, D i)) (U : I → AddSubgroup K)
    (hU : ∀ j x y, x-y ∈ U j ↔ ∀ i, i ≠ j → e x i = e y i)
    (g : K → Y) (h : ¬ ∃ c, ∀ x, g x = c) : ∃ j, DigitActive g (U j) := by
  classical
  by_contra! hnone
  have hu (z : ∀ i, D i) (j : I) (a : D j) :
      g (e.symm (Function.update z j a)) = g (e.symm z) := by
    apply (not_digitActive_iff g (U j)).mp (hnone j)
    apply (hU j _ _).mpr
    intro i hi
    simp [Function.update_of_ne hi]
  apply h
  refine ⟨g 0,fun x => ?_⟩
  simpa using eq_of_update_invariant (fun z => g (e.symm z)) hu (e x) (e 0)


/-- Translating the shared output of a bijective block test preserves coverage. -/
theorem shared_activation_add {a b : ℕ} {J K : Type*}
    (f : J → (ZMod a × ZMod b) × K) (hf : Function.Bijective f) (c : ZMod a) :
    Function.Bijective fun j => (((f j).1.1 + c, (f j).1.2), (f j).2) := by
  let e := (Equiv.addRight c).prodCongr (.refl (ZMod b))
  exact ((e.prodCongr (.refl K)).bijective.comp hf)

/-- A right-hand block supplies every value of the private coordinate. -/
theorem LabeledBlocks.privateOutput_surjective {K A B : Type*} {a b : ℕ}
    (D : LabeledBlocks K A B a b) (c : B) :
    Function.Surjective (fun x => (D.C x).2) := by
  intro y
  exact ⟨D.decode.symm (.inr (c,y)), by simp⟩

/-- Activation batches can leave any additional coordinates free. Coverage
depends on the base section and the outputs that occur in the batch equations. -/
theorem tiles_indexed_activation_iff {H X Y J : Type*} [AddCommGroup H]
    (F : Finset H) (point : X → H) (hpoint : Function.Injective point)
    (base : H → X) (target : H → Y)
    (source : X → J → X) (hsource : ∀ x, Function.Injective (source x))
    (testMap : X → J → Y)
    (htarget : ∀ x y, ∃ v, base v = x ∧ target v = y)
    (hmem : ∀ v x, v - point x ∈ F ↔
      ∃ j, source (base v) j = x ∧ testMap (base v) j = target v) :
    Tiles F (Set.range point) ↔ ∀ x, Function.Bijective (testMap x) := by
  rw [tiles_range_iff_unique_base point hpoint]
  simp_rw [hmem]
  constructor
  · intro h x
    apply (Function.bijective_iff_existsUnique _).mpr
    intro y
    obtain ⟨v,hv,hvy⟩ := htarget x y
    obtain ⟨w,⟨j,hj,hjy⟩,hu⟩ := h v
    rw [hv] at hj
    rw [hv,hvy] at hjy hu
    refine ⟨j,hjy,fun j' hj' => hsource x ?_⟩
    exact (hu (source x j') ⟨j',rfl,hj'⟩).trans hj.symm
  · intro h v
    obtain ⟨j,hj,hu⟩ := (h (base v)).existsUnique (target v)
    refine ⟨source (base v) j,⟨j,rfl,hj⟩,?_⟩
    rintro x ⟨j',rfl,hj'⟩
    rw [hu j' hj']


end TranslationTiling.FiniteCompiler
