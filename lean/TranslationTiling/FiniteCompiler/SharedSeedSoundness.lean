import TranslationTiling.FiniteCompiler.Activation

namespace TranslationTiling.FiniteCompiler

open scoped BigOperators

/-- The seed test cannot be bijective if its observed useful output
depends only on the residue of the spatial input. -/
theorem sharedSeed_not_bijective_of_inactive {a b : ℕ} [NeZero a] [NeZero b]
    {K S : Type*} [Fintype K] [Nonempty K] [Fintype S]
    (hs : Fintype.card S = 1225)
    (hab : (a = 2 ∧ b = 1229) ∨ (a = 3 ∧ b = 773))
    (q : S → ZMod a × ZMod b)
    (f : (K × ShiftIndex a b) × S → ((ZMod a × ZMod b) × K) × ZMod 1225)
    (hf : ∀ j, (f j).1.1 = q j.2 + shift a b j.1.2) :
    ¬ Function.Bijective f := by
  classical
  intro hbij
  let Q : ZMod a × ZMod b → ℕ := fun c => ∑ s, if q s = c then 1 else 0
  have hmass : (∑ c, Q c) = 1225 := by
    unfold Q
    rw [Finset.sum_comm]
    simp [hs]
  have hcov (c : ZMod a × ZMod b) :
      (∑ δ : ShiftIndex a b, Q (c-shift a b δ)) = 1225 := by
    have hcount := sum_firstFirstCoordinate_of_bijective f hbij c
    simp_rw [hf,← eq_sub_iff_add_eq] at hcount
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hcount
    change (∑ _ : K, ∑ δ : ShiftIndex a b, Q (c-shift a b δ)) = _ at hcount
    have he : Fintype.card K * (∑ δ : ShiftIndex a b, Q (c-shift a b δ)) =
        Fintype.card K * 1225 := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,ZMod.card] using hcount
    exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos he
  have ha : 2 ≤ a := by rcases hab with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
  have hb : 2 ≤ b := by rcases hab with ⟨_,rfl⟩|⟨_,rfl⟩ <;> decide
  obtain ⟨u,v,hsep⟩ := histogram_separable Q
    (mixedDifferenceZero_of_shift_sum ha hb Q hmass hcov)
  obtain ⟨U,V,h⟩ : ∃ U V : ℕ, 1225 = b*U+a*V :=
    ⟨_,_,hmass.symm.trans (histogram_mass_eq Q u v hsep)⟩
  rcases hab with ⟨ha,hb⟩|⟨ha,hb⟩ <;> rw [ha,hb] at h <;> omega

end TranslationTiling.FiniteCompiler
