import TranslationTiling.FiniteCompiler.Effective.SharedModelActivation

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical

noncomputable section

local instance sharedModelDependenceFrame : SeedFrame := compactSeedFrame
set_option maxHeartbeats 3000000

variable {k : ℕ} (pick : SharedPicker k)

theorem sharedSeedPair_eq (t : Fin 2) {v w : SharedBase k}
    (hx : SharedSeed.residue seedModel.system v.1 = SharedSeed.residue seedModel.system w.1)
    (hl : v.2 (sharedSeedRow k t) = w.2 (sharedSeedRow k t)) :
    sharedSeedPair k t v = sharedSeedPair k t w := by
  unfold sharedSeedPair
  rw [hx]
  change (seedPairToModel k t).symm (seedUseful modelE t _
       (seedLowToModel k t (v.2 (sharedSeedRow k t)))) =
    (seedPairToModel k t).symm (seedUseful modelE t _
       (seedLowToModel k t (w.2 (sharedSeedRow k t))))
  rw [hl]

theorem sharedModel_dependence : HasSharedDependence k (tailSlopes k) (sharedModel pick) := by
  constructor
  · intro i j hne v
    have h₁ : (v-lowStep (sharedLayout k) j).1 = v.1 := by simp [lowStep]
    have h₂ : (v-lowStep (sharedLayout k) j).2 i = v.2 i := by
      change v.2 i - Function.update (0 : ∀ i : SharedRow k, RowLow i) j 1 i = v.2 i
      simp [Function.update_of_ne hne.symm]
    by_cases hi : i.val < (sharedRows k).length-2
    · rw [sharedModel_pair pick i hi,sharedModel_pair pick i hi]
      exact sharedOrdinaryPair_eq pick i hi (congrArg (sharedLineValue k i) h₁) h₂
    · obtain ⟨t,ht⟩ : ∃ t : Fin 2, sharedSeedRow k t = i := by
        refine ⟨⟨i.val-((sharedRows k).length-2),?_⟩,?_⟩
        · have := i.isLt; have := sharedRows_length k; omega
        · apply Fin.ext
          change (sharedRows k).length-2 + (i.val-((sharedRows k).length-2)) = i.val
          omega
      subst i
      rw [sharedModel_seedPair,sharedModel_seedPair]
      exact sharedSeedPair_eq t (congrArg (SharedSeed.residue seedModel.system) h₁) h₂
  · intro i hi v
    rw [sharedModel_pair pick i hi,sharedModel_pair pick i hi]
    apply sharedOrdinaryPair_eq pick i hi
    · unfold sharedLineValue
      dsimp only [Prod.fst_sub,Prod.snd_sub]
      ring
    · change v.2 i - 0 = v.2 i
      simp
  · intro t v
    rw [sharedModel_seedPair,sharedModel_seedPair]
    apply sharedSeedPair_eq
    · have hn : (35 : ZMod residueModulus) = 0 := by
        exact (ZMod.natCast_eq_zero_iff 35 _).mpr
          (by rw [residueModulus_value]; exact dvd_refl 35)
      apply Prod.ext <;> simp [SharedSeed.residue,Int.cast_sub,hn]
    · change v.2 (sharedSeedRow k t) - 0 = _
      simp
  · intro t v
    rw [sharedModel_seedPair,sharedModel_seedPair]
    apply sharedSeedPair_eq
    · have hn : (35 : ZMod residueModulus) = 0 := by
        exact (ZMod.natCast_eq_zero_iff 35 _).mpr
          (by rw [residueModulus_value]; exact dvd_refl 35)
      apply Prod.ext <;> simp [SharedSeed.residue,Int.cast_sub,hn]
    · change v.2 (sharedSeedRow k t) - 0 = _
      simp
  · intro s v
    simp only [sharedModel_line,sharedSum]
    apply Finset.sum_congr rfl
    intro i _
    apply sharedContribution_eq pick s i
    · cases s <;> simp <;> ring
    · change v.2 i - 0 = _
      simp

theorem sharedModel_ordinaryActive (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (x : Plane) (j : SharedLabel i) :
    DigitActive (sharedPrivateAt (sharedModel pick) x i) (sharedDigitSubgroup i j) ↔
      j = pick i hi (sharedLineValue k i x) := by
  let v := pick i hi (sharedLineValue k i x)
  have hPair (u : RowLow i) :
      sharedPrivateAt (sharedModel pick) x i u =
        if hf : i.val < 18 then (adjustFirst (ordinaryFirst_fixed i hf)).symm ((sharedBlocks i hi v).C u)
        else (0,((sharedBlocks i hi v).C u).2) := by
    unfold sharedPrivateAt
    rw [sharedModel_pair pick i hi]
    simp only [sharedOrdinaryPair,sharedBlockPair,Function.update_self,v]
    rfl
  constructor
  · rintro ⟨a,b,hd,hn⟩
    by_contra hq
    apply hn
    have h := (sharedDigitSubgroup_sub i j a b).mp hd v (Ne.symm hq)
    have he : (sharedBlocks i hi v).C a = (sharedBlocks i hi v).C b := by
      simp only [sharedBlocks_C,h]
    rw [hPair,hPair,he]
  · intro hj
    have ha := (sharedBlocks_active i hi v j).mpr hj
    obtain ⟨a,b,hd,hn⟩ := ha
    refine ⟨a,b,hd,?_⟩
    intro h
    apply hn
    rw [hPair,hPair] at h
    split_ifs at h with hf
    · exact congrArg Prod.snd ((adjustFirst (ordinaryFirst_fixed i hf)).symm.injective h)
    · exact congrArg (fun p : SharedCoordinates.Useful (sharedLayout k) i => p.2) h

theorem sharedModel_seedActive (t : Fin 2) (x : Plane) :
    DigitActive (sharedPrivateAt (sharedModel pick) x (sharedSeedRow k t))
      (sharedDigitSubgroup (sharedSeedRow k t) (sharedSeedLabel k t)) ↔
    SharedSeed.residue seedModel.system x ∈ seedActiveRegion seedModel.system t := by
  let i := sharedSeedRow k t
  let e := seedLowToModel k t
  let f := seedPairToModel k t
  let R := SharedSeed.residue seedModel.system x
  have hPair (u : RowLow i) :
      sharedPrivateAt (sharedModel pick) x i u = f.symm (seedUseful modelE t R (e u)) := by
    unfold sharedPrivateAt
    rw [sharedModel_seedPair]
    simp only [sharedSeedPair,seedModelInput,Function.update_self,f,e,i,R]
  rw [← seedUseful_active_iff modelE t]
  have hu (z : K modelE (.inr t)) : z ∈ digitSubgroup modelE (.inr t) () :=
    fun j hj => (hj (by
      change j = (() : Unit)
      cases j
      rfl)).elim
  constructor
  · rintro ⟨a,b,_,hn⟩
    refine ⟨e a,e b,hu _,?_⟩
    intro h
    exact hn (by rw [hPair,hPair,h])
  · rintro ⟨a,b,_,hn⟩
    refine ⟨e.symm a,e.symm b,sharedSeedSubgroup_all k t _,?_⟩
    rw [hPair,hPair,e.apply_symm_apply,e.apply_symm_apply]
    exact fun he => hn (f.symm.injective he)

end
end TranslationTiling.FiniteCompiler.Packed
