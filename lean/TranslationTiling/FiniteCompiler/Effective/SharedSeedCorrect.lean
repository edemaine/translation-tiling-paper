import TranslationTiling.FiniteCompiler.Effective.SharedSeedDeck
import TranslationTiling.FiniteCompiler.Effective.SharedDigits
import TranslationTiling.FiniteCompiler.Effective.SharedLocal
import TranslationTiling.FiniteCompiler.SharedSeedSoundness

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical
noncomputable section

local instance sharedSeedCorrectFrame : SeedFrame := compactSeedFrame
set_option maxHeartbeats 2000000

theorem sharedSeedDigits_length (k : ℕ) (t : Fin 2) :
    (rowDigits (sharedRows k) (sharedSeedRow k t)).length = 1 := by
  unfold rowDigits
  rw [sharedSeedRow_val,sharedRows_seed_at]
  fin_cases t <;> rfl

def sharedSeedLabel (k : ℕ) (t : Fin 2) : SharedLabel (sharedSeedRow k t) :=
  ⟨0,by rw [sharedSeedDigits_length]; decide⟩

theorem sharedSeedSubgroup_all (k : ℕ) (t : Fin 2)
    (z : SharedCoordinates.Low (sharedLayout k) (sharedSeedRow k t)) :
    z ∈ sharedDigitSubgroup (sharedSeedRow k t) (sharedSeedLabel k t) := by
  intro q hq
  exfalso
  apply hq
  apply Fin.ext
  have h := q.isLt
  simp only [sharedSeedDigits_length] at h
  change q.val = 0
  omega

private theorem modelWidth : residueModulus = 35 := by
  norm_num [residueModulus_value,compactSeedFrame]

private def modelResidueTo35 : ModelResidue ≃+ ZMod 35 × ZMod 35 :=
  ((ZMod.ringEquivCongr modelWidth).prodCongr (ZMod.ringEquivCongr modelWidth)).toAddEquiv

private def modelZTo1225 : ZMod (D seedModel.system) ≃+ ZMod 1225 :=
  (ZMod.ringEquivCongr (congrArg (fun n : ℕ => n^2) modelWidth)).toAddEquiv

theorem seed_active {k : ℕ} {o : SharedOutput k} {slopes : List ℕ}
    (hd : HasSharedDependence k slopes o) (t : Fin 2) (h : seedDeck k t o (seedRaw k t)) :
    ∃ x : Plane, DigitActive (sharedPrivateAt o x (sharedSeedRow k t))
      (sharedDigitSubgroup (sharedSeedRow k t) (sharedSeedLabel k t)) := by
  by_contra! hn
  let L := sharedLayout k
  let i := sharedSeedRow k t
  let x : SharedBase k := 0
  let Q (s : ModelResidue) := seedPairToModel k t
    (sharedPrivateAt o (seedRep35 (modelResidueTo35 (-s))) i 0)
  have hq (j : ModelSeedIndex t) :
      seedModelProjection k t (SharedCoordinates.point L o (seedSource k t x j)).2 = Q j.2 := by
    let y := seedSource k t x j
    change seedPairToModel k t (o.privateOutput y i) = _
    rw [hd.privateAt_eq y i,hd.privateAt_seed t y.1]
    have he : seedResidues35 y.1 = modelResidueTo35 (-j.2) := by
      have hres := seedOffset_residue modelE t j
      have e1 := congrArg Prod.fst hres
      have e2 := congrArg Prod.snd hres
      apply Prod.ext
      · change ((0-(seedOffset modelE t j).1 : ℤ) : ZMod 35) =
          ZMod.ringEquivCongr modelWidth (-j.2.1)
        rw [zero_sub, ← e1, ← Int.cast_neg, map_intCast]
      · change ((0-(seedOffset modelE t j).2 : ℤ) : ZMod 35) =
          ZMod.ringEquivCongr modelWidth (-j.2.2)
        rw [zero_sub, ← e2, ← Int.cast_neg, map_intCast]
    rw [he]
    congr 1
    exact (not_digitActive_iff _ _).mp (hn (seedRep35 (modelResidueTo35 (-j.2))))
      _ _ (sharedSeedSubgroup_all k t _)
  have hab : (modelE.a (.inr t) = 2 ∧ modelE.b (.inr t) = 1229) ∨
      (modelE.a (.inr t) = 3 ∧ modelE.b (.inr t) = 773) := by
    fin_cases t
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  exact sharedSeed_not_bijective_of_inactive
    (K := K modelE (.inr t)) (S := ModelResidue)
    (by rw [Fintype.card_congr modelResidueTo35.toEquiv]; simp)
    hab Q _ (fun j => congrArg (fun p => p + shift _ _ j.1.2) (hq j)) ((seedRaw_iff k t o).mp h x)

def sharedSeedPair (k : ℕ) (t : Fin 2) (x : SharedBase k) :
    ZMod ((sharedLayout k).firstSize (sharedSeedRow k t)) ×
      ZMod ((sharedLayout k).secondSize (sharedSeedRow k t)) :=
  (seedPairToModel k t).symm
    (seedUseful modelE t (SharedSeed.residue seedModel.system x.1) (seedModelInput k x (.inr t)))

def sharedSeedHigh (k : ℕ) (t : Fin 2) (x : SharedBase k) :
    SharedCoordinates.Low (sharedLayout k) (sharedSeedRow k t) :=
  (seedLowToModel k t).symm
    (seedHigh modelE t x.1.1 (SharedSeed.residue seedModel.system x.1) (seedModelInput k x (.inr t)))

def sharedSeedZ (k : ℕ) (x : SharedBase k) : ZMod 1225 :=
  modelZTo1225 (SharedSeed.commonZ seedModel.system x.1 (seedModelInput k x))

theorem seedRaw_complete (k : ℕ) (t : Fin 2) (o : SharedOutput k)
    (hc : ∀ x, o.privateOutput x (sharedSeedRow k t) = sharedSeedPair k t x)
    (hh : ∀ x, o.high x (sharedSeedRow k t) = sharedSeedHigh k t x)
    (hz : ∀ x, (o.fixed x).1.1 = sharedSeedZ k x) :
    seedDeck k t o (seedRaw k t) := by
  apply (seedRaw_iff k t o).mpr
  intro x
  let e := (Equiv.refl (P modelE (.inr t) × K modelE (.inr t))).prodCongr modelZTo1225.toEquiv
  have he := e.bijective.comp (seedActualForward_bijective modelE t x.1 (seedModelInput k x))
  convert he using 2
  rename_i j
  let y := seedSource k t x j
  change ((seedPairToModel k t (o.privateOutput y (sharedSeedRow k t)) + _,
    seedLowToModel k t (o.high y (sharedSeedRow k t))), (o.fixed y).1.1) = _
  rw [hc,hh,hz]
  dsimp only [e,Function.comp_apply,Equiv.prodCongr_apply,Equiv.refl_apply,AddEquiv.coe_toEquiv]
  simp only [sharedSeedPair,sharedSeedHigh,AddEquiv.apply_symm_apply,RingEquiv.apply_symm_apply,
    seedActualForward,seedC,seedBeta,seedSourceInput_same,sharedSeedZ]
  have hlow := seedSource_self k t x j
  change seedModelInput k y (.inr t) = _ at hlow
  rw [hlow]
  rfl

end
end TranslationTiling.FiniteCompiler.Packed
