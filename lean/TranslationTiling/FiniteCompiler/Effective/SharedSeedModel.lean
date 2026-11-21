import TranslationTiling.FiniteCompiler.Effective.SharedDeckDependence
import TranslationTiling.FiniteCompiler.CommonSeedOutputs

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical

noncomputable section

local instance sharedSeedModelFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private def seedModelWang : LeanWang.TileSet := [⟨0,0,0,0⟩]

private def seedModelCode : PairSmall.Code seedModelWang profile1.radices.prod :=
  code seedModelWang _ (by decide) (by decide)

private instance seedModelOriginalAlphabet : AlphabetFamily (PairSmall.system seedModelCode) :=
  GuardedCompiler.alphabet seedModelCode

/-- A fixed instance of the existing seed circuitry. All of its local
parameters agree with the seed rows in the shared compiler. -/
def seedModel :=
  refinement profile1 checked1.layout seedModelCode

instance seedModelAlphabet : AlphabetFamily seedModel.system := seedModel.family

def seedModelEncoding : EncodingParameters seedModel.system := by
  exact encoding profile1 profile1_valid rfl (fun _ => rfl) profile1_injective

theorem sharedSeedRow_val (k : ℕ) (t : Fin 2) :
    (sharedSeedRow k t).val = 18+2*k+t.val := by
  simp [sharedSeedRow]
  omega

private theorem sharedSeedRow_data (k : ℕ) (t : Fin 2) :
    (sharedRows k).getD (sharedSeedRow k t).val (0,0,[]) = sharedSeedRows.getD t.val (0,0,[]) := by
  rw [sharedSeedRow_val,sharedRows_seed_at]

@[simp] theorem sharedSeedSizeR (k : ℕ) (t : Fin 2) :
    (sharedLayout k).lowSize (sharedSeedRow k t) = seedModelEncoding.r (.inr t) := by
  change ((sharedRows k).getD (sharedSeedRow k t).val (0,0,[])).2.2.prod = _
  rw [sharedSeedRow_data]
  rw [show seedModelEncoding.r (.inr t) = profile1.r (profile1.width+t.val) from by
    rw [show seedModelEncoding.r (.inr t) =
      profile1.r (channelEquiv profile1 (T:=seedModel.system) rfl (.inr t)).val from
        encoding_r profile1 profile1_valid rfl (fun _ => rfl) profile1_injective (.inr t)]
    exact congrArg profile1.r (channel_inr profile1 (T:=seedModel.system) rfl t)]
  fin_cases t <;> rfl

theorem sharedSeedOrdinaryA (k : ℕ) (t : Fin 2) :
    rowA (sharedRows k) (sharedSeedRow k t) = seedModelEncoding.a (.inr t) := by
  change ((sharedRows k).getD (sharedSeedRow k t).val (0,0,[])).1 = _
  rw [sharedSeedRow_data]
  fin_cases t <;> rfl

@[simp] theorem sharedSeedSizeA (k : ℕ) (t : Fin 2) :
    (sharedLayout k).firstSize (sharedSeedRow k t) = seedModelEncoding.a (.inr t) := by
  change sharedObservedA (sharedRows k) (sharedSeedRow k t) = _
  rw [sharedObservedA,ite_eq_right (by have := t.isLt; simp [sharedSeedRow])]
  exact sharedSeedOrdinaryA k t

@[simp] theorem sharedSeedSizeB (k : ℕ) (t : Fin 2) :
    (sharedLayout k).secondSize (sharedSeedRow k t) = seedModelEncoding.b (.inr t) := by
  change ((sharedRows k).getD (sharedSeedRow k t).val (0,0,[])).2.1 = _
  rw [sharedSeedRow_data]
  fin_cases t <;> rfl

theorem sharedSeedRow_other (k : ℕ) (t : Fin 2) :
    (sharedSeedRow k (otherSeed t)).val = (sharedRows k).length-2+(1-t.val) := by
  fin_cases t <;> rfl

abbrev ModelResidue := Residues seedModel.system

abbrev ModelSeedIndex (t : Fin 2) := SeedActivationIndex seedModelEncoding t

def seedLowToModel (k : ℕ) (t : Fin 2) :
    SharedCoordinates.Low (sharedLayout k) (sharedSeedRow k t) ≃+* K seedModelEncoding (.inr t) :=
  ZMod.ringEquivCongr (sharedSeedSizeR k t)

def seedPairToModel (k : ℕ) (t : Fin 2) :
    (ZMod ((sharedLayout k).firstSize (sharedSeedRow k t)) ×
      ZMod ((sharedLayout k).secondSize (sharedSeedRow k t))) ≃+ P seedModelEncoding (.inr t) :=
  ((ZMod.ringEquivCongr (sharedSeedSizeA k t)).prodCongr
    (ZMod.ringEquivCongr (sharedSeedSizeB k t))).toAddEquiv

def seedModelInput (k : ℕ) (u : SharedBase k) : Input seedModelEncoding :=
  fun j => match j with
    | .inl _ => 0
    | .inr t => seedLowToModel k t (u.2 (sharedSeedRow k t))

def seedModelProjection (k : ℕ) (t : Fin 2) : SharedFactor k →+ P seedModelEncoding (.inr t) :=
  (seedPairToModel k t).toAddMonoidHom.comp (privateUseful (sharedLayout k) (sharedSeedRow k t))

theorem seedModelProjection_decode (k : ℕ) (t : Fin 2) (n : ℕ) :
    seedModelProjection k t (decode (sharedLayout k) n) =
      ((n : ZMod (seedModelEncoding.a (.inr t))),(n : ZMod (seedModelEncoding.b (.inr t)))) := by
  change (((ZMod.ringEquivCongr (sharedSeedSizeA k t)) (n : ZMod _)),
    ((ZMod.ringEquivCongr (sharedSeedSizeB k t)) (n : ZMod _))) = _
  rw [map_natCast,map_natCast]

end
end TranslationTiling.FiniteCompiler.Packed
