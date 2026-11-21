import TranslationTiling.FiniteCompiler.Effective.SharedSeedModel
import TranslationTiling.FiniteCompiler.Effective.SharedBatchDeck

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

local instance sharedSeedDeckFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxHeartbeats 2000000

abbrev modelE := seedModelEncoding

def seedRaw (k : ℕ) (t : Fin 2) : CyclicTile :=
  seedCodes (sharedEnvironment (sharedRows k) (sharedSeedRow k t))
    (rowA (sharedRows k) (sharedSeedRow k (otherSeed t))) 35

def seedDeck (k : ℕ) (t : Fin 2) (o : SharedOutput k) (F : CyclicTile) : Prop :=
  Tiles (F.toFinset.image (decodePoint (sharedLayout k)))
    (Set.range (SharedCoordinates.point (sharedLayout k) o))

def seedSource (k : ℕ) (t : Fin 2) (x : SharedBase k) (j : ModelSeedIndex t) : SharedBase k :=
  SharedCoordinates.activationSource (sharedLayout k) (sharedSeedRow k t)
    (seedOffset modelE t j) ((seedOffset modelE t j).1 : ℤ) x

theorem seedSource_self (k : ℕ) (t : Fin 2) (x : SharedBase k) (j : ModelSeedIndex t) :
    seedLowToModel k t ((seedSource k t x j).2 (sharedSeedRow k t)) =
      seedModelInput k x (.inr t) - j.1.1 := by
  simp only [seedSource,SharedCoordinates.activationSource,Function.update_self,map_sub,seedModelInput]
  change _ - ZMod.ringEquivCongr (sharedSeedSizeR k t) _ = _ - _
  rw [map_intCast,seedOffset_low]

theorem seedRaw_iff (k : ℕ) (t : Fin 2) (o : SharedOutput k) :
    seedDeck k t o (seedRaw k t) ↔ ∀ x : SharedBase k, Function.Bijective (fun j : ModelSeedIndex t =>
      ((seedModelProjection k t (SharedCoordinates.point (sharedLayout k) o (seedSource k t x j)).2 +
        shift (modelE.a (.inr t)) (modelE.b (.inr t)) j.1.2,
        seedLowToModel k t (o.high (seedSource k t x j) (sharedSeedRow k t))),
        (o.fixed (seedSource k t x j)).1.1)) := by
  let L := sharedLayout k
  let i := sharedSeedRow k t
  let a := modelE.a (.inr t)
  let b := modelE.b (.inr t)
  let ψ := seedModelProjection k t
  let A : ActivationEnvironment := ((order L,guardedOther (sharedRows k) i),(L.lowSize i,a,b,1225))
  let z (v : SharedCoordinates.Ambient L) := v.2.1.1.1
  let tgt (v : SharedCoordinates.Ambient L) :=
    ((ψ v.2,seedLowToModel k t (highCoordinate L i v)),z v)
  have henv : sharedEnvironment (sharedRows k) i = A := by
    change ((sharedOrder (sharedRows k),_),(L.lowSize i,rowA _ i,rowB _ i,1225)) =
      ((order L,_),(L.lowSize i,a,b,1225))
    rw [sharedLayout_order,sharedSeedOrdinaryA,show rowB (sharedRows k) i = b from sharedSeedSizeB k t]
  have hr : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
  have hW : seedRaw k t = seedCodes A (modelE.a (.inr (otherSeed t))) residueModulus := by
    unfold seedRaw
    rw [henv,sharedSeedOrdinaryA,hr]
  let e (j : ModelSeedIndex t) := shift a b j.1.2
  let ω := seedOffset modelE t
  have hj (j : ModelSeedIndex t) :
      seedBatchCodes A (modelE.a (.inr (otherSeed t))) residueModulus (rawSeedIndex modelE t j) =
        activationBatchCodes (A.1,A.2,ω j,((e j).1.val,(e j).2.val),false) := by
    unfold seedBatchCodes
    dsimp only
    have he : numericalSeedFirst
        (((a,b,L.lowSize i),(rawSeedIndex modelE t j).1),
          (residueModulus,modelE.a (.inr (otherSeed t)),
            (rawSeedIndex modelE t j).2.1,(rawSeedIndex modelE t j).2.2)) = (ω j).1 := by
      rw [show L.lowSize i = modelE.r (.inr t) from sharedSeedSizeR k t]
      exact numericalSeedFirst_eq modelE t j
    rw [he]
    rfl
  have hmem (v : SharedCoordinates.Ambient L) :
      v ∈ ((seedRaw k t).toFinset.image (decodePoint L)) ↔
      ∃ j : ModelSeedIndex t, ActivationBatch L i ψ (ω j) (e j) v ∧ z v = 0 := by
    have hbatch (j : ModelSeedIndex t) :
        v ∈ (seedBatchCodes A (modelE.a (.inr (otherSeed t))) residueModulus (rawSeedIndex modelE t j)).toFinset.image
          (decodePoint L) ↔ ActivationBatch L i ψ (ω j) (e j) v ∧ z v = 0 := by
      rw [hj,mem_decoded_activation_batch L (sharedLayoutCRT k) ψ (seedModelProjection_decode k t)
        i _ (sharedOther_membership k i)]
      simp only [ActivationBatch,z,Bool.false_eq_true,false_or,and_assoc]
    rw [hW]
    have hc (j : SeedCode) : j ∈ seedIndices a b (L.lowSize i) residueModulus ↔
        ∃ u : ModelSeedIndex t, rawSeedIndex modelE t u = j := by
      rw [show L.lowSize i = modelE.r (.inr t) from sharedSeedSizeR k t]
      exact seedIndices_native modelE t j
    simp only [seedCodes,A,List.mem_flatMap,Finset.mem_image,List.mem_toFinset,hc]
    constructor
    · rintro ⟨f,⟨d,⟨j,rfl⟩,hf⟩,hv⟩
      exact ⟨j,(hbatch j).mp (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,hv⟩)⟩
    · rintro ⟨j,h⟩
      obtain ⟨f,hf,hv⟩ := Finset.mem_image.mp ((hbatch j).mpr h)
      exact ⟨f,⟨_,⟨j,rfl⟩,List.mem_toFinset.mp hf⟩,hv⟩
  have hsrc (x : SharedBase k) : Function.Injective (seedSource k t x) := by
    intro j j' h
    apply seedOffset_injective modelE t
    exact sub_right_inj.mp (congrArg (fun v : SharedBase k => v.1) h)
  have ht (x : SharedBase k) (c : (P modelE (.inr t) × K modelE (.inr t)) × ZMod 1225) :
      ∃ v : SharedCoordinates.Ambient L, baseProjection L v = x ∧ tgt v = c := by
    let o' : SharedOutput k :=
      ⟨fun _ => ((c.2,0),0),fun _ => Function.update 0 i ((seedPairToModel k t).symm c.1.1),
        fun _ => Function.update 0 i ((seedLowToModel k t).symm c.1.2)⟩
    refine ⟨SharedCoordinates.point L o' x,baseProjection_point L _ _,?_⟩
    refine Prod.ext ?_ (show z (SharedCoordinates.point L o' x) = c.2 from rfl)
    apply Prod.ext
    · change seedPairToModel k t (o'.privateOutput x i) = c.1.1
      simp [o']
    · dsimp only [tgt]
      rw [highCoordinate_point]
      simp [o']
  unfold seedDeck
  apply tiles_indexed_activation_iff _ _ (SharedCoordinates.point_injective L o) (baseProjection L) tgt
    (seedSource k t) hsrc _ ht
  intro v x
  rw [hmem]
  apply exists_congr
  intro j
  rw [sub_point_activationBatch L i ψ]
  change (seedSource k t (baseProjection L v) j = x ∧ _ ∧ _) ∧ _ ↔ _
  constructor
  · rintro ⟨⟨rfl,hc,hd⟩,hz⟩
    refine ⟨rfl,Prod.ext (Prod.ext hc (congrArg (seedLowToModel k t) hd)) ?_⟩
    exact (sub_eq_zero.mp hz).symm
  · rintro ⟨rfl,h⟩
    have he := congrArg Prod.fst h
    exact ⟨⟨rfl,congrArg Prod.fst he,(seedLowToModel k t).injective (congrArg Prod.snd he)⟩,
      sub_eq_zero.mpr (congrArg Prod.snd h).symm⟩

end
end TranslationTiling.FiniteCompiler.Packed
