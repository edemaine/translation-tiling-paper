import TranslationTiling.FiniteCompiler.Effective.FourValueDependence
import TranslationTiling.FiniteCompiler.Effective.SharedSeedCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

local instance fourValueSeedFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem fourValueSeedRow_val (k : ℕ) (t : Fin 2) :
    (fourValueSeedRow k t).val = 18+2*k+t.val := by
  simp [fourValueSeedRow]
  omega

private theorem fourValueSeedRow_data (k : ℕ) (t : Fin 2) :
    (fourValueRows k).getD (fourValueSeedRow k t).val (0,0,[]) = sharedSeedRows.getD t.val (0,0,[]) := by
  rw [fourValueSeedRow_val,fourValueRows_seed_at]

@[simp] theorem fourValueSeedSizeR (k : ℕ) (t : Fin 2) :
    (fourValueLayout k).lowSize (fourValueSeedRow k t) = seedModelEncoding.r (.inr t) := by
  change ((fourValueRows k).getD (fourValueSeedRow k t).val (0,0,[])).2.2.prod = _
  rw [fourValueSeedRow_data]
  rw [show seedModelEncoding.r (.inr t) = profile1.r (profile1.width+t.val) from by
    rw [show seedModelEncoding.r (.inr t) =
      profile1.r (channelEquiv profile1 (T:=seedModel.system) rfl (.inr t)).val from
        encoding_r profile1 profile1_valid rfl (fun _ => rfl) profile1_injective (.inr t)]
    exact congrArg profile1.r (channel_inr profile1 (T:=seedModel.system) rfl t)]
  fin_cases t <;> rfl

theorem fourValueSeedOrdinaryA (k : ℕ) (t : Fin 2) :
    rowA (fourValueRows k) (fourValueSeedRow k t) = seedModelEncoding.a (.inr t) := by
  change ((fourValueRows k).getD (fourValueSeedRow k t).val (0,0,[])).1 = _
  rw [fourValueSeedRow_data]
  fin_cases t <;> rfl

@[simp] theorem fourValueSeedSizeA (k : ℕ) (t : Fin 2) :
    (fourValueLayout k).firstSize (fourValueSeedRow k t) = seedModelEncoding.a (.inr t) := by
  change sharedObservedA (fourValueRows k) (fourValueSeedRow k t) = _
  rw [sharedObservedA,ite_eq_right (by have := t.isLt; simp [fourValueSeedRow])]
  exact fourValueSeedOrdinaryA k t

@[simp] theorem fourValueSeedSizeB (k : ℕ) (t : Fin 2) :
    (fourValueLayout k).secondSize (fourValueSeedRow k t) = seedModelEncoding.b (.inr t) := by
  change ((fourValueRows k).getD (fourValueSeedRow k t).val (0,0,[])).2.1 = _
  rw [fourValueSeedRow_data]
  fin_cases t <;> rfl

theorem fourValueSeedRow_other (k : ℕ) (t : Fin 2) :
    (fourValueSeedRow k (otherSeed t)).val = (fourValueRows k).length-2+(1-t.val) := by
  fin_cases t <;> rfl

def fourValueSeedLowToModel (k : ℕ) (t : Fin 2) :
    SharedCoordinates.Low (fourValueLayout k) (fourValueSeedRow k t) ≃+* K seedModelEncoding (.inr t) :=
  ZMod.ringEquivCongr (fourValueSeedSizeR k t)

def fourValueSeedPairToModel (k : ℕ) (t : Fin 2) :
    (ZMod ((fourValueLayout k).firstSize (fourValueSeedRow k t)) ×
      ZMod ((fourValueLayout k).secondSize (fourValueSeedRow k t))) ≃+ P seedModelEncoding (.inr t) :=
  ((ZMod.ringEquivCongr (fourValueSeedSizeA k t)).prodCongr
    (ZMod.ringEquivCongr (fourValueSeedSizeB k t))).toAddEquiv

def fourValueSeedInput (k : ℕ) (u : FourValueBase k) : Input seedModelEncoding :=
  fun j => match j with
    | .inl _ => 0
    | .inr t => fourValueSeedLowToModel k t (u.2 (fourValueSeedRow k t))

def fourValueSeedProjection (k : ℕ) (t : Fin 2) : FourValueFactor k →+ P seedModelEncoding (.inr t) :=
  (fourValueSeedPairToModel k t).toAddMonoidHom.comp (privateUseful (fourValueLayout k) (fourValueSeedRow k t))

theorem fourValueSeedProjection_decode (k : ℕ) (t : Fin 2) (n : ℕ) :
    fourValueSeedProjection k t (decode (fourValueLayout k) n) =
      ((n : ZMod (seedModelEncoding.a (.inr t))),(n : ZMod (seedModelEncoding.b (.inr t)))) := by
  change (((ZMod.ringEquivCongr (fourValueSeedSizeA k t)) (n : ZMod _)),
    ((ZMod.ringEquivCongr (fourValueSeedSizeB k t)) (n : ZMod _))) = _
  rw [map_natCast,map_natCast]

def fourValueSeedRaw (k : ℕ) (t : Fin 2) : CyclicTile :=
  seedCodes (sharedEnvironment (fourValueRows k) (fourValueSeedRow k t))
    (rowA (fourValueRows k) (fourValueSeedRow k (otherSeed t))) 35

def fourValueSeedDeck (k : ℕ) (t : Fin 2) (o : FourValueOutputGraph k) (F : CyclicTile) : Prop :=
  Tiles (F.toFinset.image (decodePoint (fourValueLayout k)))
    (Set.range (SharedCoordinates.point (fourValueLayout k) o))

def fourValueSeedSource (k : ℕ) (t : Fin 2) (x : FourValueBase k) (j : ModelSeedIndex t) : FourValueBase k :=
  SharedCoordinates.activationSource (fourValueLayout k) (fourValueSeedRow k t)
    (seedOffset modelE t j) ((seedOffset modelE t j).1 : ℤ) x

theorem fourValueSeedSource_self (k : ℕ) (t : Fin 2) (x : FourValueBase k) (j : ModelSeedIndex t) :
    fourValueSeedLowToModel k t ((fourValueSeedSource k t x j).2 (fourValueSeedRow k t)) =
      fourValueSeedInput k x (.inr t) - j.1.1 := by
  simp only [fourValueSeedSource,SharedCoordinates.activationSource,Function.update_self,map_sub,fourValueSeedInput]
  change _ - ZMod.ringEquivCongr (fourValueSeedSizeR k t) _ = _ - _
  rw [map_intCast,seedOffset_low]

theorem fourValueSeedRaw_iff (k : ℕ) (t : Fin 2) (o : FourValueOutputGraph k) :
    fourValueSeedDeck k t o (fourValueSeedRaw k t) ↔ ∀ x : FourValueBase k, Function.Bijective (fun j : ModelSeedIndex t =>
      ((fourValueSeedProjection k t (SharedCoordinates.point (fourValueLayout k) o (fourValueSeedSource k t x j)).2 +
        shift (modelE.a (.inr t)) (modelE.b (.inr t)) j.1.2,
        fourValueSeedLowToModel k t (o.high (fourValueSeedSource k t x j) (fourValueSeedRow k t))),
        (o.fixed (fourValueSeedSource k t x j)).1.1)) := by
  let L := fourValueLayout k
  let i := fourValueSeedRow k t
  let a := modelE.a (.inr t)
  let b := modelE.b (.inr t)
  let ψ := fourValueSeedProjection k t
  let A : ActivationEnvironment := ((order L,guardedOther (fourValueRows k) i),(L.lowSize i,a,b,1225))
  let z (v : SharedCoordinates.Ambient L) := v.2.1.1.1
  let tgt (v : SharedCoordinates.Ambient L) :=
    ((ψ v.2,fourValueSeedLowToModel k t (highCoordinate L i v)),z v)
  have henv : sharedEnvironment (fourValueRows k) i = A := by
    change ((sharedOrder (fourValueRows k),_),(L.lowSize i,rowA _ i,rowB _ i,1225)) =
      ((order L,_),(L.lowSize i,a,b,1225))
    rw [fourValueLayout_order,fourValueSeedOrdinaryA,show rowB (fourValueRows k) i = b from fourValueSeedSizeB k t]
  have hr : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
  have hW : fourValueSeedRaw k t = seedCodes A (modelE.a (.inr (otherSeed t))) residueModulus := by
    unfold fourValueSeedRaw
    rw [henv,fourValueSeedOrdinaryA,hr]
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
      rw [show L.lowSize i = modelE.r (.inr t) from fourValueSeedSizeR k t]
      exact numericalSeedFirst_eq modelE t j
    rw [he]
    rfl
  have hmem (v : SharedCoordinates.Ambient L) :
      v ∈ ((fourValueSeedRaw k t).toFinset.image (decodePoint L)) ↔
      ∃ j : ModelSeedIndex t, ActivationBatch L i ψ (ω j) (e j) v ∧ z v = 0 := by
    have hbatch (j : ModelSeedIndex t) :
        v ∈ (seedBatchCodes A (modelE.a (.inr (otherSeed t))) residueModulus (rawSeedIndex modelE t j)).toFinset.image
          (decodePoint L) ↔ ActivationBatch L i ψ (ω j) (e j) v ∧ z v = 0 := by
      rw [hj,mem_decoded_activation_batch L (fourValueLayoutCRT k) ψ (fourValueSeedProjection_decode k t)
        i _ (fourValueOther_membership k i)]
      simp only [ActivationBatch,z,Bool.false_eq_true,false_or,and_assoc]
    rw [hW]
    have hc (j : SeedCode) : j ∈ seedIndices a b (L.lowSize i) residueModulus ↔
        ∃ u : ModelSeedIndex t, rawSeedIndex modelE t u = j := by
      rw [show L.lowSize i = modelE.r (.inr t) from fourValueSeedSizeR k t]
      exact seedIndices_native modelE t j
    simp only [seedCodes,A,List.mem_flatMap,Finset.mem_image,List.mem_toFinset,hc]
    constructor
    · rintro ⟨f,⟨d,⟨j,rfl⟩,hf⟩,hv⟩
      exact ⟨j,(hbatch j).mp (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,hv⟩)⟩
    · rintro ⟨j,h⟩
      obtain ⟨f,hf,hv⟩ := Finset.mem_image.mp ((hbatch j).mpr h)
      exact ⟨f,⟨_,⟨j,rfl⟩,List.mem_toFinset.mp hf⟩,hv⟩
  have hsrc (x : FourValueBase k) : Function.Injective (fourValueSeedSource k t x) := by
    intro j j' h
    apply seedOffset_injective modelE t
    exact sub_right_inj.mp (congrArg (fun v : FourValueBase k => v.1) h)
  have ht (x : FourValueBase k) (c : (P modelE (.inr t) × K modelE (.inr t)) × ZMod 1225) :
      ∃ v : SharedCoordinates.Ambient L, baseProjection L v = x ∧ tgt v = c := by
    let o' : FourValueOutputGraph k :=
      ⟨fun _ => ((c.2,0),0),fun _ => Function.update 0 i ((fourValueSeedPairToModel k t).symm c.1.1),
        fun _ => Function.update 0 i ((fourValueSeedLowToModel k t).symm c.1.2)⟩
    refine ⟨SharedCoordinates.point L o' x,baseProjection_point L _ _,?_⟩
    refine Prod.ext ?_ (show z (SharedCoordinates.point L o' x) = c.2 from rfl)
    apply Prod.ext
    · change fourValueSeedPairToModel k t (o'.privateOutput x i) = c.1.1
      simp [o']
    · dsimp only [tgt]
      rw [highCoordinate_point]
      simp [o']
  unfold fourValueSeedDeck
  apply tiles_indexed_activation_iff _ _ (SharedCoordinates.point_injective L o) (baseProjection L) tgt
    (fourValueSeedSource k t) hsrc _ ht
  intro v x
  rw [hmem]
  apply exists_congr
  intro j
  rw [sub_point_activationBatch L i ψ]
  change (fourValueSeedSource k t (baseProjection L v) j = x ∧ _ ∧ _) ∧ _ ↔ _
  constructor
  · rintro ⟨⟨rfl,hc,hd⟩,hz⟩
    refine ⟨rfl,Prod.ext (Prod.ext hc (congrArg (fourValueSeedLowToModel k t) hd)) ?_⟩
    exact (sub_eq_zero.mp hz).symm
  · rintro ⟨rfl,h⟩
    have he := congrArg Prod.fst h
    exact ⟨⟨rfl,congrArg Prod.fst he,(fourValueSeedLowToModel k t).injective (congrArg Prod.snd he)⟩,
      sub_eq_zero.mpr (congrArg Prod.snd h).symm⟩

private theorem modelWidth : residueModulus = 35 := by
  norm_num [residueModulus_value,compactSeedFrame]

private def modelResidueTo35 : ModelResidue ≃+ ZMod 35 × ZMod 35 :=
  ((ZMod.ringEquivCongr modelWidth).prodCongr (ZMod.ringEquivCongr modelWidth)).toAddEquiv

private def modelZTo1225 : ZMod (D seedModel.system) ≃+ ZMod 1225 :=
  (ZMod.ringEquivCongr (congrArg (fun n : ℕ => n^2) modelWidth)).toAddEquiv

theorem fourValue_seed_active {k : ℕ} {o : FourValueOutputGraph k} {slopes : List ℕ}
    (hd : HasFourValueDependence k slopes o) (t : Fin 2) (h : fourValueSeedDeck k t o (fourValueSeedRaw k t)) :
    ∃ x : Plane, DigitActive (fourValuePrivateAt o x (fourValueSeedRow k t))
      ⊤ := by
  by_contra! hn
  let L := fourValueLayout k
  let i := fourValueSeedRow k t
  let x : FourValueBase k := 0
  let Q (s : ModelResidue) := fourValueSeedPairToModel k t
    (fourValuePrivateAt o (fourValueRep35 (modelResidueTo35 (-s))) i 0)
  have hq (j : ModelSeedIndex t) :
      fourValueSeedProjection k t (SharedCoordinates.point L o (fourValueSeedSource k t x j)).2 = Q j.2 := by
    let y := fourValueSeedSource k t x j
    change fourValueSeedPairToModel k t (o.privateOutput y i) = _
    rw [hd.privateAt_eq y i,hd.privateAt_seed t y.1]
    have he : fourValueResidues35 y.1 = modelResidueTo35 (-j.2) := by
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
    exact (not_digitActive_iff _ _).mp (hn (fourValueRep35 (modelResidueTo35 (-j.2))))
      _ _ (by trivial)
  have hab : (modelE.a (.inr t) = 2 ∧ modelE.b (.inr t) = 1229) ∨
      (modelE.a (.inr t) = 3 ∧ modelE.b (.inr t) = 773) := by
    fin_cases t
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  exact sharedSeed_not_bijective_of_inactive
    (K := K modelE (.inr t)) (S := ModelResidue)
    (by rw [Fintype.card_congr modelResidueTo35.toEquiv]; simp)
    hab Q _ (fun j => congrArg (fun p => p + shift _ _ j.1.2) (hq j)) ((fourValueSeedRaw_iff k t o).mp h x)

def fourValueSeedPair (k : ℕ) (t : Fin 2) (x : FourValueBase k) :
    ZMod ((fourValueLayout k).firstSize (fourValueSeedRow k t)) ×
      ZMod ((fourValueLayout k).secondSize (fourValueSeedRow k t)) :=
  (fourValueSeedPairToModel k t).symm
    (seedUseful modelE t (SharedSeed.residue seedModel.system x.1) (fourValueSeedInput k x (.inr t)))

def fourValueSeedHigh (k : ℕ) (t : Fin 2) (x : FourValueBase k) :
    SharedCoordinates.Low (fourValueLayout k) (fourValueSeedRow k t) :=
  (fourValueSeedLowToModel k t).symm
    (seedHigh modelE t x.1.1 (SharedSeed.residue seedModel.system x.1) (fourValueSeedInput k x (.inr t)))

def fourValueSeedZ (k : ℕ) (x : FourValueBase k) : ZMod 1225 :=
  modelZTo1225 (SharedSeed.commonZ seedModel.system x.1 (fourValueSeedInput k x))

theorem fourValueSeedRaw_complete (k : ℕ) (t : Fin 2) (o : FourValueOutputGraph k)
    (hc : ∀ x, o.privateOutput x (fourValueSeedRow k t) = fourValueSeedPair k t x)
    (hh : ∀ x, o.high x (fourValueSeedRow k t) = fourValueSeedHigh k t x)
    (hz : ∀ x, (o.fixed x).1.1 = fourValueSeedZ k x) :
    fourValueSeedDeck k t o (fourValueSeedRaw k t) := by
  apply (fourValueSeedRaw_iff k t o).mpr
  intro x
  let e := (Equiv.refl (P modelE (.inr t) × K modelE (.inr t))).prodCongr modelZTo1225.toEquiv
  have he := e.bijective.comp (seedActualForward_bijective modelE t x.1 (fourValueSeedInput k x))
  convert he using 2
  rename_i j
  let y := fourValueSeedSource k t x j
  change ((fourValueSeedPairToModel k t (o.privateOutput y (fourValueSeedRow k t)) + _,
    fourValueSeedLowToModel k t (o.high y (fourValueSeedRow k t))), (o.fixed y).1.1) = _
  rw [hc,hh,hz]
  dsimp only [e,Function.comp_apply,Equiv.prodCongr_apply,Equiv.refl_apply,AddEquiv.coe_toEquiv]
  simp only [fourValueSeedPair,fourValueSeedHigh,AddEquiv.apply_symm_apply,RingEquiv.apply_symm_apply,
    seedActualForward,seedC,seedBeta,seedSourceInput_same,fourValueSeedZ]
  have hlow := fourValueSeedSource_self k t x j
  change fourValueSeedInput k y (.inr t) = _ at hlow
  rw [hlow]
  rfl


end
end TranslationTiling.FiniteCompiler.Packed
