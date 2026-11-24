import TranslationTiling.FiniteCompiler.Effective.FourValueCycleCorrect
import TranslationTiling.FiniteCompiler.Effective.FourValueWangComplete
import TranslationTiling.FiniteCompiler.Effective.FourValueSeeds

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Effective SharedCoordinates
open scoped Classical BigOperators

noncomputable section

local instance fourValueModelFrame : SeedFrame := compactSeedFrame

set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow fourValueOutput
set_option maxRecDepth 2500

def fourValueLineValue {k : ℕ} (i : FourValueRow k) (x : Plane) : ℤ :=
  x.2 + ((tailSlopes k).getD i.val 0 : ℤ)*x.1

structure FourValuePicker (k : ℕ) where
  fixed : ∀ i : FourValueRow k, i.val < 18 → ℤ → FourValueLabel i
  wang : WangDigitRow k → ℤ → WangChoice

variable {k : ℕ} (pick : FourValuePicker k)

def fourValueFixedPair (i : FourValueRow k) (hi : i.val < 18) (x : FourValueBase k) :
    SharedCoordinates.Useful (fourValueLayout k) i :=
  (adjustFirst (fourValueFirst_fixed i hi)).symm
    ((fourValueFixedBlocks i hi (pick.fixed i hi (fourValueLineValue i x.1))).C (x.2 i))

def fourValueFixedHigh (i : FourValueRow k) (hi : i.val < 18) (x : FourValueBase k) :
    FourValueLow i :=
  (fourValueFixedBlocks i hi (pick.fixed i hi (fourValueLineValue i x.1))).T x.1.1 (x.2 i)

def wangModelPair (w : WangDigitRow k) (x : FourValueBase k) :=
  (joinWangUseful w).symm (wangBlockOutput w (pick.wang w (wangLineValue w x.1)) (x.2 (wangDigitRow w)))

def wangModelPrivate (w : WangDigitRow k) (x : FourValueBase k) :
    SharedCoordinates.Useful (fourValueLayout k) (wangDigitRow w) :=
  (0,(wangModelPair pick w x).2)

def wangModelHigh (w : WangDigitRow k) (x : FourValueBase k) :
    FourValueLow (wangDigitRow w) :=
  wangBlockHigh w (pick.wang w (wangLineValue w x.1)) x.1.1 (x.2 (wangDigitRow w))

def fourValueContribution (s : Bool) (w : WangDigitRow k) (x : FourValueBase k) :
    ZMod (sharedPrime s) :=
  if h : wangSlopeFactor w = s then
    ZMod.ringEquivCongr (congrArg sharedPrime h) (wangModelPair pick w x).1
  else 0

def fourValueSum (s : Bool) (x : FourValueBase k) : ZMod (sharedPrime s) :=
  ∑ w : WangDigitRow k, fourValueContribution pick s w x

private def seedIndex (i : FourValueRow k) (h : ¬ i.val < (fourValueRows k).length-2) : Fin 2 :=
  ⟨i.val-((fourValueRows k).length-2),by have := i.isLt; have := fourValueRows_length k; omega⟩

private theorem seedIndex_row (i : FourValueRow k) (h : ¬ i.val < (fourValueRows k).length-2) :
    fourValueSeedRow k (seedIndex i h) = i := by
  apply Fin.ext
  have := i.isLt
  change (fourValueRows k).length-2+(i.val-((fourValueRows k).length-2)) = i.val
  omega

def fourValueModel : FourValueOutputGraph k where
  fixed x := ((fourValueSeedZ k x,fourValueSum pick true x),fourValueSum pick false x)
  privateOutput x i :=
    if h : i.val < 18 then fourValueFixedPair pick i h x
    else if h' : IsWangRow i then (wangRowOf_eq i h') ▸ wangModelPrivate pick (wangRowOf i h') x
    else
      let h'' : ¬ i.val < (fourValueRows k).length-2 := fun hi => h' ⟨Nat.le_of_not_gt h,hi⟩
      (seedIndex_row i h'') ▸ fourValueSeedPair k (seedIndex i h'') x
  high x i :=
    if h : i.val < 18 then fourValueFixedHigh pick i h x
    else if h' : IsWangRow i then (wangRowOf_eq i h') ▸ wangModelHigh pick (wangRowOf i h') x
    else
      let h'' : ¬ i.val < (fourValueRows k).length-2 := fun hi => h' ⟨Nat.le_of_not_gt h,hi⟩
      (seedIndex_row i h'') ▸ fourValueSeedHigh k (seedIndex i h'') x

@[simp] theorem fourValueModel_line (s : Bool) (x : FourValueBase k) :
    fourValueLine s ((fourValueModel pick).fixed x) = fourValueSum pick s x := by
  cases s <;> rfl

theorem fourValueModel_fixedPair (i : FourValueRow k) (hi : i.val < 18) (x : FourValueBase k) :
    (fourValueModel pick).privateOutput x i = fourValueFixedPair pick i hi x := dif_pos hi

theorem fourValueModel_fixedHigh (i : FourValueRow k) (hi : i.val < 18) (x : FourValueBase k) :
    (fourValueModel pick).high x i = fourValueFixedHigh pick i hi x := dif_pos hi

theorem fourValueModel_wangPair (w : WangDigitRow k) (x : FourValueBase k) :
    (fourValueModel pick).privateOutput x (wangDigitRow w) = wangModelPrivate pick w x := by
  have hw := isWangRow_digit w
  dsimp only [fourValueModel]
  rw [dif_neg (not_lt.mpr hw.1),dif_pos hw]
  have he : wangRowOf (wangDigitRow w) hw = w := Fin.ext (Nat.add_sub_cancel_left 18 _)
  have castSame (u : WangDigitRow k) (eq : wangDigitRow u = wangDigitRow w) (hu : u = w) :
      (eq ▸ wangModelPrivate pick u x) = wangModelPrivate pick w x := by
    subst u
    rfl
  exact castSame _ _ he

theorem fourValueModel_wangHigh (w : WangDigitRow k) (x : FourValueBase k) :
    (fourValueModel pick).high x (wangDigitRow w) = wangModelHigh pick w x := by
  have hw := isWangRow_digit w
  dsimp only [fourValueModel]
  rw [dif_neg (not_lt.mpr hw.1),dif_pos hw]
  have he : wangRowOf (wangDigitRow w) hw = w := Fin.ext (Nat.add_sub_cancel_left 18 _)
  have castSame (u : WangDigitRow k) (eq : wangDigitRow u = wangDigitRow w) (hu : u = w) :
      (eq ▸ wangModelHigh pick u x) = wangModelHigh pick w x := by
    subst u
    rfl
  exact castSame _ _ he

private theorem seedRow_not_wang (t : Fin 2) : ¬ IsWangRow (fourValueSeedRow k t) := by
  intro h
  have he : (fourValueRows k).length-2+t.val < (fourValueRows k).length-2 := h.2
  omega

private theorem seedRow_not_fixed (t : Fin 2) : ¬ (fourValueSeedRow k t).val < 18 := by
  rw [fourValueSeedRow_val]
  omega

private theorem seedIndex_self (t : Fin 2)
    (h : ¬ (fourValueSeedRow k t).val < (fourValueRows k).length-2) :
    seedIndex (fourValueSeedRow k t) h = t :=
  Fin.ext (Nat.add_sub_cancel_left _ _)

theorem fourValueModel_seedPair (t : Fin 2) (x : FourValueBase k) :
    (fourValueModel pick).privateOutput x (fourValueSeedRow k t) = fourValueSeedPair k t x := by
  dsimp only [fourValueModel]
  rw [dif_neg (seedRow_not_fixed t),dif_neg (seedRow_not_wang t)]
  have castSame (u : Fin 2) (e : fourValueSeedRow k u = fourValueSeedRow k t) (he : u = t) :
      (e ▸ fourValueSeedPair k u x) = fourValueSeedPair k t x := by subst u; rfl
  exact castSame _ _ (seedIndex_self t _)

theorem fourValueModel_seedHigh (t : Fin 2) (x : FourValueBase k) :
    (fourValueModel pick).high x (fourValueSeedRow k t) = fourValueSeedHigh k t x := by
  dsimp only [fourValueModel]
  rw [dif_neg (seedRow_not_fixed t),dif_neg (seedRow_not_wang t)]
  have castSame (u : Fin 2) (e : fourValueSeedRow k u = fourValueSeedRow k t) (he : u = t) :
      (e ▸ fourValueSeedHigh k u x) = fourValueSeedHigh k t x := by subst u; rfl
  exact castSame _ _ (seedIndex_self t _)

theorem fourValueModel_fixed_tiles (i : FourValueRow k) (hi : i.val < 18) :
    Tiles ((compactCodes (sharedEnvironment (fourValueRows k) i)
      ((tailSlopes k).getD i 0)).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) (fourValueModel pick))) := by
  apply fourValue_fixed_complete i hi _ (pick.fixed i hi)
  · intro x
    rw [fixedUseful_point_fixed i hi,fourValueModel_fixedPair pick i hi]
    exact (adjustFirst (b:=FixedB i) (fourValueFirst_fixed i hi)).apply_symm_apply _
  · exact fourValueModel_fixedHigh pick i hi

theorem fourValueModel_seed_tiles (t : Fin 2) :
    fourValueSeedDeck k t (fourValueModel pick) (fourValueSeedRaw k t) :=
  fourValueSeedRaw_complete k t _ (fourValueModel_seedPair pick t) (fourValueModel_seedHigh pick t)
    (fun _ => rfl)

private theorem wangModelPair_eq (w : WangDigitRow k) {x y : FourValueBase k}
    (hx : wangLineValue w x.1 = wangLineValue w y.1)
    (hl : x.2 (wangDigitRow w) = y.2 (wangDigitRow w)) :
    wangModelPair pick w x = wangModelPair pick w y := by
  unfold wangModelPair
  rw [hx,hl]

private theorem contribution_eq (s : Bool) (w : WangDigitRow k) {x y : FourValueBase k}
    (hx : x.1.2+(if s then 0 else 2)*x.1.1 = y.1.2+(if s then 0 else 2)*y.1.1)
    (hl : x.2 (wangDigitRow w) = y.2 (wangDigitRow w)) :
    fourValueContribution pick s w x = fourValueContribution pick s w y := by
  unfold fourValueContribution
  split_ifs with h
  · have he : (if w.val < k then (0 : ℤ) else 2) = if s then 0 else 2 := by
      rw [← h]
      simp [wangSlopeFactor]
    rw [wangModelPair_eq pick w (by simpa only [wangLineValue,he] using hx) hl]
  · rfl

theorem fourValueModel_wang_tiles (w : WangDigitRow k) :
    Tiles ((fourValueWangActivation k w).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) (fourValueModel pick))) := by
  apply fourValue_wang_complete w
  intro x
  let s := wangSlopeFactor w
  let off := ∑ u ∈ Finset.univ.erase w, fourValueContribution pick s u x
  refine ⟨pick.wang w (wangLineValue w x.1),joinWangUseful w (off,0),fun v => ?_⟩
  dsimp only
  let y := wangActivationSource w x v
  have hy := wangLineValue_source w x v
  have hy' : y.1.2+(if s then 0 else 2)*y.1.1 = x.1.2+(if s then 0 else 2)*x.1.1 := by
    by_cases h : w.val < k <;> simpa [s,wangSlopeFactor,wangLineValue,h] using hy
  have hoff : ∑ u ∈ Finset.univ.erase w, fourValueContribution pick s u y = off := by
    apply Finset.sum_congr rfl
    intro u hu
    exact contribution_eq pick s u hy' (wangActivationSource_other w x v (wangDigitRow u) (by
      intro h
      apply (Finset.mem_erase.mp hu).1
      exact Fin.ext (by have := congrArg Fin.val h; simpa [wangDigitRow] using this)))
  constructor
  · rw [wangActivationProjection_point,fourValueModel_line,fourValueModel_wangPair]
    unfold fourValueSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ w),hoff]
    have hself : fourValueContribution pick s w y = (wangModelPair pick w y).1 := by
      simp [fourValueContribution,s]
    rw [hself]
    change joinWangUseful w (off+(wangModelPair pick w y).1,(wangModelPair pick w y).2) = _
    rw [show (off+(wangModelPair pick w y).1,(wangModelPair pick w y).2) =
      wangModelPair pick w y + (off,0) from
        Prod.ext (add_comm _ _) (add_zero _).symm]
    rw [map_add]
    unfold wangModelPair
    rw [AddEquiv.apply_symm_apply,hy]
  · rw [fourValueModel_wangHigh]
    unfold wangModelHigh
    rw [hy]

private theorem fourValueSeedPair_eq (t : Fin 2) {v w : FourValueBase k}
    (hx : SharedSeed.residue seedModel.system v.1 = SharedSeed.residue seedModel.system w.1)
    (hl : v.2 (fourValueSeedRow k t) = w.2 (fourValueSeedRow k t)) :
    fourValueSeedPair k t v = fourValueSeedPair k t w := by
  unfold fourValueSeedPair
  rw [hx]
  change (fourValueSeedPairToModel k t).symm (seedUseful modelE t _
       (fourValueSeedLowToModel k t (v.2 (fourValueSeedRow k t)))) =
    (fourValueSeedPairToModel k t).symm (seedUseful modelE t _
       (fourValueSeedLowToModel k t (w.2 (fourValueSeedRow k t))))
  rw [hl]

theorem fourValueModel_dependence : HasFourValueDependence k (tailSlopes k) (fourValueModel pick) := by
  constructor
  · intro i j hne v
    let u := v - lowStep (fourValueLayout k) j
    have h₁ : u.1 = v.1 := by simp [u,lowStep]
    have h₂ : u.2 i = v.2 i := by
      change v.2 i - Function.update (0 : ∀ i : FourValueRow k, FourValueLow i) j 1 i = v.2 i
      simp [Function.update_of_ne hne.symm]
    change (fourValueModel pick).privateOutput u i = _
    by_cases hi : i.val < 18
    · rw [fourValueModel_fixedPair pick i hi,fourValueModel_fixedPair pick i hi]
      unfold fourValueFixedPair
      rw [h₁,h₂]
    · by_cases hw : IsWangRow i
      · rw [← wangRowOf_eq i hw] at h₂ ⊢
        simp only [fourValueModel_wangPair,wangModelPrivate]
        rw [wangModelPair_eq pick _ (congrArg _ h₁) h₂]
      · let re : ¬ i.val < (fourValueRows k).length-2 := fun h => hw ⟨by omega,h⟩
        rw [← seedIndex_row i re] at h₂ ⊢
        simp only [fourValueModel_seedPair]
        exact fourValueSeedPair_eq _ (congrArg (SharedSeed.residue seedModel.system) h₁) h₂
  · intro i hi v
    let u := v - (((1,-((tailSlopes k).getD i.val 0 : ℤ)) : Plane),0)
    have h₁ : fourValueLineValue i u.1 = fourValueLineValue i v.1 := by
      unfold fourValueLineValue u
      dsimp
      ring
    have h₂ : u.2 = v.2 := sub_zero _
    change (fourValueModel pick).privateOutput u i = _
    by_cases hf : i.val < 18
    · rw [fourValueModel_fixedPair pick i hf,fourValueModel_fixedPair pick i hf]
      unfold fourValueFixedPair
      rw [h₁,h₂]
    · let w := wangRowOf i ⟨Nat.le_of_not_gt hf,hi⟩
      have hw : wangDigitRow w = i := wangRowOf_eq i _
      rw [← hw,fourValueModel_wangPair,fourValueModel_wangPair]
      have hl (y : Plane) : wangLineValue w y = fourValueLineValue i y := by
        rw [← hw]
        unfold fourValueLineValue wangLineValue
        rw [wangDigitRow_slope]
        split <;> rfl
      simp only [wangModelPrivate]
      rw [wangModelPair_eq pick w (by rw [hl,hl,h₁]) (congrFun h₂ _)]
  · intro t v
    rw [fourValueModel_seedPair,fourValueModel_seedPair]
    apply fourValueSeedPair_eq
    · have hn : (35 : ZMod residueModulus) = 0 := by
        exact (ZMod.natCast_eq_zero_iff 35 _).mpr
          (by rw [residueModulus_value]; exact dvd_refl 35)
      apply Prod.ext <;> simp [SharedSeed.residue,Int.cast_sub,hn]
    · change v.2 (fourValueSeedRow k t) - 0 = _
      simp
  · intro t v
    rw [fourValueModel_seedPair,fourValueModel_seedPair]
    apply fourValueSeedPair_eq
    · have hn : (35 : ZMod residueModulus) = 0 := by
        exact (ZMod.natCast_eq_zero_iff 35 _).mpr
          (by rw [residueModulus_value]; exact dvd_refl 35)
      apply Prod.ext <;> simp [SharedSeed.residue,Int.cast_sub,hn]
    · change v.2 (fourValueSeedRow k t) - 0 = _
      simp
  · intro s v
    simp only [fourValueModel_line,fourValueSum]
    apply Finset.sum_congr rfl
    intro i _
    apply contribution_eq pick s i
    · cases s <;> simp <;> ring
    · change v.2 (wangDigitRow i) - 0 = _
      simp

theorem fourValueModel_fixed_active (i : FourValueRow k) (hi : i.val < 18)
    (x : Plane) (j : FourValueLabel i) :
    DigitActive (fourValuePrivateAt (fourValueModel pick) x i) (fourValueDigitSubgroup i j) ↔
      j = pick.fixed i hi (fourValueLineValue i x) := by
  let v := pick.fixed i hi (fourValueLineValue i x)
  have hp (d : FourValueLow i) : fourValuePrivateAt (fourValueModel pick) x i d =
      (adjustFirst (fourValueFirst_fixed i hi)).symm ((fourValueFixedBlocks i hi v).C d) := by
    unfold fourValuePrivateAt
    rw [fourValueModel_fixedPair pick i hi]
    simp only [fourValueFixedPair,Function.update_self,v] <;> rfl
  constructor
  · rintro ⟨a,b,hd,hn⟩
    by_contra hq
    apply hn
    have h := (fourValueDigitSubgroup_sub i j a b).mp hd v (Ne.symm hq)
    rw [hp,hp,fourValueFixedBlocks_C,fourValueFixedBlocks_C,h]
  · intro h
    obtain ⟨a,b,hd,hn⟩ := (fourValueFixedBlocks_active i hi v j).mpr h
    refine ⟨a,b,hd,?_⟩
    rw [hp,hp]
    exact fun e => hn (congrArg Prod.snd ((adjustFirst (fourValueFirst_fixed i hi)).symm.injective e))

theorem fourValueModel_seed_active (t : Fin 2) (x : Plane) :
    DigitActive (fourValuePrivateAt (fourValueModel pick) x (fourValueSeedRow k t)) ⊤ ↔
      SharedSeed.residue seedModel.system x ∈ seedActiveRegion seedModel.system t := by
  let i := fourValueSeedRow k t
  let e := fourValueSeedLowToModel k t
  let f := fourValueSeedPairToModel k t
  let R := SharedSeed.residue seedModel.system x
  have hPair (u : FourValueLow i) :
      fourValuePrivateAt (fourValueModel pick) x i u = f.symm (seedUseful modelE t R (e u)) := by
    unfold fourValuePrivateAt
    rw [fourValueModel_seedPair]
    simp only [fourValueSeedPair,fourValueSeedInput,Function.update_self,f,e,i,R]
  rw [← seedUseful_active_iff modelE t]
  have hu (z : K modelE (.inr t)) : z ∈ digitSubgroup modelE (.inr t) () :=
    fun j hj => (hj (by change j = (() : Unit); cases j; rfl)).elim
  constructor
  · rintro ⟨a,b,_,hn⟩
    refine ⟨e a,e b,hu _,?_⟩
    intro h
    exact hn (by rw [hPair,hPair,h])
  · rintro ⟨a,b,_,hn⟩
    refine ⟨e.symm a,e.symm b,AddSubgroup.mem_top _,?_⟩
    rw [hPair,hPair,e.apply_symm_apply,e.apply_symm_apply]
    exact fun he => hn (f.symm.injective he)

end
end TranslationTiling.FiniteCompiler.Packed
