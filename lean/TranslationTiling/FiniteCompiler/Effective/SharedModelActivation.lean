import TranslationTiling.FiniteCompiler.Effective.SharedModel
import TranslationTiling.FiniteCompiler.Effective.SharedOrdinarySoundness

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {k : ℕ} (pick : SharedPicker k)

theorem sharedBlockPair_eq (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    {v w : SharedBase k}
    (hx : sharedLineValue k i v.1 = sharedLineValue k i w.1)
    (hl : v.2 i = w.2 i) :
    sharedBlockPair pick i hi v = sharedBlockPair pick i hi w := by
  unfold sharedBlockPair
  rw [hx,hl]

theorem sharedOrdinaryPair_eq (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    {v w : SharedBase k}
    (hx : sharedLineValue k i v.1 = sharedLineValue k i w.1)
    (hl : v.2 i = w.2 i) :
    sharedOrdinaryPair pick i hi v = sharedOrdinaryPair pick i hi w := by
  unfold sharedOrdinaryPair
  rw [sharedBlockPair_eq pick i hi hx hl]

theorem sharedLineValue_wang (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (hf : 18 ≤ i.val) (x : Plane) :
    sharedLineValue k i x = x.2 + (if sharedSlope k i then 0 else 2)*x.1 := by
  unfold sharedLineValue
  rw [wangSlope_eq i hi hf]
  cases sharedSlope k i <;> rfl

theorem sharedContribution_eq (s : Bool) (i : SharedRow k) {v w : SharedBase k}
    (hx : v.1.2+(if s then 0 else 2)*v.1.1 = w.1.2+(if s then 0 else 2)*w.1.1)
    (hl : v.2 i = w.2 i) :
    sharedContribution pick s i v = sharedContribution pick s i w := by
  unfold sharedContribution
  split_ifs with h
  · have he : sharedLineValue k i v.1 = sharedLineValue k i w.1 := by
      simp only [sharedLineValue_wang i h.2.1 h.1,h.2.2,hx]
    rw [sharedBlockPair_eq pick i h.2.1 he hl]
  · rfl

theorem sharedContribution_at (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (hf : 18 ≤ i.val) (v : SharedBase k) :
    (ZMod.ringEquivCongr (ordinaryFirst_shared i hf hi))
      (sharedContribution pick (sharedSlope k i) i v) = (sharedBlockPair pick i hi v).1 := by
  unfold sharedContribution
  rw [dite_eq_left ⟨hf,hi,rfl⟩]
  exact RingEquiv.apply_symm_apply _ _

theorem sharedModel_ordinary (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) :
    Tiles ((compactCodes (sharedEnvironment (sharedRows k) i) ((tailSlopes k).getD i 0)).toFinset.image
      (decodePoint (sharedLayout k)))
      (Set.range (SharedCoordinates.point (sharedLayout k) (sharedModel pick))) := by
  let h := ordinaryPairFacts i hi
  letI : NeZero (OrdinaryA i) := ⟨h.firstPrime.ne_zero⟩
  let L := sharedLayout k
  let s := (tailSlopes k).getD i 0
  let o := sharedModel pick
  apply (sharedOrdinary_iff i hi s o).mpr
  intro x
  let src (j : SharedOrdinaryIndex i) :=
    SharedCoordinates.activationSource L i (compactOffset L i s j) j.1 x
  let v := pick i hi (sharedLineValue k i x.1)
  let D := sharedBlocks i hi v
  let f (j : SharedOrdinaryIndex i) :=
    (D.C (x.2 i-j.1) + shift (OrdinaryA i) (OrdinaryB i) j.2,
      D.T (x.1.1-(compactOffset L i s j).1) (x.2 i-j.1))
  have hbij : Function.Bijective f := sharedBlock_bijective i hi v s x.1.1 (x.2 i)
  have hx (j : SharedOrdinaryIndex i) :
      sharedLineValue k i (src j).1 = sharedLineValue k i x.1 := by
    unfold sharedLineValue
    change x.1.2 - (-(s:ℤ)*(compactOffset L i s j).1) +
      (s:ℤ)*(x.1.1-(compactOffset L i s j).1) = _
    ring
  have hl (j : SharedOrdinaryIndex i) : (src j).2 i = x.2 i - j.1 := by
    simp only [src,SharedCoordinates.activationSource,Function.update_self]
  have hc (j : SharedOrdinaryIndex i) :
      sharedBlockPair pick i hi (src j) = D.C (x.2 i-j.1) := by
    unfold sharedBlockPair
    rw [hx,hl]
  have hh (j : SharedOrdinaryIndex i) : o.high (src j) i = (f j).2 := by
    change (sharedModel pick).high (src j) i = _
    rw [sharedModel_high pick i hi]
    unfold sharedBlockHigh
    rw [hx,hl]
    rfl
  by_cases hf : i.val < 18
  · convert hbij using 2
    rename_i j
    change (_,o.high (src j) i) = f j
    rw [hh]
    have he := ordinaryUseful_point_fixed i hi hf o (src j)
    rw [he]
    change (_,_) = _
    rw [show o.privateOutput (src j) i = sharedOrdinaryPair pick i hi (src j) from
      sharedModel_pair pick i hi _]
    simp only [sharedOrdinaryPair,dite_eq_left hf,hc]
    let e := adjustFirst (b:=OrdinaryB i) (ordinaryFirst_fixed i hf)
    change ((e (e.symm (D.C (x.2 i-j.1))) + _),(f j).2) = _
    rw [e.apply_symm_apply]
  · let g := sharedSlope k i
    let e := ZMod.ringEquivCongr (ordinaryFirst_shared i (Nat.le_of_not_gt hf) hi)
    let other := ∑ a ∈ (Finset.univ : Finset (SharedRow k)).erase i,
      sharedContribution pick g a x
    have hs (j : SharedOrdinaryIndex i) : sharedSum pick g (src j) =
        other + sharedContribution pick g i (src j) := by
      unfold sharedSum
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have hne := (Finset.mem_erase.mp ha).1
      have ht : (src j).2 a = x.2 a := by
        change Function.update _ i _ a = _
        exact Function.update_of_ne hne _ _
      exact sharedContribution_eq pick g a
        (by simpa only [sharedLineValue_wang i hi (Nat.le_of_not_gt hf)] using hx j) ht
    have h' := shared_activation_add f hbij (e other)
    convert h' using 2
    rename_i j
    change (_,o.high (src j) i) = _
    rw [hh,ordinaryUseful_point_shared i hi (Nat.le_of_not_gt hf)]
    have he : o.privateOutput (src j) i = sharedOrdinaryPair pick i hi (src j) :=
      sharedModel_pair pick i hi _
    rw [he,show sharedLine g (o.fixed (src j)) = sharedSum pick g (src j) from
      sharedModel_line pick g _,hs]
    have heq : e (sharedContribution pick g i (src j)) = (sharedBlockPair pick i hi (src j)).1 :=
      sharedContribution_at pick i hi (Nat.le_of_not_gt hf) _
    refine Prod.ext ?_ (show (f j).2 = (f j).2 from rfl)
    apply Prod.ext
    · change e (other + sharedContribution pick g i (src j)) + _ = _
      rw [map_add,heq,hc]
      change e other + (D.C _).1 + _ = ((D.C _).1 + _) + e other
      abel
    · simp only [sharedOrdinaryPair,dite_eq_right hf]
      change (sharedBlockPair pick i hi (src j)).2 + _ = _
      rw [hc]
      rfl

end
end TranslationTiling.FiniteCompiler.Packed
