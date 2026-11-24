import TranslationTiling.FiniteCompiler.Effective.FourValuePatterns

namespace TranslationTiling.FiniteCompiler.Packed

open Effective Compiler.Effective SharedCoordinates PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance fourValueColumnFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxHeartbeats 3000000
set_option maxRecDepth 2500

private theorem digitActive_top_iff {K A : Type*} [AddGroup K] (g : K → A) :
    DigitActive g ⊤ ↔ ¬ ∃ t, ∀ d, g d = t := by
  constructor
  · rintro ⟨a,b,_,hab⟩ ⟨t,ht⟩
    exact hab ((ht a).trans (ht b).symm)
  · intro h
    by_contra hn
    exact h ⟨g 0,fun d => (not_digitActive_iff _ _).mp hn d 0 (AddSubgroup.mem_top _)⟩

private theorem digitActive_of_eq_iff {K A B : Type*} [AddGroup K]
    (g : K → A) (h : K → B) (U : AddSubgroup K)
    (he : ∀ a b, g a = g b ↔ h a = h b) :
    DigitActive g U ↔ DigitActive h U := by
  constructor <;> rintro ⟨a,b,hu,hn⟩
  · exact ⟨a,b,hu,fun hh => hn ((he a b).mpr hh)⟩
  · exact ⟨a,b,hu,fun hh => hn ((he a b).mp hh)⟩

theorem read_injective_of_fixed {k : ℕ} (i : FourValueRow k) (v : ℕ) (hi : ¬ IsWangRow i) :
    Function.Injective (fourValueCycleRead i v (fun h => (hi h).elim)) := by
  have h : fourValueCycleModulus i v = (fourValueLayout k).secondSize i := if_neg hi
  have e (x : ZMod ((fourValueLayout k).secondSize i)) :
      ZMod.castHom (fourValueCycleModulus_dvd i v (fun h => (hi h).elim)) _ x =
        (ZMod.ringEquivCongr h).symm x := by
    have : NeZero ((fourValueLayout k).secondSize i) := inferInstance
    rw [← ZMod.natCast_zmod_val x,map_natCast,map_natCast]
  rintro ⟨a,b⟩ ⟨c,d⟩ hh
  have hb := congrArg Prod.snd hh
  have ha : a = c := congrArg Prod.fst hh
  exact Prod.ext ha
    ((ZMod.ringEquivCongr h).symm.injective ((e b).symm.trans (hb.trans (e d))))

theorem cycle_active_fixed_iff {k : ℕ} (i : FourValueRow k) (v : FourValueLabel i)
    (hi : ¬ IsWangRow i) (o : FourValueOutputGraph k) (x : Plane) :
    DigitActive (fun d => fourValueCycleRead i v.val (fun h => (hi h).elim) (fourValuePrivateAt o x i d))
        (fourValueCycleSubgroup i v.val (fun _ => v.isLt)) ↔
      DigitActive (fourValuePrivateAt o x i) (fourValueDigitSubgroup i v) := by
  rw [fourValueCycleSubgroup,dif_neg hi]
  apply digitActive_of_eq_iff
  intro a b
  exact (read_injective_of_fixed i _ hi).eq_iff

theorem wangRead_label {k : ℕ} (w : WangDigitRow k) (v : Fin 4)
    (p : SharedCoordinates.Useful (fourValueLayout k) (wangDigitRow w)) :
    let h := show fourValueCycleModulus (wangDigitRow w) v.val = wangValueModulus w (labelIndex v) by
      rw [fourValueCycleModulus,ite_eq_left (isWangRow_digit w),wangValueModulus_label]
      simp [wangDigitRow]
    ZMod.ringEquivCongr h ((fourValueCycleRead (wangDigitRow w) v.val (fun _ => v.isLt) p).2) =
      joinWangUseful w (0,p.2) (labelIndex v) := by
  dsimp only
  obtain ⟨a,b⟩ := p
  conv_lhs => rw [← ZMod.natCast_zmod_val b]
  conv_rhs => rw [← ZMod.natCast_zmod_val b]
  rw [← joinWangUseful_nonzero w (labelIndex v) (labelIndex_ne v)
    ((b.val : ℕ) : ZMod (sharedPrime (wangSlopeFactor w)))]
  rw [joinWangUseful_natCast]
  change ZMod.ringEquivCongr _ (ZMod.castHom (fourValueCycleModulus_dvd (wangDigitRow w) v.val
    (fun _ => v.isLt)) (ZMod (fourValueCycleModulus (wangDigitRow w) v.val)) (Nat.cast b.val)) = _
  rw [map_natCast,map_natCast]

theorem cycle_active_wang_iff {k : ℕ} (w : WangDigitRow k) (v : Fin 4)
    (o : FourValueOutputGraph k) (x : Plane) :
    DigitActive (fun d => fourValueCycleRead (wangDigitRow w) v.val (fun _ => v.isLt)
      (fourValuePrivateAt o x (wangDigitRow w) d))
        (fourValueCycleSubgroup (wangDigitRow w) v.val (fun h => (h (isWangRow_digit w)).elim)) ↔
      ¬ ∃ t, ∀ d, joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) (labelIndex v) = t := by
  rw [fourValueCycleSubgroup,dif_pos (isWangRow_digit w),← digitActive_top_iff]
  apply digitActive_of_eq_iff
  intro a b
  let f := fourValuePrivateAt o x (wangDigitRow w)
  have hs : (fourValueLayout k).firstSize (wangDigitRow w) = 1 := by
    change sharedObservedA (fourValueRows k) (wangDigitRow w) = 1
    exact ite_eq_left (isWangRow_digit w)
  haveI : Subsingleton (ZMod ((fourValueLayout k).firstSize (wangDigitRow w))) := by
    rw [hs]
    infer_instance
  rw [← wangRead_label w v (f a),← wangRead_label w v (f b)]
  constructor
  · intro h
    exact congrArg _ (congrArg Prod.snd h)
  · intro h
    exact Prod.ext (Subsingleton.elim _ _) ((ZMod.ringEquivCongr _).injective h)

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance fourValueColumnAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
local notation "S" => fourValueRefinement hk c

theorem fourValueColumn_arity (i : Column (S).system) :
    (radixLayoutProfile 4 k).arity i.val = if i.val < 9 then 4 else if i.val < 18 then 6 else 4 := by
  have h : i.val < (S).width := i.isLt
  rw [tailRefinement_width] at h
  exact radixLayout_arity hk (by simpa using h)

theorem fourValueColumn_valid_wang (i : Column (S).system) (v : Letter (S).system i)
    (h : IsWangRow (fourValueColumnRow hk c i)) : v.val < 4 := by
  have hf : 18 ≤ i.val := h.1
  have ho := v.isLt
  change v.val < (radixLayoutProfile 4 k).arity i.val at ho
  rwa [fourValueColumn_arity hk c i,if_neg (by omega),if_neg (by omega)] at ho

theorem fourValueColumn_valid_fixed (i : Column (S).system) (v : Letter (S).system i)
    (h : ¬ IsWangRow (fourValueColumnRow hk c i)) :
    v.val < (rowDigits (fourValueRows k) (fourValueColumnRow hk c i)).length := by
  have hfix : i.val < 18 := by
    by_contra! he
    exact h ⟨he,fourValueColumnRow_lt hk c i⟩
  rw [fourValueColumnRow_val,fourValueRows_arity hk i.val hfix]
  exact v.isLt

def fourValueColumnActive (o : FourValueOutputGraph k) (i : Column (S).system)
    (v : Letter (S).system i) (x : Plane) : Prop :=
  let j := fourValueColumnRow hk c i
  DigitActive (fun d => fourValueCycleRead j v.val (fourValueColumn_valid_wang hk c i v)
    (fourValuePrivateAt o x j d))
    (fourValueCycleSubgroup j v.val (fourValueColumn_valid_fixed hk c i v))

theorem fourValueColumn_at (i : Column (S).system) (x : Plane) :
    x.2 + ((tailSlopes k).getD (fourValueColumnRow hk c i).val 0 : ℤ)*x.1 =
      lineValue (S).system i x := by
  unfold lineValue
  rw [fourValueColumn_slope hk c i,fourValueColumnRow_val]

theorem fourValueColumn_active_line (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o) (i : Column (S).system)
    (v : Letter (S).system i) (x : Plane) :
    fourValueColumnActive hk c o i v x ↔
      fourValueColumnActive hk c o i v (0,lineValue (S).system i x) := by
  dsimp only [fourValueColumnActive]
  have h : fourValuePrivateAt o x (fourValueColumnRow hk c i) =
      fourValuePrivateAt o (0,lineValue (S).system i x) (fourValueColumnRow hk c i) := by
    funext d
    apply hd.privateAt_line _ (fourValueColumnRow_lt hk c i)
    simpa only [Int.mul_zero,add_zero] using fourValueColumn_at hk c i x
  rw [h]

theorem fourValueColumn_fixed_activity (o : FourValueOutputGraph k) (i : Column (S).system)
    (v : Letter (S).system i) (x : Plane) (h : i.val < 18) :
    fourValueColumnActive hk c o i v x ↔
      DigitActive (fourValuePrivateAt o x (fourValueColumnRow hk c i))
        (fourValueDigitSubgroup _ ⟨v.val,fourValueColumn_valid_fixed hk c i v (fun he => by
          have hf : 18 ≤ i.val := he.1
          omega)⟩) := by
  let j := fourValueColumnRow hk c i
  have hn : ¬ IsWangRow j := fun hh => (not_le_of_gt h) hh.1
  exact cycle_active_fixed_iff j ⟨v.val,fourValueColumn_valid_fixed hk c i v hn⟩ hn o x

attribute [local irreducible] wangValueModulus fourValueOutput

theorem fourValueColumn_wang_activity (o : FourValueOutputGraph k) (i : Column (S).system)
    (v : Letter (S).system i) (x : Plane) (h : 18 ≤ i.val) :
    let j := fourValueColumnRow hk c i
    let hw : IsWangRow j := ⟨h,fourValueColumnRow_lt hk c i⟩
    let w := wangRowOf j hw
    let u : Fin 4 := ⟨v.val,fourValueColumn_valid_wang hk c i v hw⟩
    fourValueColumnActive hk c o i v x ↔
      ¬ ∃ t, ∀ d, joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) (labelIndex u) = t := by
  dsimp only
  let j := fourValueColumnRow hk c i
  let hw : IsWangRow j := ⟨h,fourValueColumnRow_lt hk c i⟩
  let w := wangRowOf j hw
  have aux (a : FourValueRow k) (ha : a = wangDigitRow w)
      (hv : v.val < 4) :
      DigitActive (fun d => fourValueCycleRead a v.val (fun _ => hv) (fourValuePrivateAt o x a d))
          (fourValueCycleSubgroup a v.val (fun hn => (hn (ha.symm ▸ isWangRow_digit w)).elim)) ↔
        ¬ ∃ t, ∀ d, joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) (labelIndex ⟨v.val,hv⟩) = t := by
    subst a
    exact cycle_active_wang_iff w ⟨v.val,hv⟩ o x
  exact aux j (wangRowOf_eq j hw).symm (fourValueColumn_valid_wang hk c i v hw)

end
end TranslationTiling.FiniteCompiler.Packed
