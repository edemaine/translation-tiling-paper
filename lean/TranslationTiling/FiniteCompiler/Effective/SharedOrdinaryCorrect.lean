import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryParameters
import TranslationTiling.FiniteCompiler.SharedActivation

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

variable {k : ℕ} (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)

abbrev RowLow (i : SharedRow k) := SharedCoordinates.Low (sharedLayout k) i
abbrev OrdinaryA (i : SharedRow k) := rowA (sharedRows k) i
abbrev OrdinaryB (i : SharedRow k) := rowB (sharedRows k) i

instance (i : SharedRow k) : NeZero (rowB (sharedRows k) i) :=
  ⟨(sharedRows_moduli_positive i.isLt).2.2.ne'⟩

theorem ordinaryUseful_point_fixed (hf : i.val < 18) (o : SharedOutput k) (x : SharedBase k) :
    ordinaryUseful i hi (SharedCoordinates.point (sharedLayout k) o x).2 =
      adjustFirst (ordinaryFirst_fixed i hf) (o.privateOutput x i) := by
  simp only [ordinaryUseful,dif_pos hf,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom]
  rfl

theorem ordinaryUseful_point_shared (hf : 18 ≤ i.val) (o : SharedOutput k) (x : SharedBase k) :
    ordinaryUseful i hi (SharedCoordinates.point (sharedLayout k) o x).2 =
      adjustFirst (ordinaryFirst_shared i hf hi)
        (sharedLine (sharedSlope k i) (o.fixed x),(o.privateOutput x i).2) := by
  simp only [ordinaryUseful,dif_neg (not_lt_of_ge hf),AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  apply congrArg (adjustFirst (b:=OrdinaryB i) (ordinaryFirst_shared i hf hi))
  generalize sharedSlope k i = s
  cases s <;> rfl

theorem ordinaryUseful_target (x : SharedBase k)
    (c : ZMod (OrdinaryA i) × ZMod (OrdinaryB i)) (d : RowLow i) :
    ∃ v : SharedCoordinates.Ambient (sharedLayout k),
      baseProjection (sharedLayout k) v = x ∧ ordinaryUseful i hi v.2 = c ∧
      highCoordinate (sharedLayout k) i v = d := by
  let L := sharedLayout k
  let β : ∀ j : SharedRow k, RowLow j := Function.update 0 i d
  suffices h : ∃ (w : Fixed) (p : ∀ j : SharedRow k, ZMod (L.firstSize j) × ZMod (L.secondSize j)),
      ordinaryUseful i hi (SharedCoordinates.point L ⟨fun _ => w,fun _ => p,fun _ => β⟩ x).2 = c by
    obtain ⟨w,p,hp⟩ := h
    exact ⟨_,baseProjection_point L _ _,hp,by rw [highCoordinate_point]; simp [β]⟩
  by_cases hf : i.val < 18
  · let e := adjustFirst (b:=OrdinaryB i) (ordinaryFirst_fixed i hf)
    refine ⟨0,Function.update 0 i (e.symm c),?_⟩
    rw [ordinaryUseful_point_fixed i hi hf]
    change e (Function.update (0 : ∀ j, ZMod (L.firstSize j) × ZMod (L.secondSize j)) i (e.symm c) i) = c
    have he : Function.update (0 : ∀ j : SharedRow k, ZMod (L.firstSize j) × ZMod (L.secondSize j))
          i (e.symm c) i = e.symm c :=
      @Function.update_self _ (fun j => ZMod (L.firstSize j) × ZMod (L.secondSize j))
        _ i (e.symm c) 0
    exact (congrArg e he).trans (e.apply_symm_apply _)
  · let s := sharedSlope k i
    let e := adjustFirst (b:=OrdinaryB i) (ordinaryFirst_shared i (Nat.le_of_not_gt hf) hi)
    let p : ∀ j : SharedRow k, ZMod (L.firstSize j) × ZMod (L.secondSize j) :=
      Function.update 0 i (0,(e.symm c).2)
    have hsurj (s' : Bool) : Function.Surjective (sharedLine s') := by
      cases s' <;> intro a
      · exact ⟨((0,0),a),rfl⟩
      · exact ⟨((0,a),0),rfl⟩
    obtain ⟨w,hw⟩ := hsurj s (e.symm c).1
    refine ⟨w,p,?_⟩
    rw [ordinaryUseful_point_shared i hi (Nat.le_of_not_gt hf)]
    change e (sharedLine s w,(p i).2) = c
    have he : p i = ((0 : ZMod (L.firstSize i)),(e.symm c).2) :=
      @Function.update_self _ (fun j => ZMod (L.firstSize j) × ZMod (L.secondSize j))
        _ i (0,(e.symm c).2) 0
    have he' : (p i).2 = (e.symm c).2 := congrArg Prod.snd he
    rw [hw,he',Prod.eta,e.apply_symm_apply]

include hi in
theorem ordinaryUseful_sep :
    ((2 : ZMod (OrdinaryA i)),(2 : ZMod (OrdinaryB i))) ≠ (-1,-1) := by
  have ha := (ordinaryPairFacts i hi).bigFirst
  letI : NeZero (OrdinaryA i) := ⟨(ordinaryPairFacts i hi).firstPrime.ne_zero⟩
  intro h
  have h' := congrArg Prod.fst h
  change (2 : ZMod (OrdinaryA i)) = -1 at h'
  have h3 : (3 : ZMod (OrdinaryA i)) = 0 := by
    linear_combination h'
  apply (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) ha)
  exact (ZMod.natCast_eq_zero_iff 3 _).mp h3

theorem sharedOrdinary_iff (s : ℕ) (o : SharedOutput k) :
    letI : NeZero (OrdinaryA i) := ⟨(ordinaryPairFacts i hi).firstPrime.ne_zero⟩
    let src := fun x j => SharedCoordinates.activationSource (sharedLayout k) i (compactOffset (sharedLayout k) i s j) j.1 x
    Tiles ((compactCodes (sharedEnvironment (sharedRows k) i) s).toFinset.image
      (decodePoint (sharedLayout k))) (Set.range (SharedCoordinates.point (sharedLayout k) o)) ↔
    ∀ x, Function.Bijective (fun j => (ordinaryUseful i hi
      (SharedCoordinates.point (sharedLayout k) o (src x j)).2 +
        shift (OrdinaryA i) (OrdinaryB i) j.2, o.high (src x j) i)) := by
  letI : NeZero (OrdinaryA i) := ⟨(ordinaryPairFacts i hi).firstPrime.ne_zero⟩
  have h := ordinaryPairFacts i hi
  unfold sharedEnvironment
  rw [← sharedLayout_order k]
  exact compactCodes_tiles_iff (sharedLayout k) (sharedLayoutCRT k) i s (ordinaryUseful i hi)
    (ordinaryUseful_decode i hi) h.firstPrime.two_le h.secondPrime.two_le h.lowFirst
    h.lowFirstSecond (ordinaryUseful_sep i hi) _ (sharedOther_membership k i) o
    (ordinaryUseful_target i hi)

end
end TranslationTiling.FiniteCompiler.Packed
