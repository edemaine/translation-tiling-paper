import TranslationTiling.FiniteCompiler.Effective.FourValueDigits
import TranslationTiling.FiniteCompiler.Effective.SharedBlockForward
import TranslationTiling.FiniteCompiler.Effective.SharedLocal

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem fixedPairFacts {k : ℕ} (i : FourValueRow k)
  (hi : i.val < 18) :
  OrdinaryPairFacts (rowA (fourValueRows k) i) (rowB (fourValueRows k) i) (rowR (fourValueRows k) i) := by
  unfold rowA rowB rowR rowDigits
  rw [fourValueRows_fixed_at hi]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (by decide +kernel : ∀ h : Fin 18, (sharedArithmeticRow h).1.Prime) ⟨i,hi⟩
  · exact (by decide +kernel : ∀ h : Fin 18, (sharedArithmeticRow h).2.1.Prime) ⟨i,hi⟩
  · exact (by decide +kernel : ∀ h : Fin 18, 3 < (sharedArithmeticRow h).1) ⟨i,hi⟩
  · exact (by decide +kernel : ∀ h : Fin 18,
      (sharedArithmeticRow h).2.2.prod.Coprime (sharedArithmeticRow h).1) ⟨i,hi⟩
  · exact (by decide +kernel : ∀ h : Fin 18,
      ((sharedArithmeticRow h).2.2.prod*(sharedArithmeticRow h).1).Coprime
        (sharedArithmeticRow h).2.1) ⟨i,hi⟩

theorem fourValueFirst_fixed {k : ℕ} (i : FourValueRow k) (hi : i.val < 18) :
    (fourValueLayout k).firstSize i = rowA (fourValueRows k) i :=
  if_neg (fun h => (not_le_of_gt hi) h.1)


def fixedUseful {k : ℕ} (i : FourValueRow k) (hi : i.val < 18) :
    FourValueFactor k →+ ZMod (rowA (fourValueRows k) i) × ZMod (rowB (fourValueRows k) i) :=
  (adjustFirst (fourValueFirst_fixed i hi)).toAddMonoidHom.comp (privateUseful (fourValueLayout k) i)

theorem fixedUseful_decode {k : ℕ} (i : FourValueRow k) (hi : i.val < 18) (n : ℕ) :
    fixedUseful i hi (decode (fourValueLayout k) n) =
      ((n : ZMod (rowA (fourValueRows k) i)),(n : ZMod (rowB (fourValueRows k) i))) := by
  simp only [fixedUseful,AddMonoidHom.comp_apply,privateUseful_decode,
    AddEquiv.coe_toAddMonoidHom]
  exact adjustFirst_natCast _ _


variable {k : ℕ} (i : FourValueRow k) (hi : i.val < 18)

abbrev FourValueLow (i : FourValueRow k) := SharedCoordinates.Low (fourValueLayout k) i
abbrev FixedA (i : FourValueRow k) := rowA (fourValueRows k) i
abbrev FixedB (i : FourValueRow k) := rowB (fourValueRows k) i

instance (i : FourValueRow k) : NeZero (rowB (fourValueRows k) i) :=
  ⟨(fourValueModuli_positive i).2.2.ne'⟩

theorem fixedUseful_point_fixed (o : FourValueOutputGraph k) (x : FourValueBase k) :
    fixedUseful i hi (SharedCoordinates.point (fourValueLayout k) o x).2 =
      adjustFirst (fourValueFirst_fixed i hi) (o.privateOutput x i) := by
  simp only [fixedUseful,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom]
  rfl

theorem fixedUseful_target (x : FourValueBase k)
    (c : ZMod (FixedA i) × ZMod (FixedB i)) (d : FourValueLow i) :
    ∃ v : SharedCoordinates.Ambient (fourValueLayout k),
      baseProjection (fourValueLayout k) v = x ∧ fixedUseful i hi v.2 = c ∧
      highCoordinate (fourValueLayout k) i v = d := by
  let L := fourValueLayout k
  let β : ∀ j : FourValueRow k, FourValueLow j := Function.update 0 i d
  suffices h : ∃ (w : Fixed) (p : ∀ j : FourValueRow k, ZMod (L.firstSize j) × ZMod (L.secondSize j)),
      fixedUseful i hi (SharedCoordinates.point L ⟨fun _ => w,fun _ => p,fun _ => β⟩ x).2 = c by
    obtain ⟨w,p,hp⟩ := h
    exact ⟨_,baseProjection_point L _ _,hp,by rw [highCoordinate_point]; simp [β]⟩
  let e := adjustFirst (b:=FixedB i) (fourValueFirst_fixed i hi)
  refine ⟨0,Function.update 0 i (e.symm c),?_⟩
  rw [fixedUseful_point_fixed i hi]
  change e (Function.update (0 : ∀ j, ZMod (L.firstSize j) × ZMod (L.secondSize j)) i (e.symm c) i) = c
  have he : Function.update (0 : ∀ j : FourValueRow k, ZMod (L.firstSize j) × ZMod (L.secondSize j))
        i (e.symm c) i = e.symm c :=
    @Function.update_self _ (fun j => ZMod (L.firstSize j) × ZMod (L.secondSize j))
      _ i (e.symm c) 0
  exact (congrArg e he).trans (e.apply_symm_apply _)

include hi in
theorem fixedUseful_sep :
    ((2 : ZMod (FixedA i)),(2 : ZMod (FixedB i))) ≠ (-1,-1) := by
  have ha := (fixedPairFacts i hi).bigFirst
  letI : NeZero (FixedA i) := ⟨(fixedPairFacts i hi).firstPrime.ne_zero⟩
  intro h
  have h' := congrArg Prod.fst h
  change (2 : ZMod (FixedA i)) = -1 at h'
  have h3 : (3 : ZMod (FixedA i)) = 0 := by
    linear_combination h'
  apply (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) ha)
  exact (ZMod.natCast_eq_zero_iff 3 _).mp h3

theorem fourValueFixed_iff (s : ℕ) (o : FourValueOutputGraph k) :
    letI : NeZero (FixedA i) := ⟨(fixedPairFacts i hi).firstPrime.ne_zero⟩
    let src := fun x j => SharedCoordinates.activationSource (fourValueLayout k) i (compactOffset (fourValueLayout k) i s j) j.1 x
    Tiles ((compactCodes (sharedEnvironment (fourValueRows k) i) s).toFinset.image
      (decodePoint (fourValueLayout k))) (Set.range (SharedCoordinates.point (fourValueLayout k) o)) ↔
    ∀ x, Function.Bijective (fun j => (fixedUseful i hi
      (SharedCoordinates.point (fourValueLayout k) o (src x j)).2 +
        shift (FixedA i) (FixedB i) j.2, o.high (src x j) i)) := by
  letI : NeZero (FixedA i) := ⟨(fixedPairFacts i hi).firstPrime.ne_zero⟩
  have h := fixedPairFacts i hi
  unfold sharedEnvironment
  rw [← fourValueLayout_order k]
  exact compactCodes_tiles_iff (fourValueLayout k) (fourValueLayoutCRT k) i s (fixedUseful i hi)
    (fixedUseful_decode i hi) h.firstPrime.two_le h.secondPrime.two_le h.lowFirst
    h.lowFirstSecond (fixedUseful_sep i hi) _ (fourValueOther_membership k i) o
    (fixedUseful_target i hi)


include hi in
theorem fourValueDigit_representation (j : FourValueLabel i) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ fourValueDigit i j = A*FixedA i+B*FixedB i := by
  let ds := rowDigits (fourValueRows k) i
  have hm : ds[j.val] ∈ ds := List.getElem_mem j.isLt
  have haux : fourValueDigit i j = ds[j.val] := rfl
  rw [haux]
  generalize hd : ds[j.val] = d at hm ⊢
  change d ∈ ((fourValueRows k).getD i.val (0,0,[])).2.2 at hm
  unfold FixedA FixedB rowA rowB
  rw [fourValueRows_fixed_at hi] at hm ⊢
  change d ∈ (profile1.row i.val).map Prod.fst at hm
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  have h := (profile1_valid.2.2.2.2.1 i.val
    (List.mem_range.mpr (by have hw : profile1.width = 20 := rfl; omega))).2 v hv
  exact ⟨v.2.1,v.2.2,h⟩

def fourValueFixedBlockCount (j : FourValueLabel i) : ℕ × ℕ :=
  ((fourValueDigit_representation i hi j).choose,
    (fourValueDigit_representation i hi j).choose_spec.choose)

theorem fourValueFixedBlockCount_spec (j : FourValueLabel i) :
    let c := fourValueFixedBlockCount i hi j
    0 < c.1 ∧ 0 < c.2 ∧ fourValueDigit i j = c.1*FixedA i + c.2*FixedB i :=
  (fourValueDigit_representation i hi j).choose_spec.choose_spec

def fourValueFixedBaseBlocks (j : FourValueLabel i) : LabeledBlocks (ZMod (fourValueDigit i j))
    (Fin (fourValueFixedBlockCount i hi j).1) (Fin (fourValueFixedBlockCount i hi j).2)
    (FixedA i) (FixedB i) := by
  letI : NeZero (FixedA i) := ⟨(fixedPairFacts i hi).firstPrime.ne_zero⟩
  letI : NeZero (fourValueDigit i j) := ⟨(fourValueDigit_prime i j).ne_zero⟩
  exact LabeledBlocks.digit _ _ _ _ _ (fourValueFixedBlockCount_spec i hi j).2.2

abbrev FourValueOtherDigits (j : FourValueLabel i) :=
  ∀ q : {q : FourValueLabel i // q ≠ j}, ZMod (fourValueDigit i q)

def fourValueFixedBlocks (j : FourValueLabel i) :
    LabeledBlocks (FourValueLow i) (Fin (fourValueFixedBlockCount i hi j).1 × FourValueOtherDigits i j)
      (Fin (fourValueFixedBlockCount i hi j).2 × FourValueOtherDigits i j) (FixedA i) (FixedB i) :=
  (LabeledBlocks.onCoordinate (fun q => ZMod (fourValueDigit i q)) j (fourValueFixedBaseBlocks i hi j)).transport
    (fourValueDigitCRT i).toEquiv

@[simp] theorem fourValueFixedBlocks_C (j : FourValueLabel i) (w : FourValueLow i) :
    (fourValueFixedBlocks i hi j).C w = (fourValueFixedBaseBlocks i hi j).C (fourValueDigitCRT i w j) := by
  simp [fourValueFixedBlocks]

theorem fourValueFixedBlocks_active (j q : FourValueLabel i) :
    DigitActive (fun w => ((fourValueFixedBlocks i hi j).C w).2) (fourValueDigitSubgroup i q) ↔ q = j := by
  constructor
  · rintro ⟨w,w',hw,hn⟩
    by_contra hj
    apply hn
    simp only [fourValueFixedBlocks_C]
    rw [(fourValueDigitSubgroup_sub i q w w').mp hw j (Ne.symm hj)]
  · intro h
    subst q
    let c : Fin (fourValueFixedBlockCount i hi j).2 := ⟨0,(fourValueFixedBlockCount_spec i hi j).2.1⟩
    obtain ⟨u,hu⟩ := (fourValueFixedBaseBlocks i hi j).privateOutput_surjective c 0
    obtain ⟨v,hv⟩ := (fourValueFixedBaseBlocks i hi j).privateOutput_surjective c 1
    let U := (fourValueDigitCRT i).symm (Pi.single j u)
    let V := (fourValueDigitCRT i).symm (Pi.single j v)
    refine ⟨U,V,(fourValueDigitSubgroup_sub i j U V).mpr ?_,?_⟩
    · intro l hl
      simp [U,V,Pi.single_eq_of_ne hl]
    · letI : Fact (1 < FixedB i) := ⟨(fixedPairFacts i hi).secondPrime.one_lt⟩
      simpa [U,V,hu,hv] using (zero_ne_one : (0 : ZMod (FixedB i)) ≠ 1)


include hi in
theorem fixedB_ne_two : FixedB i ≠ 2 := by
  unfold FixedB rowB
  rw [fourValueRows_fixed_at hi]
  exact (by decide +kernel : ∀ j : Fin 18, (sharedArithmeticRow j).2.1 ≠ 2) ⟨i,hi⟩

private theorem twoUnit {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    IsUnit (2 : ZMod p) :=
  (ZMod.isUnit_iff_coprime 2 p).mpr ((Nat.coprime_primes Nat.prime_two hp).mpr hne.symm)

abbrev FourValueFixedIndex (i : FourValueRow k) :=
  OrdinaryIndex ((fourValueLayout k).lowSize i) (FixedA i) (FixedB i)

theorem fourValueFixedBlock_bijective (j : FourValueLabel i) (s : ℕ) (x : ℤ) (l : FourValueLow i) :
    letI : NeZero (FixedA i) := ⟨(fixedPairFacts i hi).firstPrime.ne_zero⟩
    Function.Bijective (fun u : FourValueFixedIndex i =>
      ((fourValueFixedBlocks i hi j).C (l-u.1) + shift (FixedA i) (FixedB i) u.2,
       (fourValueFixedBlocks i hi j).T (x-(compactOffset (fourValueLayout k) i s u).1) (l-u.1))) := by
  let h := fixedPairFacts i hi
  letI : NeZero (FixedA i) := ⟨h.firstPrime.ne_zero⟩
  letI : NeZero (rowR (fourValueRows k) i) := ⟨(fourValueModuli_positive i).1.ne'⟩
  let S := BlockShiftData.compact h.firstPrime.two_le h.secondPrime.two_le
    (twoUnit h.firstPrime (Nat.ne_of_gt (lt_trans (by decide : 2 < 3) h.bigFirst)))
    (twoUnit h.secondPrime (fixedB_ne_two i hi))
  let H (u : FourValueFixedIndex i) : ℤ := (compactOffset (fourValueLayout k) i s u).1
  let B := fourValueFixedBlocks i hi j
  have hA (u : FourValueFixedIndex i) : (H u : ZMod (FixedA i)) = S.rhoA u.2 :=
    congrArg (fun v : (FourValueLow i × ZMod (FixedA i)) × ZMod (FixedB i) => v.1.2)
      (compactFirst_residues h.lowFirst h.lowFirstSecond u)
  have hB (u : FourValueFixedIndex i) : (H u : ZMod (FixedB i)) = S.rhoB u.2 :=
    congrArg Prod.snd (compactFirst_residues h.lowFirst h.lowFirstSecond u)
  exact (BlockShiftData.blockInverseEquiv B S H hA hB x l).bijective




include hi in
theorem fourValue_fixed_active {o : FourValueOutputGraph k} (hd : HasFourValueDependence k (tailSlopes k) o)
    (hcover : Tiles ((compactCodes (sharedEnvironment (fourValueRows k) i)
      ((tailSlopes k).getD i 0)).toFinset.image (decodePoint (fourValueLayout k)))
        (Set.range (SharedCoordinates.point (fourValueLayout k) o)))
    (x : Plane) : ∃ j : FourValueLabel i, DigitActive (fourValuePrivateAt o x i) (fourValueDigitSubgroup i j) := by
  have h := fixedPairFacts i hi
  letI : NeZero (FixedA i) := ⟨h.firstPrime.ne_zero⟩
  let L := fourValueLayout k
  let s := (tailSlopes k).getD i 0
  let J := OrdinaryIndex (L.lowSize i) (FixedA i) (FixedB i)
  let src (j : J) := SharedCoordinates.activationSource L i (compactOffset L i s j) j.1 (x,0)
  let sample (l : FourValueLow i) : FourValueBase k := (x,Function.update 0 i (-l))
  let read (v : FourValueBase k) := fixedUseful i hi (SharedCoordinates.point L o v).2
  apply exists_active_private_digit (fourValueDigitCRT i).toEquiv (fourValueDigitSubgroup i)
    (fourValueDigitSubgroup_sub i)
  intro hc
  obtain ⟨c,hc⟩ := hc
  have hl (j : J) :
      (src j).1.2 + (s : ℤ)*(src j).1.1 = x.2 + (s : ℤ)*x.1 := by
    change x.2 - (-(s:ℤ)*(compactOffset L i s j).1) +
      (s:ℤ)*(x.1-(compactOffset L i s j).1) = _
    ring
  have hp (j : J) : o.privateOutput (src j) i = fourValuePrivateAt o x i (-j.1) := by
    rw [hd.privateAt_eq (src j) i]
    have he : (src j).2 i = -j.1 := by simp [src,SharedCoordinates.activationSource]
    rw [he]
    exact hd.privateAt_line i (by have := fourValueRows_length k; omega) (src j).1 x (hl j) _
  have he (j : J) : read (src j) = read (sample j.1) := by
    have hs (l : FourValueLow i) :
        o.privateOutput (sample l) i = fourValuePrivateAt o x i (-l) := rfl
    change fixedUseful i hi (SharedCoordinates.point (fourValueLayout k) o (src j)).2 =
      fixedUseful i hi (SharedCoordinates.point (fourValueLayout k) o (sample j.1)).2
    rw [fixedUseful_point_fixed i hi,fixedUseful_point_fixed i hi,hp,hs]
  have hz (l : FourValueLow i) : (read (sample l)).2 = c.2 := by
    rw [show read (sample l) = _ from fixedUseful_point_fixed i hi o (sample l)]
    change (fourValuePrivateAt o x i (-l)).2 = c.2
    rw [hc]
  have hbij := (fourValueFixed_iff i hi s o).mp hcover (x,0)
  change Function.Bijective (fun j : J =>
    (read (src j) + shift (FixedA i) (FixedB i) j.2, o.high (src j) i)) at hbij
  simp only [he] at hbij
  have hdiv : ¬ FixedA i ∣ Fintype.card (FourValueLow i) := by
    rw [ZMod.card]
    exact (h.firstPrime.coprime_iff_not_dvd.mp h.lowFirst.symm)
  exact shared_activation_private_nonconstant h.firstPrime.two_le h.secondPrime.two_le hdiv
    (fun l => (read (sample l)).1) (fun l => (read (sample l)).2)
    (fun j => o.high (src j) i) hbij ⟨c.2,hz⟩


theorem fourValue_fixed_complete (o : FourValueOutputGraph k)
    (pick : ℤ → FourValueLabel i)
    (hpair : ∀ x : FourValueBase k, fixedUseful i hi
        (SharedCoordinates.point (fourValueLayout k) o x).2 =
      (fourValueFixedBlocks i hi (pick (x.1.2+((tailSlopes k).getD i.val 0 : ℤ)*x.1.1))).C (x.2 i))
    (hhigh : ∀ x : FourValueBase k, o.high x i =
      (fourValueFixedBlocks i hi (pick (x.1.2+((tailSlopes k).getD i.val 0 : ℤ)*x.1.1))).T x.1.1 (x.2 i)) :
    Tiles ((compactCodes (sharedEnvironment (fourValueRows k) i)
      ((tailSlopes k).getD i 0)).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) o)) := by
  let h := fixedPairFacts i hi
  letI : NeZero (FixedA i) := ⟨h.firstPrime.ne_zero⟩
  let L := fourValueLayout k
  let s := (tailSlopes k).getD i 0
  apply (fourValueFixed_iff i hi s o).mpr
  intro x
  let src (j : FourValueFixedIndex i) := SharedCoordinates.activationSource L i (compactOffset L i s j) j.1 x
  let v := pick (x.1.2+(s : ℤ)*x.1.1)
  let D := fourValueFixedBlocks i hi v
  let f (j : FourValueFixedIndex i) :=
    (D.C (x.2 i-j.1) + shift (FixedA i) (FixedB i) j.2,
      D.T (x.1.1-(compactOffset L i s j).1) (x.2 i-j.1))
  have hbij : Function.Bijective f := fourValueFixedBlock_bijective i hi v s x.1.1 (x.2 i)
  have hx (j : FourValueFixedIndex i) :
      (src j).1.2 + (s : ℤ)*(src j).1.1 = x.1.2 + (s : ℤ)*x.1.1 := by
    change x.1.2 - (-(s:ℤ)*(compactOffset L i s j).1) +
      (s:ℤ)*(x.1.1-(compactOffset L i s j).1) = _
    ring
  have hl (j : FourValueFixedIndex i) : (src j).2 i = x.2 i-j.1 := by
    simp only [src,SharedCoordinates.activationSource,Function.update_self]
  change Function.Bijective (fun j : FourValueFixedIndex i =>
    (fixedUseful i hi (SharedCoordinates.point L o (src j)).2 + shift _ _ j.2, o.high (src j) i))
  convert hbij using 2
  rename_i j
  rw [hpair,hhigh,hx,hl]
  rfl

end
end TranslationTiling.FiniteCompiler.Packed
