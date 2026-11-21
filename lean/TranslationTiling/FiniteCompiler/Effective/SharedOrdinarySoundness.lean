import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryCorrect
import TranslationTiling.FiniteCompiler.Effective.SharedLocal

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

set_option maxHeartbeats 3000000

theorem wangSlope_eq {k : ℕ} (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (hl : 18 ≤ i.val) :
    (tailSlopes k).getD i.val 0 = if sharedSlope k i then 0 else 2 := by
  have h : i.val < (tailSlopes k).length := by
    have h' := sharedRows_length k
    simp [tailSlopes]
    omega
  rw [List.getD_eq_getElem _ _ h]
  simp [tailSlopes,Profile.slope,not_lt_of_ge hl,ternaryLayoutProfile,radixLayoutProfile,sharedSlope]

variable {k : ℕ} {o : SharedOutput k} (i : SharedRow k)
  (hi : i.val < (sharedRows k).length-2)

include hi in
theorem ordinary_active (hd : HasSharedDependence k (tailSlopes k) o)
    (hcover : Tiles ((compactCodes (sharedEnvironment (sharedRows k) i)
      ((tailSlopes k).getD i 0)).toFinset.image (decodePoint (sharedLayout k)))
        (Set.range (SharedCoordinates.point (sharedLayout k) o)))
    (x : Plane) : ∃ j : SharedLabel i, DigitActive (sharedPrivateAt o x i) (sharedDigitSubgroup i j) := by
  have h := ordinaryPairFacts i hi
  letI : NeZero (OrdinaryA i) := ⟨h.firstPrime.ne_zero⟩
  let L := sharedLayout k
  let s := (tailSlopes k).getD i 0
  let J := OrdinaryIndex (L.lowSize i) (OrdinaryA i) (OrdinaryB i)
  let src (j : J) := SharedCoordinates.activationSource L i (compactOffset L i s j) j.1 (x,0)
  let sample (l : RowLow i) : SharedBase k := (x,Function.update 0 i (-l))
  let read (v : SharedBase k) := ordinaryUseful i hi (SharedCoordinates.point L o v).2
  apply exists_active_private_digit (sharedDigitCRT i).toEquiv (sharedDigitSubgroup i)
    (sharedDigitSubgroup_sub i)
  intro hc
  obtain ⟨c,hc⟩ := hc
  have hl (j : J) :
      (src j).1.2 + (s : ℤ)*(src j).1.1 = x.2 + (s : ℤ)*x.1 := by
    change x.2 - (-(s:ℤ)*(compactOffset L i s j).1) +
      (s:ℤ)*(x.1-(compactOffset L i s j).1) = _
    ring
  have hp (j : J) : o.privateOutput (src j) i = sharedPrivateAt o x i (-j.1) := by
    rw [hd.privateAt_eq (src j) i]
    have he : (src j).2 i = -j.1 := by simp [src,SharedCoordinates.activationSource]
    rw [he]
    exact hd.privateAt_line i hi (src j).1 x (hl j) _
  have he (j : J) : read (src j) = read (sample j.1) := by
    have hs (l : RowLow i) :
        o.privateOutput (sample l) i = sharedPrivateAt o x i (-l) := rfl
    change ordinaryUseful i hi (SharedCoordinates.point (sharedLayout k) o (src j)).2 =
      ordinaryUseful i hi (SharedCoordinates.point (sharedLayout k) o (sample j.1)).2
    by_cases hf : i.val < 18
    · rw [ordinaryUseful_point_fixed i hi hf,ordinaryUseful_point_fixed i hi hf,hp,hs]
    · have hf' := Nat.le_of_not_gt hf
      have hm : sharedLine (sharedSlope k i) (o.fixed (src j)) =
          sharedLine (sharedSlope k i) (o.fixed (sample j.1)) := by
        have hlow : (src j).2 = (sample j.1).2 := by
          change Function.update (0 : ∀ j : SharedRow k, RowLow j) i (0-j.1) =
            Function.update (0 : ∀ j : SharedRow k, RowLow j) i (-j.1)
          rw [zero_sub]
        rw [show src j = ((src j).1,(sample j.1).2) from Prod.ext rfl hlow]
        apply hd.sharedAt_line
        have hh : ((s : ℕ) : ℤ) = if sharedSlope k i then 0 else 2 := by
          have e := wangSlope_eq i hi hf'
          change ((tailSlopes k).getD i.val 0 : ℤ) = _
          rw [e]
          cases sharedSlope k i <;> rfl
        simpa only [hh] using hl j
      rw [ordinaryUseful_point_shared i hi hf',ordinaryUseful_point_shared i hi hf',hm,hp,hs]
  have hz (l : RowLow i) : (read (sample l)).2 = c.2 := by
    by_cases hf : i.val < 18
    · rw [show read (sample l) = _ from ordinaryUseful_point_fixed i hi hf o (sample l)]
      change (sharedPrivateAt o x i (-l)).2 = c.2
      rw [hc]
    · rw [show read (sample l) = _ from ordinaryUseful_point_shared i hi
        (Nat.le_of_not_gt hf) o (sample l)]
      change (sharedPrivateAt o x i (-l)).2 = c.2
      rw [hc]
  have hbij := (sharedOrdinary_iff i hi s o).mp hcover (x,0)
  change Function.Bijective (fun j : J =>
    (read (src j) + shift (OrdinaryA i) (OrdinaryB i) j.2, o.high (src j) i)) at hbij
  simp only [he] at hbij
  have hdiv : ¬ OrdinaryA i ∣ Fintype.card (RowLow i) := by
    rw [ZMod.card]
    exact (h.firstPrime.coprime_iff_not_dvd.mp h.lowFirst.symm)
  exact shared_activation_private_nonconstant h.firstPrime.two_le h.secondPrime.two_le hdiv
    (fun l => (read (sample l)).1) (fun l => (read (sample l)).2)
    (fun j => o.high (src j) i) hbij ⟨c.2,hz⟩

end
end TranslationTiling.FiniteCompiler.Packed
