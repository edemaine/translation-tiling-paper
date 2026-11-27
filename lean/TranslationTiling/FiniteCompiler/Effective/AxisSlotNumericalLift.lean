import TranslationTiling.FiniteCompiler.Effective.AxisSlotFinite
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalLift

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective FiniteCompiler.Effective
open scoped Classical

set_option maxHeartbeats 1000000

open SlotParameters (numericalArithmeticLift)

noncomputable section

variable {k m : ℕ} (s : AxisParameters k m)
local instance numericalLiftAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

theorem numericalArithmeticLift_correct (F : CyclicTile) (lows : List ℕ)
    (hl : ∀ r, r ∈ lows ↔ ∃ i : AxisAddedRow k m, s.layout.lowSize (.inr i) = r) :
    (numericalArithmeticLift (order s.layout) (order (fourValueLayout 0)) lows F).toFinset.image
      (decodePoint s.layout) =
      s.oldTileLift (F.toFinset.image (decodePoint (fourValueLayout 0))) := by
  let N := order s.layout
  let M := order (fourValueLayout 0)
  let e := fourValueLayoutCRT 0
  have hmod (u v : ℕ) : u % M = v % M ↔
      decode (fourValueLayout 0) u = decode (fourValueLayout 0) v := by
    have hu : decode (fourValueLayout 0) u = e (u : ZMod M) := (map_natCast e u).symm
    have hv : decode (fourValueLayout 0) v = e (v : ZMod M) := (map_natCast e v).symm
    rw [hu,hv]
    rw [e.injective.eq_iff, ← (ZMod.val_injective M).eq_iff,
      ZMod.val_natCast,ZMod.val_natCast]
  have hlow (u : ℕ) : KernelTest lows u ↔ s.extraProjection (s.splitFactor (decode s.layout u)).2 = 0 := by
    change _ ↔ (fun i : AxisAddedRow k m => CyclicShear.low (s.layout.lowSize (.inr i))
      (u : SharedCoordinates.Square s.layout (.inr i))) = 0
    constructor
    · intro h
      funext i
      rw [CyclicShear.low_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_iff_mod_eq_zero.mpr
        (h _ ((hl _).mpr ⟨i,rfl⟩)))
    · intro h r hr
      obtain ⟨i,rfl⟩ := (hl _).mp hr
      have he := congrFun h i
      rw [CyclicShear.low_natCast] at he
      exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp he)
  have hrec (p : CyclicPoint) (u : ℕ) :
      decide (u % M = p.2 % M ∧ KernelTest lows u) = true ↔
      (s.splitFactor (decode s.layout u)).1 = decode (fourValueLayout 0) p.2 ∧
      s.extraProjection (s.splitFactor (decode s.layout u)).2 = 0 := by
    rw [decide_eq_true_eq,hmod,hlow]
    rfl
  have hbatch (p : CyclicPoint) (v : SharedCoordinates.Ambient s.layout) :
      v ∈ (((List.range N).filter fun r => decide (r % M = p.2 % M ∧ KernelTest lows r)).map
        fun r => (p.1,r)).toFinset.image (decodePoint s.layout) ↔
      v.1 = p.1 ∧ (s.splitFactor v.2).1 = decode (fourValueLayout 0) p.2 ∧
        s.extraProjection (s.splitFactor v.2).2 = 0 :=
    decoded_range_filter_iff s.layout s.crt p.1
      (fun r => decide (r % M = p.2 % M ∧ KernelTest lows r))
      (fun a => (s.splitFactor a).1 = decode (fourValueLayout 0) p.2 ∧
        s.extraProjection (s.splitFactor a).2 = 0) (hrec p) v
  ext v
  have hnum : v ∈ (numericalArithmeticLift N M lows F).toFinset.image (decodePoint s.layout) ↔
      ∃ p ∈ F, v.1 = p.1 ∧ (s.splitFactor v.2).1 = decode (fourValueLayout 0) p.2 ∧
        s.extraProjection (s.splitFactor v.2).2 = 0 := by
    simp only [numericalArithmeticLift,Finset.mem_image,List.mem_toFinset,List.mem_flatMap]
    constructor
    · rintro ⟨r,⟨p,hp,hr⟩,h⟩
      exact ⟨p,hp,(hbatch p v).mp (Finset.mem_image.mpr ⟨r,List.mem_toFinset.mpr hr,h⟩)⟩
    · rintro ⟨p,hp,h⟩
      obtain ⟨r,hr,hv⟩ := Finset.mem_image.mp ((hbatch p v).mpr h)
      exact ⟨r,⟨p,hp,List.mem_toFinset.mp hr⟩,hv⟩
  apply hnum.trans
  constructor
  · rintro ⟨p,hp,hplane,hfactor,hzero⟩
    apply Finset.mem_map.mpr
    refine ⟨s.splitAmbient v,Finset.mem_product.mpr ⟨?_,?_⟩,s.splitAmbient.symm_apply_apply v⟩
    · exact Finset.mem_image.mpr ⟨p,List.mem_toFinset.mpr hp,Prod.ext hplane.symm hfactor.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩
  · intro hv
    obtain ⟨q,hq,h⟩ := Finset.mem_map.mp hv
    obtain ⟨hF,hZ⟩ := Finset.mem_product.mp hq
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hF
    have hzero := (Finset.mem_filter.mp hZ).2
    have hq : q = s.splitAmbient v := by
      change s.splitAmbient.symm q = v at h
      rw [← h,s.splitAmbient.apply_symm_apply]
    subst q
    exact ⟨p,List.mem_toFinset.mp hp,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm,hzero⟩

end

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
