import TranslationTiling.FiniteCompiler.Effective.AxisSlotKernelGeometry
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalKernel

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective FiniteCompiler.Effective
open scoped Classical

open SlotParameters (numericalKernel)

variable {k m : ℕ} (s : AxisParameters k m)

theorem numericalKernel_correct :
    cyclicTileSet (order s.layout) (numericalKernel (order s.layout) s.period) =
      cyclicTileSet (order s.layout) (s.encodeTile (productKernel s.layout)) := by
  let N := order s.layout
  let R := s.period
  let K := cyclicTileSet N (numericalKernel N R)
  let H := cyclicTileSet N (s.encodeTile (productKernel s.layout))
  have hR : 0 < R := s.period_pos
  have hNR : N / R * R = N := Nat.div_mul_cancel s.period_dvd
  have hsub : K ⊆ H := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    simpa [cyclicPoint,R,Int.cast_mul,Int.cast_natCast] using s.kernel_column (i : ℤ)
  apply Finset.eq_of_subset_of_card_le hsub
  have hK : K.card = N/R := by
    have hset : K = (Finset.range (N/R)).image (fun i => ((0 : Plane), ((R*i : ℕ) : ZMod N))) := by
      ext p
      simp [K,numericalKernel,cyclicTileSet,cyclicPoint]
    rw [hset,Finset.card_image_of_injOn,Finset.card_range]
    intro a ha b hb he
    have ha' : R*a < N := by
      have hh := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp ha) hR
      rwa [mul_comm R (N/R),hNR] at hh
    have hb' : R*b < N := by
      have hh := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hb) hR
      rwa [mul_comm R (N/R),hNR] at hh
    have hval := congrArg (fun v : Plane × ZMod N => v.2.val) he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb'] at hval
    exact Nat.eq_of_mul_eq_mul_left hR hval
  let o : SharedCoordinates.Outputs s.layout := ⟨0,0,0⟩
  have ht := (productKernel_iff s.layout _).mpr ⟨o,rfl⟩
  have hH : H.card * R = N := s.encode_mass _ o ht
  rw [hK]
  exact (Nat.eq_of_mul_eq_mul_right hR (hH.trans hNR.symm)).le

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
