import TranslationTiling.FiniteCompiler.Effective.SlotKernelGeometry

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective FiniteCompiler.Effective
open scoped Classical

/-- The kernel starts at the origin and contains one copy of each
multiple of the low period in the cyclic height. -/
def numericalKernel (N R : ℕ) : CyclicTile :=
  (List.range (N/R)).map fun i => ((0 : Plane),R*i)

theorem numericalKernel_primrec : Primrec (fun z : ℕ × ℕ => numericalKernel z.1 z.2) := by
  unfold numericalKernel
  have h : Primrec (fun z : ℕ × ℕ => List.range (z.1/z.2)) := by fun_prop
  exact Primrec.list_map h (Primrec.to₂ (show
    Primrec (fun z : (ℕ × ℕ) × ℕ => ((0 : Plane),z.1.2*z.2)) from by fun_prop))

variable {k m : ℕ} (s : SlotParameters k m)

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

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
