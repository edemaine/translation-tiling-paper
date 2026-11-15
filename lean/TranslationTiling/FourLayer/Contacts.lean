import TranslationTiling.FourLayer.Partition
import TranslationTiling.FourLayer.Rigidity

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

def widths : Fin 3 → ℕ := ![2*m+1,2*m+1,4]

@[simp] theorem band_zero : band m 0=0 := by apply Fin.ext; simp [band]
@[simp] theorem band_twice : band m (2*(m:ℤ))=0 := by
  apply Fin.ext
  change (2*(m:ℤ)).toNat%m=0
  have h : (2*(m:ℤ)).toNat=2*m := by omega
  rw [h]
  simp

theorem internal_contact (p q : Equiv.Perm (Fin m)) (i j : Fin m) :
    ∃ u v, Fiber m p q i u ∧ Fiber m p q j v ∧ v=u+Pi.single 2 1 := by
  have hi := i.isLt
  have hj := j.isLt
  refine ⟨![(j.val:ℤ),(i.val:ℤ),0],![(j.val:ℤ),(i.val:ℤ),1],?_,?_,?_⟩
  · constructor
    · simp [InBox]; omega
    · simp [color]
  · constructor
    · simp [InBox]; omega
    · simp [color]
  · ext k; fin_cases k <;> simp

theorem x_contact (p q : Equiv.Perm (Fin m)) (j : Fin m) :
    ∃ u v, Fiber m p q (p j) u ∧ Fiber m p q j v ∧
      u+Pi.single 0 1=gridMap (widths m) (Pi.single 0 1)+v := by
  have hj := j.isLt
  have hm := NeZero.pos m
  have hmR : (0:ℤ)<m := by exact_mod_cast hm
  refine ⟨![2*(m:ℤ),(j.val:ℤ),2],![0,(j.val:ℤ),2],?_,?_,?_⟩
  · constructor
    · simp [InBox]; omega
    · simp [color,show ¬2*(m:ℤ)<m by omega]
  · constructor
    · simp [InBox]; omega
    · simp [color,NeZero.ne m]
  · ext k; fin_cases k <;> simp [gridMap,widths] <;> omega

theorem y_contact (p q : Equiv.Perm (Fin m)) (j : Fin m) :
    ∃ u v, Fiber m p q (q j) u ∧ Fiber m p q j v ∧
      u+Pi.single 1 1=gridMap (widths m) (Pi.single 1 1)+v := by
  have hj := j.isLt
  have hmR : (0:ℤ)<m := by exact_mod_cast NeZero.pos m
  refine ⟨![(j.val:ℤ),2*(m:ℤ),3],![(j.val:ℤ),0,3],?_,?_,?_⟩
  · constructor
    · simp [InBox]; omega
    · simp [color,show ¬2*(m:ℤ)<m by omega]
  · constructor
    · simp [InBox]; omega
    · simp [color,NeZero.ne m]
  · ext k; fin_cases k <;> simp [gridMap,widths] <;> omega

theorem z_contact (p q : Equiv.Perm (Fin m)) (i j : Fin m) :
    ∃ u v, Fiber m p q i u ∧ Fiber m p q j v ∧
      u+Pi.single 2 1=gridMap (widths m) (Pi.single 2 1)+v := by
  have hi := i.isLt
  have hj := j.isLt
  have hjR : (j.val:ℤ)<m := by exact_mod_cast hj
  refine ⟨![(i.val:ℤ),(j.val:ℤ),3],![(i.val:ℤ),(j.val:ℤ),0],?_,?_,?_⟩
  · constructor
    · simp [InBox]; omega
    · simp [color,hjR]
  · constructor
    · simp [InBox]; omega
    · simp [color]
  · ext k; fin_cases k <;> simp [gridMap,widths]

theorem anchor_colors (p q : Equiv.Perm (Fin m)) :
    Fiber m p q 0 ![0,0,0] ∧
    Fiber m p q 0 ![2*(m:ℤ),0,0] ∧
    Fiber m p q 0 ![0,2*(m:ℤ),0] ∧
    Fiber m p q 0 ![0,0,3] := by
  have hm := NeZero.pos m
  have hmR : (0:ℤ)<m := by exact_mod_cast hm
  simp [Fiber,InBox,color,NeZero.ne m]

end
end TranslationTiling.FourLayer
