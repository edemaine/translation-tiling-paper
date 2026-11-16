import TranslationTiling.Rails.RailPaths
import TranslationTiling.FourLayer.Rigidity

namespace TranslationTiling.Rails
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable (a b : ℕ) [NeZero a] [NeZero b]

theorem x_contact (p q : Equiv.Perm (Fin a)) (j : Fin a) :
    ∃ r t, Fiber a b p q (p j).val r ∧ Fiber a b p q j.val t ∧
      r+Pi.single 0 1=FourLayer.gridMap (widths a b) (Pi.single 0 1)+t := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hj := j.isLt
  refine ⟨point ((lengthX a b:ℤ)-1) (a+j.val) 3,point 0 (a+j.val) 3,?_,?_,?_⟩
  · apply small_point
    · simp [box_point,lengthX,lengthY]; omega
    · omega
    · right; omega
    · simp [small,FourLayer.band_add,show ¬(lengthX a b:ℤ)-1<(a:ℤ) by simp [lengthX]; omega]
  · apply small_point
    · simp [box_point,lengthX,lengthY]; omega
    · omega
    · left; omega
    · simp [small,FourLayer.band_add,ha]
  · ext k; fin_cases k <;> simp [point,FourLayer.gridMap,widths] <;> omega

theorem y_contact (p q : Equiv.Perm (Fin a)) (j : Fin a) :
    ∃ r t, Fiber a b p q (q j).val r ∧ Fiber a b p q j.val t ∧
      r+Pi.single 1 1=FourLayer.gridMap (widths a b) (Pi.single 1 1)+t := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hj := j.isLt
  refine ⟨point (a+j.val) ((lengthY a:ℤ)-1) 4,point (a+j.val) 0 4,?_,?_,?_⟩
  · apply small_point
    · simp [box_point,lengthX,lengthY]; omega
    · omega
    · left; omega
    · simp [small,FourLayer.band_add,show ¬(lengthY a:ℤ)-1<(a:ℤ) by simp [lengthY]; omega]
  · apply small_point
    · simp [box_point,lengthX,lengthY]; omega
    · omega
    · left; omega
    · simp [small,FourLayer.band_add,ha]
  · ext k; fin_cases k <;> simp [point,FourLayer.gridMap,widths] <;> omega

theorem z_contact (p q : Equiv.Perm (Fin a)) (i : Fin b) (hi : i.val+1<b) :
    ∃ r t, Fiber a b p q (railLabel a i.val) r ∧
      Fiber a b p q (railLabel a (i.val+1)) t ∧
      r+Pi.single 2 1=FourLayer.gridMap (widths a b) (Pi.single 2 1)+t := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hib := i.isLt
  let x : ℤ := 4*a+7*(i.val+1)
  refine ⟨point x 1 7,point x 1 0,?_,?_,?_⟩
  · refine ⟨by simp [box_point,x,lengthX,lengthY]; omega,?_⟩
    simp only [color,point,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,
      show (7:ℤ)≠0 by decide,ite_false,ite_true]
    exact rail_eq a b i x 7 (by dsimp [x]; omega) (by dsimp [x]; omega)
  · refine ⟨by simp [box_point,x,lengthX,lengthY]; omega,?_⟩
    simp only [color,point,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,
      ite_true,show (1:ℤ)≠0 by decide,ite_false]
    exact rail_eq a b ⟨i.val+1,hi⟩ x 0 (by dsimp [x]; omega) (by dsimp [x]; omega)
  · ext k; fin_cases k <;> simp [point,FourLayer.gridMap,widths] <;> omega

theorem internal_contact (p q : Equiv.Perm (Fin a)) (i : Fin b) (j : Fin a) :
    ∃ r t, Fiber a b p q (railLabel a i.val) r ∧ Fiber a b p q j.val t ∧
      t=r+Pi.single 2 1 := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hi := i.isLt
  have hj := j.isLt
  let x : ℤ := if i.val=0 then 0 else 4*a+7*i.val
  let y : ℤ := if j.val=0 then a else j.val
  have hy : 0<y ∧ y<(lengthY a:ℤ) ∧ y≠2*(a:ℤ) := by
    dsimp [y]
    split_ifs with hj0
    · dsimp [lengthY]; omega
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
      dsimp [lengthY]; omega
  have hx : 0≤x ∧ x<(lengthX a b:ℤ) := by
    dsimp [x]; split_ifs <;> simp [lengthX] <;> omega
  have hband : FourLayer.band a y=j := by
    dsimp [y]
    split_ifs with hj0
    · have hh := FourLayer.band_add a (0 : Fin a)
      have hje : j=(0 : Fin a) := Fin.ext hj0
      simpa [hje] using hh
    · exact FourLayer.band_val a j
  refine ⟨point x y 0,point x y 1,?_,?_,?_⟩
  · refine ⟨by simp only [box_point]; omega,?_⟩
    simp only [color,point,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,
      ite_true,show y≠0 by omega,ite_false]
    by_cases hi0 : i.val=0
    · simp only [x,if_pos hi0,railLabel,hi0,ite_true]
      apply (rail_zero_iff a b 0 0).mpr; left; omega
    · exact rail_eq a b i x 0 (by simp [x,hi0] <;> omega) (by simp [x,hi0] <;> omega)
  · apply small_point
    · simp only [box_point]; omega
    · omega
    · exact Or.inr hy.2.2
    · simp [small,hband]
  · ext k; fin_cases k <;> simp [point]

def corner (k : Fin 3) : Lattice 3 := fun j => if j=k then (widths a b j:ℤ)-1 else 0

theorem corner_color (p q : Equiv.Perm (Fin a)) (k : Fin 3) :
    color a b p q (corner a b k)=0 := by
  have ha := NeZero.pos a
  have hr0 : rail a b 0 0=0 := (rail_zero_iff a b 0 0).mpr (Or.inl (by omega))
  have hr7 : rail a b 0 7=0 := (rail_zero_iff a b 0 7).mpr (Or.inl (by omega))
  fin_cases k <;> simp [corner,color,widths,hr0,hr7]

theorem origin_color (p q : Equiv.Perm (Fin a)) : color a b p q 0=0 := by simp [color]

end
end TranslationTiling.Rails
