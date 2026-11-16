import TranslationTiling.Rails.Partition

namespace TranslationTiling.Rails
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable (a b : ℕ) [NeZero a] [NeZero b]

def point (x y z : ℤ) : Lattice 3 := ![x,y,z]

@[simp] theorem box_point (x y z : ℤ) : Box a b (point x y z) ↔
    0≤x ∧ x<(lengthX a b:ℤ) ∧ 0≤y ∧ y<(lengthY a:ℤ) ∧ 0≤z ∧ z≤7 := Iff.rfl

theorem axis_x (p q : Equiv.Perm (Fin a)) (i : ℕ) (x y z c : ℤ)
    (h : ∀ t, min x c≤t → t≤max x c → Fiber a b p q i (point t y z)) :
    FacePath (Fiber a b p q i) (point x y z) (point c y z) := by
  have hh := FacePath.axis (Fiber a b p q i) (point x y z) 0 c (by
    intro t ht hu
    have he : Function.update (point x y z) 0 t=point t y z := by
      ext k; fin_cases k <;> simp [point]
    rw [he]
    exact h t ht hu)
  convert hh using 1 <;> ext k <;> fin_cases k <;> simp [point]

theorem axis_y (p q : Equiv.Perm (Fin a)) (i : ℕ) (x y z c : ℤ)
    (h : ∀ t, min y c≤t → t≤max y c → Fiber a b p q i (point x t z)) :
    FacePath (Fiber a b p q i) (point x y z) (point x c z) := by
  have hh := FacePath.axis (Fiber a b p q i) (point x y z) 1 c (by
    intro t ht hu
    have he : Function.update (point x y z) 1 t=point x t z := by
      ext k; fin_cases k <;> simp [point]
    rw [he]
    exact h t ht hu)
  convert hh using 1 <;> ext k <;> fin_cases k <;> simp [point]

theorem axis_z (p q : Equiv.Perm (Fin a)) (i : ℕ) (x y z c : ℤ)
    (h : ∀ t, min z c≤t → t≤max z c → Fiber a b p q i (point x y t)) :
    FacePath (Fiber a b p q i) (point x y z) (point x y c) := by
  have hh := FacePath.axis (Fiber a b p q i) (point x y z) 2 c (by
    intro t ht hu
    have he : Function.update (point x y z) 2 t=point x y t := by
      ext k; fin_cases k <;> simp [point]
    rw [he]
    exact h t ht hu)
  convert hh using 1 <;> ext k <;> fin_cases k <;> simp [point]

theorem step_z (p q : Equiv.Perm (Fin a)) (i : ℕ) (x y z : ℤ)
    (h : Fiber a b p q i (point x y z)) (h' : Fiber a b p q i (point x y (z+1))) :
    FacePath (Fiber a b p q i) (point x y z) (point x y (z+1)) := by
  apply FacePath.step h h'
  refine ⟨2,Or.inl ?_⟩
  ext k; fin_cases k <;> simp [point]

theorem small_at (p q : Equiv.Perm (Fin a)) (x y z : ℤ) (hz : 1≤z ∧ z≤6)
    (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ)) :
    color a b p q (point x y z)=small a p q x y z := by
  have hn : ¬ (4*(a:ℤ)≤x ∧ y=2*(a:ℤ)) := by omega
  simp [color,point,show z≠0 by omega,show z≠7 by omega,hn]

theorem small_point (p q : Equiv.Perm (Fin a)) (j : Fin a) (x y z : ℤ)
    (hb : Box a b (point x y z)) (hz : 1≤z ∧ z≤6)
    (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ)) (he : small a p q x y z=j.val) :
    Fiber a b p q j.val (point x y z) := ⟨hb,(small_at a b p q x y z hz hc).trans he⟩

theorem band_three (j : Fin a) : FourLayer.band a (3*(a:ℤ)+j.val)=j := by
  apply Fin.ext
  simp only [FourLayer.band]
  have he : (3*(a:ℤ)+j.val).toNat=3*a+j.val := by omega
  rw [he]
  simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

def hub (j : Fin a) := point j.val j.val 2

theorem row_to_hub (p q : Equiv.Perm (Fin a)) (j : Fin a) (x y : ℤ)
    (hb : Box a b (point x y 1)) (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ))
    (he : FourLayer.band a y=j) :
    FacePath (Fiber a b p q j.val) (point x y 1) (hub a j) := by
  have ha := NeZero.pos a
  have hbp := NeZero.pos b
  have hj := j.isLt
  have hbox := hb
  simp only [box_point] at hbox
  have hr : FacePath (Fiber a b p q j.val) (point x y 1) (point j.val y 1) := by
    apply axis_x
    intro t ht hu
    apply small_point
    · simp [box_point,lengthX,lengthY] at *; omega
    · omega
    · omega
    · simp [small,he]
  have h1 : Fiber a b p q j.val (point j.val y 1) := by
    apply small_point
    · simp [box_point,lengthX,lengthY] at *; omega
    · omega
    · left; omega
    · simp [small,he]
  have h2 : Fiber a b p q j.val (point j.val y 2) := by
    apply small_point
    · simp [box_point,lengthX,lengthY] at *; omega
    · omega
    · left; omega
    · simp [small,FourLayer.band_val]
  have hv := step_z a b p q j.val j.val y 1 h1 h2
  have hy : FacePath (Fiber a b p q j.val) (point j.val y 2) (point j.val j.val 2) := by
    apply axis_y
    intro t ht hu
    apply small_point
    · simp [box_point,lengthX,lengthY] at *; omega
    · omega
    · left; omega
    · simp [small,FourLayer.band_val]
  exact (hr.trans hv).trans hy

theorem column_to_hub (p q : Equiv.Perm (Fin a)) (j : Fin a) (x y : ℤ)
    (hb : Box a b (point x y 2)) (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ))
    (he : FourLayer.band a x=j) :
    FacePath (Fiber a b p q j.val) (point x y 2) (hub a j) := by
  have ha := NeZero.pos a
  have hbp := NeZero.pos b
  have hj := j.isLt
  have hbox := hb
  simp only [box_point] at hbox
  let c : ℤ := if x<4*(a:ℤ) ∨ y<2*(a:ℤ) then j.val else 3*a+j.val
  have hcb : 0≤c ∧ c<(lengthY a:ℤ) := by
    dsimp [c]; split_ifs <;> simp [lengthY] <;> omega
  have hcc : x<4*(a:ℤ) ∨ c≠2*(a:ℤ) := by dsimp [c]; split_ifs <;> omega
  have hband : FourLayer.band a c=j := by
    dsimp [c]; split_ifs
    · exact FourLayer.band_val a j
    · exact band_three a j
  have hy : FacePath (Fiber a b p q j.val) (point x y 2) (point x c 2) := by
    apply axis_y
    intro t ht hu
    apply small_point
    · simp only [box_point]; omega
    · omega
    · dsimp [c] at ht hu; split_ifs at ht hu <;> omega
    · simp [small,he]
  have h1 : Fiber a b p q j.val (point x c 1) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · exact hcc
    · simp [small,hband]
  have h2 : Fiber a b p q j.val (point x c 2) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · exact hcc
    · simp [small,he]
  exact (hy.trans (FacePath.reverse (step_z a b p q j.val x c 1 h1 h2))).trans
    (row_to_hub a b p q j x c (by simp only [box_point]; omega) hcc hband)

theorem third_to_hub (p q : Equiv.Perm (Fin a)) (j : Fin a) (x y : ℤ)
    (hb : Box a b (point x y 3)) (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ))
    (he : small a p q x y 3=j.val) :
    FacePath (Fiber a b p q j.val) (point x y 3) (hub a j) := by
  have ha := NeZero.pos a
  have hbp := NeZero.pos b
  have hj := j.isLt
  have hbox := hb
  simp only [box_point] at hbox
  let c : ℤ := if x<(a:ℤ) then j.val else a+j.val
  have hcb : 0≤c ∧ c<(lengthX a b:ℤ) ∧ c<4*(a:ℤ) := by
    dsimp [c]; split_ifs <;> simp [lengthX] <;> omega
  have hphase : c<(a:ℤ) ↔ x<(a:ℤ) := by dsimp [c]; split_ifs <;> omega
  have hband : FourLayer.band a c=j := by
    dsimp [c]; split_ifs
    · exact FourLayer.band_val a j
    · exact FourLayer.band_add a j
  have hx : FacePath (Fiber a b p q j.val) (point x y 3) (point c y 3) := by
    apply axis_x
    intro t ht hu
    have htphase : t<(a:ℤ) ↔ x<(a:ℤ) := by omega
    apply small_point
    · simp only [box_point]; omega
    · omega
    · omega
    · simpa [small,htphase] using he
  have h2 : Fiber a b p q j.val (point c y 2) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · left; exact hcb.2.2
    · simp [small,hband]
  have h3 : Fiber a b p q j.val (point c y 3) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · left; exact hcb.2.2
    · simpa [small,hphase] using he
  exact (hx.trans (FacePath.reverse (step_z a b p q j.val c y 2 h2 h3))).trans
    (column_to_hub a b p q j c y (by simp only [box_point]; omega) (Or.inl hcb.2.2) hband)

theorem upper_to_hub (p q : Equiv.Perm (Fin a)) (j : Fin a) (x y z : ℤ)
    (hb : Box a b (point x y z)) (hz : 4≤z ∧ z≤6)
    (hc : x<4*(a:ℤ) ∨ y≠2*(a:ℤ)) (he : small a p q x y 4=j.val) :
    FacePath (Fiber a b p q j.val) (point x y z) (hub a j) := by
  have ha := NeZero.pos a
  have hbp := NeZero.pos b
  have hj := j.isLt
  have hbox := hb
  simp only [box_point] at hbox
  let k : Fin a := if x<(a:ℤ) then j else p.symm j
  have hk := k.isLt
  let c : ℤ := if y<(a:ℤ) then k.val else if y≤2*(a:ℤ) then a+k.val else 3*a+k.val
  have hcb : 0≤c ∧ c<(lengthY a:ℤ) := by
    dsimp [c]; split_ifs <;> simp [lengthY] <;> omega
  have hphase : c<(a:ℤ) ↔ y<(a:ℤ) := by dsimp [c]; split_ifs <;> omega
  have hcc : x<4*(a:ℤ) ∨ c≠2*(a:ℤ) := by dsimp [c]; split_ifs <;> omega
  have hband : FourLayer.band a c=k := by
    dsimp [c]; split_ifs
    · exact FourLayer.band_val a k
    · exact FourLayer.band_add a k
    · exact band_three a k
  have hdown : FacePath (Fiber a b p q j.val) (point x y z) (point x y 4) := by
    apply axis_z
    intro t ht hu
    apply small_point
    · simp only [box_point]; omega
    · omega
    · exact hc
    · simpa [small,show t≠1 by omega,show t≠2 by omega,show t≠3 by omega] using he
  have hy : FacePath (Fiber a b p q j.val) (point x y 4) (point x c 4) := by
    apply axis_y
    intro t ht hu
    have htphase : t<(a:ℤ) ↔ y<(a:ℤ) := by omega
    apply small_point
    · simp only [box_point]; omega
    · omega
    · dsimp [c] at ht hu; split_ifs at ht hu <;> omega
    · simpa [small,htphase] using he
  have hrow : small a p q x c 3=j.val := by
    by_cases hh : x<(a:ℤ)
    · have hkj : k=j := by simp [k,hh]
      simp [small,hh,hband,hkj]
    · have hkj : k=p.symm j := by simp [k,hh]
      simp [small,hh,hband,hkj]
  have h3 : Fiber a b p q j.val (point x c 3) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · exact hcc
    · exact hrow
  have h4 : Fiber a b p q j.val (point x c 4) := by
    apply small_point
    · simp only [box_point]; omega
    · omega
    · exact hcc
    · simpa [small,hphase] using he
  exact ((hdown.trans hy).trans (FacePath.reverse (step_z a b p q j.val x c 3 h3 h4))).trans
    (third_to_hub a b p q j x c (by simp only [box_point]; omega) hcc hrow)

theorem small_to_hub (p q : Equiv.Perm (Fin a)) (j : Fin a) (v : Lattice 3)
    (hv : Fiber a b p q j.val v) (hz : 1≤v 2 ∧ v 2≤6)
    (hc : v 0<4*(a:ℤ) ∨ v 1≠2*(a:ℤ)) :
    FacePath (Fiber a b p q j.val) v (hub a j) := by
  have hvv : v=point (v 0) (v 1) (v 2) := by ext k; fin_cases k <;> rfl
  have he : small a p q (v 0) (v 1) (v 2)=j.val := by
    rw [←small_at a b p q _ _ _ hz hc,←hvv]; exact hv.2
  have hB : Box a b (point (v 0) (v 1) (v 2)) := by rw [←hvv]; exact hv.1
  rw [hvv]
  rcases (show v 2=1 ∨ v 2=2 ∨ v 2=3 ∨ 4≤v 2 by omega) with h | h | h | h
  · have hrow : FourLayer.band a (v 1)=j := Fin.ext (by simpa [small,h] using he)
    simpa only [h] using row_to_hub a b p q j (v 0) (v 1) (by simpa only [h] using hB) hc hrow
  · have hcol : FourLayer.band a (v 0)=j := Fin.ext (by simpa [small,h] using he)
    simpa only [h] using column_to_hub a b p q j (v 0) (v 1) (by simpa only [h] using hB) hc hcol
  · simpa only [h] using third_to_hub a b p q j (v 0) (v 1) (by simpa only [h] using hB) hc (by simpa [h] using he)
  · exact upper_to_hub a b p q j (v 0) (v 1) (v 2)
      hB ⟨h,hz.2⟩ hc
      (by simpa [small,show v 2≠1 by omega,show v 2≠2 by omega,show v 2≠3 by omega] using he)

end
end TranslationTiling.Rails
