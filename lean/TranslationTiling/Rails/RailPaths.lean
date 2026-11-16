import TranslationTiling.Rails.SmallPaths

namespace TranslationTiling.Rails
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable (a b : ℕ) [NeZero a] [NeZero b]

theorem positive_point_iff (p q : Equiv.Perm (Fin a)) (i : ℕ) (hi : 0 < i) (hib : i < b)
    (x y z : ℤ) : Fiber a b p q (a+i) (point x y z) ↔
    Box a b (point x y z) ∧
    (4*(a:ℤ)+z+7*i≤x ∧ x < 4*(a:ℤ)+z+7*(i+1)) ∧
    (z=0 → y≠0) ∧ (z=0 ∨ z=7 ∨ y=2*(a:ℤ)) := by
  have ha := NeZero.pos a
  constructor
  · rintro ⟨hb,hc⟩
    change (if z=0 then (if y=0 then 0 else rail a b x 0)
      else if z=7 then rail a b x 7
      else if 4*(a:ℤ)≤x ∧ y=2*(a:ℤ) then rail a b x z
      else small a p q x y z)=a+i at hc
    split_ifs at hc with h0 hy h7 hline
    · omega
    · have hh := (rail_large a b i hi hib x 0).mp hc
      refine ⟨hb,?_,?_,?_⟩ <;> omega
    · have hh := (rail_large a b i hi hib x 7).mp hc
      refine ⟨hb,?_,?_,?_⟩ <;> omega
    · have hh := (rail_large a b i hi hib x z).mp hc
      refine ⟨hb,?_,?_,?_⟩ <;> omega
    · have hh := small_lt a p q x y z
      omega
  · rintro ⟨hb,hx,hzero,hmode⟩
    refine ⟨hb,?_⟩
    have hri := (rail_large a b i hi hib x z).mpr hx
    have hbox := hb
    simp only [box_point] at hbox
    dsimp only [color,point]
    by_cases h0 : z=0
    · simp only [h0] at hri
      simp [h0,hzero h0,hri]
    · by_cases h7 : z=7
      · simp only [h7] at hri
        simp [h0,h7,hri]
      · have hline : 4*(a:ℤ)≤x ∧ y=2*(a:ℤ) := by omega
        simp [h0,h7,hline,hri]

theorem positive_to_root (p q : Equiv.Perm (Fin a)) (i : ℕ) (hi : 0 < i) (hib : i < b)
    (x y z : ℤ) (hv : Fiber a b p q (a+i) (point x y z)) :
    FacePath (Fiber a b p q (a+i)) (point x y z) (point (4*(a:ℤ)+7*i+6) (2*a) 0) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  obtain ⟨hbox,hx,hzero,hmode⟩ := (positive_point_iff a b p q i hi hib x y z).mp hv
  simp only [box_point] at hbox
  have hy : FacePath (Fiber a b p q (a+i)) (point x y z) (point x (2*a) z) := by
    apply axis_y
    intro t ht hu
    apply (positive_point_iff a b p q i hi hib x t z).mpr
    simp [box_point,lengthX,lengthY] at *
    constructor
    · omega
    constructor
    · exact hx
    constructor <;> omega
  let c : ℤ := 4*a+7*i+(if z=7 then 7 else 6)
  have hxc : FacePath (Fiber a b p q (a+i)) (point x (2*a) z) (point c (2*a) z) := by
    apply axis_x
    intro t ht hu
    apply (positive_point_iff a b p q i hi hib t (2*a) z).mpr
    dsimp [c] at ht hu
    split_ifs at ht hu <;> simp [box_point,lengthX,lengthY] <;> omega
  by_cases hz7 : z=7
  · have hd : FacePath (Fiber a b p q (a+i)) (point c (2*a) z) (point c (2*a) 1) := by
      apply axis_z
      intro t ht hu
      apply (positive_point_iff a b p q i hi hib c (2*a) t).mpr
      simp [c,hz7,box_point,lengthX,lengthY] at *
      omega
    have hm : FacePath (Fiber a b p q (a+i)) (point c (2*a) 1)
        (point (4*(a:ℤ)+7*i+6) (2*a) 1) := by
      apply axis_x
      intro t ht hu
      apply (positive_point_iff a b p q i hi hib t (2*a) 1).mpr
      simp [c,hz7,box_point,lengthX,lengthY] at *
      omega
    have hf : FacePath (Fiber a b p q (a+i)) (point (4*(a:ℤ)+7*i+6) (2*a) 1)
        (point (4*(a:ℤ)+7*i+6) (2*a) 0) := by
      apply axis_z
      intro t ht hu
      apply (positive_point_iff a b p q i hi hib _ (2*a) t).mpr
      simp [box_point,lengthX,lengthY] at *
      omega
    exact (((hy.trans hxc).trans hd).trans hm).trans hf
  · have hz6 : z≤6 := by omega
    have hd : FacePath (Fiber a b p q (a+i)) (point c (2*a) z) (point c (2*a) 0) := by
      apply axis_z
      intro t ht hu
      apply (positive_point_iff a b p q i hi hib c (2*a) t).mpr
      simp [c,hz7,box_point,lengthX,lengthY] at *
      omega
    simpa only [c,if_neg hz7] using (hy.trans hxc).trans hd

theorem bottom_zero (p q : Equiv.Perm (Fin a)) (x y : ℤ)
    (hv : Fiber a b p q 0 (point x y 0)) :
    FacePath (Fiber a b p q 0) (point x y 0) (point 0 0 0) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hbox := hv.1
  simp only [box_point] at hbox
  have hc : y=0 ∨ rail a b x 0=0 := by
    by_cases hy : y=0
    · exact Or.inl hy
    · exact Or.inr (by simpa [color,point,hy] using hv.2)
  have hy : FacePath (Fiber a b p q 0) (point x y 0) (point x 0 0) := by
    apply axis_y
    intro t ht hu
    refine ⟨by simp [box_point,lengthX,lengthY] at *; omega,?_⟩
    by_cases ht0 : t=0
    · simp [color,point,ht0]
    · have hr : rail a b x 0=0 := by
        rcases hc with hh | hh
        · omega
        · exact hh
      simp [color,point,ht0,hr]
  have hx : FacePath (Fiber a b p q 0) (point x 0 0) (point 0 0 0) := by
    apply axis_x
    intro t ht hu
    refine ⟨by simp [box_point,lengthX,lengthY] at *; omega,by simp [color,point]⟩
  exact hy.trans hx

theorem zero_lane_mem (p q : Equiv.Perm (Fin a)) (x z : ℤ) (hz : 0≤z ∧ z≤7)
    (hx : 0≤x ∧ x < (lengthX a b:ℤ)) (hbase : 4*(a:ℤ)≤x)
    (hr : rail a b x z=0) : Fiber a b p q 0 (point x (2*a) z) := by
  have ha := NeZero.pos a
  refine ⟨by simp [box_point,lengthY]; omega,?_⟩
  have hy : 2*(a:ℤ)≠0 := by omega
  by_cases h0 : z=0
  · subst z
    simpa [color,point,hy] using hr
  · by_cases h7 : z=7
    · subst z
      simpa [color,point] using hr
    · simp [color,point,h0,h7,hbase,hr]

theorem lane_zero (p q : Equiv.Perm (Fin a)) (x z : ℤ)
    (hz : 0≤z ∧ z≤7) (hx : 4*(a:ℤ)≤x ∧ x < (lengthX a b:ℤ)) (hr : rail a b x z=0) :
    FacePath (Fiber a b p q 0) (point x (2*a) z) (point 0 0 0) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  obtain hleft | hright := (rail_zero_iff a b x z).mp hr
  · have hm : FacePath (Fiber a b p q 0) (point x (2*a) z) (point (4*a) (2*a) z) := by
      apply axis_x
      intro t ht hu
      apply zero_lane_mem a b p q t z hz (by simp [lengthX] at *; omega) (by omega)
      apply (rail_zero_iff a b t z).mpr
      left; omega
    have hd : FacePath (Fiber a b p q 0) (point (4*a) (2*a) z) (point (4*a) (2*a) 0) := by
      apply axis_z
      intro t ht hu
      apply zero_lane_mem a b p q _ t (by omega) (by simp [lengthX] <;> omega) (by omega)
      apply (rail_zero_iff a b _ t).mpr
      left; omega
    exact (hm.trans hd).trans (bottom_zero a b p q _ _ (by
      apply zero_lane_mem a b p q _ 0 (by omega) (by simp [lengthX] <;> omega) (by omega)
      apply (rail_zero_iff a b _ 0).mpr; left; omega))
  · let c : ℤ := (lengthX a b:ℤ)-1
    have hm : FacePath (Fiber a b p q 0) (point x (2*a) z) (point c (2*a) z) := by
      apply axis_x
      intro t ht hu
      apply zero_lane_mem a b p q t z hz (by dsimp [c] at *; simp [lengthX] at *; omega) (by dsimp [c] at *; simp [lengthX] at *; omega)
      apply (rail_zero_iff a b t z).mpr
      right; dsimp [c] at *; simp [lengthX] at *; omega
    have hd : FacePath (Fiber a b p q 0) (point c (2*a) z) (point c (2*a) 0) := by
      apply axis_z
      intro t ht hu
      apply zero_lane_mem a b p q c t (by omega) (by dsimp [c]; simp [lengthX] <;> omega) (by dsimp [c]; simp [lengthX] <;> omega)
      apply (rail_zero_iff a b c t).mpr
      right; dsimp [c]; simp [lengthX] <;> omega
    exact (hm.trans hd).trans (bottom_zero a b p q _ _ (by
      apply zero_lane_mem a b p q c 0 (by omega) (by dsimp [c]; simp [lengthX] <;> omega) (by dsimp [c]; simp [lengthX] <;> omega)
      apply (rail_zero_iff a b c 0).mpr; right; dsimp [c]; simp [lengthX] <;> omega))

theorem origin_mem (p q : Equiv.Perm (Fin a)) (z : ℤ) (hz : 0≤z ∧ z≤7) :
    Fiber a b p q 0 (point 0 0 z) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hr (t : ℤ) (ht : 0≤t) : rail a b 0 t=0 :=
    (rail_zero_iff a b 0 t).mpr (Or.inl (by omega))
  refine ⟨by simp [box_point,lengthX,lengthY]; omega,?_⟩
  simp [color,point,small,show ¬4*(a:ℤ)≤0 by omega,
    show (0:ℤ)<a by exact_mod_cast ha,FourLayer.band,ha,hr 0 (by omega),hr 7 (by omega)]

theorem top_zero (p q : Equiv.Perm (Fin a)) (x y : ℤ)
    (hv : Fiber a b p q 0 (point x y 7)) :
    FacePath (Fiber a b p q 0) (point x y 7) (point 0 0 0) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos b
  have hbox := hv.1
  simp only [box_point] at hbox
  have hr : rail a b x 7=0 := by simpa [color,point] using hv.2
  obtain hl | hu := (rail_zero_iff a b x 7).mp hr
  · have hx : FacePath (Fiber a b p q 0) (point x y 7) (point 0 y 7) := by
      apply axis_x
      intro t ht hu
      refine ⟨by simp [box_point,lengthX,lengthY] at *; omega,?_⟩
      have ht0 : rail a b t 7=0 := (rail_zero_iff a b t 7).mpr (Or.inl (by omega))
      simpa [color,point] using ht0
    have hy : FacePath (Fiber a b p q 0) (point 0 y 7) (point 0 0 7) := by
      apply axis_y
      intro t ht hu
      refine ⟨by simp [box_point,lengthX,lengthY] at *; omega,?_⟩
      have ht0 : rail a b 0 7=0 := (rail_zero_iff a b 0 7).mpr (Or.inl (by omega))
      simpa [color,point] using ht0
    have hz : FacePath (Fiber a b p q 0) (point 0 0 7) (point 0 0 0) := by
      apply axis_z
      intro t ht hu
      apply origin_mem a b p q t
      omega
    exact (hx.trans hy).trans hz
  · let c : ℤ := (lengthX a b:ℤ)-1
    have hx : FacePath (Fiber a b p q 0) (point x y 7) (point c y 7) := by
      apply axis_x
      intro t ht hu'
      refine ⟨by dsimp [c] at *; simp [box_point,lengthX,lengthY] at *; omega,?_⟩
      have ht0 : rail a b t 7=0 := (rail_zero_iff a b t 7).mpr (Or.inr (by dsimp [c] at *; simp [lengthX] at *; omega))
      simpa [color,point] using ht0
    have hc : 4*(a:ℤ)≤c ∧ c < (lengthX a b:ℤ) := by dsimp [c]; simp [lengthX]; omega
    have hrc : rail a b c 7=0 := (rail_zero_iff a b c 7).mpr (Or.inr (by dsimp [c]; simp [lengthX]; omega))
    have hy : FacePath (Fiber a b p q 0) (point c y 7) (point c (2*a) 7) := by
      apply axis_y
      intro t ht hu'
      refine ⟨by dsimp [c] at *; simp [box_point,lengthX,lengthY] at *; omega,?_⟩
      simpa [color,point] using hrc
    exact (hx.trans hy).trans (lane_zero a b p q c 7 (by omega) hc hrc)

theorem zero_to_origin (p q : Equiv.Perm (Fin a)) (v : Lattice 3)
    (hv : Fiber a b p q 0 v) : FacePath (Fiber a b p q 0) v (point 0 0 0) := by
  have ha := NeZero.pos a
  have hvv : v=point (v 0) (v 1) (v 2) := by ext k; fin_cases k <;> rfl
  have hbox := hv.1
  dsimp [Box] at hbox
  by_cases h0 : v 2=0
  · have hh := bottom_zero a b p q (v 0) (v 1) (by rw [←h0,←hvv]; exact hv)
    have hp : point (v 0) (v 1) 0=v := by rw [←h0]; exact hvv.symm
    rw [hp] at hh
    exact hh
  by_cases h7 : v 2=7
  · have hh := top_zero a b p q (v 0) (v 1) (by rw [←h7,←hvv]; exact hv)
    have hp : point (v 0) (v 1) 7=v := by rw [←h7]; exact hvv.symm
    rw [hp] at hh
    exact hh
  have hz : 1≤v 2 ∧ v 2≤6 := by omega
  by_cases hline : 4*(a:ℤ)≤v 0 ∧ v 1=2*(a:ℤ)
  · have hr : rail a b (v 0) (v 2)=0 := by simpa [color,h0,h7,hline] using hv.2
    have hh := lane_zero a b p q (v 0) (v 2) (by omega) ⟨hline.1,hbox.2.1⟩ hr
    rw [←hline.2,←hvv] at hh
    exact hh
  · have hc : v 0<4*(a:ℤ) ∨ v 1≠2*(a:ℤ) := by omega
    have hh := small_to_hub a b p q (0 : Fin a) v hv hz hc
    have hc0 : FacePath (Fiber a b p q 0) (point 0 0 0) (hub a (0 : Fin a)) := by
      apply axis_z
      intro t ht hu
      apply origin_mem a b p q t
      omega
    exact hh.trans (FacePath.reverse hc0)

theorem rail_cases (x z : ℤ) : rail a b x z=0 ∨
    ∃ i : ℕ, 0 < i ∧ i < b ∧ rail a b x z=a+i := by
  dsimp only [rail]
  split_ifs with h
  · right
    refine ⟨((x-4*a-z)/7).toNat,?_,?_,rfl⟩ <;> omega
  · exact Or.inl rfl

theorem color_cases (p q : Equiv.Perm (Fin a)) (v : Lattice 3) :
    color a b p q v < a ∨ ∃ i : ℕ, 0 < i ∧ i < b ∧ color a b p q v=a+i := by
  have hrail (x z : ℤ) : rail a b x z < a ∨ ∃ i : ℕ, 0 < i ∧ i < b ∧ rail a b x z=a+i := by
    rcases rail_cases a b x z with hh | hh
    · left; rw [hh]; exact NeZero.pos a
    · exact Or.inr hh
  unfold color
  split_ifs
  · left; exact NeZero.pos a
  · exact hrail _ _
  · exact hrail _ _
  · exact hrail _ _
  · left; exact small_lt a p q _ _ _

theorem small_nonzero_position (p q : Equiv.Perm (Fin a)) (j : Fin a) (hj : j.val≠0)
    (v : Lattice 3) (hv : Fiber a b p q j.val v) :
    (1≤v 2 ∧ v 2≤6) ∧ (v 0<4*(a:ℤ) ∨ v 1≠2*(a:ℤ)) := by
  have hc := hv.2
  have hbox := hv.1
  dsimp [Box] at hbox
  have hr (x z : ℤ) (he : rail a b x z=j.val) : False := by
    apply hj
    exact he.symm.trans (rail_small a b x z (by rw [he]; exact j.isLt))
  unfold color at hc
  split_ifs at hc with h0 hy h7 hline
  · exact (hj hc.symm).elim
  · exact (hr _ _ hc).elim
  · exact (hr _ _ hc).elim
  · exact (hr _ _ hc).elim
  · constructor <;> omega

theorem fiber_connected (p q : Equiv.Perm (Fin a)) (i : ℕ) {v w : Lattice 3}
    (hv : Fiber a b p q i v) (hw : Fiber a b p q i w) : FacePath (Fiber a b p q i) v w := by
  by_cases hi : i=0
  · subst i
    exact (zero_to_origin a b p q v hv).trans (FacePath.reverse (zero_to_origin a b p q w hw))
  by_cases hs : i < a
  · let j : Fin a := ⟨i,hs⟩
    have hposv := small_nonzero_position a b p q j hi v hv
    have hposw := small_nonzero_position a b p q j hi w hw
    exact (small_to_hub a b p q j v hv hposv.1 hposv.2).trans
      (FacePath.reverse (small_to_hub a b p q j w hw hposw.1 hposw.2))
  · obtain ⟨k,hk,hkb,he⟩ := (color_cases a b p q v).resolve_left (by rw [hv.2]; exact hs)
    have hik : i=a+k := hv.2.symm.trans he
    have hvv : v=point (v 0) (v 1) (v 2) := by ext r; fin_cases r <;> rfl
    have hww : w=point (w 0) (w 1) (w 2) := by ext r; fin_cases r <;> rfl
    rw [hik] at hv hw ⊢
    rw [hvv] at hv ⊢
    rw [hww] at hw ⊢
    exact (positive_to_root a b p q k hk hkb _ _ _ hv).trans
      (FacePath.reverse (positive_to_root a b p q k hk hkb _ _ _ hw))

end
end TranslationTiling.Rails
