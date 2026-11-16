import TranslationTiling.Rails.Slots

namespace TranslationTiling.Rails
open FourLayer (Rect gridMap)
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem slot_path_zero (A B : ℕ) (hB : 0<B) (v : Lattice 3) (hv : SlotSet A B v) :
    FacePath (SlotSet A B) v 0 := by
  rcases hv with hp | ⟨h0,h1,h2,hB'⟩
  · apply FacePath.box3 _ ![-(A:ℤ),-(A:ℤ),0] ![(A:ℤ),(A:ℤ),0] v 0
    · intro k; fin_cases k <;> simp [Plane] at hp ⊢ <;> omega
    · intro k; fin_cases k <;> simp
    · intro z hz
      left
      have hx := hz 0; have hy := hz 1; have hz' := hz 2
      simp at hx hy hz'
      exact ⟨hx.1,hx.2,hy.1,hy.2,by omega⟩
  · apply FacePath.box3 _ (0 : Lattice 3) ![0,0,v 2] v 0
    · intro k; fin_cases k <;> simp_all
    · intro k; fin_cases k <;> simp_all
    · intro z hz
      right
      have hx := hz 0; have hy := hz 1; have hz' := hz 2
      simp at hx hy hz'
      exact ⟨by omega,by omega,hz'.1,by omega⟩

theorem slot_path (A B i j : ℕ) (hB : 0<B)
    (hi : Used (planeList A).length B i) (hj : Used (planeList A).length B j) :
    FacePath (fun v => ∃ k, Used (planeList A).length B k ∧ slot A k=v) (slot A i) (slot A j) :=
  FacePath.mono ((slot_path_zero A B hB _ (used_slot A B i hB hi)).trans
    (FacePath.reverse (slot_path_zero A B hB _ (used_slot A B j hB hj))))
      (fun v hv => slot_exists A B hB v hv)

theorem slot_difference (A B : ℕ) (hA : 0<A) (hB : 0<B) {u v : Lattice 3}
    (hu : Rect ![A,A,B] u) (hv : Rect ![A,A,B] v) :
    ∃ i : Fin B, ∃ j : Fin (planeList A).length,
      (u+slot A (railLabel (planeList A).length i.val)=v+slot A j.val) ∨
      (v+slot A (railLabel (planeList A).length i.val)=u+slot A j.val) := by
  have hu0 := hu 0; have hu1 := hu 1; have hu2 := hu 2
  have hv0 := hv 0; have hv1 := hv 1; have hv2 := hv 2
  simp at hu0 hu1 hu2 hv0 hv1 hv2
  have forward (x y : Lattice 3) (h0 : -(A:ℤ)≤x 0-y 0 ∧ x 0-y 0≤A)
      (h1 : -(A:ℤ)≤x 1-y 1 ∧ x 1-y 1≤A) (h2 : 0≤y 2-x 2 ∧ y 2-x 2<(B:ℤ)) :
      ∃ i : Fin B, ∃ j : Fin (planeList A).length,
        x+slot A (railLabel (planeList A).length i.val)=y+slot A j.val := by
    let w := point (x 0-y 0) (x 1-y 1) 0
    have hw : Plane A w := by
      simp [Plane,w,point]
      omega
    obtain ⟨j,hj⟩ := (FourLayer.mem_range_slots (planeList A) w).mpr ((planeList_mem A w).mpr hw)
    refine ⟨⟨(y 2-x 2).toNat,by omega⟩,j,?_⟩
    rw [slot_rail,slot_small,hj]
    ext k; fin_cases k <;> simp [w,point] <;> omega
  by_cases h : u 2≤v 2
  · obtain ⟨i,j,he⟩ := forward u v (by omega) (by omega) (by omega)
    exact ⟨i,j,Or.inl he⟩
  · obtain ⟨i,j,he⟩ := forward v u (by omega) (by omega) (by omega)
    exact ⟨i,j,Or.inr he⟩

end
end TranslationTiling.Rails
