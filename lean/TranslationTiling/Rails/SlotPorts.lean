import TranslationTiling.Rails.SlotGeometry

namespace TranslationTiling.Rails
open FourLayer (gridMap)
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem slot_large (A k : ℕ) (hk : 0<k) :
    slot A ((planeList A).length+k)=point 0 0 k := by
  have he : (planeList A).length+k=railLabel (planeList A).length k := by simp [railLabel,show k≠0 by omega]
  rw [he,slot_rail]

theorem slot_neighbor (A B i j : ℕ)
    (hi : Used (planeList A).length B i) (hj : Used (planeList A).length B j)
    (k : Fin 3) (he : slot A j=slot A i+Pi.single k 1) :
    ((k=0 ∨ k=1) ∧ i<(planeList A).length ∧ j<(planeList A).length) ∨
    (k=2 ∧ ∃ r : ℕ, r<B ∧ r+1<B ∧
      i=railLabel (planeList A).length r ∧ j=railLabel (planeList A).length (r+1)) := by
  rcases hi with hi | ⟨r,hr,hrB,rfl⟩ <;> rcases hj with hj | ⟨s,hs,hsB,rfl⟩
  · have hiz := (slot_small_plane A i hi).2.2.2.2
    have hjz := (slot_small_plane A j hj).2.2.2.2
    fin_cases k
    · exact Or.inl ⟨Or.inl rfl,hi,hj⟩
    · exact Or.inl ⟨Or.inr rfl,hi,hj⟩
    · have hh := congrFun he 2
      simp at hh
      omega
  · have hiz := (slot_small_plane A i hi).2.2.2.2
    have hz := congrFun he 2
    rw [slot_large A s hs] at hz
    fin_cases k
    · simp [point] at hz; omega
    · simp [point] at hz; omega
    · have hs1 : s=1 := by simp [point] at hz; omega
      have hi0 : i=0 := by
        apply slot_injective A B i 0 (Or.inl hi) (Or.inl (NeZero.pos _))
        rw [slot_zero]
        ext l
        have hh := congrFun he l
        rw [slot_large A s hs] at hh
        fin_cases l <;> simp [point] at hh ⊢ <;> omega
      right
      refine ⟨rfl,0,by omega,by omega,?_,?_⟩
      · simpa [railLabel] using hi0
      · simp [railLabel,hs1]
  · have hjz := (slot_small_plane A j hj).2.2.2.2
    have hz := congrFun he 2
    rw [slot_large A r hr] at hz
    fin_cases k <;> simp [point] at hz <;> omega
  · rw [slot_large A r hr,slot_large A s hs] at he
    fin_cases k
    · have hh := congrFun he 0; simp [point] at hh
    · have hh := congrFun he 1; simp [point] at hh
    · have hz := congrFun he 2
      have hrs : s=r+1 := by simp [point] at hz; omega
      right
      refine ⟨rfl,r,hrB,by omega,?_,?_⟩
      · simp [railLabel,show r≠0 by omega]
      · simp [railLabel,hrs]

theorem slot_ports (A B : ℕ) [NeZero B]
    (p q : Equiv.Perm (Fin (planeList A).length))
    (hp : ∀ i j, FourLayer.slots (planeList A) j=FourLayer.slots (planeList A) i+Pi.single 0 1 → p j=i)
    (hq : ∀ i j, FourLayer.slots (planeList A) j=FourLayer.slots (planeList A) i+Pi.single 1 1 → q j=i)
    (i j : ℕ) (hi : Used (planeList A).length B i) (hj : Used (planeList A).length B j)
    (k : Fin 3) (he : slot A j=slot A i+Pi.single k 1) :
    ∃ r t, MicroFiber (planeList A).length B p q i r ∧ MicroFiber (planeList A).length B p q j t ∧
      r+Pi.single k 1=gridMap (scales (planeList A).length B) (Pi.single k 1)+t := by
  rcases slot_neighbor A B i j hi hj k he with ⟨hk,hi,hj⟩ | ⟨rfl,r,hr,hr1,rfl,rfl⟩
  · have he' : FourLayer.slots (planeList A) ⟨j,hj⟩=FourLayer.slots (planeList A) ⟨i,hi⟩+Pi.single k 1 := by
      rw [←slot_small A ⟨i,hi⟩,←slot_small A ⟨j,hj⟩]
      exact he
    rcases hk with rfl | rfl
    · have hh := hp ⟨i,hi⟩ ⟨j,hj⟩ he'
      simpa only [hh] using x_micro_contact (planeList A).length B p q ⟨j,hj⟩
    · have hh := hq ⟨i,hi⟩ ⟨j,hj⟩ he'
      simpa only [hh] using y_micro_contact (planeList A).length B p q ⟨j,hj⟩
  · exact z_micro_contact (planeList A).length B p q ⟨r,hr⟩ hr1

end
end TranslationTiling.Rails
