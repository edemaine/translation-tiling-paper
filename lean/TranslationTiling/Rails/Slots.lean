import TranslationTiling.Rails.Geometry
import TranslationTiling.FourLayer.EffectiveBoundary

namespace TranslationTiling.Rails
open FourLayer (Rect gridMap matching matching_spec tablePermutation tablePermutation_match TableValid)
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Plane (A : ℕ) (v : Lattice 3) : Prop :=
  -(A:ℤ)≤v 0 ∧ v 0≤A ∧ -(A:ℤ)≤v 1 ∧ v 1≤A ∧ v 2=0

def planeEnum (A : ℕ) : Tile 3 :=
  (List.range (2*A+1)).flatMap fun (i : ℕ) =>
    (List.range (2*A+1)).map fun (j : ℕ) => point ((i:ℤ)-A) ((j:ℤ)-A) 0

def planeList (A : ℕ) : Tile 3 :=
  0 :: (planeEnum A).dedup.filter (fun v => decide (v≠0))

instance planeLength_neZero (A : ℕ) : NeZero (planeList A).length := ⟨by simp [planeList]⟩

@[fun_prop] theorem planeEnum_primrec : Primrec planeEnum := by
  unfold planeEnum point
  fun_prop

@[fun_prop] theorem planeList_primrec : Primrec planeList := by
  unfold planeList
  apply Primrec.list_cons.comp (Primrec.const 0)
  exact filterList (dedup_primrec.comp planeEnum_primrec) (by fun_prop)

theorem planeList_nodup (A : ℕ) : (planeList A).Nodup := by
  constructor
  · simp only [List.mem_filter,List.mem_dedup,decide_eq_true_eq]
    rintro v ⟨_,hv⟩ he
    exact hv he.symm
  · exact (List.nodup_dedup _).filter _

theorem planeList_required (A : ℕ) : FourLayer.Required (planeList A) := by
  intro i hi j hj
  by_cases h : i=j
  · exact Or.inl h
  · right
    intro he
    rw [List.getD_eq_getElem _ _ (List.mem_range.mp hi),List.getD_eq_getElem _ _ (List.mem_range.mp hj)] at he
    exact h ((planeList_nodup A).getElem_inj_iff.mp he)

theorem planeEnum_mem (A : ℕ) (v : Lattice 3) : v∈planeEnum A ↔ Plane A v := by
  simp only [planeEnum,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,j,hj,rfl⟩
    simp [Plane,point]; omega
  · intro hv
    dsimp [Plane] at hv
    refine ⟨(v 0+A).toNat,by omega,(v 1+A).toNat,by omega,?_⟩
    ext k; fin_cases k <;> simp [point] <;> omega

theorem planeList_mem (A : ℕ) (v : Lattice 3) : v∈planeList A ↔ Plane A v := by
  simp only [planeList,List.mem_cons,List.mem_filter,List.mem_dedup,decide_eq_true_eq,planeEnum_mem]
  constructor
  · rintro (rfl | ⟨h,_⟩)
    · simp [Plane]
    · exact h
  · intro h
    by_cases hv : v=0
    · exact Or.inl hv
    · exact Or.inr ⟨h,hv⟩

theorem planeList_length_le (A : ℕ) (hA : 0<A) : (planeList A).length≤10*A^2 := by
  have he : (planeEnum A).length=(2*A+1)^2 := by
    simp [planeEnum,List.length_flatMap,Function.comp_def,List.map_const,List.sum_replicate,pow_two]
  have hd : (planeEnum A).dedup.length≤(planeEnum A).length := by
    simpa only [List.card_toFinset] using List.toFinset_card_le (planeEnum A)
  have hh := (List.length_filter_le (fun v => decide (v≠0)) (planeEnum A).dedup).trans hd
  simp only [planeList,List.length_cons]
  rw [he] at hh
  nlinarith [sq_nonneg (A-1 : ℤ)]

def slot (A i : ℕ) : Lattice 3 :=
  if i<(planeList A).length then (planeList A).getD i 0 else point 0 0 (i-(planeList A).length)

@[simp] theorem slot_small (A : ℕ) (i : Fin (planeList A).length) :
    slot A i.val=FourLayer.slots (planeList A) i := by simp [slot,i.isLt,FourLayer.slots]

@[simp] theorem slot_zero (A : ℕ) : slot A 0=0 := by simp [slot,planeList]

@[simp] theorem slot_rail (A : ℕ) (i : ℕ) :
    slot A (railLabel (planeList A).length i)=point 0 0 i := by
  by_cases hi : i=0
  · subst i; simp [railLabel,point]; ext k; fin_cases k <;> simp
  · have hn : ¬(planeList A).length+i<(planeList A).length := by omega
    simp [slot,railLabel,hi,hn]

theorem slot_small_plane (A : ℕ) (i : ℕ) (hi : i<(planeList A).length) : Plane A (slot A i) := by
  apply (planeList_mem A _).mp
  simp only [slot,if_pos hi,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

def SlotSet (A B : ℕ) (v : Lattice 3) : Prop := Plane A v ∨
  (v 0=0 ∧ v 1=0 ∧ 0≤v 2 ∧ v 2<(B:ℤ))

theorem used_slot (A B i : ℕ) (hB : 0<B) (hi : Used (planeList A).length B i) :
    SlotSet A B (slot A i) := by
  rcases hi with hi | ⟨k,hk,hkb,rfl⟩
  · exact Or.inl (slot_small_plane A i hi)
  · right
    rw [show (planeList A).length+k=railLabel (planeList A).length k by simp [railLabel,show k≠0 by omega],slot_rail]
    simp [point]; omega

theorem slot_exists (A B : ℕ) (hB : 0<B) (v : Lattice 3) (hv : SlotSet A B v) :
    ∃ i, Used (planeList A).length B i ∧ slot A i=v := by
  rcases hv with hp | ⟨h0,h1,h2,hB'⟩
  · obtain ⟨i,hi⟩ := (FourLayer.mem_range_slots (planeList A) v).mpr ((planeList_mem A v).mpr hp)
    exact ⟨i.val,Or.inl i.isLt,(slot_small A i).trans hi⟩
  · by_cases hz : v 2=0
    · refine ⟨0,Or.inl (NeZero.pos _),?_⟩
      rw [slot_zero]; ext k; fin_cases k <;> simp_all
    · refine ⟨railLabel (planeList A).length (v 2).toNat,?_,?_⟩
      · right
        refine ⟨(v 2).toNat,by omega,by omega,?_⟩
        simp [railLabel,show (v 2).toNat≠0 by omega]
      · rw [slot_rail]; ext k; fin_cases k <;> simp [point] <;> omega

theorem slot_injective (A B i j : ℕ)
    (hi : Used (planeList A).length B i) (hj : Used (planeList A).length B j)
    (he : slot A i=slot A j) : i=j := by
  rcases hi with hi | ⟨k,hk,hkb,rfl⟩ <;> rcases hj with hj | ⟨l,hl,hlb,rfl⟩
  · have hh : FourLayer.slots (planeList A) ⟨i,hi⟩=FourLayer.slots (planeList A) ⟨j,hj⟩ := by
      rw [←slot_small A ⟨i,hi⟩,←slot_small A ⟨j,hj⟩]
      exact he
    exact congrArg Fin.val ((FourLayer.slots_injective _ (planeList_required A)) hh)
  · have h := (slot_small_plane A i hi).2.2.2.2
    have hh := congrFun he 2
    simp only [show (planeList A).length+l=railLabel (planeList A).length l by simp [railLabel,show l≠0 by omega],slot_rail] at hh
    simp [point] at hh
    omega
  · have h := (slot_small_plane A j hj).2.2.2.2
    have hh := congrFun he 2
    simp only [show (planeList A).length+k=railLabel (planeList A).length k by simp [railLabel,show k≠0 by omega],slot_rail] at hh
    simp [point] at hh
    omega
  · have hh := congrFun he 2
    simp only [show (planeList A).length+k=railLabel (planeList A).length k by simp [railLabel,show k≠0 by omega],
      show (planeList A).length+l=railLabel (planeList A).length l by simp [railLabel,show l≠0 by omega],slot_rail] at hh
    simp [point] at hh
    omega

attribute [irreducible] planeEnum planeList

end
end TranslationTiling.Rails
