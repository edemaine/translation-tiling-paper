import TranslationTiling.FourLayer.Boundary
import TranslationTiling.FourLayer.EffectiveMatching
import TranslationTiling.Compiler.GeometricSizeBound

namespace TranslationTiling.FourLayer
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def boundaryList (A B : ℕ) : Tile 3 :=
  0 :: (Kim.cube (max A B)).filter (fun v => decide (Boundary ![A,A,B] v ∧ v≠0))

instance boundaryLength_neZero (A B : ℕ) : NeZero (boundaryList A B).length :=
  ⟨by simp [boundaryList]⟩

@[fun_prop] theorem boundaryList_primrec : Primrec (fun z : ℕ×ℕ => boundaryList z.1 z.2) := by
  have hb : PrimrecPred (fun z : (ℕ×ℕ)×Lattice 3 => Boundary ![z.1.1,z.1.1,z.1.2] z.2 ∧ z.2≠0) := by
    simp [Boundary,Rect,Fin.forall_fin_succ,Fin.exists_fin_succ]
    fun_prop
  unfold boundaryList
  apply Primrec.list_cons.comp (Primrec.const 0)
  exact filterList (by fun_prop) hb

theorem boundaryList_nodup (A B : ℕ) : (boundaryList A B).Nodup := by
  have hc : (Kim.cube (max A B)).Nodup := by
    apply List.nodup_iff_length_dedup_eq.mpr
    rw [← List.card_toFinset,Kim.cube_card,Compiler.Size.kim_cube_length]
  constructor
  · simp only [List.mem_filter,decide_eq_true_eq]
    rintro a ⟨_,_,h⟩ he
    exact h he.symm
  · exact hc.filter _

theorem boundaryList_required (A B : ℕ) : Required (boundaryList A B) := by
  intro i hi j hj
  by_cases h : i=j
  · exact Or.inl h
  · right
    intro he
    rw [List.getD_eq_getElem _ _ (List.mem_range.mp hi),List.getD_eq_getElem _ _ (List.mem_range.mp hj)] at he
    exact h ((boundaryList_nodup A B).getElem_inj_iff.mp he)

theorem mem_range_slots (X : Tile 3) (v : Lattice 3) : v∈Set.range (slots X) ↔ v∈X := by
  constructor
  · rintro ⟨i,rfl⟩
    simp only [slots,List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem i.isLt
  · intro hv
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hv
    refine ⟨⟨i,hi⟩,?_⟩
    change X.getD i 0=v
    rw [List.getD_eq_getElem _ _ hi]
    exact he

theorem boundaryList_mem (A B : ℕ) (hA : 0<A) (hAB : A≤B) (v : Lattice 3) :
    v∈boundaryList A B ↔ Boundary ![A,A,B] v := by
  have hB : 0<B := lt_of_lt_of_le hA hAB
  have hz : Boundary ![A,A,B] (0 : Lattice 3) := (mem_boundaryFinset _ _).mp (boundary_zero _ (by intro i; fin_cases i <;> simp <;> assumption))
  simp only [boundaryList,List.mem_cons,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨_,hv,_⟩)
    · exact hz
    · exact hv
  · intro hv
    by_cases he : v=0
    · exact Or.inl he
    · right
      refine ⟨?_,hv,he⟩
      rw [Nat.max_eq_right hAB]
      apply (Kim.mem_cube_iff B _).mpr
      intro i
      have h := hv.1 i
      fin_cases i
      · change 0≤v 0 ∧ v 0<(A:ℤ) at h
        change 0≤v 0 ∧ v 0<(B:ℤ)
        omega
      · change 0≤v 1 ∧ v 1<(A:ℤ) at h
        change 0≤v 1 ∧ v 1<(B:ℤ)
        omega
      · simpa using h

theorem boundaryList_length_le (A B : ℕ) (hA : 0<A) (hAB : A≤B) :
    (boundaryList A B).length≤6*A*B := by
  have he : (boundaryList A B).toFinset=boundaryFinset ![A,A,B] := by
    ext v
    simp [boundaryList_mem A B hA hAB]
  rw [← List.toFinset_card_of_nodup (boundaryList_nodup A B),he]
  exact boundary_card_le A B hAB

theorem boundary_slots_zero (A B : ℕ) : slots (boundaryList A B) 0=0 := by
  simp [slots,boundaryList]

theorem boundary_slots_path (A B : ℕ) (hA : 0<A) (hAB : A≤B)
    (i j : Fin (boundaryList A B).length) :
    FacePath (Set.range (slots (boundaryList A B))) (slots (boundaryList A B) i) (slots (boundaryList A B) j) := by
  have hmem (i : Fin (boundaryList A B).length) : Boundary ![A,A,B] (slots (boundaryList A B) i) :=
    (boundaryList_mem A B hA hAB _).mp ((mem_range_slots _ _).mp ⟨i,rfl⟩)
  have hr : ∀ i : Fin 3, 0<(![A,A,B] : Fin 3→ℕ) i := by
    have hB : 0<B := lt_of_lt_of_le hA hAB
    intro i; fin_cases i <;> simp <;> assumption
  exact (boundary_connected _ hr (hmem i) (hmem j)).mono (fun v hv =>
    (mem_range_slots _ _).mpr ((boundaryList_mem A B hA hAB v).mpr hv))

theorem boundary_slots_difference (A B : ℕ) (hA : 0<A) (hAB : A≤B) {u v : Lattice 3}
    (hu : Rect ![A,A,B] u) (hv : Rect ![A,A,B] v) (hne : u≠v) :
    ∃ i j : Fin (boundaryList A B).length, i≠j ∧ u+slots (boundaryList A B) i=v+slots (boundaryList A B) j := by
  obtain ⟨a,b,ha,hb,he,hab⟩ := boundary_difference hu hv hne
  obtain ⟨i,hi⟩ := (mem_range_slots _ a).mpr ((boundaryList_mem A B hA hAB a).mpr ha)
  obtain ⟨j,hj⟩ := (mem_range_slots _ b).mpr ((boundaryList_mem A B hA hAB b).mpr hb)
  refine ⟨i,j,?_,?_⟩
  · intro hij
    apply hab
    rw [← hi,← hj,hij]
  · simpa only [hi,hj] using he

end
end TranslationTiling.FourLayer
