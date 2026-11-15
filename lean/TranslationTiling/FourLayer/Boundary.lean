import TranslationTiling.FourLayer.Rectangle
import TranslationTiling.FourLayer.Residues
import Mathlib.Algebra.BigOperators.Fin

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def boundaryFinset (r : Fin 3 → ℕ) : Finset (Lattice 3) :=
  (boxFinset r).filter (Boundary r)

@[simp] theorem mem_boundaryFinset (r : Fin 3 → ℕ) (v : Lattice 3) :
    v∈boundaryFinset r ↔ Boundary r v := by
  simp [boundaryFinset,Boundary]

def endpoint (a : ℕ) (e : Fin 2) : ℤ := if e=0 then 0 else (a:ℤ)-1

def facePoint (A B : ℕ) (t : Fin 3×Fin 2×Fin A×Fin B) : Lattice 3 :=
  if t.1=0 then ![endpoint A t.2.1,t.2.2.1.val,t.2.2.2.val]
  else if t.1=1 then ![t.2.2.1.val,endpoint A t.2.1,t.2.2.2.val]
  else ![t.2.2.1.val,t.2.2.2.val,endpoint B t.2.1]

theorem boundary_card_le (A B : ℕ) (hAB : A≤B) :
    (boundaryFinset ![A,A,B]).card≤6*A*B := by
  have hep (a : ℕ) (z : ℤ) (hz : z=0 ∨ z=(a:ℤ)-1) : ∃ e : Fin 2, z=endpoint a e := by
    rcases hz with rfl | rfl
    · exact ⟨0,by simp [endpoint]⟩
    · exact ⟨1,by simp [endpoint]⟩
  have hcover (v : Lattice 3) (hv : Boundary ![A,A,B] v) :
      ∃ t : Fin 3×Fin 2×Fin A×Fin B, facePoint A B t=v := by
    obtain ⟨hbox,k,hk⟩ := hv
    have h0 := hbox 0; have h1 := hbox 1; have h2 := hbox 2
    change 0≤v 0 ∧ v 0<(A:ℤ) at h0
    change 0≤v 1 ∧ v 1<(A:ℤ) at h1
    change 0≤v 2 ∧ v 2<(B:ℤ) at h2
    fin_cases k
    · obtain ⟨e,he⟩ := hep A (v 0) hk
      refine ⟨(0,e,⟨(v 1).toNat,by omega⟩,⟨(v 2).toNat,by omega⟩),?_⟩
      ext j; fin_cases j <;> simp [facePoint] <;> omega
    · obtain ⟨e,he⟩ := hep A (v 1) hk
      refine ⟨(1,e,⟨(v 0).toNat,by omega⟩,⟨(v 2).toNat,by omega⟩),?_⟩
      ext j; fin_cases j <;> simp [facePoint] <;> omega
    · obtain ⟨e,he⟩ := hep B (v 2) hk
      refine ⟨(2,e,⟨(v 0).toNat,by omega⟩,⟨(v 1).toNat,by omega⟩),?_⟩
      ext j; fin_cases j <;> simp [facePoint] <;> omega
  have hsub : boundaryFinset ![A,A,B]⊆Finset.univ.image (facePoint A B) := by
    intro v hv
    obtain ⟨t,ht⟩ := hcover v ((mem_boundaryFinset _ _).mp hv)
    exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,ht⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_image_le.trans
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  nlinarith

theorem boundary_zero (r : Fin 3 → ℕ) (hr : ∀ i, 0<r i) :
    (0 : Lattice 3)∈boundaryFinset r := by
  apply (mem_boundaryFinset _ _).mpr
  refine ⟨fun i => ⟨by simp,by simpa using hr i⟩,0,Or.inl rfl⟩

end
end TranslationTiling.FourLayer
