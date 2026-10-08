import TranslationTiling.External.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-! Bounds and boundary descriptions for MSS's centered boxes and frames. -/

namespace TranslationTiling.MSS

open scoped Classical

theorem mem_box_iff (k : ℕ) (v : Lattice 3) :
    v ∈ box k ↔ ∀ i, -(k : ℤ) ≤ v i ∧ v i ≤ k := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mem_frame_iff (k : ℕ) (hk : 0 < k) (v : Lattice 3) :
    v ∈ frame k ↔ (∀ i, -(k : ℤ) ≤ v i ∧ v i ≤ k) ∧
      ∃ i, v i = -(k : ℤ) ∨ v i = k := by
  rw [frame, Finset.mem_sdiff, mem_box_iff, mem_box_iff]
  constructor
  · rintro ⟨hv, hn⟩
    refine ⟨hv, ?_⟩
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    have := hv i
    exact ⟨i, by omega⟩
  · rintro ⟨hv, i, hi⟩
    refine ⟨hv, ?_⟩
    intro hn
    have := hn i
    rcases hi with hi | hi <;> omega

def bodyCenter (i : Fin 4) : Lattice 3 :=
  ![0, ![213, 0, 0], ![24, 201, 0], ![36, 0, 201]] i

def bodyRadius (i : Fin 4) : ℕ := ![100, 1, 2, 3] i

/-- The detached frames and the main body lie in four separated boxes. -/
theorem baseShape_bounds (v : Lattice 3) (hv : v ∈ baseShape) :
    ∃ i : Fin 4, ∀ k,
      bodyCenter i k - (bodyRadius i : ℤ) ≤ v k ∧
        v k ≤ bodyCenter i k + (bodyRadius i : ℤ) := by
  rcases Finset.mem_union.mp hv with hv | hv
  · refine ⟨0, ?_⟩
    have hb := (mem_box_iff _ _).mp (Finset.mem_sdiff.mp hv).1
    intro k; simpa [bodyCenter, bodyRadius] using hb k
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    have hb := (mem_box_iff _ _).mp (Finset.mem_sdiff.mp hu).1
    fin_cases j
    · refine ⟨1, ?_⟩
      intro k; have := hb k; fin_cases k <;>
        simp [bodyCenter, bodyRadius, marker, scale] at this ⊢ <;> omega
    · refine ⟨2, ?_⟩
      intro k; have := hb k; fin_cases k <;>
        simp [bodyCenter, bodyRadius, marker, scale] at this ⊢ <;> omega
    · refine ⟨3, ?_⟩
      intro k; have := hb k; fin_cases k <;>
        simp [bodyCenter, bodyRadius, marker, scale] at this ⊢ <;> omega

end TranslationTiling.MSS
