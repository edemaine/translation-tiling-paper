/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.CycleTests
import TranslationTiling.Proofs.SudokuSoundness
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.FinCases

set_option maxRecDepth 1000

namespace TranslationTiling

noncomputable section

namespace Compiler


variable {T : LeanWang.TileSet}

/-- Both arithmetic digits take the seed value; the Wang decoration is unrestricted. -/
def SeedSet (t : Fin 2) (j : Symbol T) : Prop :=
  j.1.val = (t.val + 1 : ℕ) ∧ j.2.1.val = (t.val + 1 : ℕ)

noncomputable def columnResidueEquiv : Sudoku.Column ≃ ZMod residueModulus :=
  (finCongr residueModulus_eq.symm).trans (ZMod.finEquiv residueModulus)

def ordinaryCycle (T : LeanWang.TileSet) : ZMod residueModulus ↪ Channel T where
  toFun j := .inl (columnResidueEquiv.symm j)
  inj' _ _ h := columnResidueEquiv.symm.injective (Sum.inl.inj h)

def ordinaryCycleLabels (w : Word T) (j : ZMod residueModulus) :
    Label T (ordinaryCycle T j) :=
  w (columnResidueEquiv.symm j)

def seedCycle (t : Fin 2) (n : Column T) : ZMod 2 ↪ Channel T where
  toFun j := Fin.cases (.inr t) (fun _ => .inl n) j
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · change Sum.inr t = Sum.inl n at h
      cases h
    · change Sum.inl n = Sum.inr t at h
      cases h
    · rfl

@[simp] theorem seedCycle_zero
    {T : LeanWang.TileSet}
    (t : Fin 2) (n : Column T) :
    seedCycle t n 0 = .inr t := rfl

@[simp] theorem seedCycle_one
    {T : LeanWang.TileSet}
    (t : Fin 2) (n : Column T) :
    seedCycle t n 1 = .inl n := rfl

def seedCycleLabels (t : Fin 2) (n : Column T) (j : Symbol T) (z : ZMod 2) :
    Label T (seedCycle t n z) :=
  Fin.cases (motive := fun z : Fin 2 => Label T (seedCycle t n z))
    () (fun _ => j) z

@[simp] theorem seedCycleLabels_zero
    {T : LeanWang.TileSet}
    (t : Fin 2) (n : Column T) (j : Symbol T) :
    seedCycleLabels t n j 0 = () := rfl

@[simp] theorem seedCycleLabels_one
    {T : LeanWang.TileSet}
    (t : Fin 2) (n : Column T) (j : Symbol T) :
    seedCycleLabels t n j 1 = j := rfl

variable (E : EncodingParameters T)

theorem ordinaryCycle_exclusion_iff (w : Word T) (o : GraphOutputs E)
    (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (∀ n : Column T, Active E o (.inl n) x (w n)) := by
  classical
  rw [cycle_exclusion_iff E (ordinaryCycle T) (ordinaryCycleLabels w) o hdep]
  constructor
  · intro h x hall
    obtain ⟨z, hz⟩ := h x
    exact hz (hall (columnResidueEquiv.symm z))
  · intro h x
    obtain ⟨n, hn⟩ := not_forall.mp (h x)
    refine ⟨columnResidueEquiv n, ?_⟩
    exact Eq.mpr
      (congrArg (fun m : Column T => ¬ Active E o (.inl m) x (w m))
        (columnResidueEquiv.symm_apply_apply n)) hn

theorem seedCycle_exclusion_iff (t : Fin 2) (n : Column T) (j : Symbol T)
    (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (Active E o (.inr t) x () ∧ Active E o (.inl n) x j) := by
  classical
  rw [cycle_exclusion_iff E (seedCycle t n) (seedCycleLabels t n j) o hdep]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := h x
    fin_cases z
    · exact hz hx.1
    · exact hz hx.2
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · refine ⟨1, ?_⟩
      change ¬ Active E o (.inl n) x j
      intro hj
      exact h x ⟨hs, hj⟩
    · exact ⟨0, hs⟩

def wordConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)).biUnion
    (fun w => cycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w))

def seedConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
      ¬ SeedSet q.1 q.2.2)).biUnion
    (fun q => cycleTiles E (seedCycle q.1 q.2.1) (seedCycleLabels q.1 q.2.1 q.2.2))

theorem nonempty_of_mem_wordConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ wordConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨w, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w) hF

theorem nonempty_of_mem_seedConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ seedConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨q, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (seedCycle q.1 q.2.1)
    (seedCycleLabels q.1 q.2.1 q.2.2) hF

theorem wordConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ wordConstraintTiles E, Tiles F (graph o)) ↔
      ∀ x w, (∀ n : Column T, Active E o (.inl n) x (w n)) → Allowed T w := by
  classical
  constructor
  · intro h x w hw
    by_contra hnot
    have hcycle : ∀ F ∈ cycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨w, by simp [hnot], hF⟩
    exact (ordinaryCycle_exclusion_iff E w o hdep).mp hcycle x hw
  · intro h F hF
    obtain ⟨w, hw, hF⟩ := Finset.mem_biUnion.mp hF
    have hnot : ¬ Allowed T w := by simpa using (Finset.mem_filter.mp hw).2
    apply (ordinaryCycle_exclusion_iff E w o hdep).mpr ?_ F hF
    intro x hx
    exact hnot (h x w hx)

theorem seedConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ seedConstraintTiles E, Tiles F (graph o)) ↔
      ∀ t n x j, Active E o (.inr t) x () → Active E o (.inl n) x j →
        SeedSet t j := by
  classical
  constructor
  · intro h t n x j hseed hord
    by_contra hj
    have hcycle : ∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨(t, n, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hF⟩
    exact (seedCycle_exclusion_iff E t n j o hdep).mp hcycle x ⟨hseed, hord⟩
  · intro h F hF
    obtain ⟨⟨t, n, j⟩, hq, hF⟩ := Finset.mem_biUnion.mp hF
    have hj : ¬ SeedSet t j := (Finset.mem_filter.mp hq).2
    apply (seedCycle_exclusion_iff E t n j o hdep).mpr ?_ F hF
    intro x hx
    exact hj (h t n x j hx.1 hx.2)

end Compiler

end

end TranslationTiling
