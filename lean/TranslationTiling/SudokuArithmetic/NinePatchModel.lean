import TranslationTiling.SudokuArithmetic.NinePatchClassification
import TranslationTiling.SudokuArithmetic.NinePatchKeys
import Mathlib.Data.List.Enum

namespace TranslationTiling.Sudoku.NinePatch
open Mathlib.Tactic

def lineAgrees (p : Nat) (W : Nat → Nat → Nat) (l : Int × Int) (ab : Nat × Nat) : Prop :=
  ∀ n y, (n,y)∈entries p l → value p ab n≠0 → W n y=value p ab n

def lineAt (p i : Nat) : Int × Int := (lines p)[i]?.getD (0,0)

/-- The assignment records the patch cells and all primitive line explanations. -/
def assignment (p : Nat) (W : Nat → Nat → Nat) : Sat.Valuation := fun k =>
  (∃ n<9, ∃ y<7, ∃ z<p, k=cell p n y z ∧ W n y=z) ∨
  (∃ i a b, (a,b)∈forms p ∧ k=coeff p i a b ∧ lineAgrees p W (lineAt p i) (a,b))

theorem assignment_cell {p n y z : Nat} (W : Nat → Nat → Nat)
    (hn : n<9) (hy : y<7) (hz : z<p) :
    assignment p W (cell p n y z) ↔ W n y=z := by
  constructor
  · intro h
    rcases h with ⟨n',hn',y',hy',z',hz',he,hw⟩ | ⟨i,a,b,_,he,_⟩
    · obtain ⟨rfl,rfl,rfl⟩ := cell_inj hy hy' hz hz' he
      exact hw
    · have := cell_lt hn hy hz
      have := coeff_ge p i a b
      omega
  · intro h
    exact Or.inl ⟨n,hn,y,hy,z,hz,rfl,h⟩

theorem assignment_coeff {p i a b : Nat} (W : Nat → Nat → Nat)
    (hab : (a,b)∈forms p) :
    assignment p W (coeff p i a b) ↔ lineAgrees p W (lineAt p i) (a,b) := by
  constructor
  · intro h
    rcases h with ⟨n,hn,y,hy,z,hz,he,_⟩ | ⟨i',a',b',hab',he,hw⟩
    · have := cell_lt hn hy hz
      have := coeff_ge p i a b
      omega
    · obtain ⟨rfl,rfl,rfl⟩ := coeff_inj hab hab' he
      exact hw
  · intro h
    exact Or.inr ⟨i,a,b,hab,rfl,h⟩

private theorem satisfies_iff (v : Sat.Valuation) (c : List Sat.Literal) :
    v.satisfies c ↔ ∃ l ∈ c, ¬ v.neg l := by
  classical
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    simp only [Sat.Valuation.satisfies, ih, List.mem_cons]
    by_cases h : v.neg l <;> simp_all

theorem lineAt_of_mem {p i : Nat} {l : Int × Int} (h : (l,i)∈(lines p).zipIdx) :
    i<(lines p).length ∧ lineAt p i=l := by
  have hh := List.mem_zipIdx h
  have hi : i<(lines p).length := by simpa using hh.2.1
  refine ⟨hi, ?_⟩
  simp only [lineAt,List.getElem?_eq_getElem hi,Option.getD_some]
  simpa using hh.2.2.symm

/-- A normalized nonzero patch obeying the finite primitive line tests supplies
all hypotheses of the contradiction certificate. -/
theorem hypotheses_hold {p : Nat} (W : Nat → Nat → Nat)
    (hw : ∀ n<9, ∀ y<7, 0<W n y ∧ W n y<p)
    (hnorm : W 0 0=1)
    (hl : ∀ i<(lines p).length, ∃ ab∈forms p, lineAgrees p W (lineAt p i) ab) :
    (assignment p W).satisfies_fmla (hypotheses p) := by
  classical
  constructor
  intro c hc
  simp only [hypotheses,List.mem_append] at hc
  rcases hc with (hc|hc)|hc
  · simp only [cellChoices,List.mem_flatMap] at hc
    obtain ⟨n,hn,y,hy,hc⟩ := hc
    have hn := List.mem_range.mp hn
    have hy := List.mem_range.mp hy
    rcases List.mem_append.mp hc with hc | hc
    · obtain rfl := List.mem_singleton.mp hc
      apply satisfies_iff _ _ |>.mpr
      have hh := hw n hn y hy
      refine ⟨.pos (cell p n y (W n y)), ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨W n y-1, List.mem_range.mpr (by omega), ?_⟩
        congr 2
        omega
      · simpa only [Sat.Valuation.neg,not_not] using (assignment_cell W hn hy hh.2).mpr rfl
    · obtain ⟨u,hu,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
      have hu := List.mem_range.mp hu
      obtain ⟨hv,huv⟩ := List.mem_filter.mp hv
      have hv := List.mem_range.mp hv
      have huv : u<v := of_decide_eq_true huv
      by_cases he : W n y=u
      · intro _ hv'
        have hv' := (assignment_cell W hn hy hv).mp hv'
        omega
      · intro hu' _
        exact he ((assignment_cell W hn hy hu).mp hu')
  · obtain rfl := List.mem_singleton.mp hc
    intro h
    apply h
    exact (assignment_cell W (by decide) (by decide) (by have := hw 0 (by decide) 0 (by decide); omega)).mpr hnorm
  · simp only [lineClauses,List.mem_flatMap] at hc
    obtain ⟨⟨l,i⟩,hli,hc⟩ := hc
    have hli' := lineAt_of_mem hli
    rcases List.mem_append.mp hc with hc | hc
    · obtain rfl := List.mem_singleton.mp hc
      obtain ⟨⟨a,b⟩,hab,hm⟩ := hl i hli'.1
      apply satisfies_iff _ _ |>.mpr
      refine ⟨.pos (coeff p i a b), List.mem_map.mpr ⟨(a,b),hab,rfl⟩, ?_⟩
      simpa only [Sat.Valuation.neg,not_not] using (assignment_coeff W hab).mpr hm
    · obtain ⟨⟨a,b⟩,hab,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨⟨n,y⟩,hny,rfl⟩ := List.mem_map.mp hc
      obtain ⟨hny,hval⟩ := List.mem_filter.mp hny
      intro hcoef hcell
      have hm := (assignment_coeff W hab).mp hcoef
      rw [hli'.2] at hm
      have hz : value p (a,b) n≠0 := of_decide_eq_true hval
      have he := hm n y hny hz
      have hbounds : n<9 ∧ y<7 := by
        simp only [entries,List.mem_filterMap] at hny
        obtain ⟨n',hn',hny⟩ := hny
        split at hny
        next hh => cases Option.some.inj hny; exact ⟨List.mem_range.mp hn', by omega⟩
        next => contradiction
      apply hcell
      exact (assignment_cell W hbounds.1 hbounds.2 (Nat.mod_lt _ (by have := hw 0 (by decide) 0 (by decide); omega))).mpr he

end TranslationTiling.Sudoku.NinePatch
