import TranslationTiling.Compiler.EffectiveFunctionTables
import TranslationTiling.Compiler.CycleTests

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

/-- Target low modulus, previous useful moduli, and a finite function table. -/
abbrev CycleRow := ℕ × ℕ × ℕ × List ℕ

def CycleRowTest (row : CycleRow) (n : ℕ) : Prop :=
  n % row.1 = (row.2.2.2.getD
    (rectangularIndex row.2.2.1 (n % row.2.1) (n % row.2.2.1)) 0) % row.1

instance (row : CycleRow) (n : ℕ) : Decidable (CycleRowTest row n) := by
  unfold CycleRowTest
  infer_instance

theorem cycleRowTest_primrec : PrimrecPred (fun z : CycleRow × ℕ => CycleRowTest z.1 z.2) := by
  have hr : Primrec (fun z : CycleRow × ℕ => z.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun z : CycleRow × ℕ => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun z : CycleRow × ℕ => z.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ht : Primrec (fun z : CycleRow × ℕ => z.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hx := Primrec.nat_mod.comp Primrec.snd ha
  have hy := Primrec.nat_mod.comp Primrec.snd hb
  have hi := Primrec.nat_add.comp (Primrec.nat_mul.comp hx hb) hy
  have hv := (Primrec.list_getD 0).comp ht hi
  exact equalValues (Primrec.nat_mod.comp Primrec.snd hr) (Primrec.nat_mod.comp hv hr)

def CycleTest (rows : List CycleRow) (n : ℕ) : Prop := ∀ row ∈ rows, CycleRowTest row n

instance (rows : List CycleRow) (n : ℕ) : Decidable (CycleTest rows n) := by
  unfold CycleTest
  infer_instance

theorem cycleTest_primrec : PrimrecPred (fun z : List CycleRow × ℕ => CycleTest z.1 z.2) := by
  unfold CycleTest
  apply allList Primrec.fst
  have hp : Primrec (fun z : (List CycleRow × ℕ) × CycleRow => (z.2, z.1.2)) := by fun_prop
  exact cycleRowTest_primrec.comp hp

def cycleCodes (N : ℕ) (rows : List CycleRow) : List NumericalPoint :=
  ((List.range N).filter fun n => decide (CycleTest rows n)).map fun n => ((0, 0), n)

theorem cycleCodes_primrec : Primrec (fun z : ℕ × List CycleRow => cycleCodes z.1 z.2) := by
  unfold cycleCodes
  apply mapList
  · apply filterList (by fun_prop)
    exact cycleTest_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  · fun_prop

theorem cycleRowTest_zero (r n : ℕ) : CycleRowTest (r, 1, 1, [0]) n ↔ n % r = 0 := by
  simp [CycleRowTest, rectangularIndex]

open scoped Classical

/-- Transfer a numerical row specification to the checked offset gadget. -/
theorem cycleCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T)
    (D : Useful E → Low E) (rows : List CycleRow)
    (hspec : ∀ n, CycleTest rows n ↔ q0 E (decodeNumericalPoint E ((0, 0), n)) =
      (0, D (usefulProjection E (decodeNumericalPoint E ((0, 0), n))))) :
    (cycleCodes E.cyclicOrder rows).toFinset.image (decodeNumericalPoint E) = offsetTile E D := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    apply (mem_offsetTile E D _).mpr
    exact (hspec n).mp (of_decide_eq_true (List.mem_filter.mp hn).2)
  · intro hg
    have hq := (mem_offsetTile E D g).mp hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = (0, 0) := congrArg Prod.fst hq
    have he : decodeNumericalPoint E ((0, 0), n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨((0, 0), n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    apply decide_eq_true
    apply (hspec n).mpr
    simpa only [he] using hq

end TranslationTiling.Compiler.Effective
