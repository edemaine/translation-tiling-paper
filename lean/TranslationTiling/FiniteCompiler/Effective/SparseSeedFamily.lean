import TranslationTiling.FiniteCompiler.Effective.SparseWordEncoding
import TranslationTiling.FiniteCompiler.Effective.CycleSpec
import TranslationTiling.FiniteCompiler.SparseTernaryBounds

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective SparseTernary
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def sparseRawSeedKeys (t i b : ℕ) : List ℕ := [Nat.pair 1 t,Nat.pair 0 (3*i+b)]
def sparseRawSeedLabels (v : ℕ) : List ℕ := [0,v]
def sparseSeedValue (t b : ℕ) : ℕ := (if t=0 then 0 else 7)/3^b%3

@[fun_prop] theorem sparseRawSeedKeys_primrec :
    Primrec (fun z : ℕ×ℕ×ℕ => sparseRawSeedKeys z.1 z.2.1 z.2.2) := by
  unfold sparseRawSeedKeys
  fun_prop
@[fun_prop] theorem sparseRawSeedLabels_primrec : Primrec sparseRawSeedLabels := by
  unfold sparseRawSeedLabels
  fun_prop

 theorem sparseSeedValue_eq (t : Fin 2) (b : Fin 3) :
    sparseSeedValue t.val b.val=(arithWord (seedArithmetic t) b).val := by
  fin_cases t <;> fin_cases b <;> decide +kernel

 theorem sparseRawSeedKeys_eq (T : LeanWang.TileSet) (t : Fin 2) (i : Sudoku.Column) (b : Fin 3) :
    sparseRawSeedKeys t.val i.val b.val=cycleKeys (T:=SparseTernary.system T) (SparseTernary.seedCycle t i b) := by
  rfl

 theorem sparseRawSeedLabels_eq (T : LeanWang.TileSet) (t : Fin 2) (i : Sudoku.Column) (b v : Fin 3) :
    sparseRawSeedLabels v.val=cycleLabels (T:=SparseTernary.system T) (SparseTernary.seedCycle t i b) (SparseTernary.seedLabels t i b v) := by
  rfl

def sparseRawSeedArguments : List (ℕ×ℕ×ℕ×ℕ) :=
  (List.range 2).flatMap fun t => (List.range 16).flatMap fun i =>
    (List.range 3).flatMap fun b => ((List.range 3).filter fun v => decide (v≠sparseSeedValue t b)).map fun v => (t,i,b,v)

 theorem mem_sparseRawSeedArguments (q : ℕ×ℕ×ℕ×ℕ) :
    q∈sparseRawSeedArguments ↔ ∃ z : Fin 2×Sudoku.Column×Fin 3×Fin 3,
      (z.1.val,z.2.1.val,z.2.2.1.val,z.2.2.2.val)=q ∧ z.2.2.2≠arithWord (seedArithmetic z.1) z.2.2.1 := by
  simp only [sparseRawSeedArguments,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht,i,hi,b,hb,v,⟨hv,hbad⟩,rfl⟩
    refine ⟨(⟨t,ht⟩,⟨i,hi⟩,⟨b,hb⟩,⟨v,hv⟩),rfl,?_⟩
    intro he
    apply hbad
    have hh := congrArg Fin.val he
    exact hh.trans (sparseSeedValue_eq ⟨t,ht⟩ ⟨b,hb⟩).symm
  · rintro ⟨⟨t,i,b,v⟩,rfl,hbad⟩
    refine ⟨t.val,t.isLt,i.val,i.isLt,b.val,b.isLt,v.val,⟨v.isLt,?_⟩,rfl⟩
    intro he
    apply hbad
    apply Fin.ext
    exact he.trans (sparseSeedValue_eq t b)

def sparseRawSeedFamilyData (z : LeanWang.TileSet×ParameterData) : List CyclicTile :=
  sparseRawSeedArguments.flatMap fun q =>
    let spec := rawCycleSpec z.2 (sparseRawSeedKeys q.1 q.2.1 q.2.2.1) (sparseRawSeedLabels q.2.2.2)
    fixedGadgets (rawOrder z.2) (rawConfigurations z.2 spec) (rawOwnDigits z.2 spec)

@[fun_prop] theorem sparseRawSeedFamilyData_primrec : Primrec sparseRawSeedFamilyData := by
  unfold sparseRawSeedFamilyData
  fun_prop

def sparseRawSeedFamily (T : LeanWang.TileSet) : List CyclicTile :=
  sparseRawSeedFamilyData (T,parameterData (SparseTernary.system T))

 theorem sparseRawSeedFamily_computable : Computable sparseRawSeedFamily :=
  sparseRawSeedFamilyData_primrec.to_comp.comp (Computable.id.pair sparseParameterData_computable)

 theorem sparseRawSeedFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (SparseTernary.system T)) (sparseRawSeedFamily T)=
      SparseTernary.seedTiles (parameters (SparseTernary.system T)) := by
  have hg (t : Fin 2) (i : Sudoku.Column) (b v : Fin 3) :=
    specifiedGadgets_correct _ _ _ (rawCycleSpec_matches
      (SparseTernary.seedCycle (T:=T) t i b) (SparseTernary.seedLabels t i b v))
  apply Finset.ext
  intro F
  rw [mem_decodedFamily]
  constructor
  · rintro ⟨xs,hxs,hF⟩
    obtain ⟨q,hq,hxs⟩ := List.mem_flatMap.mp hxs
    obtain ⟨⟨t,i,b,v⟩,he,hbad⟩ := (mem_sparseRawSeedArguments q).mp hq
    subst q
    apply Finset.mem_biUnion.mpr
    refine ⟨(t,i,b,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩,?_⟩
    rw [←hg t i b v,←sparseRawSeedKeys_eq,←sparseRawSeedLabels_eq]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs,hxs,hF⟩)
  · intro hF
    obtain ⟨⟨t,i,b,v⟩,hq,hF⟩ := Finset.mem_biUnion.mp hF
    have hbad := (Finset.mem_filter.mp hq).2
    rw [←hg t i b v,←sparseRawSeedKeys_eq,←sparseRawSeedLabels_eq] at hF
    obtain ⟨xs,hxs,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    refine ⟨xs,List.mem_flatMap.mpr ⟨(t.val,i.val,b.val,v.val),?_,hxs⟩,he⟩
    exact (mem_sparseRawSeedArguments _).mpr ⟨(t,i,b,v),rfl,hbad⟩

end
end TranslationTiling.FiniteCompiler.Effective
