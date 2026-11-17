import TranslationTiling.FiniteCompiler.Effective.JointInput
import TranslationTiling.FiniteCompiler.Effective.CycleSpec
import TranslationTiling.FiniteCompiler.JointBounds
import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.FamilyCompiler

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 100000

def rawJointKeys (T : LeanWang.TileSet) (t i : ℕ) : List ℕ :=
  Nat.pair 1 t :: (List.range (jointWidth T.length)).map fun b =>
    denseChannelKey (Sudoku.Width*jointWidth T.length) (i*jointWidth T.length+b)

def rawJointLabels (T : LeanWang.TileSet) (s : RawSymbol) : List ℕ :=
  0 :: (List.range (jointWidth T.length)).map (rawJointCode T s)

@[fun_prop] theorem rawJointKeys_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ × ℕ => rawJointKeys z.1 z.2.1 z.2.2) := by
  unfold rawJointKeys
  fun_prop

@[fun_prop] theorem rawJointLabels_primrec :
    Primrec (fun z : LeanWang.TileSet × RawSymbol => rawJointLabels z.1 z.2) := by
  unfold rawJointLabels
  fun_prop

theorem rawJointKeys_eq (T : LeanWang.TileSet) (t : Fin 2) (i : Sudoku.Column) :
    rawJointKeys T t.val i.val = cycleKeys (JointSystem.cycle (jointCode T) t i) := by
  unfold rawJointKeys cycleKeys
  rw [List.ofFn_succ]
  congr 1
  apply List.ext_getElem
  · simp
  · intro b hb hb'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    have hbl : b<jointWidth T.length := by simpa only [List.length_map,List.length_range] using hb
    have hi := i.isLt
    have hk := jointWidth_pos T.length
    have hidx : i.val*jointWidth T.length+b<Sudoku.Width*jointWidth T.length := by nlinarith
    change denseChannelKey (Sudoku.Width*jointWidth T.length) (i.val*jointWidth T.length+b) =
      Nat.pair 0 (b+jointWidth T.length*i.val)
    rw [denseChannelKey,if_pos hidx]
    congr 1
    ac_rfl

theorem rawJointLabels_eq (T : LeanWang.TileSet) (t : Fin 2) (i : Sudoku.Column)
    (s : Sudoku.Symbol T) : rawJointLabels T (rawSymbol s) =
      cycleLabels (JointSystem.cycle (jointCode T) t i)
        (JointSystem.labels (jointCode T) t i ((jointCode T).word s)) := by
  unfold rawJointLabels cycleLabels
  rw [List.ofFn_succ]
  congr 1
  apply List.ext_getElem
  · simp
  · intro b hb hb'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rfl

def rawJointSeedArguments (T : LeanWang.TileSet) : List (ℕ × ℕ × RawSymbol) :=
  (List.range 2).flatMap fun t => (List.range Sudoku.Width).flatMap fun i =>
    ((symbols T).filter fun s => decide (¬(s.1=t+1 ∧ s.2.1=t+1))).map fun s => (t,i,s)

@[fun_prop] theorem rawJointSeedArguments_primrec : Primrec rawJointSeedArguments := by
  unfold rawJointSeedArguments
  fun_prop

def rawJointSeedFamilyData (z : LeanWang.TileSet × ParameterData) : List CyclicTile :=
  (rawJointSeedArguments z.1).flatMap fun q =>
    let spec := rawCycleSpec z.2 (rawJointKeys z.1 q.1 q.2.1) (rawJointLabels z.1 q.2.2)
    fixedGadgets (rawOrder z.2) (rawConfigurations z.2 spec) (rawOwnDigits z.2 spec)

@[fun_prop] theorem rawJointSeedFamilyData_primrec : Primrec rawJointSeedFamilyData := by
  unfold rawJointSeedFamilyData
  fun_prop

def rawJointSeedFamily (T : LeanWang.TileSet) : List CyclicTile :=
  rawJointSeedFamilyData (T,parameterData (jointSystem T))

theorem jointParameterData_computable : Computable (fun T => parameterData (jointSystem T)) := by
  have hw : Primrec (fun T : LeanWang.TileSet => Sudoku.Width*jointWidth T.length) := by fun_prop
  have hc := parameterCertificate_computable.comp (hw.to_comp.pair (Computable.const 3))
  exact hw.to_comp.pair ((Computable.const _).pair hc)

theorem rawJointSeedFamily_computable : Computable rawJointSeedFamily :=
  rawJointSeedFamilyData_primrec.to_comp.comp (Computable.id.pair jointParameterData_computable)

theorem mem_rawJointSeedArguments (T : LeanWang.TileSet) (q : ℕ × ℕ × RawSymbol) :
    q∈rawJointSeedArguments T ↔ ∃ z : Fin 2 × Sudoku.Column × Sudoku.Symbol T,
      (z.1.val,z.2.1.val,rawSymbol z.2.2)=q ∧ ¬Compiler.SeedSet z.1 z.2.2 := by
  simp only [rawJointSeedArguments,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,
    decide_eq_true_eq,mem_symbols]
  constructor
  · rintro ⟨t,ht,i,hi,s,⟨⟨s',rfl⟩,hs⟩,rfl⟩
    refine ⟨(⟨t,ht⟩,⟨i,hi⟩,s'),rfl,?_⟩
    exact fun h => hs ((rawSeedSet_iff (⟨t,ht⟩ : Fin 2) s').mpr h)
  · rintro ⟨⟨t,i,s⟩,rfl,hs⟩
    exact ⟨t.val,t.isLt,i.val,i.isLt,rawSymbol s,
      ⟨⟨s,rfl⟩,fun h => hs ((rawSeedSet_iff t s).mp h)⟩,rfl⟩

theorem rawJointSeedFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (jointSystem T)) (rawJointSeedFamily T) =
      JointSystem.seedTiles (jointCode T) (parameters (jointSystem T)) := by
  have hg (t : Fin 2) (i : Sudoku.Column) (s : Sudoku.Symbol T) :=
    specifiedGadgets_correct _ _ _ (rawCycleSpec_matches
      (JointSystem.cycle (jointCode T) t i) (JointSystem.labels (jointCode T) t i ((jointCode T).word s)))
  apply Finset.ext
  intro F
  rw [mem_decodedFamily]
  constructor
  · rintro ⟨xs,hxs,hF⟩
    obtain ⟨q,hmem,hxs⟩ := List.mem_flatMap.mp hxs
    obtain ⟨⟨t,i,s⟩,heq,hbad⟩ := (mem_rawJointSeedArguments T q).mp hmem
    subst q
    apply Finset.mem_biUnion.mpr
    refine ⟨(t,i,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩,?_⟩
    rw [←hg t i s,←rawJointKeys_eq,←rawJointLabels_eq]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs,hxs,hF⟩)
  · intro hF
    obtain ⟨⟨t,i,s⟩,hq,hF⟩ := Finset.mem_biUnion.mp hF
    have hq' := (Finset.mem_filter.mp hq).2
    rw [←hg t i s,←rawJointKeys_eq,←rawJointLabels_eq] at hF
    obtain ⟨xs,hxs,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    refine ⟨xs,List.mem_flatMap.mpr ⟨(t.val,i.val,rawSymbol s),?_,hxs⟩,he⟩
    exact (mem_rawJointSeedArguments T _).mpr ⟨(t,i,s),rfl,hq'⟩

theorem jointSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0≤(jointSystem T).slope n := by
  intro n
  change 0≤((finProdFinEquiv.symm n : Sudoku.Column × Fin (jointWidth T.length)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem jointSystem_slope_bound (T : LeanWang.TileSet) : ∀ n,
    ((jointSystem T).slope n).natAbs≤Sudoku.Width := by
  intro n
  change (((finProdFinEquiv.symm n : Sudoku.Column × Fin (jointWidth T.length)).1.val : ℤ)).natAbs≤_
  rw [Int.natAbs_natCast]
  exact (finProdFinEquiv.symm n : Sudoku.Column × Fin (jointWidth T.length)).1.isLt.le

def jointInput (T : LeanWang.TileSet) : InputData :=
  (parameterData (jointSystem T),jointPayload T)

theorem jointInput_computable : Computable jointInput :=
  jointParameterData_computable.pair jointPayload_primrec.to_comp

def rawJointFamily (T : LeanWang.TileSet) : List CyclicTile :=
  rawFamily (jointInput T) ++ rawJointSeedFamily T

theorem rawJointFamily_computable : Computable rawJointFamily := by
  have hraw : Computable (fun T => rawFamily (jointInput T)) :=
    rawFamily_primrec.to_comp.comp jointInput_computable
  have ha : Primrec (fun z : List CyclicTile × List CyclicTile => z.1++z.2) := by fun_prop
  have h := ha.to_comp.comp (hraw.pair rawJointSeedFamily_computable)
  exact h.of_eq (fun T => rfl)

def jointFamily (T : LeanWang.TileSet) : List CyclicTile :=
  canonicalFamily (rawHorizontal (parameterData (jointSystem T)))
    (rawOrder (parameterData (jointSystem T))) (rawJointFamily T)

theorem jointFamily_computable : Computable jointFamily := by
  have h := canonicalFamily_primrec.to_comp.comp
    (((rawHorizontal_primrec.to_comp.comp jointParameterData_computable).pair
      (rawOrder_primrec.to_comp.comp jointParameterData_computable)).pair rawJointFamily_computable)
  exact h.of_eq (fun T => rfl)

theorem rawJointFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (jointSystem T)) (rawJointFamily T) =
      JointSystem.testTiles (jointCode T) (parameters (jointSystem T)) := by
  rw [rawJointFamily,decodedFamily_append,rawJointSeedFamily_correct]
  rw [show jointInput T=(parameterData (jointSystem T),jointPayload T) from rfl,
    rawFamily_correct _ _ (jointPayload_correct T) (jointSystem_nonnegative T)]
  rfl

theorem rawJointFamily_horizontal (T : LeanWang.TileSet) :
    ∀ F∈rawJointFamily T, ∀ f∈F,
      f.1.1.natAbs≤rawHorizontal (parameterData (jointSystem T)) ∧
      f.1.2.natAbs≤rawHorizontal (parameterData (jointSystem T)) := by
  intro F hF f hf
  have hm : F.toFinset.image (decodeNumericalPoint (parameters (jointSystem T))) ∈
      JointSystem.testTiles (jointCode T) (parameters (jointSystem T)) := by
    rw [←rawJointFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  exact JointSystem.test_horizontal _ _ (parameters_rawBudget _ (jointSystem_slope_bound T)).1 hm
    (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)

theorem jointFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (jointSystem T)) (jointFamily T) =
      JointSystem.testTiles (jointCode T) (parameters (jointSystem T)) := by
  unfold jointFamily
  rw [rawOrder_eq,canonicalDecoded_correct _ _ _ (rawJointFamily_horizontal T),rawJointFamily_correct]

theorem jointFamily_length (T : LeanWang.TileSet) :
    (jointFamily T).length = (JointSystem.testTiles (jointCode T) (parameters (jointSystem T))).card := by
  rw [←jointFamily_correct,decodedFamily_card]
  unfold jointFamily
  rw [rawOrder_eq]
  exact canonicalFamily_length _ _ _

theorem jointFamily_budget (T : LeanWang.TileSet) (hn : 0<T.length) :
    FamilyBudget (jointSystem T) (jointFamily T) := by
  have hm (F : CyclicTile) (hF : F∈jointFamily T) :
      F.toFinset.image (decodeNumericalPoint (parameters (jointSystem T))) ∈
      JointSystem.testTiles (jointCode T) (parameters (jointSystem T)) := by
    rw [←jointFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [jointFamily_length]
    apply Finset.card_pos.mpr
    exact ⟨_,Finset.mem_union_left _ (kernelTile_mem_testTiles _)⟩
  · rw [jointFamily_length]
    exact JointSystem.testTiles_card _ _ (jointWidth_three hn)
  · intro F hF he
    have hh := JointSystem.nonempty_of_mem_testTiles _ _ (hm F hF)
    rw [he] at hh
    exact Finset.not_nonempty_empty (by simpa only [List.toFinset_nil,Finset.image_empty] using hh)
  · exact canonicalFamily_horizontal _ _ _
  · intro F hF
    have hh := JointSystem.test_card _ _ (hm F hF)
    rw [decodedTile_eq_image,Finset.card_image_of_injective _ (ambientCyclicEquiv (parameters (jointSystem T))).symm.injective] at hh
    exact hh

theorem joint_family_solution_iff (T : LeanWang.TileSet) :
    (∃ A : Set (Ambient (parameters (jointSystem T))),
      JointSystem.Solves (jointCode T) (parameters (jointSystem T)) A) ↔
      ∃ B : Set (Plane × ZMod (parameters (jointSystem T)).cyclicOrder),
        ∀ i : Fin (jointFamily T).length,
          Tiles (cyclicTileSet (parameters (jointSystem T)).cyclicOrder ((jointFamily T).getD i.val [])) B := by
  let E := parameters (jointSystem T)
  let Fs := jointFamily T
  have he := jointFamily_correct T
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm : (Fs.getD i.val []).toFinset.image (decodeNumericalPoint E) ∈
        JointSystem.testTiles (jointCode T) E := by
      rw [←he]
      exact (mem_decodedFamily _ _ _).mpr ⟨_,getD_mem_of_lt Fs i.val [] i.isLt,rfl⟩
    have h := covers_image (ambientCyclicEquiv E) _ A (hA _ hm)
    rwa [decodedTile_image] at h
  · rintro ⟨B,hB⟩
    refine ⟨(ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    rw [←he,mem_decodedFamily] at hF
    obtain ⟨xs,hxs,rfl⟩ := hF
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hxs
    have hi' : Fs.getD i []=Fs[i] := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    have h := covers_image (ambientCyclicEquiv E).symm _ B (hB ⟨i,hi⟩)
    rw [hi',←decodedTile_eq_image] at h
    exact h

end
end TranslationTiling.FiniteCompiler.Effective
