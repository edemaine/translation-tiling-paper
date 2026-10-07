import TranslationTiling.Compiler.EffectiveParameters
import TranslationTiling.Compiler.EffectiveLists
import TranslationTiling.Compiler.CyclicFactorCRT

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped BigOperators

/-- Label indices retain only the arithmetic digits and Wang tile, never a
proof of membership in the input alphabet. Duplicate input tiles disappear. -/
def labelCodes (T : LeanWang.TileSet) : FixedChannel → List ℕ
  | .inl _ => ((symbols T).map Encodable.encode).dedup
  | .inr _ => [0]

theorem labelCodes_primrec : Primrec (fun z : LeanWang.TileSet × FixedChannel =>
    labelCodes z.1 z.2) := by
  have hordinary : Primrec₂ (fun z : LeanWang.TileSet × FixedChannel =>
      fun _ : Sudoku.Column => ((symbols z.1).map Encodable.encode).dedup) := by
    change Primrec _
    exact dedup_primrec.comp (mapList
      (symbols_primrec.comp (Primrec.fst.comp Primrec.fst)) (by fun_prop))
  exact (Primrec.sumCasesOn Primrec.snd hordinary (Primrec.const [0]).to₂).of_eq
    (fun z => by cases z.2 <;> rfl)

theorem mem_labelCodes (T : LeanWang.TileSet) (i : FixedChannel) (code : ℕ) :
    code ∈ labelCodes T i ↔ ∃ j : Label T i, labelCode i j = code := by
  cases i with
  | inl n =>
    simp only [labelCodes, List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨s, hs, he⟩
      obtain ⟨j, rfl⟩ := (mem_symbols T s).mp hs
      exact ⟨j, he⟩
    · rintro ⟨j, he⟩
      exact ⟨rawSymbol j, (mem_symbols T _).mpr ⟨j, rfl⟩, he⟩
  | inr t =>
    change code ∈ [0] ↔ ∃ j : Unit, (0 : ℕ) = code
    simp only [List.mem_singleton, exists_const, eq_comm]

theorem labelCodes_nodup (T : LeanWang.TileSet) (i : FixedChannel) :
    (labelCodes T i).Nodup := by
  cases i with
  | inl n => exact List.nodup_dedup _
  | inr t => simp [labelCodes]

noncomputable def numericalR (T : LeanWang.TileSet) (i : FixedChannel) : ℕ :=
  ((labelCodes T i).map (digitLookup i)).prod

theorem numericalR_computable : Computable (fun z : LeanWang.TileSet × FixedChannel =>
    numericalR z.1 z.2) := by
  have hproject : Primrec (fun z : (LeanWang.TileSet × FixedChannel) × ℕ =>
      (z.1.2, z.2)) := by fun_prop
  have hlookup := digitLookup_computable.comp hproject.to_comp
  have hg : Computable (fun z : (LeanWang.TileSet × FixedChannel) × ℕ =>
      digitLookup z.1.2 z.2) := hlookup
  have hm := computableListMap (f := fun z : LeanWang.TileSet × FixedChannel =>
    labelCodes z.1 z.2) (g := fun z c => digitLookup z.2 c) labelCodes_primrec.to_comp hg
  have hprod := product_primrec.to_comp.comp hm
  exact hprod

theorem numericalR_eq (T : LeanWang.TileSet) (i : FixedChannel) :
    numericalR T i = (parameters T).r i := by
  classical
  have hs : (labelCodes T i).toFinset = Finset.univ.image (labelCode (T := T) i) := by
    ext code
    simp only [List.mem_toFinset, mem_labelCodes, Finset.mem_image, Finset.mem_univ, true_and]
  unfold numericalR
  rw [← List.prod_toFinset _ (labelCodes_nodup T i), hs]
  rw [Finset.prod_image (labelCode_injective i).injOn]
  rfl

noncomputable def numericalOrder (T : LeanWang.TileSet) : ℕ :=
  Sudoku.Width ^ 2 * ((Finset.univ : Finset FixedChannel).toList.map fun i =>
    numericalR T i ^ 2 * usefulPrime (.inl i) * usefulPrime (.inr i)).prod

theorem numericalOrder_computable : Computable numericalOrder := by
  have hbase : Primrec (fun i : FixedChannel =>
      (usefulPrime (.inl i), usefulPrime (.inr i))) :=
    finiteFunction_primrec _
  have harith : Primrec (fun z : ℕ × (ℕ × ℕ) => z.1 ^ 2 * z.2.1 * z.2.2) := by
    simp only [pow_two]
    fun_prop
  have hbaseJoint : Primrec (fun z : LeanWang.TileSet × FixedChannel =>
      (usefulPrime (.inl z.2), usefulPrime (.inr z.2))) := hbase.comp Primrec.snd
  have hdata := numericalR_computable.pair hbaseJoint.to_comp
  have hblockRaw := harith.to_comp.comp hdata
  have hblock : Computable (fun z : LeanWang.TileSet × FixedChannel =>
      numericalR z.1 z.2 ^ 2 * usefulPrime (.inl z.2) * usefulPrime (.inr z.2)) := hblockRaw
  have hlist := computableListMap
    (f := fun _ : LeanWang.TileSet => (Finset.univ : Finset FixedChannel).toList)
    (g := fun T i => numericalR T i ^ 2 * usefulPrime (.inl i) * usefulPrime (.inr i))
    (Computable.const _) hblock
  have hresult := Primrec.nat_mul.to_comp.comp (Computable.const (Sudoku.Width ^ 2))
    (product_primrec.to_comp.comp hlist)
  exact hresult

/-- Block coefficients as numerical lookup data. -/
noncomputable def numericalCombination (z : FixedChannel × ℕ) : ℕ × ℕ :=
  positiveCombination (usefulPrime (.inl z.1), usefulPrime (.inr z.1),
    digitLookup z.1 z.2)

theorem numericalCombination_computable : Computable numericalCombination := by
  have hbase : Primrec (fun i : FixedChannel =>
      (usefulPrime (.inl i), usefulPrime (.inr i))) := finiteFunction_primrec _
  have ha := Primrec.fst.comp hbase
  have hb := Primrec.snd.comp hbase
  exact positiveCombination_computable.comp
    ((ha.to_comp.comp Computable.fst).pair
      ((hb.to_comp.comp Computable.fst).pair digitLookup_computable))

theorem numericalOrder_eq (T : LeanWang.TileSet) :
    numericalOrder T = (parameters T).cyclicOrder := by
  classical
  unfold numericalOrder EncodingParameters.cyclicOrder
  rw [residueModulus_eq, ← List.prod_toFinset _ (Finset.nodup_toList (Finset.univ : Finset FixedChannel))]
  simp only [Finset.toList_toFinset, EncodingParameters.blockModulus, numericalR_eq]
  rfl

end TranslationTiling.Compiler.Effective
