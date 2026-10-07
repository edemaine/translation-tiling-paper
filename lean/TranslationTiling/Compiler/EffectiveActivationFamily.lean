import TranslationTiling.Compiler.EffectiveActivationCompiler

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

attribute [local fun_prop] Primrec.sumInl Primrec.sumInr

open scoped Classical

noncomputable def otherChannelModuli (T : LeanWang.TileSet) (i : FixedChannel) : List ℕ :=
  ((Finset.univ : Finset FixedChannel).filter (· ≠ i)).toList.map (numericalR T)

theorem otherChannelModuli_computable : Computable (fun z : LeanWang.TileSet × FixedChannel =>
    otherChannelModuli z.1 z.2) := by
  have hfixed : Primrec (fun i : FixedChannel =>
      ((Finset.univ : Finset FixedChannel).filter (· ≠ i)).toList) := finiteFunction_primrec _
  have hp : Primrec (fun z : (LeanWang.TileSet × FixedChannel) × FixedChannel =>
      (z.1.1, z.2)) := by fun_prop
  have hg := numericalR_computable.comp hp.to_comp
  have h := computableListMap
    (f := fun z : LeanWang.TileSet × FixedChannel =>
      ((Finset.univ : Finset FixedChannel).filter (· ≠ z.2)).toList)
    (g := fun z i => numericalR z.1 i) (hfixed.comp Primrec.snd).to_comp hg
  exact h

noncomputable def activationEnvironment (T : LeanWang.TileSet) (i : FixedChannel) :
    ActivationEnvironment :=
  ((numericalOrder T, otherChannelModuli T i),
    (numericalR T i, usefulPrime (.inl i), usefulPrime (.inr i), Sudoku.Width ^ 2))

theorem activationEnvironment_computable : Computable (fun z : LeanWang.TileSet × FixedChannel =>
    activationEnvironment z.1 z.2) := by
  have hfixed : Primrec (fun i : FixedChannel =>
      (usefulPrime (.inl i), usefulPrime (.inr i), Sudoku.Width ^ 2)) :=
    finiteFunction_primrec _
  exact ((numericalOrder_computable.comp Computable.fst).pair otherChannelModuli_computable).pair
    (numericalR_computable.pair (hfixed.comp Primrec.snd).to_comp)

theorem activationEnvironment_eq (T : LeanWang.TileSet) (i : FixedChannel) :
    activationEnvironment T i = nativeActivationEnvironment (parameters T) i := by
  unfold activationEnvironment nativeActivationEnvironment otherChannelModuli
  have hr : numericalR T = (parameters T).r := funext (numericalR_eq T)
  simp only [numericalOrder_eq, hr, parameters_a, parameters_b]
  rw [D, residueModulus_eq]

noncomputable def ordinaryCompiler (T : LeanWang.TileSet) (n : Sudoku.Column) :
    List NumericalPoint := ordinaryCodes (activationEnvironment T (.inl n)) n.val

theorem ordinaryCompiler_computable : Computable (fun z : LeanWang.TileSet × Sudoku.Column =>
    ordinaryCompiler z.1 z.2) := by
  have hp : Primrec (fun z : LeanWang.TileSet × Sudoku.Column => (z.1, (Sum.inl z.2 : FixedChannel))) := by
    fun_prop
  have he := activationEnvironment_computable.comp hp.to_comp
  have hn : Primrec (fun z : LeanWang.TileSet × Sudoku.Column => z.2.val) := by fun_prop
  have h := ordinaryCodes_primrec.to_comp.comp (he.pair hn.to_comp)
  exact h

theorem ordinaryCompiler_correct (T : LeanWang.TileSet) (n : Sudoku.Column) :
    (ordinaryCompiler T n).toFinset.image (decodeNumericalPoint (parameters T)) =
      ordinaryActivationTile (parameters T) n := by
  unfold ordinaryCompiler
  rw [activationEnvironment_eq]
  exact ordinaryCodes_correct _ _

noncomputable def seedCompiler (T : LeanWang.TileSet) (t : Fin 2) :
    List NumericalPoint := seedCodes (activationEnvironment T (.inr t))
      (usefulPrime (.inl (.inr (otherSeed t)))) Sudoku.Width

theorem seedCompiler_computable : Computable (fun z : LeanWang.TileSet × Fin 2 =>
    seedCompiler z.1 z.2) := by
  have hp : Primrec (fun z : LeanWang.TileSet × Fin 2 => (z.1, (Sum.inr z.2 : FixedChannel))) := by
    fun_prop
  have he := activationEnvironment_computable.comp hp.to_comp
  have ht : Primrec (fun t : Fin 2 => (usefulPrime (.inl (.inr (otherSeed t))), Sudoku.Width)) :=
    finiteFunction_primrec _
  have h := seedCodes_primrec.to_comp.comp (he.pair (ht.comp Primrec.snd).to_comp)
  exact h

theorem seedCompiler_correct (T : LeanWang.TileSet) (t : Fin 2) :
    (seedCompiler T t).toFinset.image (decodeNumericalPoint (parameters T)) =
      seedActivationTile (parameters T) t := by
  unfold seedCompiler
  rw [activationEnvironment_eq, ← parameters_a T, ← residueModulus_eq]
  exact seedCodes_correct _ _

noncomputable def ordinaryFamily (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  (Finset.univ : Finset Sudoku.Column).toList.map (ordinaryCompiler T)

noncomputable def seedFamily (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  (Finset.univ : Finset (Fin 2)).toList.map (seedCompiler T)

theorem ordinaryFamily_computable : Computable ordinaryFamily :=
  computableListMap (Computable.const _) ordinaryCompiler_computable

theorem seedFamily_computable : Computable seedFamily :=
  computableListMap (Computable.const _) seedCompiler_computable

theorem ordinaryFamily_correct (T : LeanWang.TileSet) :
    ((ordinaryFamily T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset =
      Finset.univ.image (ordinaryActivationTile (parameters T)) := by
  unfold ordinaryFamily
  rw [List.map_map]
  ext F
  simp only [Function.comp_def, ordinaryCompiler_correct, List.mem_toFinset, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, Finset.mem_image]

theorem seedFamily_correct (T : LeanWang.TileSet) :
    ((seedFamily T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset =
      Finset.univ.image (seedActivationTile (parameters T)) := by
  unfold seedFamily
  rw [List.map_map]
  ext F
  simp only [Function.comp_def, seedCompiler_correct, List.mem_toFinset, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, Finset.mem_image]

end TranslationTiling.Compiler.Effective
