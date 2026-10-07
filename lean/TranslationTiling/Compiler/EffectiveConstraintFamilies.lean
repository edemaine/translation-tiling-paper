import TranslationTiling.Compiler.EffectiveCycleCorrect
import TranslationTiling.Compiler.ConstraintCycles

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

attribute [local fun_prop] Primrec.sumInl Primrec.sumInr
local instance : Inhabited RawSymbol := ⟨emptyRawSymbol⟩

noncomputable def columnPredecessor (n : Sudoku.Column) : Sudoku.Column :=
  columnResidueEquiv.symm (columnResidueEquiv n - 1)

noncomputable def wordSpec (w : RawWord) (s : ChannelSlot) : Bool × FixedChannel × ℕ :=
  match channelEquiv.symm s with
  | .inl n => (true, .inl (columnPredecessor n), Encodable.encode (w n))
  | .inr t => (false, .inr t, 0)

theorem wordSpec_primrec : Primrec wordSpec := by
  apply piValue
  intro s
  cases hi : channelEquiv.symm s with
  | inl n =>
    have hp : Primrec (fun w : RawWord => (true, (Sum.inl (columnPredecessor n) : FixedChannel),
        Encodable.encode (w n))) :=
      pairValue (Primrec.const _) ((Primrec.const _).pair (Primrec.encode.comp (evalFin n)))
    exact hp.of_eq (fun w => by simp only [wordSpec, hi])
  | inr t =>
    have hp : Primrec (fun _ : RawWord => (false, (Sum.inr t : FixedChannel), 0)) :=
      Primrec.const _
    exact hp.of_eq (fun w => by simp only [wordSpec, hi])

theorem wordSpec_matches {T : LeanWang.TileSet} (w : Word T) :
    CycleSpecMatches (wordSpec (rawWord w)) (ordinaryCycle T) (ordinaryCycleLabels w) := by
  constructor
  · intro j
    change wordSpec (rawWord w) (channelEquiv (.inl (columnResidueEquiv.symm j))) =
      (true, .inl (columnResidueEquiv.symm (j - 1)),
        labelCode (.inl (columnResidueEquiv.symm j)) (w (columnResidueEquiv.symm j)))
    simp only [wordSpec, Equiv.symm_apply_apply, columnPredecessor, Equiv.apply_symm_apply]
    rfl
  · intro i hi
    cases i with
    | inl n => exact False.elim (hi (columnResidueEquiv n)
        (by change Sum.inl (columnResidueEquiv.symm (columnResidueEquiv n)) = Sum.inl n
            rw [Equiv.symm_apply_apply]))
    | inr t => simp only [wordSpec, Equiv.symm_apply_apply]

noncomputable def seedSpec (t : Fin 2) (n : Sudoku.Column) (j : RawSymbol)
    (s : ChannelSlot) : Bool × FixedChannel × ℕ :=
  let i := channelEquiv.symm s
  if i = .inr t then (true, .inl n, 0)
  else if i = .inl n then (true, .inr t, Encodable.encode j)
  else (false, i, 0)

theorem seedSpec_primrec : Primrec (fun z : Fin 2 × Sudoku.Column × RawSymbol =>
    seedSpec z.1 z.2.1 z.2.2) := by
  apply piValue
  intro s
  unfold seedSpec
  fun_prop

theorem seedSpec_matches {T : LeanWang.TileSet} (t : Fin 2) (n : Column T) (j : Symbol T) :
    CycleSpecMatches (seedSpec t n (rawSymbol j)) (seedCycle t n) (seedCycleLabels t n j) := by
  constructor
  · intro z
    by_cases hz : z = 0
    · subst z
      rw [show (0 : ZMod 2) - 1 = 1 from by decide]
      change seedSpec t n (rawSymbol j) (channelEquiv (.inr t)) = (true, .inl n, 0)
      simp [seedSpec]
    · have hz' : z = 1 := by
        fin_cases z
        · exact False.elim (hz (by rfl))
        · rfl
      subst z
      rw [show (1 : ZMod 2) - 1 = 0 from by decide]
      change seedSpec t n (rawSymbol j) (channelEquiv (.inl n)) =
        (true, .inr t, Encodable.encode (rawSymbol j))
      simp [seedSpec]
  · intro i hi
    have hs : i ≠ .inr t := (hi 0).symm
    have hn : i ≠ .inl n := (hi 1).symm
    simp only [seedSpec, Equiv.symm_apply_apply, if_neg hs, if_neg hn]

def badWords (T : LeanWang.TileSet) : List RawWord :=
  (words T).filter fun w => decide (¬ WordTest T w)

theorem badWords_primrec : Primrec badWords := filterList words_primrec wordTest_primrec.not

theorem mem_badWords (T : LeanWang.TileSet) (w : RawWord) :
    w ∈ badWords T ↔ ∃ W : Word T, rawWord W = w ∧ ¬ Allowed T W := by
  simp only [badWords, List.mem_filter, decide_eq_true_eq, mem_words]
  constructor
  · rintro ⟨⟨W, rfl⟩, hw⟩
    exact ⟨W, rfl, fun h => hw ((wordTest_iff W).mpr h)⟩
  · rintro ⟨W, rfl, hw⟩
    exact ⟨⟨W, rfl⟩, fun h => hw ((wordTest_iff W).mp h)⟩

noncomputable def wordFamily (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  (badWords T).flatMap fun w => cycleFamily T (wordSpec w)

theorem wordFamily_computable : Computable wordFamily := by
  have hp : Primrec (fun z : LeanWang.TileSet × RawWord => (z.1, wordSpec z.2)) :=
    Primrec.fst.pair (wordSpec_primrec.comp Primrec.snd)
  have hg := cycleFamily_computable.comp hp.to_comp
  -- Computable mapping followed by primitive-recursive concatenation.
  have hm := computableListMap (f := badWords)
    (g := fun T w => cycleFamily T (wordSpec w)) badWords_primrec.to_comp hg
  have hjoin : Primrec (List.flatten : List (List (List NumericalPoint)) → List (List NumericalPoint)) :=
    Primrec.list_flatten
  exact (hjoin.to_comp.comp hm).of_eq (fun T => rfl)

open scoped Classical

theorem wordFamily_correct (T : LeanWang.TileSet) :
    ((wordFamily T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset = wordConstraintTiles (parameters T) := by
  ext F
  simp only [wordFamily, List.mem_toFinset, List.mem_map, List.mem_flatMap, mem_badWords,
    wordConstraintTiles, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_allowedWords]
  constructor
  · rintro ⟨xs, ⟨w, ⟨W, rfl, hW⟩, hxs⟩, hF⟩
    refine ⟨W, hW, ?_⟩
    rw [← cycleFamily_correct _ _ _ (wordSpec_matches W)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs, hxs, hF⟩)
  · rintro ⟨W, hW, hF⟩
    rw [← cycleFamily_correct _ _ _ (wordSpec_matches W)] at hF
    obtain ⟨xs, hxs, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact ⟨xs, ⟨rawWord W, ⟨W, rfl, hW⟩, hxs⟩, he⟩

abbrev SeedArgument := Fin 2 × Sudoku.Column × RawSymbol

def RawSeedSet (t : Fin 2) (j : RawSymbol) : Prop :=
  j.1 = t.val + 1 ∧ j.2.1 = t.val + 1

instance (t : Fin 2) (j : RawSymbol) : Decidable (RawSeedSet t j) := by
  unfold RawSeedSet
  infer_instance

theorem rawSeedSet_primrec : PrimrecPred (fun z : SeedArgument => RawSeedSet z.1 z.2.2) := by
  unfold RawSeedSet
  fun_prop

theorem rawSeedSet_iff {T : LeanWang.TileSet} (t : Fin 2) (j : Symbol T) :
    RawSeedSet t (rawSymbol j) ↔ SeedSet t j := by
  have hp : t.val + 1 < Sudoku.p := by have := t.isLt; unfold Sudoku.p; omega
  have hq : t.val + 1 < Sudoku.q := by have := t.isLt; unfold Sudoku.q; omega
  unfold RawSeedSet rawSymbol SeedSet
  rw [← (ZMod.val_injective Sudoku.p).eq_iff, ← (ZMod.val_injective Sudoku.q).eq_iff]
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]

noncomputable def seedArguments (T : LeanWang.TileSet) : List SeedArgument :=
  (Finset.univ : Finset (Fin 2)).toList.flatMap fun t =>
    (Finset.univ : Finset Sudoku.Column).toList.flatMap fun n =>
      (symbols T).map fun j => (t, n, j)

theorem seedArguments_primrec : Primrec seedArguments := by
  unfold seedArguments
  fun_prop

noncomputable def badSeedArguments (T : LeanWang.TileSet) : List SeedArgument :=
  (seedArguments T).filter fun z => decide (¬ RawSeedSet z.1 z.2.2)

theorem badSeedArguments_primrec : Primrec badSeedArguments :=
  filterList seedArguments_primrec (rawSeedSet_primrec.not.comp Primrec.snd)

theorem mem_badSeedArguments (T : LeanWang.TileSet) (z : SeedArgument) :
    z ∈ badSeedArguments T ↔ ∃ j : Symbol T, rawSymbol j = z.2.2 ∧ ¬ SeedSet z.1 j := by
  simp only [badSeedArguments, List.mem_filter, decide_eq_true_eq, seedArguments,
    List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨t, n, j, hj, he⟩, hbad⟩
    have ht := congrArg Prod.fst he
    have hn := congrArg (fun z : SeedArgument => z.2.1) he
    have hs := congrArg (fun z : SeedArgument => z.2.2) he
    obtain ⟨J, hJ⟩ := (mem_symbols T j).mp hj
    refine ⟨J, hJ.trans hs, ?_⟩
    intro hseed
    apply hbad
    rw [← hJ.trans hs]
    exact (rawSeedSet_iff z.1 J).mpr hseed
  · rintro ⟨j, hj, hbad⟩
    refine ⟨⟨z.1, z.2.1, z.2.2, (mem_symbols T _).mpr ⟨j, hj⟩, rfl⟩, ?_⟩
    intro hseed
    apply hbad
    rw [← hj] at hseed
    exact (rawSeedSet_iff z.1 j).mp hseed

noncomputable def seedConstraintFamily (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  (badSeedArguments T).flatMap fun z => cycleFamily T (seedSpec z.1 z.2.1 z.2.2)

theorem seedConstraintFamily_computable : Computable seedConstraintFamily := by
  have hspec : Primrec (fun z : LeanWang.TileSet × SeedArgument =>
      seedSpec z.2.1 z.2.2.1 z.2.2.2) := seedSpec_primrec.comp Primrec.snd
  have hp : Primrec (fun z : LeanWang.TileSet × SeedArgument =>
      (z.1, seedSpec z.2.1 z.2.2.1 z.2.2.2)) := Primrec.fst.pair hspec
  have hg := cycleFamily_computable.comp hp.to_comp
  have hm := computableListMap (f := badSeedArguments)
    (g := fun T z => cycleFamily T (seedSpec z.1 z.2.1 z.2.2))
    badSeedArguments_primrec.to_comp hg
  have hjoin : Primrec (List.flatten : List (List (List NumericalPoint)) → List (List NumericalPoint)) :=
    Primrec.list_flatten
  exact (hjoin.to_comp.comp hm).of_eq (fun T => rfl)

theorem seedConstraintFamily_correct (T : LeanWang.TileSet) :
    ((seedConstraintFamily T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset = seedConstraintTiles (parameters T) := by
  ext F
  simp only [seedConstraintFamily, List.mem_toFinset, List.mem_map, List.mem_flatMap,
    mem_badSeedArguments, seedConstraintTiles, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨xs, ⟨z, ⟨j, hj, hbad⟩, hxs⟩, hF⟩
    refine ⟨(z.1, z.2.1, j), hbad, ?_⟩
    rw [← hj] at hxs
    rw [← cycleFamily_correct _ _ _ (seedSpec_matches z.1 z.2.1 j)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs, hxs, hF⟩)
  · rintro ⟨⟨t, n, j⟩, hbad, hF⟩
    rw [← cycleFamily_correct _ _ _ (seedSpec_matches t n j)] at hF
    obtain ⟨xs, hxs, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact ⟨xs, ⟨(t, n, rawSymbol j), ⟨j, rfl, hbad⟩, hxs⟩, he⟩

end TranslationTiling.Compiler.Effective
