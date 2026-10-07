import TranslationTiling.Compiler.EffectiveCycleTiles
import TranslationTiling.Compiler.EffectiveDigitSubgroups
import TranslationTiling.Compiler.EffectiveVectors

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

abbrev ChannelSlot := Fin (Fintype.card FixedChannel)
noncomputable def channelEquiv : FixedChannel ≃ ChannelSlot := Fintype.equivFin _

abbrev CycleSpec := ChannelSlot → Bool × FixedChannel × ℕ
abbrev CycleConfiguration := ℕ × List ℕ × ℕ × ℕ × Bool

/-- All useful-coordinate spaces fit in this fixed table size. -/
noncomputable def functionTableSize : ℕ := usefulBound * usefulBound

theorem usefulProduct_le_tableSize (T : LeanWang.TileSet) (i : FixedChannel) :
    (parameters T).a i * (parameters T).b i ≤ functionTableSize := by
  rw [parameters_a, parameters_b]
  exact Nat.mul_le_mul (usefulPrime_le_bound _) (usefulPrime_le_bound _)

noncomputable def cycleAlphabet (d : CycleConfiguration) : List (List ℕ) :=
  if d.2.2.2.2 then subgroupTables d.1 d.2.1 functionTableSize else [[]]

theorem cycleAlphabet_primrec : Primrec cycleAlphabet := by
  have hd : Primrec (fun d : CycleConfiguration => (d.1, d.2.1, functionTableSize)) := by fun_prop
  have hb : Primrec (fun d : CycleConfiguration => d.2.2.2.2) := by fun_prop
  have h := Primrec.cond hb (subgroupTables_primrec.comp hd) (Primrec.const [[]])
  exact h.of_eq (fun a => by cases ha : a.2.2.2.2 <;> simp [cycleAlphabet, ha])

def configurationRow (d : CycleConfiguration) (xs : List ℕ) : CycleRow :=
  if d.2.2.2.2 then (d.1, d.2.2.1, d.2.2.2.1, xs) else (d.1, 1, 1, [0])

theorem configurationRow_primrec : Primrec (fun z : CycleConfiguration × List ℕ =>
    configurationRow z.1 z.2) := by
  unfold configurationRow
  fun_prop

noncomputable def cycleGadgets (N : ℕ) (configuration : ChannelSlot → CycleConfiguration) :
    List (List NumericalPoint) :=
  (vectors (fun s => cycleAlphabet (configuration s))).map fun tables =>
    cycleCodes N (List.ofFn fun s => configurationRow (configuration s) (tables s))

theorem cycleGadgets_primrec : Primrec (fun z : ℕ × (ChannelSlot → CycleConfiguration) =>
    cycleGadgets z.1 z.2) := by
  have ha : Primrec (fun z : ℕ × (ChannelSlot → CycleConfiguration) =>
      fun s => cycleAlphabet (z.2 s)) := by
    apply piValue
    intro s
    exact cycleAlphabet_primrec.comp ((evalFin s).comp Primrec.snd)
  have hr : Primrec (fun z : (ℕ × (ChannelSlot → CycleConfiguration)) ×
      (ChannelSlot → List ℕ) => List.ofFn fun s => configurationRow (z.1.2 s) (z.2 s)) := by
    apply Primrec.list_ofFn
    intro s
    exact configurationRow_primrec.comp
      (((evalFin s).comp (Primrec.snd.comp Primrec.fst)).pair ((evalFin s).comp Primrec.snd))
  have hg := cycleCodes_primrec.comp ((Primrec.fst.comp Primrec.fst).pair hr)
  exact mapList (vectors_primrec.comp ha) hg

noncomputable def cycleConfiguration (T : LeanWang.TileSet) (spec : CycleSpec)
    (s : ChannelSlot) : CycleConfiguration :=
  let i := channelEquiv.symm s
  let entry := spec s
  (numericalR T i, numericalOtherPrimes T i entry.2.2,
    usefulPrime (.inl entry.2.1), usefulPrime (.inr entry.2.1), entry.1)

theorem cycleConfiguration_computable : Computable (fun z : LeanWang.TileSet × CycleSpec =>
    cycleConfiguration z.1 z.2) := by
  apply computablePi
  intro s
  have hi : Primrec (fun z : LeanWang.TileSet × CycleSpec =>
      (z.1, channelEquiv.symm s)) := by fun_prop
  have hr := numericalR_computable.comp hi.to_comp
  have hs : Primrec (fun z : LeanWang.TileSet × CycleSpec => z.2 s) :=
    (evalFin s).comp Primrec.snd
  have hc : Primrec (fun z : LeanWang.TileSet × CycleSpec =>
      (z.1, channelEquiv.symm s, (z.2 s).2.2)) :=
    pairValue Primrec.fst (pairValue (Primrec.const _) ((Primrec.snd.comp Primrec.snd).comp hs))
  have ho := numericalOtherPrimes_computable.comp hc.to_comp
  have hp : Primrec (fun e : Bool × FixedChannel × ℕ =>
      (usefulPrime (.inl e.2.1), usefulPrime (.inr e.2.1), e.1)) := by
    have hfixed : Primrec (fun i : FixedChannel =>
        (usefulPrime (.inl i), usefulPrime (.inr i))) := finiteFunction_primrec _
    exact ((Primrec.fst.comp hfixed).comp (Primrec.fst.comp Primrec.snd)).pair
      (((Primrec.snd.comp hfixed).comp (Primrec.fst.comp Primrec.snd)).pair Primrec.fst)
  exact hr.pair (ho.pair ((hp.comp hs).to_comp))

noncomputable def cycleFamily (T : LeanWang.TileSet) (spec : CycleSpec) :
    List (List NumericalPoint) :=
  cycleGadgets (numericalOrder T) (cycleConfiguration T spec)

theorem cycleFamily_computable : Computable (fun z : LeanWang.TileSet × CycleSpec =>
    cycleFamily z.1 z.2) := by
  have hd := (numericalOrder_computable.comp Computable.fst).pair cycleConfiguration_computable
  have h := cycleGadgets_primrec.to_comp.comp hd
  exact h

end TranslationTiling.Compiler.Effective
