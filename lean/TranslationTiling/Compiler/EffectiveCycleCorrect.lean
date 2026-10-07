import TranslationTiling.Compiler.EffectiveCycleFamily

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

variable {T : LeanWang.TileSet} {t : ℕ} [NeZero t]

def CycleSpecMatches (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) : Prop :=
  (∀ j, spec (channelEquiv (cycle j)) =
    (true, cycle (j - 1), labelCode (cycle j) (labels j))) ∧
  (∀ i, (∀ j, cycle j ≠ i) → (spec (channelEquiv i)).1 = false)

def ValidCycleTables (T : LeanWang.TileSet) (spec : CycleSpec)
    (tables : ChannelSlot → List ℕ) : Prop :=
  ∀ s, tables s ∈ cycleAlphabet (cycleConfiguration T spec s)

theorem validCycleTables_on (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (ht : ValidCycleTables T spec tables) (j : ZMod t) :
    tables (channelEquiv (cycle j)) ∈ subgroupTables ((parameters T).r (cycle j))
      (numericalOtherPrimes T (cycle j) (labelCode (cycle j) (labels j))) functionTableSize := by
  have h := ht (channelEquiv (cycle j))
  simpa only [cycleAlphabet, cycleConfiguration, Equiv.symm_apply_apply,
    hs.1 j, ↓reduceIte, numericalR_eq] using h

noncomputable def decodeCycleTables (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (ht : ValidCycleTables T spec tables)
    (j : ZMod t) (e : P (parameters T) (cycle (j - 1))) :
    digitSubgroup (parameters T) (cycle j) (labels j) := by
  let n := (tables (channelEquiv (cycle j))).getD
    (rectangularIndex ((parameters T).b (cycle (j - 1))) e.1.val e.2.val) 0
  refine ⟨(n : ℕ), ?_⟩
  apply (numericalOtherPrimes_test T (cycle j) (labels j) n).mp
  exact (subgroupTables_getD _ _ ((parameters T).r_pos _) _ _
    (validCycleTables_on spec cycle labels hs tables ht j) _).2

theorem configurationRow_on (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (j : ZMod t) :
    configurationRow (cycleConfiguration T spec (channelEquiv (cycle j)))
      (tables (channelEquiv (cycle j))) =
    ((parameters T).r (cycle j), (parameters T).a (cycle (j - 1)),
      (parameters T).b (cycle (j - 1)), tables (channelEquiv (cycle j))) := by
  simp only [configurationRow, cycleConfiguration, Equiv.symm_apply_apply,
    hs.1 j, ↓reduceIte, numericalR_eq, parameters_a, parameters_b]

theorem configurationRow_off (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (i : Channel T) (hi : ∀ j, cycle j ≠ i) :
    configurationRow (cycleConfiguration T spec (channelEquiv i))
      (tables (channelEquiv i)) = ((parameters T).r i, 1, 1, [0]) := by
  simp only [configurationRow, cycleConfiguration, Equiv.symm_apply_apply,
    hs.2 i hi, Bool.false_eq_true, ↓reduceIte, numericalR_eq]

theorem cycleRows_correct (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (ht : ValidCycleTables T spec tables) (n : ℕ) :
    CycleTest (List.ofFn fun s => configurationRow (cycleConfiguration T spec s) (tables s)) n ↔
    q0 (parameters T) (decodeNumericalPoint (parameters T) ((0, 0), n)) =
      (0, cycleShift cycle (fun j => digitSubgroup (parameters T) (cycle j) (labels j))
        (decodeCycleTables spec cycle labels hs tables ht)
        (usefulProjection (parameters T) (decodeNumericalPoint (parameters T) ((0, 0), n)))) := by
  let E := parameters T
  let d := decodeCycleTables spec cycle labels hs tables ht
  have hrow (i : Channel T) :
      CycleRowTest (configurationRow (cycleConfiguration T spec (channelEquiv i))
        (tables (channelEquiv i))) n ↔
      (n : K E i) = cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0, 0), n))) i := by
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [configurationRow_on spec cycle labels hs tables j, cycleShift_apply]
      change (n % E.r (cycle j) =
        (tables (channelEquiv (cycle j))).getD
          (rectangularIndex (E.b (cycle (j - 1)))
            (n % E.a (cycle (j - 1))) (n % E.b (cycle (j - 1)))) 0 % E.r (cycle j)) ↔
        (n : K E (cycle j)) = (decodeCycleTables spec cycle labels hs tables ht j
          ((n : ZMod (E.a (cycle (j - 1)))), (n : ZMod (E.b (cycle (j - 1))))) : K E (cycle j))
      rw [← (ZMod.val_injective (E.r (cycle j))).eq_iff]
      simp only [decodeCycleTables, ZMod.val_natCast]
      rfl
    · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      rw [configurationRow_off spec cycle labels hs tables i hoff,
        cycleRowTest_zero, cycleShift_eq_zero (M := K E) (N := P E) cycle
          (fun j => digitSubgroup E (cycle j) (labels j)) d _ hoff]
      rw [← (ZMod.val_injective (E.r i)).eq_iff]
      simp only [ZMod.val_natCast, ZMod.val_zero]
      rfl
  have hrows : CycleTest (List.ofFn fun s =>
      configurationRow (cycleConfiguration T spec s) (tables s)) n ↔
      ∀ i : Channel T, (n : K E i) = cycleShift cycle
        (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0, 0), n))) i := by
    simp only [CycleTest, List.forall_mem_ofFn_iff]
    constructor
    · intro h i
      exact (hrow i).mp (h (channelEquiv i))
    · intro h s
      have he := (hrow (channelEquiv.symm s)).mpr (h _)
      simpa only [Equiv.apply_symm_apply] using he
  rw [hrows]
  constructor
  · intro h
    refine Prod.ext (by rfl) ?_
    funext i
    change low E i (n : ZMod (E.r i ^ 2)) = _
    rw [CyclicShear.low_natCast]
    exact h i
  · intro h i
    have hi := congrFun (congrArg Prod.snd h) i
    change low E i (n : ZMod (E.r i ^ 2)) = _ at hi
    rw [CyclicShear.low_natCast] at hi
    exact hi

theorem cycleTables_correct (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (tables : ChannelSlot → List ℕ) (ht : ValidCycleTables T spec tables) :
    (cycleCodes (numericalOrder T) (List.ofFn fun s =>
      configurationRow (cycleConfiguration T spec s) (tables s))).toFinset.image
      (decodeNumericalPoint (parameters T)) =
    cycleTile (parameters T) cycle labels (decodeCycleTables spec cycle labels hs tables ht) := by
  rw [numericalOrder_eq]
  exact cycleCodes_correct (parameters T) _ _ (cycleRows_correct spec cycle labels hs tables ht)

noncomputable def encodeCycleTables (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j))
    (d : ∀ j, P (parameters T) (cycle (j - 1)) →
      digitSubgroup (parameters T) (cycle j) (labels j))
    (s : ChannelSlot) : List ℕ :=
  if h : ∃ j, cycle j = channelEquiv.symm s then
    functionTable functionTableSize (fun e => (d (Classical.choose h) e).val.val)
  else []

theorem encodeCycleTables_on (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j))
    (d : ∀ j, P (parameters T) (cycle (j - 1)) →
      digitSubgroup (parameters T) (cycle j) (labels j)) (j : ZMod t) :
    encodeCycleTables cycle labels d (channelEquiv (cycle j)) =
      functionTable functionTableSize (fun e => (d j e).val.val) := by
  have h : ∃ z, cycle z = channelEquiv.symm (channelEquiv (cycle j)) :=
    ⟨j, (channelEquiv.symm_apply_apply _).symm⟩
  have hc : Classical.choose h = j := cycle.injective
    ((Classical.choose_spec h).trans (channelEquiv.symm_apply_apply _))
  rw [encodeCycleTables, dif_pos h]
  exact congrArg (fun z => functionTable functionTableSize (fun e => (d z e).val.val)) hc

theorem encodeCycleTables_valid (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (d : ∀ j, P (parameters T) (cycle (j - 1)) →
      digitSubgroup (parameters T) (cycle j) (labels j)) :
    ValidCycleTables T spec (encodeCycleTables cycle labels d) := by
  intro s
  by_cases hi : ∃ j, cycle j = channelEquiv.symm s
  · obtain ⟨j, hj⟩ := hi
    have he : s = channelEquiv (cycle j) :=
      (channelEquiv.apply_symm_apply s).symm.trans (congrArg channelEquiv hj.symm)
    subst s
    rw [encodeCycleTables_on]
    simp only [cycleAlphabet, cycleConfiguration, Equiv.symm_apply_apply,
      hs.1 j, ↓reduceIte, numericalR_eq]
    apply functionTable_mem_subgroupTables
    intro e
    refine ⟨ZMod.val_lt (d j e).val, ?_⟩
    apply (numericalOtherPrimes_test T (cycle j) (labels j) _).mpr
    simpa only [ZMod.natCast_zmod_val] using (d j e).property
  · have hoff : ∀ j, cycle j ≠ channelEquiv.symm s := by simpa only [not_exists] using hi
    have hb : (spec s).1 = false := by
      simpa only [Equiv.apply_symm_apply] using hs.2 (channelEquiv.symm s) hoff
    simp only [encodeCycleTables, dif_neg hi, cycleAlphabet, cycleConfiguration,
      hb, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]

theorem decode_encodeCycleTables (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels)
    (d : ∀ j, P (parameters T) (cycle (j - 1)) →
      digitSubgroup (parameters T) (cycle j) (labels j)) :
    decodeCycleTables spec cycle labels hs (encodeCycleTables cycle labels d)
      (encodeCycleTables_valid spec cycle labels hs d) = d := by
  funext j e
  apply Subtype.ext
  change (((encodeCycleTables cycle labels d (channelEquiv (cycle j))).getD
    (rectangularIndex ((parameters T).b (cycle (j - 1))) e.1.val e.2.val) 0 : ℕ) :
      K (parameters T) (cycle j)) = (d j e).val
  rw [encodeCycleTables_on, functionTable_apply functionTableSize
    (usefulProduct_le_tableSize T _), ZMod.natCast_zmod_val]

/-- The numerical family contains exactly all the cycle gadgets, including
every arbitrary finite function used in the collision argument. -/
theorem cycleFamily_correct (spec : CycleSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : CycleSpecMatches spec cycle labels) :
    ((cycleFamily T spec).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset = cycleTiles (parameters T) cycle labels := by
  unfold cycleFamily cycleGadgets
  rw [List.map_map]
  ext F
  simp only [List.mem_toFinset, List.mem_map, mem_vectors, Function.comp_def,
    cycleTiles, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨tables, ht, hF⟩
    have hv : ValidCycleTables T spec tables := ht
    exact ⟨decodeCycleTables spec cycle labels hs tables hv,
      (cycleTables_correct spec cycle labels hs tables hv).symm.trans hF⟩
  · rintro ⟨d, hF⟩
    refine ⟨encodeCycleTables cycle labels d, encodeCycleTables_valid spec cycle labels hs d, ?_⟩
    rw [cycleTables_correct spec cycle labels hs _ (encodeCycleTables_valid spec cycle labels hs d),
      decode_encodeCycleTables]
    exact hF

end TranslationTiling.Compiler.Effective
