import TranslationTiling.FiniteCompiler.Effective.SlotNumericalActivationDeck
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalGuards
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalLift
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalKernel
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalAssembly
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalPatterns
import TranslationTiling.FiniteCompiler.Effective.SlotDeckCount

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Compiler Compiler.Effective Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

private def extraLows (k m : ℕ) : List ℕ :=
  (List.range (2*k*m+4*m)).map fun i => (numericalSlotRow k m (20+i)).1

private theorem extraLows_primrec : Primrec (fun z : ℕ × ℕ => extraLows z.1 z.2) := by
  unfold extraLows
  apply mapList (by fun_prop)
  let args (z : (ℕ × ℕ) × ℕ) : ℕ × ℕ × ℕ := (z.1.1,z.1.2,20+z.2)
  have ha : Primrec args := by unfold args; fun_prop
  exact (Primrec.fst.comp (numericalSlotRow_primrec.comp ha)).of_eq (by intro z; rfl)

/-- The old arithmetic tiles are lifted by the kernel in every added row. -/
def numericalArithmeticMasks (N k m : ℕ) : List CyclicTile :=
  arithmeticBaseline.map (numericalArithmeticLift N (order (fourValueLayout 0)) (extraLows k m))

theorem numericalArithmeticMasks_primrec : Primrec (fun z : ℕ × ℕ × ℕ =>
    numericalArithmeticMasks z.1 z.2.1 z.2.2) := by
  unfold numericalArithmeticMasks
  apply mapList (Primrec.const arithmeticBaseline)
  let args (z : (ℕ × ℕ × ℕ) × CyclicTile) :
      (ℕ × ℕ × List ℕ) × CyclicTile :=
    ((z.1.1,order (fourValueLayout 0),extraLows z.1.2.1 z.1.2.2),z.2)
  have hlo : Primrec (fun z : (ℕ × ℕ × ℕ) × CyclicTile => extraLows z.1.2.1 z.1.2.2) :=
    extraLows_primrec.comp (by fun_prop)
  have ha : Primrec args := by unfold args; fun_prop
  exact (numericalArithmeticLift_primrec.comp ha).of_eq (by intro z; rfl)

section
variable {k m : ℕ} (s : SlotParameters k m)
local instance numericalDeckDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

private theorem addedRow_iff (i : SlotRow k m) :
    20 ≤ slotRowNumber i ↔ ∃ j : AddedRow k m, Sum.inr j = i := by
  rcases i with i | ⟨g,d,i⟩ | ⟨g,i,b⟩
  · have h : i.val < 20 := by simpa [fourValueRows_length] using i.isLt
    simp [slotRowNumber,h.not_ge]
  · simp [slotRowNumber]
  · simp [slotRowNumber]
    omega

private theorem extraLows_mem (hs : s.prime = rankedSlotPrime k m) (r : ℕ) :
    r ∈ extraLows k m ↔ ∃ i : AddedRow k m, s.layout.lowSize (.inr i) = r := by
  simp only [extraLows,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j,hj,he⟩
    let i := (slotRowEquiv k m).symm ⟨20+j,by omega⟩
    have hval : slotRowNumber i = 20+j := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply _)
    obtain ⟨r₀,hr⟩ := (addedRow_iff i).mp (by omega)
    have he' := (congrArg Prod.fst (numericalSlotRow_eq s hs i)).symm
    exact ⟨r₀,hr ▸ he'.trans (hval.symm ▸ he)⟩
  · rintro ⟨i,rfl⟩
    let a : SlotRow k m := .inr i
    have hlo := (addedRow_iff a).mpr ⟨i,rfl⟩
    have hhi : slotRowNumber a < 20+2*k*m+4*m := by
      rw [← slotRowEquiv_val]
      exact (slotRowEquiv k m a).isLt
    refine ⟨slotRowNumber a-20,by omega,?_⟩
    rw [Nat.add_sub_of_le hlo]
    exact congrArg Prod.fst (numericalSlotRow_eq s hs a)

theorem numericalArithmeticMasks_correct (hs : s.prime = rankedSlotPrime k m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalArithmeticMasks (order s.layout) k m,
      G.toFinset.image (decodePoint s.layout) = F) ↔ F ∈ s.arithmeticTiles := by
  simp only [numericalArithmeticMasks,arithmeticTiles,List.mem_map]
  constructor
  · rintro ⟨G,⟨H,hH,rfl⟩,h⟩
    exact ⟨H,hH,(s.numericalArithmeticLift_correct H (extraLows k m) (s.extraLows_mem hs)).symm.trans h⟩
  · rintro ⟨H,hH,rfl⟩
    exact ⟨_,⟨H,hH,rfl⟩,s.numericalArithmeticLift_correct H (extraLows k m) (s.extraLows_mem hs)⟩

end

/-- All masks other than the kernel, in the order in which they are stacked. -/
def numericalSlotTests (T : LeanWang.TileSet) (N k m w : ℕ) : List CyclicTile :=
  numericalArithmeticMasks N k m ++ numericalAnchorMasks N k m ++ numericalMarkerMasks N k m ++
    numericalFallbackMasks N k m ++ numericalSlotActivationMasks N k m w ++
    numericalSeedMasks N k m ++ numericalGuardMasks T N k m w

private abbrev SlotDeckArgs := LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ

theorem numericalSlotTests_primrec : Primrec (fun z : SlotDeckArgs =>
    numericalSlotTests z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  let triple (z : SlotDeckArgs) : ℕ × ℕ × ℕ := (z.2.1,z.2.2.1,z.2.2.2.1)
  have ht : Primrec triple := by unfold triple; fun_prop
  have ha := numericalArithmeticMasks_primrec.comp ht
  have hc := numericalAnchorMasks_primrec.comp ht
  have hm := numericalMarkerMasks_primrec.comp ht
  have hf := numericalFallbackMasks_primrec.comp ht
  have hv := numericalSlotActivationMasks_primrec.comp (Primrec.snd :
    Primrec (Prod.snd : SlotDeckArgs → ℕ × ℕ × ℕ × ℕ))
  have hs := numericalSeedMasks_primrec.comp ht
  have hg := numericalGuardMasks_primrec
  unfold numericalSlotTests
  exact (appendList (appendList (appendList (appendList (appendList (appendList ha hc) hm) hf) hv) hs)
    hg).of_eq (by intro z; rfl)

private theorem numericalLocalMasks_length_le (N k m p slope : ℕ) (excluded : List ℕ) :
    (numericalLocalMasks N k m p slope excluded).length ≤ 21+2*k*m+4*m := by
  simp only [numericalLocalMasks,List.length_cons,List.length_map]
  have hf := List.length_filter_le (l := List.range (20+2*k*m+4*m)) (p := fun j => decide (j ∉ excluded))
  rw [List.length_range] at hf
  omega

private theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length*n := by
  rw [List.length_flatMap]
  exact (listSumMap_le h).trans_eq (by simp)

theorem numericalSlotTests_length (T : LeanWang.TileSet) (N k m w : ℕ) :
    (numericalSlotTests T N k m w).length+1 ≤ slotDeckCap k m ((slotRadix m w)^k) := by
  let B := 21+2*k*m+4*m
  have ha : (numericalAnchorMasks N k m).length ≤ 20*(2*k*m+4*m) := by
    unfold numericalAnchorMasks
    apply (length_flatMap_le _ _ (2*k*m+4*m) _).trans_eq
    · simp
    · intro i _
      simp only [List.length_map]
      have he : (List.range (20+2*k*m+4*m)).filter (fun j => decide (20 ≤ j)) =
          List.range' 20 (2*k*m+4*m) := by
        apply List.Perm.eq_of_sortedLE
        · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT.sortedLE
        · exact List.sortedLE_range' 20 _ 1
        · have hsrc : ((List.range (20+2*k*m+4*m)).filter (fun j => decide (20 ≤ j))).Nodup :=
            List.nodup_range.filter _
          have hdst := (List.sortedLT_range' 20 (2*k*m+4*m) (by decide : (1 : ℕ) ≠ 0)).nodup
          apply (List.perm_ext_iff_of_nodup hsrc hdst).mpr
          intro x
          simp only [List.mem_filter,List.mem_range,decide_eq_true_eq,List.mem_range'_1]
          omega
      rw [he,List.length_range']
  have hm : (numericalMarkerMasks N k m).length ≤ 6*k*m*B := by
    unfold numericalMarkerMasks
    apply (length_flatMap_le _ _ (k*(m*(3*B))) _).trans_eq
    · simp only [List.length_cons,List.length_nil]
      ring
    · intro g _
      apply (length_flatMap_le _ _ (m*(3*B)) _).trans_eq
      · rw [List.length_range]
      · intro d _
        apply (length_flatMap_le _ _ (3*B) _).trans_eq
        · rw [List.length_range]
        · intro i _
          apply (length_flatMap_le _ _ B _).trans_eq
          · rw [List.length_range]
          · intro j _
            exact numericalLocalMasks_length_le ..
  have hf : (numericalFallbackMasks N k m).length ≤ 2*m*B := by
    unfold numericalFallbackMasks
    apply (length_flatMap_le _ _ (m*B) _).trans_eq
    · simp only [List.length_cons,List.length_nil]
      ring
    · intro g _
      apply (length_flatMap_le _ _ B _).trans_eq
      · rw [List.length_range]
      · intro i _
        exact numericalLocalMasks_length_le ..
  have hsum : (numericalMarkerMasks N k m).length + (numericalFallbackMasks N k m).length ≤
      (6*k*m+2*m)*B := by rw [Nat.add_mul]; exact Nat.add_le_add hm hf
  have hv : (numericalSlotActivationMasks N k m w).length ≤ 2*k*2^m := by
    rw [numericalSlotActivationMasks_length]
    apply Nat.mul_le_mul_left
    exact Nat.choose_le_two_pow _ _
  have hg := numericalGuardMasks_length T N k m w
  have hs := numericalSeedMasks_length N k m
  simp only [numericalSlotTests,numericalArithmeticMasks,List.length_append,List.length_map]
  unfold slotDeckCap B at *
  omega

section
local instance numericalMatchFrame : SeedFrame := compactSeedFrame
variable {k m w : ℕ} {T : LeanWang.TileSet}
variable (hn : 0 < T.length) (hcap : T.length ≤ (slotRadix m w)^k)

private abbrev numericCode : Code T ((slotRadix m w)^k) := Packed.code T _ hn hcap

local instance numericalMatchAlphabet : AlphabetFamily (system (numericCode hn hcap)) :=
  GuardedCompiler.alphabet (numericCode hn hcap)

variable (s : SlotParameters k m)
local instance numericalMatchDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

private theorem seedRelated (hs : s.prime = rankedSlotPrime k m)
    (t : Fin 2) (i : Fin 18) (a : Letter (system (numericCode hn hcap)) (arithmeticColumn i)) :
    ∃ G, numericalSlotCycle (order s.layout) k m (numericalSeedAssignments (numericCode hn hcap) t i a) =
      [G] ∧ s.SlotMaskMatches (G.toFinset.image (decodePoint s.layout)) (s.seedMask (numericCode hn hcap) t i a) := by
  obtain ⟨G,hG,hv,hm,h⟩ := s.numericalSeedFor_spec (numericCode hn hcap) hs t i a
  exact ⟨G,hG,Or.inr ⟨hv,hm,fun o ho => (h o ho).trans (s.seedMask_spec (numericCode hn hcap) t i a o ho).symm⟩⟩

private theorem guardRelated (hs : s.prime = rankedSlotPrime k m)
    (p : PartialTest (system (numericCode hn hcap))) (hp : p ∈ patterns (numericCode hn hcap)) :
    ∃ G, numericalSlotCycle (order s.layout) k m (expandSlotMask k m w (testMask (numericCode hn hcap) p)) =
      [G] ∧ s.SlotMaskMatches (G.toFinset.image (decodePoint s.layout))
        (s.guardMask (numericCode hn hcap) p hp) := by
  obtain ⟨G,hG,hv,hm,h⟩ := s.numericalGuardFor_spec (numericCode hn hcap) hs p hp
  exact ⟨G,hG,Or.inr ⟨hv,hm,fun o ho => (h o ho).trans (s.guardMask_spec (numericCode hn hcap) p hp o ho).symm⟩⟩

private theorem numericalSeedMatch (hs : s.prime = rankedSlotPrime k m) (G : CyclicTile)
    (hG : G ∈ numericalSeedMasks (order s.layout) k m) :
    ∃ t i a, ¬ LetterSeedSet (system (numericCode hn hcap)) t (arithmeticColumn i) a ∧
      s.SlotMaskMatches (G.toFinset.image (decodePoint s.layout)) (s.seedMask (numericCode hn hcap) t i a) := by
  obtain ⟨xs,hxs,hG⟩ := List.mem_flatMap.mp hG
  obtain ⟨t,i,a,ha,rfl⟩ := (numericalSeeds_lists (numericCode hn hcap) xs).mp hxs
  obtain ⟨A,hA,h⟩ := s.seedRelated hn hcap hs t i a
  rw [hA,List.mem_singleton] at hG
  exact ⟨t,i,a,ha,hG.symm ▸ h⟩

private theorem numericalGuardMatch (hs : s.prime = rankedSlotPrime k m)
    (G : CyclicTile) (hG : G ∈ numericalGuardMasks T (order s.layout) k m w) :
    ∃ (p : PartialTest (system (numericCode hn hcap))) (hp : p ∈ patterns (numericCode hn hcap)),
      s.SlotMaskMatches (G.toFinset.image (decodePoint s.layout)) (s.guardMask (numericCode hn hcap) p hp) := by
  obtain ⟨xs,hxs,hG⟩ := List.mem_flatMap.mp hG
  obtain ⟨p,hp,rfl⟩ := (rawMask_membership hn hcap xs).mp hxs
  change G ∈ numericalSlotCycle (order s.layout) k m (expandSlotMask k m w (testMask (numericCode hn hcap) p)) at hG
  obtain ⟨A,hA,h⟩ := s.guardRelated hn hcap hs p hp
  rw [hA,List.mem_singleton] at hG
  exact ⟨p,hp,hG.symm ▸ h⟩

private theorem numericalKernel_decodes :
    (numericalKernel (order s.layout) s.period).toFinset.image (decodePoint s.layout) =
      productKernel s.layout := by
  let e : Plane × ZMod (order s.layout) → SharedCoordinates.Ambient s.layout :=
    fun p => (p.1,s.crt p.2)
  have he : e ∘ cyclicPoint (order s.layout) = decodePoint s.layout := by
    funext p
    exact Prod.ext rfl (map_natCast s.crt p.2)
  have h := congrArg (Finset.image e) s.numericalKernel_correct
  simp only [cyclicTileSet,Finset.image_image,he,s.encodeTile_decode] at h
  exact h

include hn hcap in
theorem numericalSlotPolycube (hs : s.prime = rankedSlotPrime k m)
    (hwm : w ≤ m) {P : ℕ}
    (hPr : PrimeBound (order s.layout) P) (hP : 3 < P) (hA : ∀ i, s.fallback i ≤ fallbackCap m)
    (hB : ∀ i j, s.marker i j ≤ markerCap k m) (hC : ∀ i, s.low i ≤ lowCap k m) :
    let K := numericalKernel (order s.layout) s.period
    let Fs := numericalSlotTests T (order s.layout) k m w
    let H := slotAssemblyRadii k m w
    let X := slotStackTestCap P (K :: Fs).length
    let U := guardedAssemblyBySlope (((order s.layout,P,X),s.period,H),K :: Fs)
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun j => H.getD j 0) s.period (order s.layout / s.period)
        (reservedPrimeCap X P) := by
  let C := numericCode hn hcap
  let N := order s.layout
  let K := numericalKernel N s.period
  let L := numericalSlotTests T N k m w
  let ds (G : CyclicTile) := G.toFinset.image (decodePoint s.layout)
  have hmem (G : CyclicTile) :
      G ∈ L ↔
        G ∈ numericalArithmeticMasks N k m ∨
        G ∈ numericalAnchorMasks N k m ∨
        G ∈ numericalMarkerMasks N k m ∨
        G ∈ numericalFallbackMasks N k m ∨
        G ∈ numericalSlotActivationMasks N k m w ∨
        G ∈ numericalSeedMasks N k m ∨ G ∈ numericalGuardMasks T N k m w := by
    simp only [L,numericalSlotTests,List.mem_append,or_assoc]
  have hArith := s.numericalArithmeticMasks_correct hs
  have hAnchor := s.numericalAnchorMasks_correct hs
  have hM := s.numericalMarkerMasks_correct hs
  have hF := s.numericalFallbackMasks_correct hs
  have hV := s.numericalSlotActivationMasks_correct hs hwm
  have hDeck := s.slotDeck_membership C hwm
  have hD (i : WangSlot k m) : s.slotOffsetFactor i ≤ slotOffsetFactorCap k m := by
    by_cases h : k = 1 ∧ m = 1
    · obtain ⟨rfl,rfl⟩ := h
      unfold slotOffsetFactor low marker fallback
      simp only [hs]
      exact (by decide +kernel : ∀ i : WangSlot 1 1,
        rankedSlotPrime 1 1 (.inl (i,none)) *
          (∏ j : Fin 3, rankedSlotPrime 1 1 (.inl (i,some j))) *
          rankedSlotPrime 1 1 (.inr (i.1,i.2.2,false)) *
          rankedSlotPrime 1 1 (.inr (i.1,i.2.2,true)) ≤ slotOffsetFactorCap 1 1) i
    · rw [slotOffsetFactorCap,ite_eq_right h]
      exact s.slotOffsetFactor_le hA hB hC i
  apply s.slot_polycube_related C hwm hPr hP hD K L s.numericalKernel_decodes
  · intro G hG
    have h := (hmem G).mp hG
    rcases h with ha | hb | hm | hf | hv | ht | hp
    · have ha' := (hArith (ds G)).mp ⟨G,ha,rfl⟩
      exact ⟨ds G,(hDeck _).mpr (Or.inr (Or.inl ha')),Or.inl rfl⟩
    · have hb' := (hAnchor (ds G)).mp ⟨G,hb,rfl⟩
      exact ⟨ds G,(hDeck _).mpr (Or.inr (Or.inr (Or.inl hb'))),Or.inl rfl⟩
    · have hm' := (hM (ds G)).mp ⟨G,hm,rfl⟩
      exact ⟨ds G,(hDeck _).mpr (Or.inr (Or.inr (Or.inr (Or.inl hm')))),Or.inl rfl⟩
    · have hf' := (hF (ds G)).mp ⟨G,hf,rfl⟩
      exact ⟨ds G,(hDeck _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf'))))),Or.inl rfl⟩
    · have hv' := (hV (ds G)).mp ⟨G,hv,rfl⟩
      exact ⟨ds G,(hDeck _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hv')))))),Or.inl rfl⟩
    · obtain ⟨t,i,a,he,hrel⟩ := s.numericalSeedMatch hn hcap hs G ht
      refine ⟨_,(hDeck _).mpr ?_,hrel⟩
      right; right; right; right; right
      exact Or.inr (Or.inl ⟨t,i,a,he,rfl⟩)
    · obtain ⟨p,hp,hrel⟩ := s.numericalGuardMatch hn hcap hs G hp
      refine ⟨_,(hDeck _).mpr ?_,hrel⟩
      right; right; right; right; right; right; right
      exact ⟨p,hp,rfl⟩
  · intro B h
    rcases (hDeck B).mp h with hb | ha | hc | hm | hf | hv | ⟨t,i,a,ha,rfl⟩ | ⟨p,hp,rfl⟩
    · exact Or.inl hb
    · obtain ⟨G,hG,he⟩ := (hArith B).mpr ha
      exact Or.inr ⟨G,(hmem _).mpr (Or.inl hG),Or.inl he⟩
    · obtain ⟨G,hG,he⟩ := (hAnchor B).mpr hc
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inl hG)),Or.inl he⟩
    · obtain ⟨G,hG,he⟩ := (hM B).mpr hm
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inr (Or.inl hG))),Or.inl he⟩
    · obtain ⟨G,hG,he⟩ := (hF B).mpr hf
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inl hG)))),Or.inl he⟩
    · obtain ⟨G,hG,he⟩ := (hV B).mpr hv
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG))))),Or.inl he⟩
    · obtain ⟨G,hG,he⟩ := s.seedRelated hn hcap hs t i a
      have ht : G ∈ numericalSeedMasks N k m := by
        apply List.mem_flatMap.mpr
        refine ⟨_,(numericalSeeds_lists C _).mpr ⟨t,i,a,ha,rfl⟩,?_⟩
        rw [hG,List.mem_singleton]
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))),he⟩
    · obtain ⟨G,hG,he⟩ := s.guardRelated hn hcap hs p hp
      have ht : G ∈ numericalGuardMasks T N k m w := by
        apply List.mem_flatMap.mpr
        refine ⟨_,(rawMask_membership hn hcap _).mpr ⟨p,hp,rfl⟩,?_⟩
        change G ∈ numericalSlotCycle (order s.layout) k m (expandSlotMask k m w (testMask (numericCode hn hcap) p))
        rw [hG,List.mem_singleton]
      exact Or.inr ⟨G,(hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ht))))))),he⟩
  · intro o h
    refine ⟨fun A ha => ?_,fun B hb => ?_,fun i j F hm => ?_⟩
    · obtain ⟨G,hG,rfl⟩ := (hArith A).mpr ha
      exact h G ((hmem _).mpr (Or.inl hG))
    · obtain ⟨G,hG,rfl⟩ := (hAnchor B).mpr hb
      exact h G ((hmem _).mpr (Or.inr (Or.inl hG)))
    · obtain ⟨G,hG,rfl⟩ := (hM F).mpr ⟨i,j,hm⟩
      exact h G ((hmem _).mpr (Or.inr (Or.inr (Or.inl hG))))

end

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
