import TranslationTiling.FiniteCompiler.PackedTailCompiler
import TranslationTiling.FiniteCompiler.Effective.GuardedAssembly
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift
open Effective PairSmall
open scoped Classical

noncomputable section

local instance packedTailCoreFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000

private def tailTests (T : LeanWang.TileSet) (k : ℕ) : List GuardedAssignments :=
  tailSeedTests k ++ (rawGuardedMasks T (3^k)).map (expandMask k)

private theorem tailTests_primrec : Primrec (fun z : LeanWang.TileSet × ℕ => tailTests z.1 z.2) := by
  unfold tailTests
  have hm := rawGuardedMasks_primrec.comp
    (show Primrec (fun z : LeanWang.TileSet × ℕ => (z.1,3^z.2)) by fun_prop)
  exact appendList (tailSeedTests_primrec.comp Primrec.snd)
    (mapList hm (expandMask_primrec.comp
      (show Primrec (fun z : (LeanWang.TileSet × ℕ) × RawMask => (z.1.2,z.2)) by fun_prop)))

private theorem guardedTests_primrec : Primrec guardedTests := by
  unfold guardedTests
  simp only [pow_two]
  fun_prop

private theorem guardedRadius_primrec : Primrec guardedRadius := by
  unfold guardedRadius
  fun_prop

def packedTailCore (T : LeanWang.TileSet) : Tile 3 :=
  let k := guardedTrits T.length
  let rs := tailRows k
  let Fs := guardedRawDeck rs (tailSlopes k) (tailTests T k)
  guardedAssembly (((guardedOrder rs,guardedDigitCap k,guardedTests T.length),
    (guardedModuli rs).prod,guardedRadius k),Fs)

theorem packedTailCore_computable : Computable packedTailCore := by
  have hk : Primrec (fun T : LeanWang.TileSet => guardedTrits T.length) := by fun_prop
  have hr := tailRows_primrec.comp hk
  have hF := guardedRawDeck_primrec.comp
    (hr.pair ((tailSlopes_primrec.comp hk).pair (tailTests_primrec.comp (Primrec.id.pair hk))))
  have hN := guardedOrder_primrec.comp hr
  have hP := guardedDigitCap_primrec.comp hk
  have hX := guardedTests_primrec.comp (show Primrec (fun T : LeanWang.TileSet => T.length) by fun_prop)
  have hR := product_primrec.comp (guardedModuli_primrec.comp hr)
  have hH := guardedRadius_primrec.comp hk
  exact guardedAssembly_computable.comp (((hN.pair (hP.pair hX)).pair (hR.pair hH)).pair hF).to_comp

private theorem cyclic_eq_decoded {S : System} [AlphabetFamily S] (E : EncodingParameters S)
    (F : CyclicTile) : cyclicTileSet E.cyclicOrder F =
      (F.toFinset.image (decodeNumericalPoint E)).image (ambientCyclicEquiv E) := by
  rw [cyclicTileSet,Finset.image_image]
  apply Finset.image_congr
  intro f _
  change (f.1,(f.2 : ZMod E.cyclicOrder)) =
    ambientCyclicEquiv E (f.1,numericalFactor E f.2)
  rw [numericalFactor_eq]
  exact (AddEquiv.apply_symm_apply (ambientCyclicEquiv E) _).symm

private theorem raw_deck_solution {S : System} [AlphabetFamily S] (E : EncodingParameters S)
    (ps : List (PartialTest S)) (Fs : List CyclicTile)
    (hF : guardedDecodedFamily E Fs = partialDeck E ps) :
    (∃ A : Set (Ambient E), ∀ F ∈ partialDeck E ps, Tiles F A) ↔
      ∃ B : Set (Plane × ZMod E.cyclicOrder), ∀ i : Fin Fs.length,
        Tiles (cyclicTileSet E.cyclicOrder (Fs.getD i.val [])) B := by
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨ambientCyclicEquiv E '' A,fun i => ?_⟩
    rw [cyclic_eq_decoded]
    apply PairSmall.ambient_covers E
    apply hA
    rw [← hF]
    exact (mem_guardedDecodedFamily _ _).mpr
      ⟨_, getD_mem_of_lt Fs i.val [] i.isLt, rfl⟩
  · rintro ⟨B,hB⟩
    refine ⟨(ambientCyclicEquiv E).symm '' B,fun F h => ?_⟩
    rw [← hF] at h
    obtain ⟨G,hG,rfl⟩ := (mem_guardedDecodedFamily _ _).mp h
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hG
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi,he,cyclic_eq_decoded] at h
    exact PairSmall.ambient_uncovers E _ _ h

section
variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (ternaryLayoutProfile k).radices.prod)

local instance tailSlopeAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

private theorem tailSlopes_correct (i : Column (tailRefinement hk c).system) :
    (tailRefinement hk c).system.slope i = (tailSlopes k).getD i.val 0 := by
  rw [show (tailRefinement hk c).system.slope i = ((ternaryLayoutProfile k).slope i.val : ℤ) from
    (packedTernary_layout _ hk rfl).slope i]
  have hi : i.val < 18+2*k := by
    have h : i.val < (tailRefinement hk c).width := i.isLt
    rwa [tailRefinement_width] at h
  simp only [tailSlopes,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some]

end

theorem packedTailCore_facts (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    packedTailCore T ≠ [] ∧ FaceConnected (packedTailCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (packedTailCore T)) ∧
    ((packedTailCore T).length : ℝ) ≤ guardedBound T.length := by
  let n := T.length
  let k := guardedTrits n
  have hk : 20 ≤ k := guardedTrits_ge hn
  have hk' : 0 < k := by omega
  have hpos : 0 < n := (by decide : 0 < 3^21).trans hn
  have hcap : n ≤ 3^k := guardedTrits_capacity n
  have hrad : (ternaryLayoutProfile k).radices.prod = 3^k := by
    simp [ternaryLayoutProfile,List.prod_replicate]
  have hc : n ≤ (ternaryLayoutProfile k).radices.prod := hcap.trans_eq hrad.symm
  let c := code T (ternaryLayoutProfile k).radices.prod hpos hc
  letI : AlphabetFamily (system c) := GuardedCompiler.alphabet c
  let S := tailRefinement hk' c
  letI : AlphabetFamily S.system := S.family
  let E : EncodingParameters S.system := tailEncoding hk rfl (fun _ => rfl)
  let ps := GuardedCompiler.refinedPatterns c S
  let rs := tailRows k
  let Fs := guardedRawDeck rs (tailSlopes k) (tailTests T k)
  let X := guardedTests n
  let P := guardedDigitCap k
  let H := guardedRadius k
  have hm : GuardedRowsMatch E rs := tailRowsMatch hk rfl (fun _ => rfl)
  have hs : ∀ i : Column S.system, S.system.slope i = (tailSlopes k).getD i.val 0 :=
    tailSlopes_correct hk' c
  have hFs : guardedDecodedFamily E Fs = partialDeck E ps := by
    apply numericalDeck_correct hm _ _ _ hs
    have he := numericalExpandedTests_correct hk' hpos hc E rs hm
    rw [congrArg (rawGuardedMasks T) hrad] at he
    rw [tailTests,List.flatMap_append,guardedDecodedFamily_append,
      numericalSeedTests_correct hk' c E rs hm, he]
  have hmem {F : CyclicTile} (hF : F∈Fs) :
      F.toFinset.image (decodeNumericalPoint E) ∈ partialDeck E ps := by
    rw [← hFs]
    exact (mem_guardedDecodedFamily _ _).mpr ⟨F,hF,rfl⟩
  have hlo : 0<Fs.length := by simp [Fs,guardedRawDeck]
  have hlen : Fs.length ≤ X := by
    have h := guardedRawDeck_length rs (tailSlopes k) (tailTests T k)
    have htest : (tailTests T k).length ≤ 180+(2313+72*(3^k)^2) := by
      simp only [tailTests,List.length_append,List.length_map]
      exact Nat.add_le_add (tailSeedTests_length k) (rawGuardedMasks_length T (3^k))
    have hc := Nat.pow_le_pow_left (guardedTrits_capacity_le ((by decide : 1 < 3^21).trans hn)) 2
    have hw : rs.length ≤ 4*(n+4) := by
      rw [hm.length,show S.system.width = 18+2*k from tailRefinement_width hk' c]
      have := Nat.log_le_self 3 (n-1)
      have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
      unfold k guardedTrits
      omega
    have hw₂ := Nat.pow_le_pow_left hw 2
    have hf : rs.length-2 ≤ rs.length := Nat.sub_le _ _
    have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
    unfold X guardedTests
    nlinarith only [h,htest,hc,hw,hw₂,hf,hn']
  have hX : 2313 ≤ X := by unfold X guardedTests; nlinarith
  have hP : 35 ≤ P := by
    have hp := (guardedPairCaps_ge hk).1
    have hd := guardedDigitCap_gt hk
    unfold guardedDigitStart at hd
    exact (by decide : 35 ≤ 16^2).trans ((Nat.pow_le_pow_left hp 2).trans (by omega))
  have hprime : PrimeBound E.cyclicOrder P :=
    prime_bound E hP (tailEncoding_prime_bound hk rfl (fun _ => rfl))
  have hXbase : n+4 ≤ X := by
    unfold X guardedTests
    calc
      n+4 ≤ (n+4)^2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide)
  have hP₁ : P ≤ X^2 :=
    (guard_digit_budget hn).trans (Nat.pow_le_pow_left hXbase 2)
  have hsupport : PartialStrip.StripBounds E (fun _ => H) :=
    tailSupport hk rfl (fun _ => rfl) (packedTernary_layout _ hk' rfl).slope
  have hnonempty : ∀ F ∈ Fs, F ≠ [] := by
    intro F hF hnil
    have h := PartialStrip.deck_tile_nonempty ps E (hmem hF)
    simp [hnil] at h
  have hmass : ∀ F ∈ Fs, (cyclicTileSet E.cyclicOrder F).card ≤ MassSize.mass E := by
    intro F hF
    rw [cyclic_eq_decoded,Finset.card_image_of_injective _ (ambientCyclicEquiv E).injective]
    exact PartialStrip.deck_mass ps E (hmem hF)
  have hstrip : ∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 (fun _ => H) f.1 := by
    intro F hF f hf
    exact PartialStrip.deck_strip ps E hsupport (hmem hF)
      (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)
  have hker (j : ℤ) : (((0:Plane), ((inputOrder E:ℤ)*j : ℤ)) : Plane × ZMod E.cyclicOrder)∈
      cyclicTileSet E.cyclicOrder (Fs.getD 0 []) := by
    rw [cyclic_eq_decoded]
    change _ ∈ ((kernelCodes (guardedOrder rs) (guardedModuli rs)).toFinset.image
      (decodeNumericalPoint E)).image _
    rw [numericalKernel_correct hm]
    exact kernel_column E j
  have hR := inputOrder_pos E
  have hRN := Nat.le_of_dvd E.cyclicOrder_pos (inputOrder_dvd E)
  have hasm := guardedAssembly_facts E.cyclicOrder_pos (by omega : 3 < P) hX hprime hP₁
    (guard_stack_budget hn) hR hRN hlo hlen hnonempty hmass hstrip hker
  have heq : guardedAssembly (((E.cyclicOrder,P,X),inputOrder E,H),Fs) = packedTailCore T := by
    rw [← rowsOrder_eq hm,← rowsInput_eq hm]
    rfl
  dsimp only at hasm
  rw [heq] at hasm
  obtain ⟨hne,hconn,hT,hvol⟩ := hasm
  refine ⟨hne,hconn,(GuardedCompiler.refined_deck_equiv c S E).trans
    ((raw_deck_solution E ps Fs hFs).trans hT),?_⟩
  have hv : ((packedTailCore T).length : ℝ) ≤
      (reservedVolumeCap 35 (fun _ => H) (inputOrder E) (MassSize.mass E) (reservedCap X P) : ℕ) := by
    exact_mod_cast hvol
  exact hv.trans (guarded_volume_bound hn hR (tailEncoding_order_mass hk rfl (fun _ => rfl)))

end
end TranslationTiling.FiniteCompiler.Packed
