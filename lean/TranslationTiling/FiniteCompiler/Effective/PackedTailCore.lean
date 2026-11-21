import TranslationTiling.Compiler.ResidueLogBound
import TranslationTiling.FiniteCompiler.Effective.ResidueRows
import TranslationTiling.FiniteCompiler.Effective.GuardedAssembly
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift
open Effective PairSmall
open scoped Classical BigOperators

noncomputable section

local instance packedTailCoreFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000

private def tailTests (T : LeanWang.TileSet) (k : ℕ) : List GuardedAssignments :=
  tailSeedTests k ++ (rawGuardedMasks T (4^k)).map (expandMask 4 k)

private theorem tailTests_primrec : Primrec (fun z : LeanWang.TileSet × ℕ => tailTests z.1 z.2) := by
  unfold tailTests
  have hm := rawGuardedMasks_primrec.comp
    (show Primrec (fun z : LeanWang.TileSet × ℕ => (z.1,4^z.2)) by fun_prop)
  exact appendList (tailSeedTests_primrec.comp Primrec.snd)
    (mapList hm (expandMask_primrec.comp
      (show Primrec (fun z : (LeanWang.TileSet × ℕ) × RawMask => (4,z.1.2,z.2)) by fun_prop)))

@[fun_prop] private theorem residueDigits_primrec : Primrec residueDigits := by
  unfold residueDigits
  have h := (natLog_primrec 4 (by decide)).comp (show Primrec (fun n : ℕ => n-1) by fun_prop)
  fun_prop

@[fun_prop] private theorem residuePrimeCap_primrec : Primrec residuePrimeCap := by
  unfold residuePrimeCap residueUsefulCap
  fun_prop

private theorem residueTests_primrec : Primrec residueTests := by
  unfold residueTests
  fun_prop

private theorem residueRadius_primrec : Primrec residueRadius := by
  unfold residueRadius residueUsefulCap
  fun_prop

def packedTailCore (T : LeanWang.TileSet) : Tile 3 :=
  let k := residueDigits T.length
  let rs := residueData k
  let Fs := guardedRawDeck rs (tailSlopes k) (tailTests T k)
  guardedAssembly (((guardedOrder rs,residuePrimeCap k,residueTests T.length),
    (guardedModuli rs).prod,residueRadius k),Fs)

theorem packedTailCore_computable : Computable packedTailCore := by
  have hk : Primrec (fun T : LeanWang.TileSet => residueDigits T.length) := by fun_prop
  have hr := residueData_computable.comp hk.to_comp
  have hF := guardedRawDeck_primrec.to_comp.comp
    (hr.pair ((tailSlopes_primrec.comp hk).to_comp.pair (tailTests_primrec.comp (Primrec.id.pair hk)).to_comp))
  have hN := guardedOrder_primrec.to_comp.comp hr
  have hP := residuePrimeCap_primrec.comp hk
  have hX := residueTests_primrec.comp (show Primrec (fun T : LeanWang.TileSet => T.length) by fun_prop)
  have hR := product_primrec.to_comp.comp (guardedModuli_primrec.to_comp.comp hr)
  have hH := residueRadius_primrec.comp hk
  exact guardedAssembly_computable.comp (((hN.pair (hP.pair hX).to_comp).pair (hR.pair hH.to_comp)).pair hF)

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
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance tailSlopeAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

private theorem tailSlopes_correct (i : Column (tailRefinement hk (by decide : 0 < 4) c).system) :
    (tailRefinement hk (by decide : 0 < 4) c).system.slope i = (tailSlopes k).getD i.val 0 := by
  rw [show (tailRefinement hk (by decide : 0 < 4) c).system.slope i = ((radixLayoutProfile 4 k).slope i.val : ℤ) from
    (packedRadix_layout _ hk (by decide) rfl).slope i]
  have hi : i.val < 18+2*k := by
    have h : i.val < (tailRefinement hk (by decide : 0 < 4) c).width := i.isLt
    rwa [tailRefinement_width] at h
  simp only [tailSlopes,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,Profile.slope,ternaryLayoutProfile,radixLayoutProfile,List.length_replicate]

end

private theorem residueRowsMatch {S : System} [AlphabetFamily S] (k : ℕ)
    (hv : Valid (residueProfile k) (residuePrimeCap k))
    (hw : S.width = (residueProfile k).width)
    (ha : ∀ i : Column S, AlphabetFamily.size (T:=S) i = (residueProfile k).arity i.val)
    (hi : (residueProfile k).injectivityCheck) :
    GuardedRowsMatch (encoding (residueProfile k) hv hw ha hi) (residueData k) := by
  let p := residueProfile k
  have hnum (i : Channel S) : channelNumber i = (channelEquiv p hw i).val := by
    rcases i with i|t
    · rfl
    · change S.width+t.val = p.width+t.val
      rw [hw]
  have hget (i : Channel S) :
      (residueData k).getD (channelNumber i) (0,0,[]) =
        (p.a (channelNumber i),p.b (channelNumber i),(p.row (channelNumber i)).map Prod.fst) :=
    residueData_at k _ (by rw [hnum]; exact (channelEquiv p hw i).isLt)
  refine ⟨(residueData_length k).trans (by rw [hw]), ?_,?_,?_,?_⟩
  · intro i
    unfold rowA
    rw [hget,hnum] <;> rfl
  · intro i
    unfold rowB
    rw [hget,hnum] <;> rfl
  · intro i
    unfold rowR rowDigits
    rw [hget,hnum,encoding_r] <;> rfl
  · intro i v
    unfold rowDigits
    rw [hget,hnum]
    let j := channelEquiv p hw i
    have hj : guardedLabelNumber i v < (p.row j.val).length := by
      rw [(hv.2.2.2.2.1 j.val (List.mem_range.mpr j.isLt)).1]
      rcases i with i|t
      · exact (ha i) ▸ v.isLt
      · change 0 < p.arity (p.width+t.val)
        unfold Profile.arity
        have hh := residueProfile_width k
        change p.width = _ at hh
        split_ifs <;> omega
    change ((p.row j.val).map Prod.fst).getD (guardedLabelNumber i v) 0 = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
    have hh : ((p.row j.val).getD (guardedLabelNumber i v) (0,0,0)).1 = _ :=
      congrArg Prod.fst (List.getD_eq_getElem _ _ hj)
    rw [← hh]
    rcases i with i|t
    · rfl
    · rw [encoding_digit_seed] <;> rfl

private theorem residueSupport {S : System} [AlphabetFamily S] (k : ℕ)
    (hv : Valid (residueProfile k) (residuePrimeCap k))
    (hw : S.width = (residueProfile k).width)
    (ha : ∀ i : Column S, AlphabetFamily.size (T:=S) i = (residueProfile k).arity i.val)
    (hi : (residueProfile k).injectivityCheck)
    (hslope : ∀ i : Column S, S.slope i = ((residueProfile k).slope i.val : ℤ)) :
    PartialStrip.StripBounds (encoding (residueProfile k) hv hw ha hi) (fun _ => residueRadius k) := by
  let p := residueProfile k
  let E := encoding p hv hw ha hi
  obtain ⟨hmain,hseed⟩ := residueProfile_radius k (residuePrimeCap k) (residueUsefulCap k) rfl rfl
  refine ⟨by unfold residueRadius; omega, ?_,?_,?_⟩
  · intro i
    rw [hslope,Int.natAbs_natCast]
    refine ⟨by positivity,?_⟩
    unfold Profile.slope
    split_ifs with hh _
    · have h₁ : i.val < ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ).length := hh
      exact (by decide : ∀ x ∈ ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ), x≤16) _
        (getD_mem_of_lt _ _ 0 h₁)
    · decide
    · decide
  · intro i
    let j : Fin p.width := ⟨i.val,hw ▸ i.isLt⟩
    have he : E.r (.inl i) = p.r j.val := encoding_r p hv hw ha hi _
    rw [he]
    exact hmain j
  · intro t
    have hr : E.r (.inr t) = p.r (p.width+t.val) := encoding_r p hv hw ha hi _
    have hb : E.b (.inr t) = p.b (p.width+t.val) := rfl
    have ha' : E.a (.inr t) = p.a (p.width+t.val) := rfl
    have hs : E.a (.inr (otherSeed t)) = 3-t.val := by
      rw [E.seed_a]
      fin_cases t <;> decide
    have hm : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
    unfold CompactSupport.B
    rw [hs,hr,ha',hb,hm]
    rw [← Nat.mul_assoc (2*(3-t.val)) (p.r (p.width+t.val))
      ((p.a (p.width+t.val)*p.b (p.width+t.val))^2)]
    exact hseed t


private theorem inputOrder_mul_mass {S : System} [AlphabetFamily S] (E : EncodingParameters S) :
    inputOrder E * MassSize.mass E = E.cyclicOrder := by
  simp only [inputOrder,MassSize.mass,D,EncodingParameters.cyclicOrder,EncodingParameters.blockModulus]
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  exact congrArg (residueModulus^2 * ·) (Finset.prod_congr rfl (fun i _ => by ring))

theorem packedTailCore_facts (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    packedTailCore T ≠ [] ∧ FaceConnected (packedTailCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (packedTailCore T)) ∧
    ((packedTailCore T).length : ℝ) ≤ residueBound T.length := by
  let n := T.length
  let k := residueDigits n
  have hk' : 0 < k := residueDigits_pos n
  have hpos : 0 < n := (by decide : 0 < 3^21).trans hn
  have hcap : n ≤ 4^k := residueDigits_capacity n
  have hrad : (radixLayoutProfile 4 k).radices.prod = 4^k := by
    simp [radixLayoutProfile,List.prod_replicate]
  have hc : n ≤ (radixLayoutProfile 4 k).radices.prod := hcap.trans_eq hrad.symm
  let c := code T (radixLayoutProfile 4 k).radices.prod hpos hc
  letI : AlphabetFamily (system c) := GuardedCompiler.alphabet c
  let S := tailRefinement hk' (by decide : 0 < 4) c
  letI : AlphabetFamily S.system := S.family
  let p := residueProfile k
  let hv := residueProfile_valid k
  let hi := valid_injectivity p hv
  let E : EncodingParameters S.system := encoding p hv rfl (fun _ => rfl) hi
  let ps := GuardedCompiler.refinedPatterns c S
  let rs := residueData k
  let Fs := guardedRawDeck rs (tailSlopes k) (tailTests T k)
  let X := residueTests n
  let P := residuePrimeCap k
  let H := residueRadius k
  have hm : GuardedRowsMatch E rs := residueRowsMatch k hv rfl (fun _ => rfl) hi
  have hs : ∀ i : Column S.system, S.system.slope i = (tailSlopes k).getD i.val 0 :=
    tailSlopes_correct hk' c
  have hFs : guardedDecodedFamily E Fs = partialDeck E ps := by
    apply numericalDeck_correct hm _ _ _ hs
    have he := numericalExpandedTests_correct hk' (by decide : 0 < 4) hpos hc E rs hm
    rw [congrArg (rawGuardedMasks T) hrad] at he
    rw [tailTests,List.flatMap_append,guardedDecodedFamily_append,
      numericalSeedTests_correct hk' (by decide : 0 < 4) c E rs hm, he]
  have hmem {F : CyclicTile} (hF : F∈Fs) :
      F.toFinset.image (decodeNumericalPoint E) ∈ partialDeck E ps := by
    rw [← hFs]
    exact (mem_guardedDecodedFamily _ _).mpr ⟨F,hF,rfl⟩
  have hlo : 0<Fs.length := by simp [Fs,guardedRawDeck]
  have hlen : Fs.length ≤ X := by
    have h := guardedRawDeck_length rs (tailSlopes k) (tailTests T k)
    have htest : (tailTests T k).length ≤ 180+(2313+72*(4^k)^2) := by
      simp only [tailTests,List.length_append,List.length_map]
      exact Nat.add_le_add (tailSeedTests_length k) (rawGuardedMasks_length T (4^k))
    have hc := Nat.pow_le_pow_left (residueDigits_capacity_le ((by decide : 1 < 3^21).trans hn)) 2
    have hw : rs.length ≤ 4*(n+4) := by
      rw [hm.length,show S.system.width = 18+2*k from tailRefinement_width hk' (by decide : 0 < 4) c]
      have := Nat.log_le_self 4 (n-1)
      have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
      unfold k residueDigits
      omega
    have hw₂ := Nat.pow_le_pow_left hw 2
    have hf : rs.length-2 ≤ rs.length := Nat.sub_le _ _
    have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
    unfold X residueTests
    nlinarith only [h,htest,hc,hw,hw₂,hf,hn']
  have hX : 2313 ≤ X := by unfold X residueTests; nlinarith
  have hP : 35 ≤ P := by
    let m := 4*residueUsefulCap k+12*k+134
    have hm : 134 ≤ m := by dsimp [m]; omega
    change 35 ≤ 4*m*(Nat.log 2 m+1)
    exact (show 35 ≤ 4*m by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hprime : PrimeBound E.cyclicOrder P :=
    prime_bound E hP (encoding_prime p hv rfl (fun _ => rfl) hi)
  have hstack : P+3 ≤ (n+4)^2 := residue_stack_budget hn
  have hXbase : (n+4)^2 ≤ X := by unfold X residueTests; omega
  have hXX : X ≤ X^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right X (by omega)
  have hP₁ : P ≤ X^2 := (Nat.le_add_right P 3).trans (hstack.trans (hXbase.trans hXX))
  have hP₂ : P+3 ≤ 2*X^2 := (hstack.trans (hXbase.trans hXX)).trans (by omega)
  have hsupport : PartialStrip.StripBounds E (fun _ => H) :=
    residueSupport k hv rfl (fun _ => rfl) hi
      ((packedRadix_layout _ hk' (by decide : 0 < 4) rfl).slope)
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
    hP₂ hR hRN hlo hlen hnonempty hmass hstrip hker
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
  have hRJ : inputOrder E * MassSize.mass E ≤ 2^1878 * P^(18*k) * (residueUsefulCap k)^(2*k) :=
    (inputOrder_mul_mass E).le.trans ((rowsOrder_eq hm).symm.le.trans (residueData_order_bound k))
  exact hv.trans (residue_volume_bound hn hR hRJ)

end
end TranslationTiling.FiniteCompiler.Packed
