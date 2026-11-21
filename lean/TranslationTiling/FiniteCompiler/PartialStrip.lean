import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.PartialTests
import TranslationTiling.FiniteCompiler.CompactShift
import TranslationTiling.FiniteCompiler.PairSmallGeometry
import TranslationTiling.FiniteCompiler.ReservedStripLift

namespace TranslationTiling.FiniteCompiler
open Compiler
open scoped Classical
variable [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T)
private theorem numerical_kernel_core (k : ℤ) :
    (((0:Plane), ((inputOrder E:ℤ)*k : ℤ)) : Plane × ZMod E.cyclicOrder)∈
      cyclicTileSet E.cyclicOrder (PairSmall.numericalTile E (kernelTile E)) := by
  rw [PairSmall.numericalTile_correct]
  exact kernel_column E k
end TranslationTiling.FiniteCompiler


namespace TranslationTiling.FiniteCompiler.PartialStrip

open PairSmall Compiler Compiler.Effective Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical
noncomputable section

local instance : SeedFrame := compactSeedFrame
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] inputOrder EncodingParameters.cyclicOrder

variable {T : System} [AlphabetFamily T] (ps : List (PartialTest T)) (E : EncodingParameters T)

private theorem deck_tile_nonempty {F : Finset (Ambient E)}
    (hF : F∈partialDeck E ps) : F.Nonempty := by
  rcases (partialDeck_cases E _).mp hF with h|⟨p,_,h⟩
  · exact nonempty_of_mem_testTiles E (structural_subset E h)
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p h
    exact nonempty_of_mem_fixedCycleTiles E cy lab hh

private theorem deck_mass {F : Finset (Ambient E)}
    (hF : F∈partialDeck E ps) : F.card≤MassSize.mass E := by
  rcases (partialDeck_cases E _).mp hF with h|⟨p,_,h⟩
  · exact MassSize.test_card E F (structural_subset E h)
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p h
    obtain rfl := Finset.mem_singleton.mp hh
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

def family : List CyclicTile := ((partialDeck E ps).toList).map (numericalTile E)

theorem family_length : (family ps E).length=(partialDeck E ps).card := by
  simp [family]

theorem family_nonempty : 0<(family ps E).length := by
  rw [family_length ps E,Finset.card_pos]
  exact ⟨kernelTile E,(partialDeck_cases E _).mpr (Or.inl (by simp [structuralTiles]))⟩

theorem family_tile_nonempty : ∀ F∈family ps E, F≠[] := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  have hne := deck_tile_nonempty ps E (Finset.mem_toList.mp hG)
  intro he
  have hh := numericalTile_correct E G
  rw [he] at hh
  have hn := hne.image (FiniteCompiler.ambientCyclicEquiv E)
  have hh' : (∅ : Finset (Plane × ZMod E.cyclicOrder))=G.image (FiniteCompiler.ambientCyclicEquiv E) := by
    simpa only [cyclicTileSet,List.toFinset_nil,Finset.image_empty] using hh
  have hfalse : (∅ : Finset (Plane × ZMod E.cyclicOrder)).Nonempty := by rw [hh']; exact hn
  exact Finset.not_nonempty_empty hfalse

theorem family_mass : ∀ F∈family ps E,
    (cyclicTileSet E.cyclicOrder F).card≤MassSize.mass E := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  rw [numericalTile_correct E,Finset.card_image_of_injective _ (FiniteCompiler.ambientCyclicEquiv E).injective]
  exact deck_mass ps E (Finset.mem_toList.mp hG)

theorem family_solution :
    (∃ A : Set (Ambient E), ∀ F ∈ partialDeck E ps, Tiles F A) ↔ ∃ B : Set (Plane × ZMod E.cyclicOrder),
      ∀ i : Fin (family ps E).length,
        Tiles (cyclicTileSet E.cyclicOrder ((family ps E).getD i.val [])) B := by
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨FiniteCompiler.ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm := getD_mem_of_lt (family ps E) i.val [] i.isLt
    obtain ⟨G,hG,he⟩ := List.mem_map.mp hm
    rw [←he,numericalTile_correct E]
    exact ambient_covers E _ A (hA _ (Finset.mem_toList.mp hG))
  · rintro ⟨B,hB⟩
    refine ⟨(FiniteCompiler.ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    have hm : numericalTile E F∈family ps E :=
      List.mem_map.mpr ⟨F,Finset.mem_toList.mpr hF,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi,he,numericalTile_correct E] at h
    exact ambient_uncovers E _ B h

theorem family_length_bound :
    (family ps E).length ≤ ps.length+(T.width+2)^2+2*T.width+7+
      2*(∑ n : Column T, AlphabetFamily.size (T:=T) n) := by
  have hdep := FixedSize.dependence_card E
  have hseed : (seedConstraintTiles E).card ≤
      2*(∑ n : Column T, AlphabetFamily.size (T:=T) n) := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles, Finset.card_singleton, Finset.sum_const, smul_eq_mul, mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
    rfl
  have hordinary : (Finset.univ.image (ordinaryActivationTile E)).card ≤ T.width :=
    Finset.card_image_le.trans_eq (by simp [Column])
  have hactivation : (Finset.univ.image (seedActivationTile E)).card ≤ 2 :=
    Finset.card_image_le.trans_eq (by simp)
  have hstr : (structuralTiles E).card ≤ (T.width+2)^2+2*T.width+7+
      2*(∑ n : Column T, AlphabetFamily.size (T:=T) n) := by
    unfold structuralTiles
    have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
    have h1 := Finset.card_union_le ({kernelTile E} ∪ dependenceTiles E) (seedConstraintTiles E)
    have h2 := Finset.card_union_le ({kernelTile E} ∪ dependenceTiles E ∪ seedConstraintTiles E)
      (Finset.univ.image (ordinaryActivationTile E))
    have h3 := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ seedConstraintTiles E ∪
        Finset.univ.image (ordinaryActivationTile E)) (Finset.univ.image (seedActivationTile E))
    simp only [Finset.card_singleton] at h0
    omega
  have hp (q : List (PartialTest T)) :
      (q.flatMap (fun p => (partialTiles E p).toList)).length ≤ q.length := by
    induction q with
    | nil => simp
    | cons p rest ih =>
      simp only [List.flatMap_cons,List.length_append,Finset.length_toList,List.length_cons]
      have h := partialTiles_card E p
      omega
  rw [family_length]
  unfold partialDeck
  have ha := Finset.card_union_le (structuralTiles E)
    ((ps.flatMap (fun p => (partialTiles E p).toList)).toFinset)
  have hb := List.toFinset_card_le (ps.flatMap (fun p => (partialTiles E p).toList))
  have hc := hp ps
  omega

private theorem compact_modulus : residueModulus=35 := by
  norm_num [residueModulus_value,compactSeedFrame]

structure StripBounds (H : ℕ → ℕ) : Prop where
  base : 35≤H 0
  slopes : ∀ n : Column T, 0 ≤ T.slope n ∧ (T.slope n).natAbs ≤ 16
  ordinary : ∀ n : Column T,
    2*(E.r (.inl n)*E.a (.inl n)*E.b (.inl n))≤H (T.slope n).natAbs
  seed : ∀ t : Fin 2, 2*E.a (.inr (otherSeed t))*CompactSupport.B E (.inr t)*residueModulus^3≤H 0

private theorem compact_test_strip {H : ℕ → ℕ} (hH : StripBounds E H)
    {F : Finset (Ambient E)} (hF : F∈testTiles E) {g : Ambient E} (hg : g∈F) :
    TestSupportAt 35 H g.1 := by
  have hzero : TestSupportAt 35 H 0 := by simp [TestSupportAt]
  have hz (h : q0 E g=0) : g.1=0 := congrArg Prod.fst h
  have ho {t : ℕ} [NeZero t] (c : ZMod t ↪ Channel T) (labels : ∀ j, Label T (c j))
      (hF : F∈fixedCycleTiles E c labels) : g.1=0 := by
    obtain rfl := Finset.mem_singleton.mp hF
    exact congrArg Prod.fst ((mem_offsetTile E _ _).mp hg)
  rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n,rfl⟩ | ⟨t,rfl⟩
  · rw [hz ((mem_kernelTile E g).mp hg)]; exact hzero
  · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hF
    rcases (mem_invarianceTile E _ _ g).mp hg with ⟨h,_⟩ | ⟨h,_⟩
    · rw [hz h]; exact hzero
    · have hh := congrArg Prod.fst h
      change g.1=(dependenceShift E d).1 at hh
      rw [hh]
      apply Or.inl
      rcases d with d | (n | ⟨t,axis⟩)
      · simp [dependenceShift,lowGenerator]
      · change (1:ℤ).natAbs≤H 0 ∧ (-T.slope n).natAbs≤35
        exact ⟨(by decide : 1≤35).trans hH.base,by rw [Int.natAbs_neg]; exact (hH.slopes n).2.trans (by decide)⟩
      · cases axis <;> simp [dependenceShift,seedStep,compact_modulus,hH.base]
  · obtain ⟨w,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact hzero
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact hzero
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    refine Or.inr ⟨(T.slope n).natAbs,(hH.slopes n).2.trans_lt (by decide),
      (ordinaryFirst_compact_le E rfl n j).trans (hH.ordinary n),?_⟩
    have hlo := (hH.slopes n).1
    have he : ((T.slope n).natAbs:ℤ)=T.slope n := by omega
    rw [he]
    rfl
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact Or.inl ⟨(CompactSupport.seed_bound E t j).1.trans (hH.seed t),
      (CompactSupport.seed_bound E t j).2.trans (by rw [compact_modulus])⟩


theorem family_strip {H : ℕ → ℕ} (hH : StripBounds E H) :
    ∀ F∈family ps E, ∀ f∈F, TestSupportAt 35 H f.1 := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  rw [numericalPoint_first,ambient_first]
  rcases (partialDeck_cases E _).mp (Finset.mem_toList.mp hG) with hs|⟨p,_,hp⟩
  · exact compact_test_strip E hH (structural_subset E hs) ha
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p hp
    obtain rfl := Finset.mem_singleton.mp hh
    have he : a.1=0 := congrArg Prod.fst ((mem_offsetTile E _ _).mp ha)
    simp [he,TestSupportAt]


theorem exists_strip_tile (H : ℕ → ℕ) (hsupport : StripBounds E H) (X : ℕ)
    (hp : PrimeBound E.cyclicOrder 65536) (hX : 2313 ≤ X)
    (hsize : (family ps E).length ≤ X) (hL : 65536+3 ≤ 2*X^2) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      ((∃ A : Set (Ambient E), ∀ F ∈ partialDeck E ps, Tiles F A) ↔ TranslationTiling.Tiles U) ∧
      U.length≤reservedVolumeCap 35 H (inputOrder E) (MassSize.mass E) (reservedCap X 65536) := by
  let Fs := family ps E
  let N := E.cyclicOrder
  have hN : 0<N := E.cyclicOrder_pos
  have hs : 0<Fs.length := family_nonempty ps E
  let R := inputOrder E
  have hs' : Fs.length-1+1=Fs.length := by omega
  have hk : numericalTile E (kernelTile E)∈Fs := by
    apply List.mem_map.mpr
    exact ⟨_,Finset.mem_toList.mpr ((partialDeck_cases E _).mpr (Or.inl (by simp [structuralTiles]))),rfl⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hk
  have hl : 5≤Stacking.differenceLog X := by
    unfold Stacking.differenceLog
    have hh := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : 2*X≠0)).mpr (show 2^4≤2*X by omega)
    omega
  obtain ⟨c,hcs,hhi,hr⟩ := exists_reserved_partition (Fs.length-1) 65536 X i R
    (by rw [hs']; exact hsize) (by omega) hl hL
  let q := c.1
  have hcop := coprime_of_primeBound hN hp hcs.1 hcs.2.1
  let data : CyclicTileData := (N*q,stackCodes (N,c,Fs))
  have hpos : 0<data.1 := Nat.mul_pos hN hcs.1.pos
  have hnq : 3*R<2*data.1 := by
    have hR : R≤N := Nat.le_of_dvd hN (inputOrder_dvd E)
    have hRpos : 0<R := inputOrder_pos E
    have hq : 65536<q := hcs.2.1
    have h1 := Nat.mul_le_mul_right q hR
    have h2 : 3*R<R*q := by
      simpa only [Nat.mul_comm q R] using
        Nat.mul_lt_mul_of_pos_right (show 3<q by omega) hRpos
    change _<2*(N*q)
    omega
  have hne := stackCodes_nonempty N c Fs hs hcs (family_tile_nonempty ps E)
  have hcol : HasForwardColumn data (3*R) := by
    apply stack_hasForwardColumn N 65536 Fs c hcs hcop hN ⟨i,hi⟩ R (inputOrder_pos E) hr
    rw [List.getD_eq_getElem _ _ hi,he]
    exact numerical_kernel_core E
  let slots := Rails.Strips.slotsAt 35 H
  let height := Rails.Strips.railHeight (3*R+1)
  let U := Rails.SlotAssembly.assemble (integerTile data) slots height
  have hc := connected_forward data 35 H (3*R) hpos hnq hcol
    (stack_support N c Fs _ (family_strip ps E hsupport))
  have hU := Rails.SlotAssembly.correct _ (Rails.Strips.validAt 35 H) (integerTile data) height
  refine ⟨U,Rails.SlotAssembly.nonempty _ (Rails.Strips.validAt 35 H) _ _
    (integerTile_nonempty data hne),hc,?_,?_⟩
  · exact (family_solution ps E).trans
      ((stackCodes_correct_coprime N 65536 hN Fs hs c hcs hcop).trans
        ((integerTile_correct MSS.rigidity data hpos hne).trans hU.symm))
  · exact reservedVolume data hpos 35 H R _ q _ hhi
      (stack_mass N 65536 hN Fs hs c hcs hcop _ (family_mass ps E))


end
end TranslationTiling.FiniteCompiler.PartialStrip
