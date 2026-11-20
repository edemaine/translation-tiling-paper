import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.ReservedStripLift

namespace TranslationTiling.FiniteCompiler
open Compiler
open scoped Classical
variable [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T)
theorem numerical_kernel (k : ℤ) :
    (((0:Plane), ((inputOrder E:ℤ)*k : ℤ)) : Plane × ZMod E.cyclicOrder)∈
      cyclicTileSet E.cyclicOrder (PairSmall.numericalTile E (kernelTile E)) := by
  rw [PairSmall.numericalTile_correct]
  exact kernel_column E k
end TranslationTiling.FiniteCompiler

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open PairSmall Compiler Compiler.Effective Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical
noncomputable section
local instance : SeedFrame := compactSeedFrame
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
attribute [local irreducible] inputOrder EncodingParameters.cyclicOrder

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance : AlphabetFamily (system code) := alphabet code
variable (E : EncodingParameters (system code))

private theorem compact_modulus : residueModulus=35 := by
  norm_num [residueModulus_value,compactSeedFrame]

structure StripBounds (H : ℕ → ℕ) : Prop where
  base : 35≤H 0
  ordinary : ∀ n : Column (system code),
    2*(E.r (.inl n)*E.a (.inl n)*E.b (.inl n))≤H ((system code).slope n).natAbs
  seed : ∀ t : Fin 2, 2*E.a (.inr (otherSeed t))*CompactSupport.B E (.inr t)*residueModulus^3≤H 0

private theorem compact_test_strip {H : ℕ → ℕ} (hH : StripBounds code E H)
    {F : Finset (Ambient E)} (hF : F∈testTiles E) {g : Ambient E} (hg : g∈F) :
    TestSupportAt 35 H g.1 := by
  have hzero : TestSupportAt 35 H 0 := by simp [TestSupportAt]
  have hz (h : q0 E g=0) : g.1=0 := congrArg Prod.fst h
  have ho {t : ℕ} [NeZero t] (c : ZMod t ↪ Channel (system code)) (labels : ∀ j, Label (system code) (c j))
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
      · change (1:ℤ).natAbs≤H 0 ∧ (-(system code).slope n).natAbs≤35
        exact ⟨(by decide : 1≤35).trans hH.base,by rw [Int.natAbs_neg]; exact (slope_bound code n).trans (by decide)⟩
      · cases axis <;> simp [dependenceShift,seedStep,compact_modulus,hH.base]
  · obtain ⟨w,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact hzero
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact hzero
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    refine Or.inr ⟨((system code).slope n).natAbs,(slope_bound code n).trans_lt (by decide),
      (ordinaryFirst_compact_le E rfl n j).trans (hH.ordinary n),?_⟩
    have hlo : 0≤(system code).slope n := by
      change 0≤PairSmall.slope n
      unfold PairSmall.slope
      split <;> positivity
    have he : (((system code).slope n).natAbs:ℤ)=(system code).slope n := by omega
    rw [he]
    rfl
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact Or.inl ⟨(CompactSupport.seed_bound E t j).1.trans (hH.seed t),
      (CompactSupport.seed_bound E t j).2.trans (by rw [compact_modulus])⟩


theorem guardedFamily_strip {H : ℕ → ℕ} (hH : StripBounds code E H) :
    ∀ F∈guardedFamily code E, ∀ f∈F, TestSupportAt 35 H f.1 := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  rw [numericalPoint_first,ambient_first]
  rcases (partialDeck_cases E _).mp (Finset.mem_toList.mp hG) with hs|⟨p,_,hp⟩
  · exact compact_test_strip code E hH (structural_subset E hs) ha
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p hp
    obtain rfl := Finset.mem_singleton.mp hh
    have he : a.1=0 := congrArg Prod.fst ((mem_offsetTile E _ _).mp ha)
    simp [he,TestSupportAt]

theorem exists_strip_tile (H : ℕ → ℕ) (hsupport : StripBounds code E H)
    (hp : ∀ i, E.primeAt i≤65536) (hd : 6≤d)
    (hL : 65536+3≤2*(testLimit d)^2) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length≤reservedVolumeCap 35 H (inputOrder E) (MassSize.mass E) (reservedCap (testLimit d) 65536) := by
  let X := testLimit d
  let Fs := guardedFamily code E
  let N := E.cyclicOrder
  have hN : 0<N := E.cyclicOrder_pos
  have hs : 0<Fs.length := guardedFamily_nonempty code E
  let R := inputOrder E
  have hs' : Fs.length-1+1=Fs.length := by omega
  have hk : numericalTile E (kernelTile E)∈Fs := by
    apply List.mem_map.mpr
    exact ⟨_,Finset.mem_toList.mpr ((partialDeck_cases E _).mpr (Or.inl (by simp [structuralTiles]))),rfl⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hk
  have hX : 2313≤X := by unfold X testLimit; omega
  have hl : 5≤Stacking.differenceLog X := by
    unfold Stacking.differenceLog
    have hh := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : 2*X≠0)).mpr (show 2^4≤2*X by omega)
    omega
  obtain ⟨c,hcs,hhi,hr⟩ := exists_reserved_partition (Fs.length-1) 65536 X i R
    (by rw [hs']; exact family_length_bound code E hd) (by omega) hl hL
  let q := c.1
  have hcop := coprime_of_primeBound hN (prime_bound code E hp) hcs.1 hcs.2.1
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
  have hne := stackCodes_nonempty N c Fs hs hcs (guardedFamily_tile_nonempty code E)
  have hcol : HasForwardColumn data (3*R) := by
    apply stack_hasForwardColumn N 65536 Fs c hcs hcop hN ⟨i,hi⟩ R (inputOrder_pos E) hr
    rw [List.getD_eq_getElem _ _ hi,he]
    exact @numerical_kernel compactSeedFrame (system code) (alphabet code) E
  let slots := Rails.Strips.slotsAt 35 H
  let height := Rails.Strips.railHeight (3*R+1)
  let U := Rails.SlotAssembly.assemble (integerTile data) slots height
  have hc := connected_forward data 35 H (3*R) hpos hnq hcol
    (stack_support N c Fs _ (guardedFamily_strip code E hsupport))
  have hU := Rails.SlotAssembly.correct _ (Rails.Strips.validAt 35 H) (integerTile data) height
  refine ⟨U,Rails.SlotAssembly.nonempty _ (Rails.Strips.validAt 35 H) _ _
    (integerTile_nonempty data hne),hc,?_,?_⟩
  · exact (guardedFamily_solution code E).trans
      ((stackCodes_correct_coprime N 65536 hN Fs hs c hcs hcop).trans
        ((integerTile_correct MSS.rigidity data hpos hne).trans hU.symm))
  · exact reservedVolume data hpos 35 H R _ q _ hhi
      (stack_mass N 65536 hN Fs hs c hcs hcop _ (guardedFamily_mass code E))

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
