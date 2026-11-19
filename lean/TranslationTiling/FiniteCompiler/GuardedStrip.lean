import TranslationTiling.FiniteCompiler.StripVolume

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

theorem guardedFamily_strip {H : ℕ} (hH : CompactSupport.Bound E H) :
    ∀ F∈guardedFamily code E, ∀ f∈F, TestSupport H f.1 := by
  have hlo (n : Column (system code)) : 0≤(system code).slope n := by
    change 0≤PairSmall.slope n
    unfold PairSmall.slope
    split <;> positivity
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  rw [numericalPoint_first,ambient_first]
  rcases (partialDeck_cases E _).mp (Finset.mem_toList.mp hG) with hs|⟨p,_,hp⟩
  · exact test_strip E hH hlo (slope_bound code) (structural_subset E hs) ha
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p hp
    obtain rfl := Finset.mem_singleton.mp hh
    have he : a.1=0 := congrArg Prod.fst ((mem_offsetTile E _ _).mp ha)
    simp [he,TestSupport]

theorem exists_strip_tile (H : ℕ) (hsupport : CompactSupport.Bound E H)
    (hp : ∀ i, E.primeAt i≤65536) (hd : 6≤d)
    (hL : 65536+3≤2*(testLimit d)^2) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length≤volumeCap H (inputOrder E) (MassSize.mass E) (stackCap (testLimit d)) := by
  let X := testLimit d
  let Fs := guardedFamily code E
  let N := E.cyclicOrder
  have hN : 0<N := E.cyclicOrder_pos
  have hs : 0<Fs.length := guardedFamily_nonempty code E
  let M := Stacking.tightThreshold X 65536
  obtain ⟨q,hq,hlo,hhi⟩ := Nat.bertrand M (by dsimp [M,Stacking.tightThreshold]; omega)
  have hcop := coprime_of_primeBound hN (prime_bound code E hp) hq
    (by dsimp [M,Stacking.tightThreshold] at hlo; omega)
  have hs' : Fs.length-1+1=Fs.length := by omega
  obtain ⟨P,hP,hfull⟩ := Stacking.partition_tight (Fs.length-1+1) X 65536 q
    (by omega) (by rw [hs']; exact family_length_bound code E hd) hL hq hlo hhi
  obtain ⟨cs,hcs⟩ := partition_certificate (Fs.length-1) 65536 q hq
    (by dsimp [M,Stacking.tightThreshold] at hlo; omega) P hP hfull
  let c : PartitionCertificate := (q,cs)
  let data : CyclicTileData := (N*q,stackCodes (N,c,Fs))
  let R := inputOrder E
  have hpos : 0<data.1 := Nat.mul_pos hN hq.pos
  have hR : 0<R*q := Nat.mul_pos (inputOrder_pos E) hq.pos
  have hdvd : R*q∣data.1 := mul_dvd_mul_right (inputOrder_dvd E) q
  have hne := stackCodes_nonempty N c Fs hs hcs (guardedFamily_tile_nonempty code E)
  have hk : numericalTile E (kernelTile E)∈Fs := by
    apply List.mem_map.mpr
    exact ⟨_,Finset.mem_toList.mpr ((partialDeck_cases E _).mpr (Or.inl (by simp [structuralTiles]))),rfl⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hk
  have hcol : HasColumn data (R*q) := by
    apply stack_hasColumn N 65536 Fs c hcs hcop hN ⟨i,hi⟩ R
    rw [List.getD_eq_getElem _ _ hi,he]
    exact @numerical_kernel compactSeedFrame (system code) (alphabet code) E
  let U := Rails.Strips.assemble (integerTile data) H (R*q)
  have hc := StripLift.connected data H (R*q) hR hpos hdvd hcol
    (stack_strip N c Fs H (guardedFamily_strip code E hsupport))
  have hU := Rails.SlotAssembly.correct _ (Rails.Strips.valid H) (integerTile data)
    (Rails.Strips.railHeight (R*q))
  refine ⟨U,Rails.SlotAssembly.nonempty _ (Rails.Strips.valid H) _ _
    (integerTile_nonempty data hne),hc,?_,?_⟩
  · exact (guardedFamily_solution code E).trans
      ((stackCodes_correct_coprime N 65536 hN Fs hs c hcs hcop).trans
        ((integerTile_correct MSS.rigidity data hpos hne).trans hU.symm))
  · exact volume data hpos H R _ q _ hhi
      (stack_mass N 65536 hN Fs hs c hcs hcop _ (guardedFamily_mass code E))

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
