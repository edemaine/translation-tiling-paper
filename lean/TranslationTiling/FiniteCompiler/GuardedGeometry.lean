import TranslationTiling.FiniteCompiler.GuardedSystem
import TranslationTiling.FiniteCompiler.GuardedVolume
import TranslationTiling.FiniteCompiler.PairSmallGeometry

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open PairSmall
open Compiler (CyclicTile cyclicTileSet cyclicPoint)
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
local instance : SeedFrame := compactSeedFrame
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance projectedGeometryFamily : AlphabetFamily (system code) := alphabet code
variable (E : EncodingParameters (system code))

private theorem deck_tile_nonempty {F : Finset (Ambient E)}
    (hF : F∈partialDeck E (patterns code)) : F.Nonempty := by
  rcases (partialDeck_cases E _).mp hF with h|⟨p,_,h⟩
  · exact nonempty_of_mem_testTiles E (structural_subset E h)
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p h
    exact nonempty_of_mem_fixedCycleTiles E cy lab hh

private theorem deck_mass {F : Finset (Ambient E)}
    (hF : F∈partialDeck E (patterns code)) : F.card≤MassSize.mass E := by
  rcases (partialDeck_cases E _).mp hF with h|⟨p,_,h⟩
  · exact MassSize.test_card E F (structural_subset E h)
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p h
    obtain rfl := Finset.mem_singleton.mp hh
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

private theorem deck_horizontal {H : ℕ} (hb : CompactSupport.Bound E H)
    (hS : ∀ n, ((system code).slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F∈partialDeck E (patterns code))
    {g : Ambient E} (hg : g∈F) : g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H := by
  rcases (partialDeck_cases E _).mp hF with h|⟨p,_,h⟩
  · exact CompactSupport.test_horizontal E hb hS (structural_subset E h) hg
  · obtain ⟨k,hk,cy,lab,hh⟩ := partialTiles_member E p h
    obtain rfl := Finset.mem_singleton.mp hh
    have he : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [he]

def guardedFamily : List CyclicTile := ((partialDeck E (patterns code)).toList).map (numericalTile E)

theorem guardedFamily_length : (guardedFamily code E).length=(partialDeck E (patterns code)).card := by
  simp [guardedFamily]

theorem guardedFamily_nonempty : 0<(guardedFamily code E).length := by
  rw [guardedFamily_length code E,Finset.card_pos]
  exact ⟨kernelTile E,(partialDeck_cases E _).mpr (Or.inl (by simp [structuralTiles]))⟩

theorem guardedFamily_tile_nonempty : ∀ F∈guardedFamily code E, F≠[] := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  have hne := deck_tile_nonempty code E (Finset.mem_toList.mp hG)
  intro he
  have hh := numericalTile_correct E G
  rw [he] at hh
  have hn := hne.image (FiniteCompiler.ambientCyclicEquiv E)
  have hh' : (∅ : Finset (Plane × ZMod E.cyclicOrder))=G.image (FiniteCompiler.ambientCyclicEquiv E) := by
    simpa only [cyclicTileSet,List.toFinset_nil,Finset.image_empty] using hh
  have hfalse : (∅ : Finset (Plane × ZMod E.cyclicOrder)).Nonempty := by rw [hh']; exact hn
  exact Finset.not_nonempty_empty hfalse

theorem guardedFamily_mass : ∀ F∈guardedFamily code E,
    (cyclicTileSet E.cyclicOrder F).card≤MassSize.mass E := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  rw [numericalTile_correct E,Finset.card_image_of_injective _ (FiniteCompiler.ambientCyclicEquiv E).injective]
  exact deck_mass code E (Finset.mem_toList.mp hG)

theorem guardedFamily_horizontal {H : ℕ} (hH : CompactSupport.Bound E H) :
    ∀ F∈guardedFamily code E, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  change (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.1.natAbs≤H ∧
    (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.2.natAbs≤H
  rw [numericalPoint_first,ambient_first]
  exact deck_horizontal code E hH (slope_bound code) (Finset.mem_toList.mp hG) ha

theorem guardedFamily_solution :
    LeanWang.TilesPlane T ↔ ∃ B : Set (Plane × ZMod E.cyclicOrder),
      ∀ i : Fin (guardedFamily code E).length,
        Tiles (cyclicTileSet E.cyclicOrder ((guardedFamily code E).getD i.val [])) B := by
  rw [deck_equiv code E]
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨FiniteCompiler.ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm := getD_mem_of_lt (guardedFamily code E) i.val [] i.isLt
    obtain ⟨G,hG,he⟩ := List.mem_map.mp hm
    rw [←he,numericalTile_correct E]
    exact ambient_covers E _ A (hA _ (Finset.mem_toList.mp hG))
  · rintro ⟨B,hB⟩
    refine ⟨(FiniteCompiler.ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    have hm : numericalTile E F∈guardedFamily code E :=
      List.mem_map.mpr ⟨F,Finset.mem_toList.mpr hF,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi,he,numericalTile_correct E] at h
    exact ambient_uncovers E _ B h

theorem family_length_bound (hd : 6≤d) : (guardedFamily code E).length≤testLimit d := by
  have hdep := FixedSize.dependence_card E
  change (dependenceTiles E).card≤(20+2)^2+20+4 at hdep
  have hseed : (seedConstraintTiles E).card≤80*d := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    have hc : Fintype.card (Σ n : Column (system code), Letter (system code) n)≤20*d := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _n : Column (system code), d := Finset.sum_le_sum (fun n _ => by
          change Fintype.card (Fin (arity d n))≤d
          rw [Fintype.card_fin]
          unfold arity
          split <;> first | omega | split <;> omega)
        _ = 20*d := by simp [Column,system]
    omega
  have ha : (Finset.univ.image (ordinaryActivationTile E)).card≤20 :=
    Finset.card_image_le.trans_eq (by simp [Column,system])
  have hb : (Finset.univ.image (seedActivationTile E)).card≤2 :=
    Finset.card_image_le.trans_eq (by simp)
  have hstr : (structuralTiles E).card≤549+80*d := by
    unfold structuralTiles
    have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
    have h1 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E) (seedConstraintTiles E)
    have h2 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪seedConstraintTiles E)
      (Finset.univ.image (ordinaryActivationTile E))
    have h3 := Finset.card_union_le
      ({kernelTile E}∪dependenceTiles E∪seedConstraintTiles E∪Finset.univ.image (ordinaryActivationTile E))
      (Finset.univ.image (seedActivationTile E))
    simp only [Finset.card_singleton] at h0
    omega
  have hall (p : List (PartialTest (system code))) :
      (p.flatMap (fun t => (partialTiles E t).toList)).length≤p.length := by
    induction p with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons,List.length_append,Finset.length_toList,List.length_cons]
      have hsize := partialTiles_card E p
      omega
  have hpat : (patterns code).length≤2313+72*d^2 := by
    unfold patterns
    simp only [List.length_append,List.length_map,Finset.length_toList]
    have h5 : Sudoku.PartialWord.codes5.length=460 := by decide +kernel
    have h7 : Sudoku.PartialWord.codes7.length=1853 := by decide +kernel
    have hn := (Finset.card_filter_le (Finset.univ : Finset (QueryIndex d)) (badQuery code))
    have hcard : (Finset.univ : Finset (QueryIndex d)).card=72*d^2 := by
      have h5 : Fintype.card ((ZMod 5)ˣ)=4 := by decide
      have h7 : Fintype.card ((ZMod 7)ˣ)=6 := by decide
      simp only [Finset.card_univ,QueryIndex,Fintype.card_prod,Fintype.card_fin,h5,h7]
      ring
    omega
  rw [guardedFamily_length]
  unfold partialDeck testLimit
  have ht := Finset.card_union_le (structuralTiles E)
    (((patterns code).flatMap fun p => (partialTiles E p).toList).toFinset)
  have hc := List.toFinset_card_le ((patterns code).flatMap fun p => (partialTiles E p).toList)
  have hl := hall (patterns code)
  omega

theorem prime_bound (hp : ∀ i, E.primeAt i≤65536) : PrimeBound E.cyclicOrder 65536 := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q∣E.cyclicOrder
    · right
      by_contra hl
      have hlarge : 65536<q := by omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤65536) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (NeZero.pos _)
        (by rw [residueModulus_value]; split <;> decide)
      have hi (i : Channel (system code)) : Nat.Coprime q (E.blockModulus i) := by
        have hr : Nat.Coprime q (E.r i) := by
          rw [E.r_eq_prod]
          apply Nat.coprime_fintype_prod_right_iff.mpr
          intro j
          exact hcop _ (E.prime_isPrime _).pos (hp _)
        exact ((hr.pow_right 2).mul_right (hcop _ (E.prime_isPrime _).pos (hp _))).mul_right
          (hcop _ (E.prime_isPrime _).pos (hp _))
      have ht : Nat.Coprime q E.cyclicOrder :=
        (hR.pow_right 2).mul_right (Nat.coprime_fintype_prod_right_iff.mpr hi)
      exact (hprime.coprime_iff_not_dvd.mp ht) hd
    · exact Or.inl hd
  · exact Or.inl hprime

theorem exists_guarded_tile (H : ℕ) (hsupport : CompactSupport.Bound E H)
    (hp : ∀ i, E.primeAt i≤65536) (hd : 6≤d)
    (hL : 65536+3≤2*(testLimit d)^2) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length≤cubeCap H E.cyclicOrder (MassSize.mass E) (stackCap (testLimit d)) := by
  obtain ⟨U,hne,hc,ht,hm⟩ := exists_connected_from_family E.cyclicOrder H (MassSize.mass E)
    (testLimit d) (guardedFamily code E) E.cyclicOrder_pos (prime_bound code E hp)
    (guardedFamily_nonempty code E) (family_length_bound code E hd) hL
    (guardedFamily_tile_nonempty code E) (guardedFamily_mass code E) (guardedFamily_horizontal code E hsupport)
  exact ⟨U,hne,hc,(guardedFamily_solution code E).trans ht,hm⟩

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
