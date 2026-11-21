import TranslationTiling.FiniteCompiler.PackedLayout
import TranslationTiling.FiniteCompiler.PackedEncoding
import TranslationTiling.FiniteCompiler.PartialStrip
import TranslationTiling.Compiler.FiniteNormalizedInput

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section

local instance : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 10000

structure CheckedProfile where
  profile : Profile
  exponent : ℕ
  valid : Valid profile
  layout : Layout profile
  injective : profile.injectivityCheck
  cap : profile.cap ≤ 2^exponent
  base : 35 ≤ profile.radius 0
  slope : ∀ i : Fin profile.width, profile.slope i.val ≤ 16
  ordinary : ∀ i : Fin profile.width,
    2*(profile.r i.val*profile.a i.val*profile.b i.val) ≤ profile.radius (profile.slope i.val)
  seed : ∀ t : Fin 2,
    2*(3-t.val)*profile.r (profile.width+t.val)*
      (profile.a (profile.width+t.val)*profile.b (profile.width+t.val))^2*35^3 ≤ profile.radius 0

def checked12 : CheckedProfile :=
  ⟨profile12,2392,profile12_valid,
    ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    profile12_injective,profile12_cap,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

def checked36 : CheckedProfile :=
  ⟨profile36,2573,profile36_valid,
    ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    profile36_injective,profile36_cap,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

def checked243 : CheckedProfile :=
  ⟨profile243,2876,profile243_valid,
    ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    profile243_injective,profile243_cap,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

private theorem patterns_length_bound {T : LeanWang.TileSet} {d : ℕ} (C : Code T d) :
    (GuardedCompiler.patterns C).length ≤ 2313+72*d^2 := by
  unfold GuardedCompiler.patterns
  simp only [List.length_append,List.length_map,Finset.length_toList]
  have h5 : Sudoku.PartialWord.codes5.length = 460 := by decide +kernel
  have h7 : Sudoku.PartialWord.codes7.length = 1853 := by decide +kernel
  have h := Finset.card_filter_le (Finset.univ : Finset (GuardedCompiler.QueryIndex d))
    (GuardedCompiler.badQuery C)
  have hc : (Finset.univ : Finset (GuardedCompiler.QueryIndex d)).card = 72*d^2 := by
    have h5 : Fintype.card ((ZMod 5)ˣ) = 4 := by decide
    have h7 : Fintype.card ((ZMod 7)ˣ) = 6 := by decide
    simp only [Finset.card_univ,GuardedCompiler.QueryIndex,Fintype.card_prod,Fintype.card_fin,h5,h7]
    ring
  omega

private theorem sum_arity (p : Profile) :
    (∑ i : Fin p.width, p.arity i.val) = ((List.range p.width).map p.arity).sum := by
  rw [← Fin.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private def code (T : LeanWang.TileSet) (d : ℕ) (hpos : 0 < T.length) (hcap : T.length ≤ d) :
    Code T d := by
  letI : Nonempty (LeanWang.TileIn T) := ⟨⟨T[0],List.getElem_mem hpos⟩⟩
  let f : LeanWang.TileIn T → Fin d :=
    fun t => ⟨T.idxOf t.val,(List.idxOf_lt_length_of_mem t.property).trans_le hcap⟩
  have hi : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    exact (List.idxOf_inj t.property).mp (congrArg Fin.val h)
  exact ⟨f,Function.invFun f,Function.leftInverse_invFun hi⟩

private theorem prime_bound {S : System} [AlphabetFamily S] (E : EncodingParameters S) (hp : ∀ i, E.primeAt i≤65536) : PrimeBound E.cyclicOrder 65536 := by
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
      have hi (i : Channel S) : Nat.Coprime q (E.blockModulus i) := by
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

theorem tile_exists (Q : CheckedProfile) (T : LeanWang.TileSet) (hn : 0 < T.length)
    (hcap : T.length ≤ Q.profile.radices.prod) :
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧ U.length ≤ 2^Q.exponent := by
  let p := Q.profile
  let C := code T p.radices.prod hn hcap
  letI : AlphabetFamily (system C) := GuardedCompiler.alphabet C
  let S := refinement p Q.layout C
  letI : AlphabetFamily S.system := S.family
  let E : EncodingParameters S.system := encoding p Q.valid rfl (fun _ => rfl) Q.injective
  have ha (i : Channel S.system) :
      E.a i = p.a (channelEquiv p rfl i).val := rfl
  have hb (i : Channel S.system) :
      E.b i = p.b (channelEquiv p rfl i).val := rfl
  have hr (i : Channel S.system) :
      E.r i = p.r (channelEquiv p rfl i).val :=
    encoding_r p Q.valid rfl (fun _ => rfl) Q.injective i
  have hslope (i : Column S.system) : S.system.slope i = (p.slope i.val : ℤ) := Q.layout.slope i
  have hsupport : PartialStrip.StripBounds E p.radius := by
    refine ⟨Q.base, ?_, ?_, ?_⟩
    · intro i
      rw [hslope]
      exact ⟨by positivity,by simpa using Q.slope i⟩
    · intro i
      rw [ha,hb,hr,hslope,Int.natAbs_natCast]
      exact Q.ordinary i
    · intro t
      have ht : (otherSeed t).val+2 = 3-t.val := by dsimp [otherSeed]; have := t.isLt; omega
      have hm : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
      rw [E.seed_a, ht, hm]
      unfold CompactSupport.B
      rw [ha,hb,hr]
      simpa only [channel_inr p (T:=S.system) rfl t, Nat.mul_assoc] using Q.seed t
  have hp : PrimeBound E.cyclicOrder 65536 :=
    prime_bound E (encoding_prime p Q.valid rfl (fun _ => rfl) Q.injective)
  have hsize : (PartialStrip.family (GuardedCompiler.refinedPatterns C S) E).length ≤ p.testLimit := by
    have h := PartialStrip.family_length_bound (GuardedCompiler.refinedPatterns C S) E
    have hp := patterns_length_bound C
    simp only [GuardedCompiler.refinedPatterns,List.length_map] at h
    change _ ≤ _ + (p.width+2)^2 + 2*p.width + 7 + 2*(∑ i : Fin p.width, p.arity i.val) at h
    rw [sum_arity] at h
    change (PartialStrip.family ((GuardedCompiler.patterns C).map S.expand) E).length ≤ p.testLimit
    unfold Profile.testLimit
    omega
  have hX : 2313 ≤ p.testLimit := by unfold Profile.testLimit; omega
  have hL : 65536+3 ≤ 2*p.testLimit^2 := by nlinarith
  obtain ⟨U,hne,hc,hiff,hvol⟩ := PartialStrip.exists_strip_tile _ E _ hsupport _ hp hX hsize hL
  rw [encoding_inputOrder p Q.valid rfl (fun _ => rfl) Q.injective,
      encoding_mass p Q.valid rfl (fun _ => rfl) Q.injective] at hvol
  exact ⟨U,hne,hc,(GuardedCompiler.refined_deck_equiv C S E).trans hiff,hvol.trans Q.cap⟩

end
end TranslationTiling.FiniteCompiler.Packed
