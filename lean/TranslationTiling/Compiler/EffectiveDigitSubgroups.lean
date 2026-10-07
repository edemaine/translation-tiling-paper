import TranslationTiling.Compiler.EffectiveCycleTables
import TranslationTiling.Compiler.EffectiveNumericParameters

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

/-- Digit-factor primes other than the selected label, using numerical label
codes rather than an input-dependent finite-type enumeration. -/
noncomputable def numericalOtherPrimes (T : LeanWang.TileSet) (i : FixedChannel)
    (selected : ℕ) : List ℕ :=
  ((labelCodes T i).filter fun code => decide (code ≠ selected)).map (digitLookup i)

theorem numericalOtherPrimes_computable : Computable (fun z :
    LeanWang.TileSet × FixedChannel × ℕ => numericalOtherPrimes z.1 z.2.1 z.2.2) := by
  have hp : Primrec (fun z : LeanWang.TileSet × FixedChannel × ℕ => (z.1, z.2.1)) := by fun_prop
  have hl := labelCodes_primrec.comp hp
  have hne : PrimrecPred (fun z : (LeanWang.TileSet × FixedChannel × ℕ) × ℕ =>
      z.2 ≠ z.1.2.2) := by fun_prop
  have hf := filterList (p := fun z code => code ≠ z.2.2) hl hne
  have hlookupInput : Primrec (fun z : (LeanWang.TileSet × FixedChannel × ℕ) × ℕ =>
      (z.1.2.1, z.2)) := by fun_prop
  have hlookup := digitLookup_computable.comp hlookupInput.to_comp
  have hm := computableListMap
    (f := fun z : LeanWang.TileSet × FixedChannel × ℕ =>
      (labelCodes z.1 z.2.1).filter fun code => decide (code ≠ z.2.2))
    (g := fun z code => digitLookup z.2.1 code) hf.to_comp hlookup
  exact hm

theorem numericalOtherPrimes_test (T : LeanWang.TileSet) (i : FixedChannel)
    (j : Label T i) (n : ℕ) :
    KernelTest (numericalOtherPrimes T i (labelCode i j)) n ↔
      (n : K (parameters T) i) ∈ digitSubgroup (parameters T) i j := by
  rw [← kernelTest_digitSubgroup]
  constructor
  · intro h r hr
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hr
    have hkj := (Finset.mem_filter.mp (Finset.mem_toList.mp hk)).2
    have hcode : labelCode i k ≠ labelCode i j := fun he => hkj (labelCode_injective i he)
    apply h r
    apply List.mem_map.mpr
    refine ⟨labelCode i k, List.mem_filter.mpr ⟨?_, decide_eq_true hcode⟩, he⟩
    exact (mem_labelCodes T i _).mpr ⟨k, rfl⟩
  · intro h r hr
    obtain ⟨code, hc, he⟩ := List.mem_map.mp hr
    obtain ⟨hcodes, hneq⟩ := List.mem_filter.mp hc
    obtain ⟨k, hk⟩ := (mem_labelCodes T i code).mp hcodes
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact (of_decide_eq_true hneq) hk.symm
    apply h r
    apply List.mem_map.mpr
    refine ⟨k, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩), ?_⟩
    change digitLookup i (labelCode i k) = r
    rw [hk]
    exact he

end TranslationTiling.Compiler.Effective
