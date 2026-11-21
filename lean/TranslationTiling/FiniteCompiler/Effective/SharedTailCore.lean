import TranslationTiling.Compiler.SharedUsefulBound
import TranslationTiling.FiniteCompiler.Effective.GuardedAssembly
import TranslationTiling.FiniteCompiler.Effective.SharedNumericalDeck
import TranslationTiling.FiniteCompiler.Effective.SharedParameterData
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect
import TranslationTiling.FiniteCompiler.Effective.SharedKernelPeriod
import TranslationTiling.FiniteCompiler.Effective.ConcreteSharedCRT

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift Rails.Strips
open Effective

noncomputable section

set_option maxHeartbeats 3000000

def sharedTests (T : LeanWang.TileSet) (k : ℕ) : List GuardedAssignments :=
  tailSeedTests k ++ (rawGuardedMasks T (3^k)).map (expandMask 3 k)

private theorem sharedTests_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ => sharedTests z.1 z.2) := by
  unfold sharedTests
  have hm := rawGuardedMasks_primrec.comp
    (show Primrec (fun z : LeanWang.TileSet × ℕ => (z.1,3^z.2)) by fun_prop)
  exact appendList (tailSeedTests_primrec.comp Primrec.snd)
    (mapList hm (expandMask_primrec.comp
      (show Primrec (fun z : (LeanWang.TileSet × ℕ) × RawMask => (3,z.1.2,z.2)) by fun_prop)))

def sharedTailCore (T : LeanWang.TileSet) : Tile 3 :=
  let k := guardedTrits T.length
  let rs := sharedRows k
  let Fs := sharedRawDeck rs (tailSlopes k) (sharedTests T k)
  guardedAssembly (((sharedOrder rs,sharedPrimeCap k,residueTests T.length),
    (guardedModuli rs).prod,sharedRadius k),Fs)

theorem sharedTailCore_computable : Computable sharedTailCore := by
  have hk : Primrec (fun T : LeanWang.TileSet => guardedTrits T.length) := by fun_prop
  have hr := sharedRows_primrec.comp hk
  have hF := sharedRawDeck_primrec.comp
    (hr.pair ((tailSlopes_primrec.comp hk).pair (sharedTests_primrec.comp (Primrec.id.pair hk))))
  have hN := sharedOrder_primrec.comp hr
  have hP : Primrec (fun k => sharedPrimeCap k) := by
    unfold sharedPrimeCap sharedPairCap
    fun_prop
  have hX : Primrec (fun T : LeanWang.TileSet => residueTests T.length) := by
    unfold residueTests
    fun_prop
  have hR := product_primrec.comp (guardedModuli_primrec.comp hr)
  have hH : Primrec (fun k => sharedRadius k) := by
    unfold sharedRadius sharedPrimeCap sharedPairCap
    fun_prop
  exact guardedAssembly_computable.comp
    (((hN.pair ((hP.comp hk).pair hX)).pair (hR.pair (hH.comp hk))).pair hF).to_comp

theorem sharedTailCore_test_count (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    (sharedRawDeck (sharedRows (guardedTrits T.length)) (tailSlopes (guardedTrits T.length))
      (sharedTests T (guardedTrits T.length))).length ≤ residueTests T.length := by
  let n := T.length
  let k := guardedTrits n
  let rs := sharedRows k
  have h := sharedRawDeck_length rs (tailSlopes k) (sharedTests T k)
  have htest : (sharedTests T k).length ≤ 180+(2313+72*(3^k)^2) := by
    simp only [sharedTests,List.length_append,List.length_map]
    exact Nat.add_le_add (tailSeedTests_length k) (rawGuardedMasks_length T (3^k))
  have hc := Nat.pow_le_pow_left (guardedTrits_capacity_le ((by decide : 1 < 3^21).trans hn)) 2
  have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
  have hw : rs.length ≤ 4*(n+4) := by
    rw [sharedRows_length]
    have := Nat.log_le_self 3 (n-1)
    unfold k guardedTrits
    omega
  have hw₂ := Nat.pow_le_pow_left hw 2
  have hf : rs.length-2 ≤ rs.length := Nat.sub_le _ _
  change _ ≤ residueTests n
  unfold residueTests
  nlinarith only [h,htest,hc,hw,hw₂,hf,hn']

/-- Quantitative assembly for the concrete shared deck given the
nonemptiness, strip and mass certificates for its tests. -/
theorem sharedTailCore_of_deck_geometry (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    let n := T.length
    let k := guardedTrits n
    let rs := sharedRows k
    let N := sharedOrder rs
    let H := sharedRadius k
    let Fs := sharedRawDeck rs (tailSlopes k) (sharedTests T k)
    (∀ F ∈ Fs, F ≠ []) →
    (∀ F ∈ Fs, (cyclicTileSet N F).card ≤ sharedMass rs) →
    (∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 (fun _ => H) f.1) →
    sharedTailCore T ≠ [] ∧ FaceConnected (sharedTailCore T) ∧
    ((∃ B : Set (Plane × ZMod N),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet N (Fs.getD i.val [])) B) ↔
      TranslationTiling.Tiles (sharedTailCore T)) ∧
    (((sharedTailCore T).length : ℕ) : ℝ) ≤ sharedUsefulBound n := by
  dsimp only
  intro hne hmass hstrip
  let n := T.length
  let k := guardedTrits n
  let rs := sharedRows k
  let X := residueTests n
  let P := sharedPrimeCap k
  let R := (guardedModuli rs).prod
  let N := sharedOrder rs
  let J := sharedMass rs
  let H := sharedRadius k
  let Fs := sharedRawDeck rs (tailSlopes k) (sharedTests T k)
  have hN : 0 < N := sharedOrder_pos k
  have hR : 0 < R := sharedInputOrder_pos k
  have hNJ : R*J = N := shared_input_mul_mass rs
  have hRN : R ≤ N := Nat.le_of_dvd hN ⟨J,hNJ.symm⟩
  have hs : 0 < Fs.length := by simp [Fs,sharedRawDeck]
  have hP : 3 < P := by
    have h₀ : 4*(2*k+136) ≤ sharedPairCap k := by
      unfold sharedPairCap guardedPrimeCap
      exact Nat.le_mul_of_pos_right _ (by omega)
    unfold P sharedPrimeCap
    omega
  have hX : 2313 ≤ X := by unfold X residueTests; nlinarith
  have hx : (n+4)^2 ≤ X := by unfold X residueTests; omega
  have hxx : X ≤ X^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hP₂ : P+3 ≤ (n+4)^2 := shared_stack_budget hn
  have hP₁ : P ≤ X^2 := (Nat.le_add_right P 3).trans (hP₂.trans (hx.trans hxx))
  have hP₂' : P+3 ≤ 2*X^2 := (hP₂.trans (hx.trans hxx)).trans (by omega)
  have hker (t : ℤ) : (((0 : Plane),((R : ℤ)*t : ℤ)) : Plane × ZMod N) ∈
      cyclicTileSet N (Fs.getD 0 []) := sharedKernel_column k t
  obtain ⟨hU,hconn,hiff,hsize⟩ := guardedAssembly_facts hN hP hX (sharedOrder_primeBound k)
    hP₁ hP₂' hR hRN hs (sharedTailCore_test_count T hn) hne hmass hstrip hker
  refine ⟨hU,hconn,hiff,(show (_ : ℝ) ≤
    (reservedVolumeCap 35 (fun _ => H) R J (reservedCap X P) : ℕ) by exact_mod_cast hsize).trans ?_⟩
  apply shared_volume_bound hn hR
  rw [hNJ]
  exact sharedRows_order_bound k

end
end TranslationTiling.FiniteCompiler.Packed
