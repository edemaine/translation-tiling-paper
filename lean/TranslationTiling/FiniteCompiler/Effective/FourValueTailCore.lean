import TranslationTiling.Compiler.FourValueBound
import TranslationTiling.FiniteCompiler.Effective.FourValueNumerical
import TranslationTiling.FiniteCompiler.Effective.FourValueMass
import TranslationTiling.FiniteCompiler.Effective.PackedTailCore

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift Rails.Strips
open Effective

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def fourValueTailCore (T : LeanWang.TileSet) : Tile 3 :=
  let k := residueDigits T.length
  let rs := fourValueRows k
  let Fs := fourValueRawDeck T k
  guardedAssembly (((sharedOrder rs,sharedPrimeCap (4*k),residueTests T.length),
    (guardedModuli rs).prod,fourValueRadius k),Fs)

theorem fourValueTailCore_computable : Computable fourValueTailCore := by
  have hk : Primrec (fun T : LeanWang.TileSet => residueDigits T.length) := by
    unfold residueDigits
    have h := (natLog_primrec 4 (by decide)).comp
      (show Primrec (fun T : LeanWang.TileSet => T.length-1) by fun_prop)
    fun_prop
  have hr := fourValueRows_primrec.comp hk
  have hF := fourValueRawDeck_primrec.comp (Primrec.id.pair hk)
  have hN := sharedOrder_primrec.comp hr
  have hP : Primrec (fun k => sharedPrimeCap (4*k)) := by
    unfold sharedPrimeCap sharedPairCap
    fun_prop
  have hX : Primrec (fun T : LeanWang.TileSet => residueTests T.length) := by
    unfold residueTests
    fun_prop
  have hR := product_primrec.comp (guardedModuli_primrec.comp hr)
  have hH : Primrec (fun k => fourValueRadius k) := by
    unfold fourValueRadius sharedPrimeCap sharedPairCap
    simp only [show ∀ k : ℕ, min 1 k = 1 - (1 - k) by intro k; omega]
    fun_prop
  exact guardedAssembly_computable.comp
    (((hN.pair ((hP.comp hk).pair hX)).pair (hR.pair (hH.comp hk))).pair hF).to_comp


private theorem fourValueActivation_length (k : ℕ) :
    (fourValueActivation k).length = (fourValueRows k).length := by
  simp only [fourValueActivation,List.length_append,List.length_map,List.length_range,fourValueRows_length]
  omega

private theorem fourValueCycleDeck_length (k : ℕ) (xs : List GuardedAssignments) :
    (xs.flatMap (fourValueCycle k)).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h : (fourValueCycle k x).length ≤ 1 := by
      unfold fourValueCycle
      split <;> simp
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    omega

theorem fourValueTailCore_test_count (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    (fourValueRawDeck T (residueDigits T.length)).length ≤ residueTests T.length := by
  let n := T.length
  let k := residueDigits n
  let rs := fourValueRows k
  let slopes := tailSlopes k
  have hbase := sharedRawDeck_length rs slopes []
  have hdep : (sharedDependence rs slopes).length + rs.length + 1 ≤
      rs.length^2 + 2*(rs.length-2) + 9 := by
    have hact : (sharedActivationCodes rs slopes).length = rs.length := by
      have hlen : 2 ≤ rs.length := by
        rw [fourValueRows_length]
        omega
      simp only [sharedActivationCodes,List.length_append,List.length_map,List.length_range]
      omega
    simp only [sharedRawDeck,List.length_cons,List.length_append,List.flatMap_nil,List.length_nil,
      hact] at hbase
    omega
  have hcount : (fourValueRawDeck T k).length ≤
      rs.length^2 + 2*(rs.length-2) + 9 + (fourValueTests T k).length := by
    have hc := fourValueCycleDeck_length k (fourValueTests T k)
    simp only [fourValueRawDeck,List.length_cons,List.length_append,fourValueActivation_length]
    change ((sharedDependence rs slopes).length + rs.length + _ + 1) ≤ _
    omega
  have htest : (fourValueTests T k).length ≤ 180+(2313+72*(4^k)^2) := by
    simp only [fourValueTests,List.length_append,List.length_map]
    exact Nat.add_le_add (tailSeedTests_length k) (rawGuardedMasks_length T (4^k))
  have hc := Nat.pow_le_pow_left (residueDigits_capacity_le ((by decide : 1 < 3^21).trans hn)) 2
  have hn' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
  have hw : rs.length ≤ 4*(n+4) := by
    rw [fourValueRows_length]
    have := Nat.log_le_self 4 (n-1)
    unfold k residueDigits
    omega
  have hw₂ := Nat.pow_le_pow_left hw 2
  have hf : rs.length-2 ≤ rs.length := Nat.sub_le _ _
  change _ ≤ residueTests n
  unfold residueTests
  nlinarith only [hcount,htest,hc,hw,hw₂,hf,hn']

/-- Quantitative assembly for the concrete shared deck given the
nonemptiness, strip and mass certificates for its tests. -/
theorem fourValueTailCore_of_deck_geometry (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    let n := T.length
    let k := residueDigits n
    let rs := fourValueRows k
    let N := sharedOrder rs
    let H := fourValueRadius k
    let Fs := fourValueRawDeck T k
    (∀ F ∈ Fs, F ≠ []) →
    (∀ F ∈ Fs, (cyclicTileSet N F).card ≤ sharedMass rs) →
    (∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 (fun _ => H) f.1) →
    fourValueTailCore T ≠ [] ∧ FaceConnected (fourValueTailCore T) ∧
    ((∃ B : Set (Plane × ZMod N),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet N (Fs.getD i.val [])) B) ↔
      TranslationTiling.Tiles (fourValueTailCore T)) ∧
    (((fourValueTailCore T).length : ℕ) : ℝ) ≤ fourValueBound n := by
  dsimp only
  intro hne hmass hstrip
  let n := T.length
  let k := residueDigits n
  let rs := fourValueRows k
  let X := residueTests n
  let P := sharedPrimeCap (4*k)
  let R := (guardedModuli rs).prod
  let N := sharedOrder rs
  let J := sharedMass rs
  let H := fourValueRadius k
  let Fs := fourValueRawDeck T k
  have hN : 0 < N := by
    unfold N rs
    rw [← fourValueLayout_order]
    exact fourValueOrder_pos k
  have hR : 0 < R := by
    unfold R rs
    rw [fourValueInputOrder_eq]
    exact Finset.prod_pos fun i _ => (fourValueLayout k).lowSize_pos i
  have hNJ : R*J = N := shared_input_mul_mass rs
  have hRN : R ≤ N := Nat.le_of_dvd hN ⟨J,hNJ.symm⟩
  have hs : 0 < Fs.length := by simp [Fs,fourValueRawDeck]
  have hP : 3 < P := by
    have h₀ : 4*(2*(4*k)+136) ≤ sharedPairCap (4*k) := by
      unfold sharedPairCap guardedPrimeCap
      exact Nat.le_mul_of_pos_right _ (by omega)
    unfold P sharedPrimeCap
    omega
  have hX : 2313 ≤ X := by unfold X residueTests; nlinarith
  have hx : (n+4)^2 ≤ X := by unfold X residueTests; omega
  have hxx : X ≤ X^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hP₂ : P+3 ≤ (n+4)^2 := four_value_stack_budget hn
  have hP₁ : P ≤ X^2 := (Nat.le_add_right P 3).trans (hP₂.trans (hx.trans hxx))
  have hP₂' : P+3 ≤ 2*X^2 := (hP₂.trans (hx.trans hxx)).trans (by omega)
  have hker (t : ℤ) : (((0 : Plane),((R : ℤ)*t : ℤ)) : Plane × ZMod N) ∈
      cyclicTileSet N (Fs.getD 0 []) := fourValueKernel_column k t
  obtain ⟨hU,hconn,hiff,hsize⟩ := guardedAssembly_facts hN hP hX (fourValueOrder_primeBound k)
    hP₁ hP₂' hR hRN hs (fourValueTailCore_test_count T hn) hne hmass hstrip hker
  refine ⟨hU,hconn,hiff,(show (_ : ℝ) ≤
    (reservedVolumeCap 35 (fun _ => H) R J (reservedCap X P) : ℕ) by exact_mod_cast hsize).trans ?_⟩
  apply four_value_volume_bound hn hR
  rw [hNJ]
  exact fourValueRows_order_bound k


end
end TranslationTiling.FiniteCompiler.Packed
