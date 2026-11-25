import TranslationTiling.FiniteCompiler.Effective.SlotPolycube
import TranslationTiling.FiniteCompiler.Effective.SlotDeckCount
import TranslationTiling.FiniteCompiler.Effective.SlotRankedLayout
import TranslationTiling.Compiler.SlotRadixBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective
open Compiler.StripLift

noncomputable section
set_option maxRecDepth 8000

def slotPrimeCap (k m : ℕ) :=
  max (fallbackCap m) (max (markerCap k m) (SlotParameters.lowCap k m))

def slotStackPrimeCap (Q : ℕ) := max 4 (max slotBasePrimeCap Q)

/-- A numerical bound for the slot simulation with `k` digits of
length `m` and weight `w`. The exponent `10*k*m` counts the five
prime factors for each slot in the two Wang words. -/
def slotSizeBound (k m w : ℕ) :=
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  10^35 * (order (fourValueLayout 0) * (Q^(10*k*m) * fallbackCap m^(4*m))) *
    X^3 * (slotRadius Q m+1)^2

/-- The same connected polycube construction works at every supported
input length and has the explicit parameterized volume bound. -/
theorem exists_connected_tile_slot_bound (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hk : 0 < k) (hw : 0 < w) (hwm : w ≤ m)
    (hcap : T.length ≤ (slotRadix m w)^k) :
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ slotSizeBound k m w := by
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  let c := Packed.code T _ hn hcap
  obtain ⟨s,_,hA,hB,hR⟩ := exists_ranked_parameters k m
  have hAQ : fallbackCap m ≤ Q := le_max_left ..
  have hBQ : markerCap k m ≤ Q := (le_max_left ..).trans (le_max_right ..)
  have hRQ : SlotParameters.lowCap k m ≤ Q := (le_max_right ..).trans (le_max_right ..)
  have hQ : ∀ i, s.prime i ≤ Q := by
    rintro (⟨i,_ | j⟩ | i)
    · exact (hR i).trans hRQ
    · exact (hB i j).trans hBQ
    · exact (hA i).trans hAQ
  have hQP : Q ≤ P := (le_max_right ..).trans (le_max_right ..)
  have h₀ : slotBasePrimeCap ≤ P := (le_max_left ..).trans (le_max_right ..)
  have hPr := s.primeBound h₀ (fun i => (hQ i).trans hQP)
  have hP : 3 < P := (show 3 < 4 by decide).trans_le (le_max_left ..)
  obtain ⟨U,hU,hcon,he,hvol⟩ := s.slot_polycube c hwm hPr hP hQ
  refine ⟨U,hU,hcon,he,?_⟩
  let N := order s.layout
  let X := stackTestCap P (s.slotDeck c hwm).length
  let X' := stackTestCap P (slotDeckCap k m ((slotRadix m w)^k))
  let H := slotRadius Q m
  have hX : X ≤ X' := by
    unfold X X' stackTestCap
    exact max_le_max_left _ (max_le_max_left _ (s.slotDeck_length c hwm))
  have hXp : 1 ≤ X := le_trans (by decide : 1 ≤ 2313) (le_max_left ..)
  have hPX : P ≤ X := (le_max_left ..).trans (le_max_right ..)
  have hvolume := slotVolume_le H s.period (N/s.period) N (reservedCap X P) s.period_pos
    (Nat.div_mul_le_self _ _)
  have hO := s.order_le hA (fun i => (hR i).trans hRQ) (fun i j => (hB i j).trans hBQ)
  have hx := (slotStack_le X P hXp hPX).trans
    (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hX 3))
  calc
    _ ≤ _ := hvol.trans hvolume
    _ ≤ 10^32 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        (128*X'^3) * (H+1)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hO) hx)
    _ ≤ _ := by
      change _ ≤ 10^35 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        X'^3 * (H+1)^2
      rw [show 10^32 * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
        (128*X'^3) * (H+1)^2 =
        (128*10^32) * (order (fourValueLayout 0) * (Q^(10*k*m)*fallbackCap m^(4*m))) *
          X'^3 * (H+1)^2 by ring]
      gcongr
      decide

/-- Specialize to the constant-weight parameters without an exceptional
small-input construction. -/
theorem exists_connected_tile_slot_adaptive (T : LeanWang.TileSet) (hn : 0 < T.length) :
    let t := slotLengthParameter T.length
    let k := slotPackedDigits T.length t
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ slotSizeBound k (4*t) (3*t) := by
  dsimp only
  have ht : 0 < slotLengthParameter T.length := (by decide : 0 < 1).trans_le (le_max_left ..)
  apply exists_connected_tile_slot_bound T hn
  · exact (by decide : 0 < 1).trans_le (le_max_left ..)
  · omega
  · omega
  · exact slotPackedDigits_capacity _ _ ht

end

end TranslationTiling.Compiler.Size
