import TranslationTiling.FiniteCompiler.Effective.SlotKernelGeometry
import TranslationTiling.FiniteCompiler.Effective.SlotStrip

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift Compiler.Size
open scoped Classical
noncomputable section

set_option maxRecDepth 5000
variable {k m : ℕ} (s : SlotParameters k m)
local instance : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

def stackTestCap (P count : ℕ) := max 2313 (max P count)

def slotRadius (Q m : ℕ) := max (fourValueRadius 0) (Q^(11*m))

/-- Only selected slots contribute to an activation displacement. -/
def slotAssemblyRadius (k m w : ℕ) :=
  max (fourValueRadius 0) ((lowCap k m^2 * markerCap k m^8 * fallbackCap m)^(min m (m+1-w)))

theorem slotAssemblyRadius_le (k m w Q : ℕ) (hA : fallbackCap m ≤ Q)
    (hB : markerCap k m ≤ Q) (hC : lowCap k m ≤ Q) :
    slotAssemblyRadius k m w ≤ slotRadius Q m := by
  unfold slotAssemblyRadius slotRadius
  apply max_le_max_left
  have h : lowCap k m^2 * markerCap k m^8 * fallbackCap m ≤ Q^11 := by
    calc
      _ ≤ Q^2 * Q^8 * Q := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hC _) (Nat.pow_le_pow_left hB _)) hA
      _ = Q^11 := by ring
  rw [pow_mul]
  exact (Nat.pow_le_pow_left h _).trans
    (Nat.pow_le_pow_right (by
      have hpos : 0 < fallbackCap m := by unfold fallbackCap guardedPrimeCap; positivity
      exact pow_pos (hpos.trans_le hA) _) (min_le_left ..))

theorem radius_pos (Q m : ℕ) : 1 ≤ slotRadius Q m := by
  apply le_trans _ (le_max_left _ _)
  unfold fourValueRadius
  omega

/-- A numerical deck can be assembled directly when decoding its lists
recovers the kernel and the required graph masks. -/
theorem slot_assembly_decoded (K : CyclicTile) (Fs : List CyclicTile) {P H : ℕ}
    (hPrime : PrimeBound (order s.layout) P) (hP : 3 < P)
    (hK : K.toFinset.image (decodePoint s.layout) = productKernel s.layout)
    (hs : ∀ F ∈ Fs, ∀ v ∈ F.toFinset.image (decodePoint s.layout),
      TestSupportAt 35 (fun _ => H) v.1)
    (hF : ∀ F ∈ Fs, ∃ o : SharedCoordinates.Outputs s.layout,
      Tiles (F.toFinset.image (decodePoint s.layout)) (Set.range (SharedCoordinates.point s.layout o))) :
    let Cs := K :: Fs
    let X := stackTestCap P Cs.length
    let U := guardedAssembly (((order s.layout,P,X),s.period,H),Cs)
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ A : Set (SharedCoordinates.Ambient s.layout), ∀ F ∈ Cs,
        Tiles (F.toFinset.image (decodePoint s.layout)) A) ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => H) s.period (order s.layout / s.period)
        (reservedCap X P) := by
  let Cs := K :: Fs
  let X := stackTestCap P Cs.length
  have hX : 2313 ≤ X := le_max_left ..
  have hXP : P ≤ X := (le_max_left P Cs.length).trans (le_max_right ..)
  have hcount : Cs.length ≤ X :=
    (le_max_right P Cs.length).trans (le_max_right 2313 (max P Cs.length))
  have hpos : 0 < Cs.length := by simp [Cs]
  have hXX : X ≤ X^2 := by
    rw [pow_two]
    simpa only [mul_one] using Nat.mul_le_mul_left X (show 1 ≤ X by omega)
  have hxs : P ≤ X^2 := hXP.trans hXX
  have hxs' : P+3 ≤ 2*X^2 := by omega
  have mass (F : CyclicTile) (hmem : F ∈ Cs) :
      (cyclicTileSet (order s.layout) F).card * s.period = order s.layout := by
    have hcard : (cyclicTileSet (order s.layout) F).card =
        (F.toFinset.image (decodePoint s.layout)).card := by
      calc
        _ = ((cyclicTileSet (order s.layout) F).image (cyclicAmbientEquiv s.layout s.crt)).card :=
          (Finset.card_image_of_injective _ (cyclicAmbientEquiv s.layout s.crt).injective).symm
        _ = _ := congrArg Finset.card (cyclicTileSet_image s.layout s.crt F)
    rw [hcard]
    rcases List.mem_cons.mp hmem with rfl | hG
    · rw [hK]
      let o : SharedCoordinates.Outputs s.layout := ⟨0,0,0⟩
      exact s.tile_mass _ o ((productKernel_iff s.layout _).mpr ⟨o,rfl⟩)
    · obtain ⟨o,ho⟩ := hF F hG
      exact s.tile_mass _ o ho
  have hne (F : CyclicTile) (hmem : F ∈ Cs) : F ≠ [] := by
    intro h
    have he := mass F hmem
    simp [h,cyclicTileSet] at he
    exact s.positive_order.ne' he.symm
  have hmass (F : CyclicTile) (hmem : F ∈ Cs) :
      (cyclicTileSet (order s.layout) F).card ≤ order s.layout / s.period :=
    (Nat.le_div_iff_mul_le s.period_pos).mpr (mass F hmem).le
  have hstrip (F : CyclicTile) (hmem : F ∈ Cs) (v : CyclicPoint) (hv : v ∈ F) :
      TestSupportAt 35 (fun _ => H) v.1 := by
    have he : decodePoint s.layout v ∈ F.toFinset.image (decodePoint s.layout) :=
      Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩
    rcases List.mem_cons.mp hmem with rfl | hG
    · rw [hK,mem_productKernel] at he
      have hx : v.1 = 0 := congrArg Prod.fst he
      rw [hx]
      exact zero_strip H
    · exact hs F hG _ he
  have hker (j : ℤ) : (((0 : Plane),((s.period : ℤ)*j : ℤ)) : Plane × ZMod (order s.layout)) ∈
      cyclicTileSet (order s.layout) (Cs.getD 0 []) := by
    change _ ∈ cyclicTileSet (order s.layout) K
    let e := cyclicAmbientEquiv s.layout s.crt
    have hEq : (cyclicTileSet (order s.layout) K).image e =
        (cyclicTileSet (order s.layout) (s.encodeTile (productKernel s.layout))).image e := by
      exact (cyclicTileSet_image s.layout s.crt K).trans (hK.trans
        ((cyclicTileSet_image s.layout s.crt _).trans (s.encodeTile_decode _)).symm)
    let v : Plane × ZMod (order s.layout) := (0,((s.period : ℤ)*j : ℤ))
    have h : e v ∈ (cyclicTileSet (order s.layout) (s.encodeTile (productKernel s.layout))).image e :=
      Finset.mem_image.mpr ⟨v,s.kernel_column j,rfl⟩
    rw [← hEq] at h
    obtain ⟨v',hv',he⟩ := Finset.mem_image.mp h
    change v ∈ cyclicTileSet (order s.layout) K
    exact Eq.mp (congrArg (fun z => z ∈ cyclicTileSet (order s.layout) K) (e.injective he)) hv'
  have hperiod := Nat.le_of_dvd s.positive_order s.period_dvd
  obtain ⟨hu,hcon,he,hvol⟩ := guardedAssembly_facts s.positive_order hP hX hPrime hxs hxs'
    s.period_pos hperiod hpos hcount hne hmass hstrip hker
  exact ⟨hu,hcon,(cyclic_deck_iff s.layout s.crt Cs).symm.trans he,hvol⟩

/-- Assemble the abstract graph masks using their cyclic representatives. -/
theorem slot_assembly (Fs : List (Finset (SharedCoordinates.Ambient s.layout))) {P H : ℕ}
    (hPrime : PrimeBound (order s.layout) P) (hP : 3 < P)
    (hs : ∀ F ∈ Fs, ∀ v ∈ F, TestSupportAt 35 (fun _ => H) v.1)
    (hF : ∀ F ∈ Fs, ∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) :
    let Js := productKernel s.layout :: Fs
    let X := stackTestCap P Js.length
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧
      ((∃ A : Set (SharedCoordinates.Ambient s.layout), ∀ F ∈ Js, Tiles F A) ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => H) s.period (order s.layout / s.period)
        (reservedCap X P) := by
  let K := s.encodeTile (productKernel s.layout)
  let Cs := Fs.map s.encodeTile
  have hs' (F : CyclicTile) (hf : F ∈ Cs) :
      ∀ x ∈ F.toFinset.image (decodePoint s.layout), TestSupportAt 35 (fun _ => H) x.1 := by
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hf
    rw [s.encodeTile_decode]
    exact hs G hG
  have hF' (F : CyclicTile) (hf : F ∈ Cs) :
      ∃ o : SharedCoordinates.Outputs s.layout,
        Tiles (F.toFinset.image (decodePoint s.layout)) (Set.range (SharedCoordinates.point s.layout o)) := by
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hf
    rw [s.encodeTile_decode]
    exact hF G hG
  obtain ⟨hu,hcon,he,hvol⟩ := s.slot_assembly_decoded K Cs hPrime hP (s.encodeTile_decode _) hs' hF'
  refine ⟨_,hu,hcon,?_,?_⟩
  · apply Iff.trans _ he
    simp only [K,Cs,List.mem_cons,List.mem_map,forall_eq_or_imp,s.encodeTile_decode]
    simp
  · simpa only [Cs,List.length_cons,List.length_map] using hvol

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
