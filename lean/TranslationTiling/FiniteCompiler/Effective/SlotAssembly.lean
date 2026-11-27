import TranslationTiling.FiniteCompiler.Effective.SlotKernelGeometry
import TranslationTiling.FiniteCompiler.Effective.SlotStrip

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift Compiler.Size
open scoped Classical
noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 2500000
attribute [local irreducible] slotSearchCap
variable {k m : ℕ} (s : SlotParameters k m)
local instance : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

def stackTestCap (P count : ℕ) := max 2313 (max P count)

def slotStackTestCap (P count : ℕ) := max 2313 (max (P.sqrt+1) count)

theorem slotStackTestCap_le {P count : ℕ} (hP : 1 < P) :
    slotStackTestCap P count ≤ stackTestCap P count :=
  max_le_max_left _ (max_le_max_right _ (Nat.succ_le_of_lt (Nat.sqrt_lt_self hP)))

def slotRadius (Q m : ℕ) := max (fourValueRadius 0) (Q^(11*m))

/-- One horizontal CRT factor for each selected slot. -/
def slotOffsetFactorCap (k m : ℕ) : ℕ :=
  if k = 1 ∧ m = 1 then 473028263936385713 else
    lowCap k m * markerCap k m^3 * fallbackCap m^2

theorem slotOffsetFactorCap_le (k m : ℕ) :
    slotOffsetFactorCap k m ≤ lowCap k m * markerCap k m^3 * fallbackCap m^2 := by
  by_cases h : k = 1 ∧ m = 1
  · rw [slotOffsetFactorCap,ite_eq_left h]
    have ha : slotBasePrimeCap ≤ fallbackCap m := threshold_le_slotSearchCap slotBasePrimeCap (4*m)
    have hb := ha.trans (fallbackCap_le_markerCap k m)
    have hc := hb.trans (markerCap_le_lowCap k m)
    exact (by decide : 473028263936385713 ≤ slotBasePrimeCap*slotBasePrimeCap^3*slotBasePrimeCap^2).trans
      (Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_left hb _)) (Nat.pow_le_pow_left ha _))
  · rw [slotOffsetFactorCap,ite_eq_right h]

theorem slotOffsetFactorCap_pos (k m : ℕ) : 0 < slotOffsetFactorCap k m := by
  unfold slotOffsetFactorCap
  split
  · decide
  · have ha := fallbackCap_pos m
    have hb := ha.trans_le (fallbackCap_le_markerCap k m)
    have hc := hb.trans_le (markerCap_le_lowCap k m)
    exact Nat.mul_pos (Nat.mul_pos hc (pow_pos hb _)) (pow_pos ha _)

/-- Only selected slots contribute to an activation displacement. -/
def slotAssemblyRadius (k m w : ℕ) :=
  max (fourValueRadius 0) ((slotOffsetFactorCap k m)^(min m (m+1-w)))

/-- The fixed arithmetic tests use their own strip widths. -/
def slotAssemblyRadii (k m w : ℕ) : List ℕ :=
  let A := (slotOffsetFactorCap k m)^(min m (m+1-w))
  arithmeticStripRadii.map (fun x => max x A)

theorem slotAssemblyRadii_getD {k m w j : ℕ} (hj : j < 17) :
    (slotAssemblyRadii k m w).getD j 0 =
      max (arithmeticStripRadii.getD j 0)
        ((slotOffsetFactorCap k m)^(min m (m+1-w))) := by
  have h : j < arithmeticStripRadii.length := by simpa [arithmeticStripRadii] using hj
  simp [slotAssemblyRadii,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h]

theorem arithmeticStripRadii_le (j : ℕ) : arithmeticStripRadii.getD j 0 ≤ fourValueRadius 0 := by
  by_cases hj : j < 17
  · exact (by decide +kernel : ∀ j : Fin 17, arithmeticStripRadii.getD j 0 ≤ fourValueRadius 0) ⟨j,hj⟩
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa [arithmeticStripRadii] using hj)]
    exact Nat.zero_le _

theorem slotAssemblyRadii_le {k m w j : ℕ} (hj : j < 17) :
    (slotAssemblyRadii k m w).getD j 0 ≤ slotAssemblyRadius k m w := by
  rw [slotAssemblyRadii_getD hj]
  exact max_le_max_right _ (arithmeticStripRadii_le j)

theorem slotAssemblyRadius_le (k m w Q : ℕ) (hA : fallbackCap m ≤ Q)
    (hB : markerCap k m ≤ Q) (hC : lowCap k m ≤ Q) :
    slotAssemblyRadius k m w ≤ slotRadius Q m := by
  unfold slotAssemblyRadius slotRadius
  apply max_le_max_left
  have hQ := (fallbackCap_pos m).trans_le hA
  have h : slotOffsetFactorCap k m ≤ Q^11 := by
    calc
      _ ≤ _ := slotOffsetFactorCap_le k m
      _ ≤ Q * Q^3 * Q^2 := Nat.mul_le_mul
        (Nat.mul_le_mul hC (Nat.pow_le_pow_left hB _)) (Nat.pow_le_pow_left hA _)
      _ = Q^6 := by ring
      _ ≤ Q^11 := Nat.pow_le_pow_right hQ (by decide)
  rw [pow_mul]
  exact (Nat.pow_le_pow_left h _).trans
    (Nat.pow_le_pow_right (by
      have hpos : 0 < fallbackCap m := fallbackCap_pos _
      exact pow_pos (hpos.trans_le hA) _) (min_le_left ..))

theorem radius_pos (Q m : ℕ) : 1 ≤ slotRadius Q m := by
  apply le_trans _ (le_max_left _ _)
  unfold fourValueRadius
  omega

/-- A numerical deck can be assembled directly when decoding its lists
recovers the kernel and the required graph masks. -/
private theorem slot_assembly_decodedWith (assemble : List CyclicTile → Tile 3)
    (K : CyclicTile) (Fs : List CyclicTile) {L : ℕ} {H : ℕ → ℕ}
    (hassemble : ∀ J, (∀ F ∈ K :: Fs, (cyclicTileSet (order s.layout) F).card ≤ J) →
      (∀ F ∈ K :: Fs, F ≠ []) → (∀ F ∈ K :: Fs, ∀ v ∈ F, TestSupportAt 35 H v.1) →
      (∀ j : ℤ, (((0 : Plane),((s.period : ℤ)*j : ℤ)) : Plane × ZMod (order s.layout)) ∈
        cyclicTileSet (order s.layout) ((K :: Fs).getD 0 [])) →
      let U := assemble (K :: Fs)
      U ≠ [] ∧ FaceConnected U ∧
      ((∃ B : Set (Plane × ZMod (order s.layout)), ∀ i : Fin (K :: Fs).length,
        FiniteCompiler.Tiles (cyclicTileSet (order s.layout) ((K :: Fs).getD i.val [])) B) ↔
        TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 H s.period J L)
    (hK : K.toFinset.image (decodePoint s.layout) = productKernel s.layout)
    (hs : ∀ F ∈ Fs, ∀ v ∈ F.toFinset.image (decodePoint s.layout),
      TestSupportAt 35 H v.1)
    (hF : ∀ F ∈ Fs, ∃ o : SharedCoordinates.Outputs s.layout,
      Tiles (F.toFinset.image (decodePoint s.layout)) (Set.range (SharedCoordinates.point s.layout o))) :
    let Cs := K :: Fs
    let U := assemble Cs
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ A : Set (SharedCoordinates.Ambient s.layout), ∀ F ∈ Cs,
        Tiles (F.toFinset.image (decodePoint s.layout)) A) ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 H s.period (order s.layout / s.period)
        L := by
  let Cs := K :: Fs
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
      TestSupportAt 35 H v.1 := by
    have he : decodePoint s.layout v ∈ F.toFinset.image (decodePoint s.layout) :=
      Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩
    rcases List.mem_cons.mp hmem with rfl | hG
    · rw [hK,mem_productKernel] at he
      have hx : v.1 = 0 := congrArg Prod.fst he
      rw [hx]
      exact Or.inl (by simp)
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
  obtain ⟨hu,hcon,he,hvol⟩ := hassemble (order s.layout/s.period) hmass hne hstrip hker
  exact ⟨hu,hcon,(cyclic_deck_iff s.layout s.crt Cs).symm.trans he,hvol⟩


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
  dsimp only
  let X := stackTestCap P (K :: Fs).length
  have hX : 2313 ≤ X := le_max_left ..
  have hPX : P ≤ X := (le_max_left ..).trans (le_max_right ..)
  have hcount : (K :: Fs).length ≤ X := (le_max_right ..).trans (le_max_right ..)
  have hXX : X ≤ X^2 := by
    rw [pow_two]
    simpa using Nat.mul_le_mul_left X (show 1 ≤ X by omega)
  have hP₂ := hPX.trans hXX
  exact s.slot_assembly_decodedWith (fun L => guardedAssembly (((order s.layout,P,X),s.period,H),L))
    K Fs (L := reservedCap X P) (H := fun _ => H) (fun J hm hn ht hk =>
    guardedAssembly_facts (J := J) s.positive_order hP hX hPrime hP₂
      (by omega) s.period_pos (Nat.le_of_dvd s.positive_order s.period_dvd)
      (by simp) hcount hn hm ht hk) hK hs hF

theorem slot_assembly_decodedBySlope (K : CyclicTile) (Fs : List CyclicTile) {P : ℕ} {H : List ℕ}
    (hPrime : PrimeBound (order s.layout) P) (hP : 3 < P)
    (hK : K.toFinset.image (decodePoint s.layout) = productKernel s.layout)
    (hs : ∀ F ∈ Fs, ∀ v ∈ F.toFinset.image (decodePoint s.layout),
      TestSupportAt 35 (fun j => H.getD j 0) v.1)
    (hF : ∀ F ∈ Fs, ∃ o : SharedCoordinates.Outputs s.layout,
      Tiles (F.toFinset.image (decodePoint s.layout)) (Set.range (SharedCoordinates.point s.layout o))) :
    let Cs := K :: Fs
    let X := slotStackTestCap P Cs.length
    let U := guardedAssemblyBySlope (((order s.layout,P,X),s.period,H),Cs)
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ A : Set (SharedCoordinates.Ambient s.layout), ∀ F ∈ Cs,
        Tiles (F.toFinset.image (decodePoint s.layout)) A) ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun j => H.getD j 0) s.period (order s.layout / s.period)
        (reservedPrimeCap X P) := by
  dsimp only
  let X := slotStackTestCap P (K :: Fs).length
  have hX : 2313 ≤ X := le_max_left ..
  have hcount : (K :: Fs).length ≤ X := (le_max_right ..).trans (le_max_right ..)
  have hroot : P.sqrt+1 ≤ X := (le_max_left ..).trans (le_max_right ..)
  have hP₂ : P ≤ X^2 := (Nat.lt_succ_sqrt' P).le.trans (Nat.pow_le_pow_left hroot _)
  have hX₂ : 3 ≤ X^2 := by nlinarith
  exact s.slot_assembly_decodedWith (fun L => guardedAssemblyBySlope (((order s.layout,P,X),s.period,H),L))
    K Fs (L := reservedPrimeCap X P) (H := fun j => H.getD j 0) (fun J hm hn ht hk =>
    guardedAssemblyBySlope_facts (J := J) s.positive_order hP hX hPrime hP₂
      (by omega) s.period_pos (Nat.le_of_dvd s.positive_order s.period_dvd)
      (by simp) hcount hn hm ht hk) hK hs hF

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
