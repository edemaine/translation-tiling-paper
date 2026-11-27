import TranslationTiling.FiniteCompiler.Effective.SlotPolycube

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift
open scoped Classical
noncomputable section

local instance numericalAssemblyFrame : SeedFrame := compactSeedFrame

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
variable (s : SlotParameters k m)
local instance numericalAssemblyDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

/-- Once a numerical list decodes to the slot deck, its assembled output
has the same tiling equivalence and volume bound. -/
theorem slot_polycube_decoded (hwm : w ≤ m) {P Q : ℕ}
    (hPr : PrimeBound (order s.layout) P) (hP : 3 < P) (hQ : ∀ j, s.prime j ≤ Q)
    (K : CyclicTile) (Fs : List CyclicTile)
    (hK : K.toFinset.image (decodePoint s.layout) = productKernel s.layout)
    (hDeck : ∀ F, F ∈ s.slotDeck c hwm ↔
      ∃ G ∈ K :: Fs, G.toFinset.image (decodePoint s.layout) = F) :
    let H := slotRadius Q m
    let X := stackTestCap P (K :: Fs).length
    let U := guardedAssembly (((order s.layout,P,X),s.period,H),K :: Fs)
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => H) s.period (order s.layout / s.period)
        (reservedCap X P) := by
  let decodeF := fun F : CyclicTile => F.toFinset.image (decodePoint s.layout)
  have hmem (F : CyclicTile) (hF : F ∈ Fs) : decodeF F ∈ s.slotDeck c hwm :=
    (hDeck _).mpr ⟨F,List.mem_cons_of_mem _ hF,rfl⟩
  obtain ⟨hu,hconn,hiff,hsize⟩ := s.slot_assembly_decoded K Fs hPr hP hK
    (fun F hF v hv => s.slotDeck_strip c hwm hQ _ (hmem F hF) v hv)
    (fun F hF => s.slotDeck_has_mass c hwm _ (hmem F hF))
  refine ⟨hu,hconn,?_,hsize⟩
  apply (s.slotDeck_iff c hwm).trans
  apply Iff.trans _ hiff
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨A,fun F hF => hA _ ((hDeck _).mpr ⟨F,hF,rfl⟩)⟩
  · rintro ⟨A,hA⟩
    refine ⟨A,?_⟩
    intro F hF
    obtain ⟨G,hG,rfl⟩ := (hDeck _).mp hF
    exact hA G hG
/-- A vertical replacement can use a different ordering of the same
cycle, provided it enforces the same condition on every admissible graph. -/
def SlotMaskMatches (A B : Finset (SharedCoordinates.Ambient s.layout)) : Prop :=
  A = B ∨ ((∀ x ∈ A, x.1 = 0) ∧
    (∃ o : SharedCoordinates.Outputs s.layout, Tiles A (Set.range (SharedCoordinates.point s.layout o))) ∧
    ∀ o, s.cycleDependencies o →
      (Tiles A (Set.range (SharedCoordinates.point s.layout o)) ↔
        Tiles B (Set.range (SharedCoordinates.point s.layout o))))

theorem SlotMaskMatches.holds {A B : Finset (SharedCoordinates.Ambient s.layout)}
    (h : s.SlotMaskMatches A B) (o : SharedCoordinates.Outputs s.layout) (hd : s.cycleDependencies o) :
    Tiles A (Set.range (SharedCoordinates.point s.layout o)) ↔
      Tiles B (Set.range (SharedCoordinates.point s.layout o)) := by
  rcases h with rfl | h
  · exact Iff.rfl
  · exact h.2.2 o hd

theorem slot_polycube_related (hwm : w ≤ m) {P : ℕ}
    (hPr : PrimeBound (order s.layout) P) (hP : 3 < P)
    (hD : ∀ i, s.slotOffsetFactor i ≤ slotOffsetFactorCap k m)
    (K : CyclicTile) (Fs : List CyclicTile)
    (hK : K.toFinset.image (decodePoint s.layout) = productKernel s.layout)
    (hforward : ∀ A ∈ Fs, ∃ B ∈ s.slotDeck c hwm,
      s.SlotMaskMatches (A.toFinset.image (decodePoint s.layout)) B)
    (hreverse : ∀ B ∈ s.slotDeck c hwm, B = productKernel s.layout ∨
      ∃ A ∈ Fs, s.SlotMaskMatches (A.toFinset.image (decodePoint s.layout)) B)
    (hdep : ∀ o, (∀ A ∈ Fs, Tiles (A.toFinset.image (decodePoint s.layout))
      (Set.range (SharedCoordinates.point s.layout o))) → s.cycleDependencies o) :
    let H := slotAssemblyRadii k m w
    let X := slotStackTestCap P (K :: Fs).length
    let U := guardedAssemblyBySlope (((order s.layout,P,X),s.period,H),K :: Fs)
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun j => H.getD j 0) s.period (order s.layout / s.period)
        (reservedPrimeCap X P) := by
  let decMask (A : CyclicTile) := A.toFinset.image (decodePoint s.layout)
  let graph (o : SharedCoordinates.Outputs s.layout) := Set.range (SharedCoordinates.point s.layout o)
  have hstrip (A : CyclicTile) (hmem : A ∈ Fs) (x : SharedCoordinates.Ambient s.layout) (hx : x ∈ decMask A) :
      TestSupportAt 35 (fun j => (slotAssemblyRadii k m w).getD j 0) x.1 := by
    obtain ⟨B,hB',hAB⟩ := hforward A hmem
    rcases hAB with he | h
    · exact s.slotDeck_strip_refined c hwm hD B hB' x (he ▸ hx)
    · rw [h.1 x hx]
      exact Or.inl (by simp)
  have hmass (A : CyclicTile) (hA : A ∈ Fs) :
      ∃ o : SharedCoordinates.Outputs s.layout, Tiles (decMask A) (graph o) := by
    obtain ⟨B,hB,hAB⟩ := hforward A hA
    rcases hAB with he | h
    · unfold decMask
      rw [he]
      exact s.slotDeck_has_mass c hwm B hB
    · exact h.2.1
  obtain ⟨hu,hconn,hiff,hsize⟩ := s.slot_assembly_decodedBySlope K Fs hPr hP hK hstrip hmass
  refine ⟨hu,hconn,?_,hsize⟩
  apply (s.slotDeck_iff c hwm).trans
  apply Iff.trans _ hiff
  constructor
  · rintro ⟨A,hA⟩
    obtain ⟨o,rfl⟩ := (productKernel_iff s.layout A).mp (hA _ (List.mem_cons_self ..))
    have hd : s.cycleDependencies o := by
      refine ⟨fun F hF => ?_,fun F hF => ?_,fun i j F hF => ?_⟩
      · exact hA F ((s.slotDeck_membership c hwm F).mpr (Or.inr (Or.inl hF)))
      · exact hA F ((s.slotDeck_membership c hwm F).mpr (Or.inr (Or.inr (Or.inl hF))))
      · exact hA F ((s.slotDeck_membership c hwm F).mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,j,hF⟩)))))
    refine ⟨graph o,?_⟩
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · rw [hK]
      exact (productKernel_iff s.layout (graph o)).mpr ⟨o,rfl⟩
    · obtain ⟨B,hB,hGB⟩ := hforward G hG
      exact (hGB.holds s o hd).mpr (hA B hB)
  · rintro ⟨A,hA⟩
    have hK' := hA K (List.mem_cons_self ..)
    rw [hK] at hK'
    obtain ⟨o,rfl⟩ := (productKernel_iff s.layout A).mp hK'
    have hd := hdep o (fun A h => hA A (List.mem_cons_of_mem _ h))
    refine ⟨graph o,?_⟩
    intro B hB
    rcases hreverse B hB with rfl | ⟨G,hG,hGB⟩
    · exact (productKernel_iff s.layout (graph o)).mpr ⟨o,rfl⟩
    · exact (hGB.holds s o hd).mp (hA G (List.mem_cons_of_mem _ hG))

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
