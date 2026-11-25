import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.Effective.SlotFinite
import TranslationTiling.FiniteCompiler.Effective.SlotObservations

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective FiniteCompiler.Effective
open scoped Classical

noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)
local instance numericalInvarianceAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

/-- Numerical low moduli and displacement residues suffice to write the
ordinary invariance mask in cyclic coordinates. -/
theorem numericalInvariance_correct {a b : ℕ} (ψ : Factor s.layout →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = ((n : ZMod a),(n : ZMod b)))
    (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ i, s.layout.lowSize i = r)
    (cs : CongruenceList) (h : Plane) (v : ∀ i, SharedCoordinates.Low s.layout i)
    (hcs : ∀ c, c ∈ cs ↔ ∃ i, (s.layout.lowSize i,(v i).val) = c) :
    (invarianceCodes (order s.layout) rs a b h cs).toFinset.image (decodePoint s.layout) =
      productInvariance s.layout ψ (h,v) := by
  ext f
  apply (mem_decoded_invariance s.layout s.crt ψ hψ rs hr cs h v hcs f).trans
  simp only [productInvariance,Finset.mem_filter,Finset.mem_union,mem_productKernel,
    Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · rintro (ht | ht)
    · exact Or.inl ht
    · exact Or.inr ⟨⟨f.2,Prod.ext (congrArg Prod.fst ht.1).symm rfl⟩,ht⟩
  · rintro (ht | ⟨_,ht⟩)
    · exact Or.inl ht
    · exact Or.inr ht

theorem observedMarker_decode (i : WangSlot k m) (j : Fin 3) (n : ℕ) :
    s.observeMarker i j (decode s.layout n) = (n : ZMod (s.marker i j)) := by
  change s.markerRead i j (n : ZMod (s.layout.secondSize (.inr (.inl i)))) = _
  exact map_natCast (ZMod.castHom
    (Finset.dvd_prod_of_mem (s.marker i) (Finset.mem_univ j)) (ZMod (s.marker i j))) n

theorem observedFallback_decode (i : SlotFallback m) (n : ℕ) :
    s.observeFallback i (decode s.layout n) = (n : ZMod (s.fallback i)) := rfl

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
