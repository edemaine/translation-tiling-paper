import TranslationTiling.FiniteCompiler.Effective.AxisSlotCRT

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates Compiler Compiler.Effective
open scoped Classical

noncomputable section

namespace AxisParameters

variable {k m : ℕ} (s : AxisParameters k m) [NeZero (order s.layout)]

/-- Encode a finite mask by its horizontal offsets and cyclic representatives. -/
def encodeTile (F : Finset (SharedCoordinates.Ambient s.layout)) : CyclicTile :=
  F.toList.map fun p => (p.1,(s.crt.symm p.2).val)

@[simp] theorem encodeTile_decode [DecidableEq CyclicPoint] [DecidableEq (SharedCoordinates.Ambient s.layout)]
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (s.encodeTile F).toFinset.image (decodePoint s.layout) = F := by
  have h (p : SharedCoordinates.Ambient s.layout) :
      decodePoint s.layout (p.1,(s.crt.symm p.2).val) = p := by
    change (p.1,decode s.layout (s.crt.symm p.2).val) = p
    refine Prod.ext rfl ?_
    change decode s.layout (s.crt.symm p.2).val = p.2
    calc
      _ = s.crt ((s.crt.symm p.2).val : ZMod (order s.layout)) :=
        (map_natCast s.crt _).symm
      _ = _ := by rw [ZMod.natCast_zmod_val,s.crt.apply_symm_apply]
  ext p
  simp only [encodeTile,Finset.mem_image,List.mem_toFinset,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨f,⟨q,hq,rfl⟩,he⟩
    rw [h q] at he
    exact he ▸ hq
  · intro hp
    exact ⟨_,⟨p,hp,rfl⟩,h p⟩

/-- Encoding the masks preserves their common tiling solutions. -/
theorem encodeDeck_iff (Fs : List (Finset (SharedCoordinates.Ambient s.layout))) :
    let codes := Fs.map s.encodeTile
    (∃ B : Set (Plane × ZMod (order s.layout)),
      ∀ i : Fin codes.length, Tiles (cyclicTileSet (order s.layout) (codes.getD i.val [])) B) ↔
    ∃ A : Set (SharedCoordinates.Ambient s.layout), ∀ F ∈ Fs, Tiles F A := by
  dsimp only
  rw [cyclic_deck_iff _ s.crt]
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨A,fun F hF => ?_⟩
    have ht := hA (s.encodeTile F) (List.mem_map.mpr ⟨F,hF,rfl⟩)
    convert ht using 1
    exact (@encodeTile_decode k m s _ _ (fun a b => Classical.propDecidable (a = b)) F).symm
  · rintro ⟨A,hA⟩
    refine ⟨A,?_⟩
    rintro F hF
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hF
    convert hA Q hQ using 1
    exact @encodeTile_decode k m s _ _ (fun a b => Classical.propDecidable (a = b)) Q

end AxisParameters

end

end TranslationTiling.FiniteCompiler.Packed
