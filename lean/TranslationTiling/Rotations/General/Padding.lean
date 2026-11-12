import TranslationTiling.Proofs.Dimension
import TranslationTiling.Proofs.FacePaths

namespace TranslationTiling.Rotations.General

/-- Appending zero coordinates preserves the coordinate unit steps. -/
theorem pad_single {a b : ℕ} (hab : a ≤ b) (k : Fin a) :
    pad hab (Pi.single k 1)=Pi.single (Fin.castLE hab k) 1 := by
  ext i
  by_cases hi : i.val < a
  · simp [pad,hi,Pi.single_apply,Fin.ext_iff]
  · have hne : i ≠ Fin.castLE hab k := by intro he; have := congrArg Fin.val he; dsimp at this; omega
    simp [pad,hi,Pi.single_eq_of_ne hne]

theorem pad_adjacent {a b : ℕ} (hab : a ≤ b) {x y : Lattice a} (hxy : FaceAdjacent x y) :
    FaceAdjacent (pad hab x) (pad hab y) := by
  obtain ⟨k,he | he⟩ := hxy
  · exact ⟨Fin.castLE hab k,Or.inl (by rw [he,map_add,pad_single])⟩
  · exact ⟨Fin.castLE hab k,Or.inr (by rw [he,map_add,pad_single])⟩

theorem pad_connected {a b : ℕ} (hab : a ≤ b) (E : Tile a) (hE : FaceConnected E) :
    FaceConnected (E.map (pad hab)) := by
  rintro x hx y hy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
  exact Relation.ReflTransGen.lift (pad hab)
    (fun p q hpq => ⟨List.mem_map.mpr ⟨p,hpq.1,rfl⟩,
      List.mem_map.mpr ⟨q,hpq.2.1,rfl⟩,pad_adjacent hab hpq.2.2⟩) u v (hE u hu v hv)

end TranslationTiling.Rotations.General
