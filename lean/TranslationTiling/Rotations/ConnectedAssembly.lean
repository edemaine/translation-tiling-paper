import TranslationTiling.Rotations.Assembly

namespace TranslationTiling.Rotations.SixKeys

theorem corner_mem (i : Fin 3) : (39 : ℤ) • Pi.single i 1 ∈ gadget := by
  apply body_subset_gadget
  rw [mem_body_iff]
  fin_cases i <;> simp [BodyPred, InCube, Fin.forall_fin_succ, Pi.single_apply]

theorem adjacent_translate (t : Point) {x y : Point} (h : FaceAdjacent x y) :
    FaceAdjacent (t+x) (t+y) := by
  obtain ⟨i, he | he⟩ := h
  · exact ⟨i, Or.inl (by rw [he]; abel)⟩
  · exact ⟨i, Or.inr (by rw [he]; abel)⟩

theorem cell_path {E : Finset Point} (e : Point) (he : e ∈ E)
    (u v : Point) (hu : u ∈ gadget) (hv : v ∈ gadget) :
    FacePath (fun x => x ∈ assembly E) (grid e+u) (grid e+v) := by
  apply Relation.ReflTransGen.lift (grid e + ·) _ u v (gadget_connected u hu v hv)
  intro a b hab
  exact ⟨(mem_assembly _ _).mpr ⟨e, he, a, hab.1, rfl⟩,
    (mem_assembly _ _).mpr ⟨e, he, b, hab.2.1, rfl⟩, adjacent_translate _ hab.2.2⟩

theorem assembly_connected (E : Finset Point) (hE : Connected (E : Set Point)) :
    Connected (assembly E : Set Point) := by
  have pos (e f : Point) (he : e ∈ E) (hf : f ∈ E) (i : Fin 3)
      (hef : f = e + Pi.single i 1) : FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    have p := cell_path e he 0 ((39 : ℤ) • Pi.single i 1)
      (body_subset_gadget zero_body) (corner_mem i)
    simp only [add_zero] at p
    apply p.tail
    refine ⟨(mem_assembly _ _).mpr ⟨e, he, _, corner_mem i, rfl⟩,
      (mem_assembly _ _).mpr ⟨f, hf, 0, body_subset_gadget zero_body, by simp⟩, i, Or.inl ?_⟩
    rw [hef]
    ext k
    simp [grid, smul_add, Pi.single_apply]
    split_ifs <;> ring
  have step (e f : Point) (he : e ∈ E) (hf : f ∈ E) (h : FaceAdjacent e f) :
      FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    obtain ⟨i, h | h⟩ := h
    · exact pos e f he hf i h
    · exact (pos f e hf he i h).reverse
  have centers (e f : Point) (he : e ∈ E) (hf : f ∈ E) :
      FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    have p := hE e he f hf
    induction p with
    | refl => exact .refl
    | @tail a b _ hab ih => exact (ih hab.1).trans (step a b hab.1 hab.2.1 hab.2.2)
  intro x hx y hy
  obtain ⟨e, he, u, hu, rfl⟩ := (mem_assembly _ _).mp hx
  obtain ⟨f, hf, v, hv, rfl⟩ := (mem_assembly _ _).mp hy
  have p := cell_path e he u 0 hu (body_subset_gadget zero_body)
  have q := cell_path f hf 0 v (body_subset_gadget zero_body) hv
  simp only [add_zero] at p q
  exact (p.trans (centers e f he hf)).trans q

end TranslationTiling.Rotations.SixKeys
