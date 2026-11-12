import TranslationTiling.Rotations.General.Assembly

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem corner_mem (hd : 2 ≤ d) (i : Fin d) :
    ((cubeSide d : ℤ)-1) • (Pi.single i 1 : Lattice d) ∈ gadget := by
  apply body_subset_gadget
  obtain ⟨j,hj⟩ := exists_other hd (0 : Fin d)
  have hp := cubeSide_pos (d := d)
  have hm := margin_pos (d := d)
  have hb (k : Fin d) :
      (((cubeSide d : ℤ)-1) • (Pi.single i 1 : Lattice d)) k = 0 ∨
      (((cubeSide d : ℤ)-1) • (Pi.single i 1 : Lattice d)) k = (cubeSide d : ℤ)-1 := by
    by_cases hk : k = i <;> simp [Pi.single_apply,hk]
  refine two_outer_body ?_ 0 j (Ne.symm hj) ?_ ?_
  · intro k
    have := hb k
    dsimp at this ⊢
    omega
  · have := hb 0
    dsimp [Outer] at this ⊢
    omega
  · have := hb j
    dsimp [Outer] at this ⊢
    omega

theorem adjacent_translate (t : (Lattice d)) {x y : (Lattice d)} (h : FaceAdjacent x y) :
    FaceAdjacent (t+x) (t+y) := by
  obtain ⟨i, he | he⟩ := h
  · exact ⟨i, Or.inl (by rw [he]; abel)⟩
  · exact ⟨i, Or.inr (by rw [he]; abel)⟩

theorem cell_path (hd : 3 ≤ d) {E : Finset (Lattice d)} (e : (Lattice d)) (he : e ∈ E)
    (u v : (Lattice d)) (hu : u ∈ gadget) (hv : v ∈ gadget) :
    FacePath (fun x => x ∈ assembly E) (grid e+u) (grid e+v) := by
  apply Relation.ReflTransGen.lift (grid e + ·) _ u v (gadget_connected hd u hu v hv)
  intro a b hab
  exact ⟨(mem_assembly _ _).mpr ⟨e, he, a, hab.1, rfl⟩,
    (mem_assembly _ _).mpr ⟨e, he, b, hab.2.1, rfl⟩, adjacent_translate _ hab.2.2⟩

theorem assembly_connected (hd : 3 ≤ d) (E : Finset (Lattice d)) (hE : Connected (E : Set (Lattice d))) :
    Connected (assembly E : Set (Lattice d)) := by
  have pos (e f : (Lattice d)) (he : e ∈ E) (hf : f ∈ E) (i : Fin d)
      (hef : f = e + (Pi.single i 1 : Lattice d)) : FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    have p := cell_path hd e he 0 (((cubeSide d : ℤ)-1) • (Pi.single i 1 : Lattice d))
      (body_subset_gadget (zero_body (by omega : 2 ≤ d))) (corner_mem (by omega : 2 ≤ d) i)
    simp only [add_zero] at p
    apply p.tail
    refine ⟨(mem_assembly _ _).mpr ⟨e, he, _, corner_mem (by omega : 2 ≤ d) i, rfl⟩,
      (mem_assembly _ _).mpr ⟨f, hf, 0, body_subset_gadget (zero_body (by omega : 2 ≤ d)), by simp⟩, i, Or.inl ?_⟩
    rw [hef]
    ext k
    simp [grid, smul_add, Pi.single_apply]
    split_ifs <;> ring
  have step (e f : (Lattice d)) (he : e ∈ E) (hf : f ∈ E) (h : FaceAdjacent e f) :
      FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    obtain ⟨i, h | h⟩ := h
    · exact pos e f he hf i h
    · exact (pos f e hf he i h).reverse
  have centers (e f : (Lattice d)) (he : e ∈ E) (hf : f ∈ E) :
      FacePath (fun x => x ∈ assembly E) (grid e) (grid f) := by
    have p := hE e he f hf
    induction p with
    | refl => exact .refl
    | @tail a b _ hab ih => exact (ih hab.1).trans (step a b hab.1 hab.2.1 hab.2.2)
  intro x hx y hy
  obtain ⟨e, he, u, hu, rfl⟩ := (mem_assembly _ _).mp hx
  obtain ⟨f, hf, v, hv, rfl⟩ := (mem_assembly _ _).mp hy
  have p := cell_path hd e he u 0 hu (body_subset_gadget (zero_body (by omega : 2 ≤ d)))
  have q := cell_path hd f hf 0 v (body_subset_gadget (zero_body (by omega : 2 ≤ d))) hv
  simp only [add_zero] at p q
  exact (p.trans (centers e f he hf)).trans q

end TranslationTiling.Rotations.General
