import TranslationTiling.Compiler.ClosedGeometryBound

/-! Surface counts and the fixed volume of the MSS pieces sharpen the geometry. -/
namespace TranslationTiling.Compiler.Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def facePoint (l : ℕ) (k : Fin 3) (b : Fin 2) (u v : Fin l) : Lattice 3 :=
  let t : ℤ := if b = 0 then 0 else (l : ℤ)-1
  if k = 0 then ![t,u.val,v.val]
  else if k = 1 then ![u.val,t,v.val] else ![u.val,v.val,t]

theorem kim_boundary_length_le_surface (l : ℕ) : (Kim.boundary l).length ≤ 6 * l ^ 2 := by
  have hn : (Kim.cube l).Nodup := by
    apply List.nodup_iff_length_dedup_eq.mpr
    rw [← List.card_toFinset,Kim.cube_card,kim_cube_length]
  have hb : (Kim.boundary l).Nodup := hn.filter _
  rw [← List.toFinset_card_of_nodup hb]
  have hsub : (Kim.boundary l).toFinset ⊆
      Finset.univ.image (fun z : Fin 3 × Fin 2 × Fin l × Fin l => facePoint l z.1 z.2.1 z.2.2.1 z.2.2.2) := by
    intro x hx
    obtain ⟨hxc,k,hk⟩ := (Kim.mem_boundary_iff l x).mp (List.mem_toFinset.mp hx)
    have hx0 := (Kim.mem_cube_iff l x).mp hxc 0
    have hx1 := (Kim.mem_cube_iff l x).mp hxc 1
    have hx2 := (Kim.mem_cube_iff l x).mp hxc 2
    have hn0 : (x 0).toNat < l := by omega
    have hn1 : (x 1).toNat < l := by omega
    have hn2 : (x 2).toNat < l := by omega
    have hx0' := Int.toNat_of_nonneg hx0.1
    have hx1' := Int.toNat_of_nonneg hx1.1
    have hx2' := Int.toNat_of_nonneg hx2.1
    fin_cases k
    · rcases hk with hk | hk
      · exact Finset.mem_image.mpr ⟨(0,0,⟨(x 1).toNat,hn1⟩,⟨(x 2).toNat,hn2⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx1',hx2'] <;> simpa using hk.symm⟩
      · exact Finset.mem_image.mpr ⟨(0,1,⟨(x 1).toNat,hn1⟩,⟨(x 2).toNat,hn2⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx1',hx2'] <;> simpa using hk.symm⟩
    · rcases hk with hk | hk
      · exact Finset.mem_image.mpr ⟨(1,0,⟨(x 0).toNat,hn0⟩,⟨(x 2).toNat,hn2⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx0',hx2'] <;> simpa using hk.symm⟩
      · exact Finset.mem_image.mpr ⟨(1,1,⟨(x 0).toNat,hn0⟩,⟨(x 2).toNat,hn2⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx0',hx2'] <;> simpa using hk.symm⟩
    · rcases hk with hk | hk
      · exact Finset.mem_image.mpr ⟨(2,0,⟨(x 0).toNat,hn0⟩,⟨(x 1).toNat,hn1⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx0',hx1'] <;> simpa using hk.symm⟩
      · exact Finset.mem_image.mpr ⟨(2,1,⟨(x 0).toNat,hn0⟩,⟨(x 1).toNat,hn1⟩),Finset.mem_univ _,by ext i; fin_cases i <;> simp [facePoint,hx0',hx1'] <;> simpa using hk.symm⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_image_le.trans
  simp [Fintype.card_prod,pow_two,Nat.mul_assoc]
  <;> omega

private theorem mss_box_card (k : ℕ) : (MSS.box k).card = (2*k+1)^3 := by
  simp only [MSS.box,Finset.card_pi,Int.card_Icc]
  have hi : ((k : ℤ) + 1 + (k : ℤ)).toNat = 2*k+1 := by omega
  simp [hi]

theorem mss_component_card_le (m j : ℕ) (hj : j ≤ 5) : (MSS.component m j).card ≤ 2 ^ 24 := by
  have hbase : MSS.baseShape.card ≤ 201 ^ 3 + 3 * 7 ^ 3 := by
    unfold MSS.baseShape
    apply (Finset.card_union_le _ _).trans
    apply Nat.add_le_add
    · exact ((Finset.card_le_card Finset.sdiff_subset)).trans (by rw [mss_box_card])
    · unfold MSS.bumps
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _i : Fin 3, 7 ^ 3 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.card_image_le.trans
          apply ((Finset.card_le_card Finset.sdiff_subset)).trans
          rw [mss_box_card]
          gcongr
          have := i.isLt
          omega
        _ = _ := by simp
  have hframe : (MSS.frame j).card ≤ 11 ^ 3 := by
    apply ((Finset.card_le_card Finset.sdiff_subset)).trans
    rw [mss_box_card]
    gcongr
    omega
  calc
    _ ≤ MSS.baseShape.card + (MSS.frame j).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset) Finset.card_image_le)
    _ ≤ (201 ^ 3 + 3 * 7 ^ 3) + 11 ^ 3 := Nat.add_le_add hbase hframe
    _ ≤ _ := by norm_num

def sparseGeometryCap (H M : ℕ) : ℕ :=
  (2 ^ 24 * ((2*H+1)^2 * M)) * (18 * latticeSide H M ^ 2 + 6)^3

theorem connectedTile_surface_bound (E : Tile 3) :
    cubeCount (connectedTile E) ≤ cubeCount E * (18 * cubeSize E ^ 2 + 6)^3 := by
  have h := connectedAssembly_cubeCount_le (positiveTile E) (cubeSize E)
    (by unfold cubeSize; omega)
  rw [positiveTile_cubeCount] at h
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  dsimp [Kim.scale]
  have := kim_boundary_length_le_surface (cubeSize E)
  omega

theorem cyclic_card_le_box {m H : ℕ} [NeZero m] (F : Finset (Plane × ZMod m))
    (h : ∀ f ∈ F, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    F.card ≤ (2*H+1)^2 * m := by
  have hs : F ⊆ ((Finset.Icc (-(H : ℤ)) H).product
      (Finset.Icc (-(H : ℤ)) H)).product Finset.univ := by
    intro f hf
    obtain ⟨hx,hy⟩ := h f hf
    simp only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,Finset.mem_univ,and_true]
    omega
  apply (Finset.card_le_card hs).trans
  have hi : ((H : ℤ) + 1 + (H : ℤ)).toNat = 2*H+1 := by omega
  simp [Finset.card_product,Int.card_Icc,ZMod.card,pow_two,hi]


theorem assembled_card_le (m : ℕ) (U : Finset (Lattice 3)) :
    (LatticeGeometry.assembled m U).card ≤ U.card * 2 ^ 24 := by
  unfold LatticeGeometry.assembled
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _u ∈ U, 2 ^ 24 := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.card_image_le.trans
      unfold LatticeGeometry.part
      split_ifs <;> exact mss_component_card_le _ _ (by decide)
    _ = _ := by simp

theorem connectedTile_sparseGeometryCap (E : Tile 3) (H M : ℕ)
    (hc : cubeCount E ≤ 2 ^ 24 * ((2*H+1)^2*M))
    (h : coordinateBound E ≤ latticeRadius H M) :
    cubeCount (connectedTile E) ≤ sparseGeometryCap H M := by
  have hside : cubeSize E ≤ latticeSide H M := by unfold cubeSize latticeSide; omega
  apply (connectedTile_surface_bound E).trans
  unfold sparseGeometryCap
  exact Nat.mul_le_mul hc (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.mul_le_mul_left 18 (Nat.pow_le_pow_left hside 2)) 6) 3)

end
end TranslationTiling.Compiler.Size
