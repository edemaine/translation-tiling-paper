import TranslationTiling.Compiler.ClosedStackBound
import TranslationTiling.Compiler.GeometricSizeBound
import TranslationTiling.MSS.FrameGeometry

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical
noncomputable section

theorem natAbs_le_of_bounds {z : ℤ} {r : ℕ} (h : -(r : ℤ) ≤ z ∧ z ≤ r) : z.natAbs ≤ r := by
  rcases Int.natAbs_eq z with hz | hz <;> omega

theorem mss_base_coordinate_bound {v : Lattice 3} (hv : v ∈ MSS.baseShape) (i : Fin 3) :
    (v i).natAbs ≤ 400 := by
  obtain ⟨j, hj⟩ := MSS.baseShape_bounds v hv
  have h := hj i
  apply natAbs_le_of_bounds
  fin_cases j <;> fin_cases i <;> simp [MSS.bodyCenter, MSS.bodyRadius] at h ⊢ <;> omega

theorem mss_component_coordinate_bound (m j : ℕ) (hj : j ≤ 5)
    {v : Lattice 3} (hv : v ∈ MSS.component m j) (i : Fin 3) :
    (v i).natAbs ≤ 201 * m + 1000 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · have h := mss_base_coordinate_bound (Finset.mem_sdiff.mp hv).1 i
    omega
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have h := (MSS.mem_box_iff j u).mp (Finset.mem_sdiff.mp hu).1 i
    have hjz : (j : ℤ) ≤ 5 := by exact_mod_cast hj
    apply natAbs_le_of_bounds
    fin_cases i <;>
      simp [MSS.kernelStep, MSS.marker, Pi.add_apply] at h ⊢ <;>
      omega

theorem coordinateBound_le_of_forall (E : Tile 3) (r : ℕ)
    (h : ∀ v ∈ E, ∀ i, (v i).natAbs ≤ r) : coordinateBound E ≤ r := by
  induction E with
  | nil => exact Nat.zero_le _
  | cons v E ih =>
    apply max_le
    · exact max_le (h v (by simp) 0) (max_le (h v (by simp) 1) (h v (by simp) 2))
    · exact ih (fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem cubeCount_le_cubeSize (E : Tile 3) : cubeCount E ≤ cubeSize E ^ 3 := by
  rw [← positiveTile_cubeCount]
  apply (Finset.card_le_card (show (positiveTile E).toFinset ⊆
      (Kim.cube (cubeSize E)).toFinset from fun x hx =>
    List.mem_toFinset.mpr (positiveTile_in_cube E x (List.mem_toFinset.mp hx)))).trans
  rw [Kim.cube_card]

def latticeRadius (H M : ℕ) : ℕ := 1000 * (2 * H + M + 1)
def latticeSide (H M : ℕ) : ℕ := 2 * latticeRadius H M + 3
def geometryCap (H M : ℕ) : ℕ :=
  latticeSide H M ^ 3 * (3 * latticeSide H M ^ 3 + 6) ^ 3

theorem connectedTile_geometryCap (E : Tile 3) (H M : ℕ)
    (h : coordinateBound E ≤ latticeRadius H M) :
    cubeCount (connectedTile E) ≤ geometryCap H M := by
  have hside : cubeSize E ≤ latticeSide H M := by unfold cubeSize latticeSide; omega
  apply (connectedTile_cubeCount_le E).trans
  unfold geometryCap
  apply Nat.mul_le_mul
  · exact (cubeCount_le_cubeSize E).trans (Nat.pow_le_pow_left hside 3)
  · gcongr

/-- The quotient-to-lattice step and connectedness step have polynomial volume
cost in the cyclic modulus and the horizontal coordinate bound. -/
theorem exists_bounded_connected_tile {T : LeanWang.TileSet} {m H M : ℕ}
    (hm : 0 < m) (hmM : m ≤ M) (F : Finset (Plane × ZMod m)) (hF : F.Nonempty)
    (hcorrect : LeanWang.TilesPlane T ↔ ∃ A, Tiles F A)
    (hcoord : ∀ f ∈ F, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ geometryCap H M := by
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨f₀, hf₀⟩ := hF
  let F₀ := F.image (fun f => f - f₀)
  have h0 : 0 ∈ F₀ := Finset.mem_image.mpr ⟨f₀, hf₀, sub_self f₀⟩
  let U := CyclicQuotient.representatives m F₀
  let G := LatticeGeometry.assembled m U
  have hU0 : 0 ∈ U := CyclicQuotient.zero_mem_representatives m h0
  have hG0 : 0 ∈ G := (LatticeGeometry.mem_assembled m U 0).mpr
    ⟨0, hU0, 0, LatticeGeometry.zero_mem_part m 0, by simp⟩
  have hU (u : Lattice 3) (hu : u ∈ U) (i : Fin 3) : (u i).natAbs ≤ 2 * H + M := by
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hgcoord := hcoord g hg
    have h₀coord := hcoord f₀ hf₀
    fin_cases i
    · change (g.1.1 - f₀.1.1).natAbs ≤ _
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.1 h₀coord.1)
      omega
    · change (g.1.2 - f₀.1.2).natAbs ≤ _
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.2 h₀coord.2)
      omega
    · change (((g - f₀).2.val : ℤ)).natAbs ≤ _
      rw [Int.natAbs_natCast]
      have h := ZMod.val_lt (g - f₀).2
      omega
  have hG (v : Lattice 3) (hv : v ∈ G) (i : Fin 3) : (v i).natAbs ≤ latticeRadius H M := by
    obtain ⟨u, hu, w, hw, rfl⟩ := (LatticeGeometry.mem_assembled m U v).mp hv
    have hwbound : (w i).natAbs ≤ 201 * m + 1000 := by
      by_cases hu0 : u = 0
      · exact mss_component_coordinate_bound m 5 (by decide) (by simpa [LatticeGeometry.part, hu0] using hw) i
      · exact mss_component_coordinate_bound m 4 (by decide) (by simpa [LatticeGeometry.part, hu0] using hw) i
    have hubound := hU u hu i
    have hscale : ((LatticeGeometry.scaleHom u) i).natAbs ≤ 201 * (2 * H + M) := by
      change ((201 : ℤ) * u i).natAbs ≤ _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left 201 hubound
    have h := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hscale hwbound)
    unfold latticeRadius
    change (((LatticeGeometry.scaleHom u) i) + w i).natAbs ≤ _
    omega
  have hbound : coordinateBound G.toList ≤ latticeRadius H M :=
    coordinateBound_le_of_forall _ _ (fun v hv => hG v (Finset.mem_toList.mp hv))
  have hlist : G.toList ≠ [] := by
    intro he
    have h : (0 : Lattice 3) ∈ G.toList := Finset.mem_toList.mpr hG0
    simp only [he, List.not_mem_nil] at h
  have hlistcorrect : (∃ A : Set (Lattice 3), Tiles G A) ↔
      TranslationTiling.Tiles G.toList := by
    simp only [Tiles, TranslationTiling.Tiles, Stacking.covers_iff_exactTiling]
    have he : {f : Lattice 3 | f ∈ G.toList} = (G : Set (Lattice 3)) := by
      ext f; exact Finset.mem_toList
    rw [he]
  have hshift : (∃ A, Tiles F A) ↔ ∃ A, Tiles F₀ A := by
    simpa only [F₀, sub_eq_add_neg] using exists_covers_shift_iff F (-f₀)
  have hGcorrect := hcorrect.trans (hshift.trans
    (LatticeGeometry.assembled_iff_quotient MSS.rigidity m hm F₀ h0))
  refine ⟨connectedTile G.toList, connectedTile_nonempty _ hlist,
    connectedTile_connected _, ?_, connectedTile_geometryCap _ H M hbound⟩
  exact (hGcorrect.trans hlistcorrect).trans (connectedTile_correct Kim.cosetRigidity _).symm

end
end TranslationTiling.Compiler.Size
