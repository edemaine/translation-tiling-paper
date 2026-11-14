import TranslationTiling.Compiler.ClosedGeometryBound

/-! A fixed small connected nontile handles the empty Wang input. -/
namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem empty_wang_not_tiles : ¬ LeanWang.TilesPlane [] := by
  rintro ⟨x,_⟩
  exact List.not_mem_nil (x (0,0)).property

theorem exists_small_nontile : ∃ P : Tile 3,
    P ≠ [] ∧ FaceConnected P ∧ ¬ TranslationTiling.Tiles P ∧ cubeCount P ≤ 2 ^ 250 := by
  let F : Fin 2 → Finset Plane := fun i => if i = 0 then {0} else {0,(1,0)}
  have hF : ∀ i, (F i).Nonempty := by intro i; unfold F; split_ifs <;> simp
  have hfalse : ¬ ∃ A : Set Plane, ∀ i, Stacking.Covers (F i) A := by
    rintro ⟨A,hA⟩
    have hall : ∀ x : Plane, x ∈ A := by
      intro x
      obtain ⟨f,hf,_⟩ := Stacking.covers_iff_unique_tile.mp (hA 0) x
      have he : f.val = 0 := Finset.mem_singleton.mp f.property
      simpa [he] using hf
    obtain ⟨f,_,hu⟩ := Stacking.covers_iff_unique_tile.mp (hA 1) 0
    have hz : (0 : Plane) ∈ F 1 := by simp [F]
    have he : (1,0) ∈ F 1 := by simp [F]
    have heq : (⟨0,hz⟩ : ↥(F 1)) = ⟨(1,0),he⟩ :=
      (hu ⟨0,hz⟩ (hall _)).trans (hu ⟨(1,0),he⟩ (hall _)).symm
    have h := congrArg (fun z : ↥(F 1) => z.val.1) heq
    norm_num at h
  obtain ⟨q,hq,hql,hqu⟩ := Nat.bertrand 260 (by decide)
  letI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨E,hpart,hfull⟩ := partition_at_prime 2 q (by decide) hq (by norm_num at *; omega)
  let S := Stacking.stack F E
  have hS : S.Nonempty := Stacking.stack_nonempty hF hfull.nonempty
  have hs : LeanWang.TilesPlane [] ↔ ∃ A, Tiles S A := by
    have ht := Stacking.exists_tiles_stack_iff (F := F) hpart hfull hfull.nonempty
    constructor
    · exact fun h => (empty_wang_not_tiles h).elim
    · intro h
      exact (hfalse (ht.mpr h)).elim
  have hcoord : ∀ f ∈ S, f.1.1.natAbs ≤ 1 ∧ f.1.2.natAbs ≤ 1 := by
    intro f hf
    obtain ⟨i,hi,_⟩ := Stacking.mem_stack.mp hf
    fin_cases i <;> simp [F] at hi
    · rw [hi]; norm_num
    · rcases hi with hi | hi <;> rw [hi] <;> norm_num
  obtain ⟨P,hP,hconn,hiff,hsize⟩ := exists_bounded_connected_tile hq.pos
    (by omega : q ≤ 520) S hS hs hcoord
  refine ⟨P,hP,hconn,fun ht => empty_wang_not_tiles (hiff.mpr ht),hsize.trans ?_⟩
  norm_num [geometryCap,latticeSide,latticeRadius]

def emptyTile : Tile 3 := (Classical.choose exists_small_nontile).dedup

theorem emptyTile_facts : emptyTile ≠ [] ∧ FaceConnected emptyTile ∧
    ¬ TranslationTiling.Tiles emptyTile ∧ emptyTile.length ≤ 2 ^ 250 := by
  obtain ⟨hn,hc,ht,hb⟩ := Classical.choose_spec exists_small_nontile
  refine ⟨(List.dedup_eq_nil _).not.mpr hn,?_,?_,?_⟩
  · simpa only [emptyTile,FaceConnected,List.mem_dedup] using hc
  · intro he
    exact ht ((tiles_of_same_members (by intro f; exact List.mem_dedup)).mp he)
  · simpa only [emptyTile,cubeCount,List.card_toFinset] using hb

end
end TranslationTiling.Compiler.Size
