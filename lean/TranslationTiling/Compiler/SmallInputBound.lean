import TranslationTiling.Compiler.SmallTilePeriodicity
import TranslationTiling.Compiler.FiniteNormalizedInput

namespace TranslationTiling.Compiler.SmallTile
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def labels (T : LeanWang.TileSet) (i : Letter) : LeanWang.WangTile :=
  T.getD i.val (T.getD 0 ⟨0,0,0,0⟩)

theorem labels_mem (T : LeanWang.TileSet) (hn : T≠[]) (i : Letter) : labels T i∈T := by
  cases T with
  | nil => exact (hn rfl).elim
  | cons t ts =>
    unfold labels
    rw [List.getD_cons_zero]
    by_cases hi : i.val<(t::ts).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem labels_index {T : LeanWang.TileSet} (hn : T.length≤3) {t : LeanWang.WangTile} (ht : t∈T) :
    labels T ⟨T.idxOf t,lt_of_lt_of_le (List.idxOf_lt_length_of_mem ht) hn⟩=t := by
  unfold labels
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem ht),List.getElem_idxOf]

def accepts (T : LeanWang.TileSet) : Prop :=
  Accepted (matrixCode (horizontal (labels T))) (matrixCode (verticalMatrix (labels T)))

instance (T : LeanWang.TileSet) : Decidable (accepts T) := by unfold accepts; infer_instance

theorem accepts_iff (T : LeanWang.TileSet) (hn : T≠[]) (hsize : T.length≤3) :
    accepts T ↔ LeanWang.TilesPlane T := by
  constructor
  · intro hc
    obtain ⟨a,ha⟩ := accepted_plane hc
    refine ⟨fun p => ⟨labels T (a p),labels_mem T hn _⟩,?_,?_⟩
    · intro p
      have h := (ha p).1
      rw [matrixCode_edge] at h
      exact of_decide_eq_true h
    · intro p
      have h := (ha p).2
      rw [matrixCode_edge] at h
      exact of_decide_eq_true h
  · rintro ⟨x,hvalid⟩
    let a : ℤ×ℤ → Letter := fun p => ⟨T.idxOf (x p).val,
      lt_of_lt_of_le (List.idxOf_lt_length_of_mem (x p).property) hsize⟩
    have he (p : ℤ×ℤ) : labels T (a p)=(x p).val := labels_index hsize (x p).property
    let patch : Fin 4 → Fin 4 → Letter := fun y z => a (z.val,y.val)
    apply matrix_patch_accepted (matching_rectangular _ _) (matching_rectangular _ _) (a:=patch)
    · intro y z
      simp only [horizontal,matching,decide_eq_true_eq]
      dsimp only [patch]
      rw [he,he]
      simpa only [Nat.cast_add,Nat.cast_one,LeanWang.WangTile.HMatches] using hvalid.1 ((z.val:ℤ),(y.val:ℤ))
    · intro y z
      simp only [verticalMatrix,matching,decide_eq_true_eq]
      dsimp only [patch]
      rw [he,he]
      simpa only [Nat.cast_add,Nat.cast_one,LeanWang.WangTile.VMatches] using hvalid.2 ((z.val:ℤ),(y.val:ℤ))

def rawTile (T : LeanWang.TileSet) : Tile 3 := by
  letI : Decidable (accepts T) := Classical.propDecidable _
  exact if accepts T then [0] else Size.emptyTile

theorem rawTile_facts (T : LeanWang.TileSet) (hn : T≠[]) (hsize : T.length≤3) :
    rawTile T≠[] ∧ FaceConnected (rawTile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (rawTile T)) ∧
    (rawTile T).length≤2^250 := by
  by_cases ha : accepts T
  · simp only [rawTile,if_pos ha]
    refine ⟨by simp,?_,iff_of_true ((accepts_iff T hn hsize).mp ha) (tiles_singleton 0),by norm_num⟩
    intro p hp q hq
    have hp' : p=0 := List.mem_singleton.mp hp
    have hq' : q=0 := List.mem_singleton.mp hq
    rw [hp',hq']
  · simp only [rawTile,if_neg ha]
    obtain ⟨hne,hc,ht,hb⟩ := Size.emptyTile_facts
    exact ⟨hne,hc,iff_of_false (fun h => ha ((accepts_iff T hn hsize).mpr h)) ht,hb⟩

def compile (n : ℕ) (hn : 0<n) (T : LeanWang.TileSet) : Tile 3 :=
  rawTile (Size.decodeInput n (Size.inputIndex n hn T))

theorem compile_computable (n : ℕ) (hn : 0<n) : Computable (compile n hn) :=
  (Effective.finFunction_primrec (fun i : Fin (Size.inputs n).length => rawTile (Size.decodeInput n i))).to_comp.comp
    (Size.inputIndex_primrec n hn).to_comp

theorem compile_facts (n : ℕ) (hn : 0<n) (hsmall : n≤3)
    (T : LeanWang.TileSet) (hlen : T.length=n) :
    compile n hn T≠[] ∧ FaceConnected (compile n hn T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compile n hn T)) ∧
    (compile n hn T).length≤2^250 := by
  have hlen' : (Size.normalize T).length=n := by simpa using hlen
  have hne : Size.normalize T≠[] := List.length_pos_iff_ne_nil.mp (by omega)
  obtain ⟨h0,h1,h2,h3⟩ := rawTile_facts (Size.normalize T) hne (by omega)
  unfold compile
  rw [Size.decodeInput_index n hn T hlen]
  exact ⟨h0,h1,(Size.normalize_tilesPlane T).symm.trans h2,h3⟩

end
end TranslationTiling.Compiler.SmallTile
