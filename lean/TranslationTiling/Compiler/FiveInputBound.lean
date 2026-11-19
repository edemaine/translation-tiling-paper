import TranslationTiling.Compiler.FiveTileInputs
import TranslationTiling.Compiler.SingleInputBound
import TranslationTiling.Compiler.FiniteNormalizedInput

namespace TranslationTiling.Compiler.FiveTile
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

theorem labels_index {T : LeanWang.TileSet} (hn : T.length≤5) {t : LeanWang.WangTile} (ht : t∈T) :
    labels T ⟨T.idxOf t,lt_of_lt_of_le (List.idxOf_lt_length_of_mem ht) hn⟩=t := by
  unfold labels
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem ht),List.getElem_idxOf]

def matching (f g : Letter → ℕ) : Matrix := fun a b => decide (f a=g b)

theorem matching_rectangular (f g : Letter → ℕ) : Rectangular (matching f g) := by
  intro a b c d ha hb
  have he : f a=f b := (of_decide_eq_true ha).trans (of_decide_eq_true hb).symm
  simp only [matching,he]

def horizontal (T : LeanWang.TileSet) : Matrix :=
  matching (fun i => (labels T i).e) (fun i => (labels T i).w)
def vertical (T : LeanWang.TileSet) : Matrix :=
  matching (fun i => (labels T i).n) (fun i => (labels T i).s)

private def pack : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 1 else 0)+2*pack bs

def matrixCode (r : Matrix) : ℕ :=
  pack (List.ofFn fun i : Fin 25 =>
    r ⟨i.val/5,by have := i.isLt; omega⟩ ⟨i.val%5,Nat.mod_lt _ (by decide)⟩)

private theorem pack_bit (l : List Bool) (i : ℕ) (hi : i<l.length) :
    (pack l).testBit i=l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    cases i with
    | zero => cases b <;> simp [pack,Nat.testBit_zero,Nat.add_mod]
    | succ i =>
      have h := ih i (by simpa using hi)
      rw [Nat.testBit_succ]
      have he : pack (b::l)/2=pack l := by cases b <;> simp only [pack,Bool.false_eq_true,ite_false,ite_true] <;> omega
      rw [he]
      exact h

theorem matrixCode_edge (r : Matrix) (a b : Letter) : edge (matrixCode r) a b=r a b := by
  have ha := a.isLt
  have hb := b.isLt
  have h : 5*a.val+b.val<25 := by omega
  have h1 : (5*a.val+b.val)/5=a.val := by omega
  have h2 : (5*a.val+b.val)%5=b.val := by omega
  unfold edge matrixCode
  rw [pack_bit _ _ (by simpa using h)]
  rw [List.getElem_ofFn]
  simp only [h1,h2,Fin.eta]

def accepts (T : LeanWang.TileSet) : Prop :=
  ∃ f : Fin 11 → Fin 11 → Letter,
    Patch (matrixCode (horizontal T)) (vertical T) (fun x y => f ⟨x%11,Nat.mod_lt _ (by decide)⟩ ⟨y%11,Nat.mod_lt _ (by decide)⟩)

variable (classification : ∀ {H : ℕ} {V : Matrix} {W : ℕ → ℕ → Letter},
  Rectangular (edge H) → Rectangular V → Patch H V W → Plane H V)

include classification in
theorem accepts_iff (T : LeanWang.TileSet) (hn : T≠[]) (hsize : T.length≤5) :
    accepts T ↔ LeanWang.TilesPlane T := by
  constructor
  · rintro ⟨f,hf⟩
    have hH : Rectangular (edge (matrixCode (horizontal T))) := by
      unfold Rectangular
      simp only [matrixCode_edge]
      exact matching_rectangular
        (fun i => (labels T i).e) (fun i => (labels T i).w)
    obtain ⟨a,ha⟩ := classification hH (matching_rectangular _ _) hf
    refine ⟨fun p => ⟨labels T (a p),labels_mem T hn _⟩,?_,?_⟩
    · intro p
      have h := (ha p).1
      rw [matrixCode_edge] at h
      exact of_decide_eq_true h
    · intro p
      exact of_decide_eq_true (ha p).2
  · rintro ⟨x,hvalid⟩
    let a : ℤ×ℤ → Letter := fun p => ⟨T.idxOf (x p).val,
      lt_of_lt_of_le (List.idxOf_lt_length_of_mem (x p).property) hsize⟩
    have he (p : ℤ×ℤ) : labels T (a p)=(x p).val := labels_index hsize (x p).property
    refine ⟨fun i j => a (i.val,j.val),?_,?_⟩
    · intro i j hi hj
      simp only [Nat.mod_eq_of_lt (show i<11 by omega),Nat.mod_eq_of_lt hi,
        Nat.mod_eq_of_lt hj,matrixCode_edge,horizontal,matching,decide_eq_true_eq]
      rw [he,he]
      simpa only [Nat.cast_add,Nat.cast_one,LeanWang.WangTile.HMatches] using hvalid.1 ((i:ℤ),(j:ℤ))
    · intro i j hi hj
      simp only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (show j<11 by omega),
        Nat.mod_eq_of_lt hj,vertical,matching,decide_eq_true_eq]
      rw [he,he]
      simpa only [Nat.cast_add,Nat.cast_one,LeanWang.WangTile.VMatches] using hvalid.2 ((i:ℤ),(j:ℤ))

/-- Check both neighbor constraints on a finite square. -/
def finitePatch (T : LeanWang.TileSet) (f : Fin 11 → Fin 11 → Letter) : Prop :=
  (∀ x : Fin 10, ∀ y : Fin 11, horizontal T (f x.castSucc y) (f x.succ y)=true) ∧
  (∀ x : Fin 11, ∀ y : Fin 10, vertical T (f x y.castSucc) (f x y.succ)=true)

instance (T : LeanWang.TileSet) (f : Fin 11 → Fin 11 → Letter) : Decidable (finitePatch T f) := by
  unfold finitePatch
  infer_instance

def hasPatch (T : LeanWang.TileSet) : Prop := ∃ f, finitePatch T f

instance (T : LeanWang.TileSet) : Decidable (hasPatch T) := by
  unfold hasPatch
  infer_instance

theorem hasPatch_iff_accepts (T : LeanWang.TileSet) : hasPatch T ↔ accepts T := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_,?_⟩
    · intro x y hx hy
      have h := hf.1 ⟨x,by omega⟩ ⟨y,hy⟩
      simpa only [Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.eta,matrixCode_edge,Nat.mod_eq_of_lt (show x<11 by omega),
        Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using h
    · intro x y hx hy
      have h := hf.2 ⟨x,hx⟩ ⟨y,by omega⟩
      simpa only [Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.eta,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt (show y<11 by omega),
        Nat.mod_eq_of_lt hy] using h
  · rintro ⟨f,hf⟩
    refine ⟨f,?_,?_⟩
    · intro x y
      have h := hf.1 x.val y.val (by have := x.isLt; omega) y.isLt
      have hx := x.isLt
      simpa only [Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.eta,matrixCode_edge,
        Nat.mod_eq_of_lt (show x.val<11 by omega),
        Nat.mod_eq_of_lt (show x.val+1<11 by omega),Nat.mod_eq_of_lt y.isLt] using h
    · intro x y
      have h := hf.2 x.val y.val x.isLt (by have := y.isLt; omega)
      have hy := y.isLt
      simpa only [Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.eta,Nat.mod_eq_of_lt x.isLt,
        Nat.mod_eq_of_lt (show y.val<11 by omega),
        Nat.mod_eq_of_lt (show y.val+1<11 by omega)] using h

def rawTile (T : LeanWang.TileSet) : Tile 3 :=
  if hasPatch T then [0] else Size.emptyTile

include classification in
theorem rawTile_facts (T : LeanWang.TileSet) (hn : T≠[]) (hsize : T.length≤5) :
    rawTile T≠[] ∧ FaceConnected (rawTile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (rawTile T)) ∧
    (rawTile T).length≤2^250 := by
  have he := (hasPatch_iff_accepts T).trans (accepts_iff classification T hn hsize)
  by_cases ha : hasPatch T
  · simp only [rawTile,if_pos ha]
    refine ⟨by simp,?_,iff_of_true (he.mp ha) (tiles_singleton 0),by norm_num⟩
    intro p hp q hq
    have hp' : p=0 := List.mem_singleton.mp hp
    have hq' : q=0 := List.mem_singleton.mp hq
    rw [hp',hq']
  · simp only [rawTile,if_neg ha]
    obtain ⟨hne,hc,ht,hb⟩ := Size.emptyTile_facts
    exact ⟨hne,hc,iff_of_false (fun h => ha (he.mpr h)) ht,hb⟩

def compile (n : ℕ) (hn : 0<n) (T : LeanWang.TileSet) : Tile 3 :=
  rawTile (Size.decodeInput n (Size.inputIndex n hn T))

theorem compile_computable (n : ℕ) (hn : 0<n) : Computable (compile n hn) :=
  (Effective.finFunction_primrec (fun i : Fin (Size.inputs n).length => rawTile (Size.decodeInput n i))).to_comp.comp
    (Size.inputIndex_primrec n hn).to_comp

include classification in
theorem compile_facts (n : ℕ) (hn : 0<n) (hsmall : n≤5)
    (T : LeanWang.TileSet) (hlen : T.length=n) :
    compile n hn T≠[] ∧ FaceConnected (compile n hn T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compile n hn T)) ∧
    (compile n hn T).length≤2^250 := by
  have hlen' : (Size.normalize T).length=n := by simpa using hlen
  have hne : Size.normalize T≠[] := List.length_pos_iff_ne_nil.mp (by omega)
  obtain ⟨h0,h1,h2,h3⟩ := rawTile_facts classification (Size.normalize T) hne (by omega)
  unfold compile
  rw [Size.decodeInput_index n hn T hlen]
  exact ⟨h0,h1,(Size.normalize_tilesPlane T).symm.trans h2,h3⟩

end
end TranslationTiling.Compiler.FiveTile
