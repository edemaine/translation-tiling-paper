import TranslationTiling.FourLayer.EffectiveBoundary
import TranslationTiling.FourLayer.Geometry

namespace TranslationTiling.FourLayer
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def colorCode (m : ℕ) (p q : List ℕ) (v : Lattice 3) : ℕ :=
  if v 2=0 then (v 1).toNat%m
  else if v 2=1 then (v 0).toNat%m
  else if v 2=2 then if v 0<m then (v 1).toNat%m else p.getD ((v 1).toNat%m) 0
  else if v 1<m then (v 0).toNat%m else q.getD ((v 0).toNat%m) 0

@[fun_prop] theorem colorCode_primrec :
    Primrec (fun z : (ℕ×List ℕ×List ℕ)×Lattice 3 => colorCode z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  unfold colorCode; fun_prop

theorem colorCode_eq (m : ℕ) [NeZero m] (p q : List ℕ) (hp : TableValid m p) (hq : TableValid m q) (v : Lattice 3) :
    colorCode m p q v=(color m (tablePermutation m p hp) (tablePermutation m q hq) v).val := by
  unfold colorCode color
  split_ifs <;> rfl

@[fun_prop] theorem scales_primrec : Primrec scales := by
  apply piValue
  intro i
  fin_cases i
  · change Primrec (fun m : ℕ => 3*(2*m+1)); fun_prop
  · change Primrec (fun m : ℕ => 3*(2*m+1)); fun_prop
  · exact Primrec.const 12

@[fun_prop] theorem gridMap_primrec : Primrec (fun z : (Fin 3→ℕ)×Lattice 3 => gridMap z.1 z.2) := by
  apply piValue
  intro i
  change Primrec (fun z : (Fin 3→ℕ)×Lattice 3 => (z.1 i:ℤ)*z.2 i)
  fun_prop

@[fun_prop] theorem dent_primrec (i : Fin 3) : Primrec (fun m => dent (scales m) i) := by
  unfold dent; fun_prop

@[fun_prop] theorem rect_primrec : PrimrecPred (fun z : (Fin 3→ℕ)×Lattice 3 => Rect z.1 z.2) := by
  simp [Rect,Fin.forall_fin_succ]
  fun_prop

def residueList (m : ℕ) : Tile 3 :=
  (Kim.cube (max (3*(2*m+1)) 12)).filter (fun r => decide (Rect (scales m) r))

@[fun_prop] theorem residueList_primrec : Primrec residueList := by
  unfold residueList
  exact filterList (by fun_prop) (rect_primrec.comp (show Primrec (fun z : ℕ×Lattice 3 => (scales z.1,z.2)) by fun_prop))

theorem residueList_mem (m : ℕ) (r : Lattice 3) : r∈residueList m ↔ Rect (scales m) r := by
  simp only [residueList,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  intro hr
  apply (Kim.mem_cube_iff _ _).mpr
  intro i
  have h := hr i
  fin_cases i <;> simp [scales,widths] at h ⊢ <;> omega

def shapeCode (X : Tile 3) (p q : List ℕ) (r : Lattice 3) : Lattice 3 :=
  if r=dent (scales X.length) 0 then Kim.bumpAt 0
  else if r=dent (scales X.length) 1 then Kim.bumpAt 1
  else if r=dent (scales X.length) 2 then Kim.bumpAt 2
  else gridMap (scales X.length) (X.getD (colorCode X.length p q (fun i => r i/3)) 0)+r

@[fun_prop] theorem shapeCode_primrec :
    Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 => shapeCode z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hb : Primrec (fun r : Lattice 3 => (fun i => r i/3 : Lattice 3)) := by
    apply piValue
    intro i
    have hd : Primrec (fun z : ℤ => z/3) := by
      apply (LeanWang.Kari.SignedPrimrec.intCasesOn Primrec.id
        (show Primrec (fun z : ℤ×ℕ => ((z.2/3 : ℕ):ℤ)) by fun_prop |>.to₂)
        (show Primrec (fun z : ℤ×ℕ => -((z.2/3 : ℕ):ℤ)-1) by fun_prop |>.to₂)).of_eq
      intro z
      cases z with
      | ofNat n => rfl
      | negSucc n =>
        change -((n/3:ℕ):ℤ)-1=Int.negSucc n/3
        rw [Int.negSucc_ediv n (by norm_num : (0:ℤ)<3)]
        push_cast
        ring
        rfl
    exact hd.comp (by fun_prop)
  have hd (i : Fin 3) : Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 => dent (scales z.1.1.length) i) :=
    (dent_primrec i).comp (by fun_prop)
  have he (i : Fin 3) : PrimrecPred (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 => z.2=dent (scales z.1.1.length) i) :=
    equalValues Primrec.snd (hd i)
  have hco : Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 =>
      colorCode z.1.1.length z.1.2.1 z.1.2.2 (fun i => z.2 i/3)) :=
    colorCode_primrec.comp ((show Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 =>
      (z.1.1.length,z.1.2.1,z.1.2.2)) by fun_prop).pair (hb.comp Primrec.snd))
  have hget := (Primrec.list_getD (0 : Lattice 3)).comp (show Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 => z.1.1) by fun_prop) hco
  have hbody := Compiler.latticePlus (gridMap_primrec.comp ((scales_primrec.comp
    (show Primrec (fun z : (Tile 3×List ℕ×List ℕ)×Lattice 3 => z.1.1.length) by fun_prop)).pair hget)) Primrec.snd
  exact iteValue (he 0) (Primrec.const _) (iteValue (he 1) (Primrec.const _) (iteValue (he 2) (Primrec.const _) hbody))

theorem shapeCode_eq (X : Tile 3) [NeZero X.length] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) (r : Lattice 3) :
    shapeCode X p q r=modified X.length (slots X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) r := by
  unfold shapeCode modified
  split_ifs <;> try rfl
  simp only [relocate,slots,← colorCode_eq]
  rfl

def shapeList (X : Tile 3) (p q : List ℕ) : Tile 3 :=
  ((residueList X.length).map (shapeCode X p q)).dedup

@[fun_prop] theorem shapeList_primrec :
    Primrec (fun z : Tile 3×List ℕ×List ℕ => shapeList z.1 z.2.1 z.2.2) := by
  unfold shapeList
  exact dedup_primrec.comp (by fun_prop)

theorem shapeList_finset (X : Tile 3) [NeZero X.length] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) :
    (shapeList X p q).toFinset=shapeFinset X.length (slots X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) := by
  ext v
  simp only [shapeList,List.mem_toFinset,List.mem_dedup,List.mem_map,shapeCode_eq X p q hp hq,
    shapeFinset,Finset.mem_image,mem_boxFinset,residueList_mem]

@[simp] theorem shapeList_mem (X : Tile 3) [NeZero X.length] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) (v : Lattice 3) :
    v∈shapeList X p q ↔ v∈Shape X.length (slots X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) := by
  rw [← List.mem_toFinset,shapeList_finset X p q hp hq,mem_shapeFinset]

theorem shapeList_length_le (X : Tile 3) [NeZero X.length] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) :
    (shapeList X p q).length≤972*X.length^2 := by
  have hn : (shapeList X p q).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hn,shapeList_finset X p q hp hq]
  exact shape_card_le _ _ _ _

end
end TranslationTiling.FourLayer
