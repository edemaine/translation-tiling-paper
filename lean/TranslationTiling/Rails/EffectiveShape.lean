import TranslationTiling.Rails.SlotPorts
import TranslationTiling.FourLayer.EffectiveShape

namespace TranslationTiling.Rails
open FourLayer (gridMap Rect dent TableValid tablePermutation boxFinset mem_boxFinset)
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

@[fun_prop] theorem intDiv_primrec (d : ℕ) (hd : 0<d) : Primrec (fun z : ℤ => z/(d:ℤ)) := by
  apply (LeanWang.Kari.SignedPrimrec.intCasesOn Primrec.id
    (show Primrec (fun z : ℤ×ℕ => ((z.2/d : ℕ):ℤ)) by fun_prop |>.to₂)
    (show Primrec (fun z : ℤ×ℕ => -((z.2/d : ℕ):ℤ)-1) by fun_prop |>.to₂)).of_eq
  intro z
  cases z with
  | ofNat n => rfl
  | negSucc n =>
    change -((n/d:ℕ):ℤ)-1=Int.negSucc n/(d:ℤ)
    rw [Int.negSucc_ediv n (by exact_mod_cast hd)]
    push_cast
    ring
    rfl

@[fun_prop] theorem point_primrec : Primrec (fun z : ℤ×ℤ×ℤ => point z.1 z.2.1 z.2.2) := by
  apply piValue
  intro i; fin_cases i <;> simp only [point,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> fun_prop

@[fun_prop] theorem rail_primrec : Primrec (fun z : (ℕ×ℕ)×(ℤ×ℤ) => rail z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hd := intDiv_primrec 7 (by decide)
  unfold rail
  fun_prop

def smallCode (a : ℕ) (p q : List ℕ) (x y z : ℤ) : ℕ :=
  if z=1 then y.toNat%a else if z=2 then x.toNat%a
  else if z=3 then if x<(a:ℤ) then y.toNat%a else p.getD (y.toNat%a) 0
  else if y<(a:ℤ) then x.toNat%a else q.getD (x.toNat%a) 0

def colorCode (a B : ℕ) (p q : List ℕ) (v : Lattice 3) : ℕ :=
  if v 2=0 then if v 1=0 then 0 else rail a B (v 0) 0
  else if v 2=7 then rail a B (v 0) 7
  else if 4*(a:ℤ)≤v 0 ∧ v 1=2*(a:ℤ) then rail a B (v 0) (v 2)
  else smallCode a p q (v 0) (v 1) (v 2)

@[fun_prop] theorem colorCode_primrec :
    Primrec (fun z : (ℕ×ℕ×List ℕ×List ℕ)×Lattice 3 => colorCode z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  unfold colorCode smallCode rail
  have hd := intDiv_primrec 7 (by decide)
  fun_prop

theorem colorCode_eq (a B : ℕ) [NeZero a] [NeZero B] (p q : List ℕ)
    (hp : TableValid a p) (hq : TableValid a q) (v : Lattice 3) :
    colorCode a B p q v=color a B (tablePermutation a p hp) (tablePermutation a q hq) v := by
  unfold colorCode color smallCode small
  split_ifs <;> rfl

@[fun_prop] theorem scales_primrec : Primrec (fun z : ℕ×ℕ => scales z.1 z.2) := by
  apply piValue
  intro i
  fin_cases i
  · change Primrec (fun z : ℕ×ℕ => 3*(4*z.1+7*(z.2+1)+1)); fun_prop
  · change Primrec (fun z : ℕ×ℕ => 3*(4*z.1+1)); fun_prop
  · exact Primrec.const 24

@[fun_prop] theorem block_primrec : Primrec block := by
  apply piValue
  intro i
  exact (intDiv_primrec 3 (by decide)).comp (by fun_prop)

def slotCode (X : Tile 3) (i : ℕ) : Lattice 3 :=
  if i<X.length then X.getD i 0 else point 0 0 (i-X.length)

@[fun_prop] theorem slotCode_primrec : Primrec (fun z : Tile 3×ℕ => slotCode z.1 z.2) := by
  unfold slotCode
  fun_prop

theorem slotCode_plane (A i : ℕ) : slotCode (planeList A) i=slot A i := rfl

def residueList (a B : ℕ) : Tile 3 :=
  (Kim.cube (max (3*lengthX a B) (max (3*lengthY a) 24))).filter (fun r => decide (Rect (scales a B) r))

@[fun_prop] theorem residueList_primrec : Primrec (fun z : ℕ×ℕ => residueList z.1 z.2) := by
  unfold residueList lengthX lengthY
  exact filterList (by fun_prop) (FourLayer.rect_primrec.comp (show Primrec (fun z : (ℕ×ℕ)×Lattice 3 => (scales z.1.1 z.1.2,z.2)) by fun_prop))

theorem residueList_mem (a B : ℕ) (r : Lattice 3) : r∈residueList a B ↔ Rect (scales a B) r := by
  simp only [residueList,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  intro hr
  apply (Kim.mem_cube_iff _ _).mpr
  intro i
  have h := hr i
  fin_cases i <;> simp [scales,widths] at h ⊢ <;> omega

def shapeCode (X : Tile 3) (B : ℕ) (p q : List ℕ) (r : Lattice 3) : Lattice 3 :=
  if r=dent (scales X.length B) 0 then Kim.bumpAt 0
  else if r=dent (scales X.length B) 1 then Kim.bumpAt 1
  else if r=dent (scales X.length B) 2 then Kim.bumpAt 2
  else gridMap (scales X.length B) (slotCode X (colorCode X.length B p q (block r)))+r

@[fun_prop] theorem shapeCode_primrec :
    Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => shapeCode z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  unfold shapeCode
  have hd (i : Fin 3) : Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => dent (scales z.1.1.length z.1.2.1) i) := by unfold dent; fun_prop
  have he (i : Fin 3) : PrimrecPred (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => z.2=dent (scales z.1.1.length z.1.2.1) i) := equalValues Primrec.snd (hd i)
  have hco : Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => colorCode z.1.1.length z.1.2.1 z.1.2.2.1 z.1.2.2.2 (block z.2)) :=
    colorCode_primrec.comp (show Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => ((z.1.1.length,z.1.2.1,z.1.2.2.1,z.1.2.2.2),block z.2)) by fun_prop)
  have hslot : Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => slotCode z.1.1 (colorCode z.1.1.length z.1.2.1 z.1.2.2.1 z.1.2.2.2 (block z.2))) := slotCode_primrec.comp ((show Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => z.1.1) by fun_prop).pair hco)
  have hscale : Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => scales z.1.1.length z.1.2.1) := scales_primrec.comp (show Primrec (fun z : (Tile 3×ℕ×List ℕ×List ℕ)×Lattice 3 => (z.1.1.length,z.1.2.1)) by fun_prop)
  have hbody := Compiler.latticePlus (FourLayer.gridMap_primrec.comp (hscale.pair hslot)) Primrec.snd
  exact iteValue (he 0) (Primrec.const _) (iteValue (he 1) (Primrec.const _) (iteValue (he 2) (Primrec.const _) hbody))

theorem shapeCode_eq (X : Tile 3) (B : ℕ) [NeZero X.length] [NeZero B] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) (r : Lattice 3) :
    shapeCode X B p q r=modified X.length B (slotCode X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) r := by
  unfold shapeCode modified relocate
  simp only [colorCode_eq X.length B p q hp hq]

def shapeList (X : Tile 3) (B : ℕ) (p q : List ℕ) : Tile 3 :=
  ((residueList X.length B).map (shapeCode X B p q)).dedup

@[fun_prop] theorem shapeList_primrec :
    Primrec (fun z : Tile 3×ℕ×List ℕ×List ℕ => shapeList z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold shapeList
  exact dedup_primrec.comp (by fun_prop)

theorem shapeList_mem (X : Tile 3) (B : ℕ) [NeZero X.length] [NeZero B] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) (v : Lattice 3) :
    v∈shapeList X B p q ↔ v∈Shape X.length B (slotCode X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) := by
  simp only [shapeList,List.mem_dedup,List.mem_map,shapeCode_eq X B p q hp hq,residueList_mem,Shape,Set.mem_range]
  constructor
  · rintro ⟨r,hr,he⟩; exact ⟨⟨r,hr⟩,he⟩
  · rintro ⟨r,he⟩; exact ⟨r.val,r.property,he⟩

theorem shapeList_length_le (X : Tile 3) (B : ℕ) [NeZero X.length] [NeZero B] (p q : List ℕ)
    (hp : TableValid X.length p) (hq : TableValid X.length q) :
    (shapeList X B p q).length≤216*(lengthX X.length B)*(lengthY X.length) := by
  have he : (shapeList X B p q).toFinset=shapeFinset X.length B (slotCode X) (tablePermutation X.length p hp) (tablePermutation X.length q hq) := by
    ext v; simp only [List.mem_toFinset,shapeList_mem X B p q hp hq,mem_shapeFinset]
  have hn : (shapeList X B p q).Nodup := List.nodup_dedup _
  rw [←List.toFinset_card_of_nodup hn,he]
  exact shape_card_le _ _ _ _ _

end
end TranslationTiling.Rails
