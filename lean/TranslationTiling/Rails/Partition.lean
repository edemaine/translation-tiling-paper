import TranslationTiling.FourLayer.Partition
import TranslationTiling.FourLayer.Rectangle

/-! An eight-layer partition with a short planar palette and a long rail. -/
namespace TranslationTiling.Rails
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable (a b : ℕ) [NeZero a] [NeZero b]

def lengthX := 4*a+7*(b+1)+1
def lengthY := 4*a+1
def widths : Fin 3→ℕ := ![lengthX a b,lengthY a,8]
def Box (v : Lattice 3) : Prop :=
  0≤v 0 ∧ v 0 < (lengthX a b:ℤ) ∧ 0≤v 1 ∧ v 1 < (lengthY a:ℤ) ∧ 0≤v 2 ∧ v 2≤7

def railLabel (i : ℕ) := if i=0 then 0 else a+i

def rail (x z : ℤ) : ℕ :=
  let i := (x-4*a-z)/7
  if 0 < i ∧ i < (b:ℤ) then a+i.toNat else 0

def small (p q : Equiv.Perm (Fin a)) (x y z : ℤ) : ℕ :=
  if z=1 then (FourLayer.band a y).val
  else if z=2 then (FourLayer.band a x).val
  else if z=3 then
    if x < (a:ℤ) then (FourLayer.band a y).val else (p (FourLayer.band a y)).val
  else if y < (a:ℤ) then (FourLayer.band a x).val else (q (FourLayer.band a x)).val

def color (p q : Equiv.Perm (Fin a)) (v : Lattice 3) : ℕ :=
  if v 2=0 then if v 1=0 then 0 else rail a b (v 0) 0
  else if v 2=7 then rail a b (v 0) 7
  else if 4*(a:ℤ)≤v 0 ∧ v 1=2*(a:ℤ) then rail a b (v 0) (v 2)
  else small a p q (v 0) (v 1) (v 2)

def Fiber (p q : Equiv.Perm (Fin a)) (i : ℕ) (v : Lattice 3) : Prop :=
  Box a b v ∧ color a b p q v=i

theorem box_iff (v : Lattice 3) : Box a b v ↔ FourLayer.Rect (widths a b) v := by
  simp [FourLayer.Rect,Fin.forall_fin_succ,widths,Box]
  omega

theorem widths_pos (k : Fin 3) : 0 < widths a b k := by
  fin_cases k  <;> simp [widths,lengthX,lengthY]  <;> omega

theorem rail_eq (i : Fin b) (x z : ℤ)
    (hx : 4*(a:ℤ)+z+7*i.val≤x) (hu : x < 4*(a:ℤ)+z+7*(i.val+1)) :
    rail a b x z=railLabel a i.val := by
  have hi : (x-4*a-z)/7=(i.val:ℤ) := by omega
  rw [rail,hi]
  simp only [Int.toNat_natCast,railLabel]
  by_cases h : i.val=0
  · simp [h]
  · rw [if_pos (by have := i.isLt; constructor  <;> omega),if_neg h]

theorem rail_zero_iff (x z : ℤ) :
    rail a b x z=0 ↔ x < 4*(a:ℤ)+z+7 ∨ 4*(a:ℤ)+z+7*b≤x := by
  have ha := NeZero.pos a
  dsimp only [rail]
  split_ifs with h
  · constructor
    · intro he; omega
    · intro he; omega
  · constructor  <;> intro he  <;> omega

theorem rail_small (x z : ℤ) : rail a b x z < a → rail a b x z=0 := by
  dsimp only [rail]
  split_ifs  <;> omega

theorem rail_large (i : ℕ) (hi : 0 < i) (hb : i < b) (x z : ℤ) :
    rail a b x z=a+i ↔ 4*(a:ℤ)+z+7*i≤x ∧ x < 4*(a:ℤ)+z+7*(i+1) := by
  dsimp only [rail]
  split_ifs with h
  · constructor  <;> intro he  <;> omega
  · constructor  <;> intro he  <;> omega

theorem small_lt (p q : Equiv.Perm (Fin a)) (x y z : ℤ) : small a p q x y z < a := by
  unfold small
  split_ifs  <;> exact Fin.isLt _

theorem box_update {v : Lattice 3} (hv : Box a b v) (k : Fin 3) (c t : ℤ)
    (hc : 0≤c ∧ c < (widths a b k:ℤ)) (ht : min (v k) c≤t) (hu : t≤max (v k) c) :
    Box a b (Function.update v k t) := by
  fin_cases k  <;> simp [Box,widths] at *  <;> omega

theorem move (p q : Equiv.Perm (Fin a)) (i : ℕ) (v : Lattice 3) (hv : Fiber a b p q i v)
    (k : Fin 3) (c : ℤ) (hc : 0≤c ∧ c < (widths a b k:ℤ))
    (hcolor : ∀ t, min (v k) c≤t → t≤max (v k) c → color a b p q (Function.update v k t)=i) :
    FacePath (Fiber a b p q i) v (Function.update v k c) := by
  apply FacePath.axis
  intro t ht hu
  exact ⟨box_update a b hv.1 k c t hc ht hu,hcolor t ht hu⟩

theorem vertical (p q : Equiv.Perm (Fin a)) (i : ℕ) (v w : Lattice 3)
    (hv : Fiber a b p q i v) (hw : Fiber a b p q i w)
    (hx : v 0=w 0) (hy : v 1=w 1) (hz : v 2+1=w 2 ∨ w 2+1=v 2) :
    FacePath (Fiber a b p q i) v w := by
  apply FacePath.step hv hw
  refine ⟨2,?_⟩
  rcases hz with hz | hz
  · left; ext k; fin_cases k  <;> simp [Pi.single_apply]  <;> omega
  · right; ext k; fin_cases k  <;> simp [Pi.single_apply]  <;> omega

end
end TranslationTiling.Rails
