import TranslationTiling.Proofs.FacePaths
import TranslationTiling.Proofs.KimGeometry
import Mathlib.Logic.Equiv.Fintype

/-! A four-layer partition with complete internal contacts and prescribed
horizontal boundary matchings. -/
namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

def band (x : ℤ) : Fin m := ⟨x.toNat % m, Nat.mod_lt _ (NeZero.pos m)⟩

def InBox (v : Lattice 3) : Prop :=
  0≤v 0 ∧ v 0≤2*m ∧ 0≤v 1 ∧ v 1≤2*m ∧ 0≤v 2 ∧ v 2≤3

def color (p q : Equiv.Perm (Fin m)) (v : Lattice 3) : Fin m :=
  if v 2=0 then band m (v 1)
  else if v 2=1 then band m (v 0)
  else if v 2=2 then if v 0<m then band m (v 1) else p (band m (v 1))
  else if v 1<m then band m (v 0) else q (band m (v 0))

def Fiber (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3) : Prop :=
  InBox m v ∧ color m p q v=i

@[simp] theorem band_val (i : Fin m) : band m (i.val:ℤ)=i := by
  apply Fin.ext
  simp [band,Nat.mod_eq_of_lt i.isLt]

@[simp] theorem band_add (i : Fin m) : band m ((m:ℤ)+i.val)=i := by
  apply Fin.ext
  change ((m:ℤ)+(i.val:ℤ)).toNat %m=i.val
  have ht : ((m:ℤ)+(i.val:ℤ)).toNat=m+i.val := by omega
  rw [ht]
  simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]

private theorem box_update (v : Lattice 3) (hv : InBox m v) (k : Fin 3) (b t : ℤ)
    (hb : 0≤b ∧ b≤(if k=2 then 3 else 2*m))
    (ht : min (v k) b≤t) (hu : t≤max (v k) b) :
    InBox m (Function.update v k t) := by
  unfold InBox at *
  fin_cases k <;> simp at * <;> omega

private theorem move (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (k : Fin 3) (b : ℤ)
    (hb : 0≤b ∧ b≤(if k=2 then 3 else 2*m))
    (hc : ∀ t, min (v k) b≤t → t≤max (v k) b →
      color m p q (Function.update v k t)=i) :
    FacePath (Fiber m p q i) v (Function.update v k b) := by
  apply FacePath.axis
  intro t ht hu
  exact ⟨box_update m v hv.1 k b t hb ht hu,hc t ht hu⟩

theorem row_path (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (b : ℤ) (hb : 0≤b ∧ b≤2*m)
    (hz : v 2=0 ∨ v 2=2)
    (hs : v 2=2 → (v 0<m ∧ b<m) ∨ (m≤v 0 ∧ m≤b)) :
    FacePath (Fiber m p q i) v (Function.update v 0 b) := by
  apply move m p q i v hv 0 b (by simpa using hb)
  intro t ht hu
  rcases hz with hz | hz
  · simpa [color,hz] using hv.2
  · rcases hs hz with hs | hs
    · have htm : t<m := by omega
      simpa [color,hz,show v 0<m from hs.1,htm] using hv.2
    · have htm : ¬t<m := by omega
      simpa [color,hz,show ¬v 0<m by omega,htm] using hv.2

theorem column_path (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (b : ℤ) (hb : 0≤b ∧ b≤2*m)
    (hz : v 2=1 ∨ v 2=3)
    (hs : v 2=3 → (v 1<m ∧ b<m) ∨ (m≤v 1 ∧ m≤b)) :
    FacePath (Fiber m p q i) v (Function.update v 1 b) := by
  apply move m p q i v hv 1 b (by simpa using hb)
  intro t ht hu
  rcases hz with hz | hz
  · simpa [color,hz] using hv.2
  · rcases hs hz with hs | hs
    · have htm : t<m := by omega
      simpa [color,hz,show v 1<m from hs.1,htm] using hv.2
    · have htm : ¬t<m := by omega
      simpa [color,hz,show ¬v 1<m by omega,htm] using hv.2

private theorem vertical (p q : Equiv.Perm (Fin m)) (i : Fin m)
    (v w : Lattice 3) (hv : Fiber m p q i v) (hw : Fiber m p q i w)
    (hx : v 0=w 0) (hy : v 1=w 1) (hz : v 2+1=w 2 ∨ w 2+1=v 2) :
    FacePath (Fiber m p q i) v w := by
  apply FacePath.step hv hw
  refine ⟨2,?_⟩
  rcases hz with hz | hz
  · left; ext k; fin_cases k <;> simp [Pi.single_apply] <;> omega
  · right; ext k; fin_cases k <;> simp [Pi.single_apply] <;> omega

def hub (i : Fin m) : Lattice 3 := ![(i.val:ℤ),(i.val:ℤ),1]

theorem hub_mem (p q : Equiv.Perm (Fin m)) (i : Fin m) : Fiber m p q i (hub m i) := by
  have hi := i.isLt
  constructor
  · simp [InBox,hub]; omega
  · simp [color,hub]

private theorem one_to_hub (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (hz : v 2=1) :
    FacePath (Fiber m p q i) v (hub m i) := by
  have hi := i.isLt
  have hb : 0≤(i.val:ℤ) ∧ (i.val:ℤ)≤2*m := by omega
  let a := Function.update v 1 (i.val:ℤ)
  have ha : Fiber m p q i a := by
    refine ⟨box_update m v hv.1 1 _ _ (by simpa using hb) (min_le_right _ _) (le_max_right _ _),?_⟩
    simpa [a,color,hz] using hv.2
  have h0 := column_path m p q i v hv _ hb (Or.inl hz) (by omega)
  let b := Function.update a 2 0
  have hbmem : Fiber m p q i b := by
    constructor
    · have hh := ha.1; simp [b,a,InBox] at *; omega
    · simp [b,a,color]
  have h1 := vertical m p q i a b ha hbmem (by simp [b]) (by simp [b]) (Or.inr (by simp [b,a,hz]))
  have h2 := row_path m p q i b hbmem (i.val:ℤ) hb (Or.inl (by simp [b])) (by simp [b])
  have hc : Function.update b 0 (i.val:ℤ) = ![(i.val:ℤ),(i.val:ℤ),0] := by ext k; fin_cases k <;> simp [b,a]
  rw [hc] at h2
  have hcmem : Fiber m p q i ![(i.val:ℤ),(i.val:ℤ),0] := by
    constructor
    · simp [InBox]; omega
    · simp [color]
  have h3 := vertical m p q i ![(i.val:ℤ),(i.val:ℤ),0] (hub m i) hcmem (hub_mem m p q i)
    (by simp [hub]) (by simp [hub]) (Or.inl (by simp [hub]))
  exact ((h0.trans h1).trans h2).trans h3

private theorem updated_box {v : Lattice 3} (hv : InBox m v) (k : Fin 3) (b : ℤ)
    (hb : 0≤b ∧ b≤(if k=2 then 3 else 2*m)) : InBox m (Function.update v k b) :=
  box_update m v hv k b b hb (min_le_right _ _) (le_max_right _ _)

private theorem zero_to_hub (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (hz : v 2=0) : FacePath (Fiber m p q i) v (hub m i) := by
  have hi := i.isLt
  have hb : 0≤(i.val:ℤ) ∧ (i.val:ℤ)≤2*m := by omega
  let a := Function.update v 0 (i.val:ℤ)
  have ha : Fiber m p q i a := ⟨updated_box m hv.1 0 _ (by simpa using hb),by simpa [a,color,hz] using hv.2⟩
  let b := Function.update a 2 1
  have hbmem : Fiber m p q i b := ⟨updated_box m ha.1 2 _ (by norm_num),by simp [b,a,color]⟩
  have h0 := row_path m p q i v hv _ hb (Or.inl hz) (by omega)
  have h1 := vertical m p q i a b ha hbmem (by simp [b]) (by simp [b]) (Or.inl (by simp [a,b,hz]))
  exact (h0.trans h1).trans (one_to_hub m p q i b hbmem (by simp [b]))

private theorem two_to_hub (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (hz : v 2=2) : FacePath (Fiber m p q i) v (hub m i) := by
  have hi := i.isLt
  let x : ℤ := if v 0<m then i.val else (m:ℤ)+i.val
  have hb : 0≤x ∧ x≤2*m := by dsimp [x]; split_ifs <;> omega
  have hs : (v 0<m ∧ x<m) ∨ (m≤v 0 ∧ m≤x) := by dsimp [x]; split_ifs <;> omega
  let a := Function.update v 0 x
  have ha : Fiber m p q i a := by
    refine ⟨updated_box m hv.1 0 x (by simpa using hb),?_⟩
    rcases hs with hs | hs
    · simpa [a,color,hz,show x<m from hs.2,show v 0<m from hs.1] using hv.2
    · simpa [a,color,hz,show ¬x<m by omega,show ¬v 0<m by omega] using hv.2
  let b := Function.update a 2 1
  have hbmem : Fiber m p q i b := by
    refine ⟨updated_box m ha.1 2 _ (by norm_num),?_⟩
    simp only [b,a,color,Function.update_self,one_ne_zero,if_false,ite_true,Function.update_of_ne (by decide : (0:Fin 3)≠2)]
    dsimp [x]
    split_ifs <;> simp
  have h0 := row_path m p q i v hv x hb (Or.inr hz) (fun _ => hs)
  have h1 := vertical m p q i a b ha hbmem (by simp [b]) (by simp [b]) (Or.inr (by simp [a,b,hz]))
  exact (h0.trans h1).trans (one_to_hub m p q i b hbmem (by simp [b]))

private theorem three_to_hub (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) (hz : v 2=3) : FacePath (Fiber m p q i) v (hub m i) := by
  let j : Fin m := if v 0<m then i else p.symm i
  have hj := j.isLt
  let y : ℤ := if v 1<m then j.val else (m:ℤ)+j.val
  have hb : 0≤y ∧ y≤2*m := by dsimp [y]; split_ifs <;> omega
  have hs : (v 1<m ∧ y<m) ∨ (m≤v 1 ∧ m≤y) := by dsimp [y]; split_ifs <;> omega
  let a := Function.update v 1 y
  have ha : Fiber m p q i a := by
    refine ⟨updated_box m hv.1 1 y (by simpa using hb),?_⟩
    rcases hs with hs | hs
    · simpa [a,color,hz,show y<m from hs.2,show v 1<m from hs.1] using hv.2
    · simpa [a,color,hz,show ¬y<m by omega,show ¬v 1<m by omega] using hv.2
  let b := Function.update a 2 2
  have hbmem : Fiber m p q i b := by
    refine ⟨updated_box m ha.1 2 _ (by norm_num),?_⟩
    by_cases hx : v 0<m <;> by_cases hy : v 1<m <;>
      simp [b,a,color,y,j,hx,hy]
  have h0 := column_path m p q i v hv y hb (Or.inr hz) (fun _ => hs)
  have h1 := vertical m p q i a b ha hbmem (by simp [b]) (by simp [b]) (Or.inr (by simp [a,b,hz]))
  exact (h0.trans h1).trans (two_to_hub m p q i b hbmem (by simp [b]))

theorem path_to_hub (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3)
    (hv : Fiber m p q i v) : FacePath (Fiber m p q i) v (hub m i) := by
  have hz := hv.1
  unfold InBox at hz
  have cases : v 2=0 ∨ v 2=1 ∨ v 2=2 ∨ v 2=3 := by omega
  rcases cases with h | h | h | h
  · exact zero_to_hub m p q i v hv h
  · exact one_to_hub m p q i v hv h
  · exact two_to_hub m p q i v hv h
  · exact three_to_hub m p q i v hv h

theorem fiber_connected (p q : Equiv.Perm (Fin m)) (i : Fin m) {v w : Lattice 3}
    (hv : Fiber m p q i v) (hw : Fiber m p q i w) : FacePath (Fiber m p q i) v w :=
  (path_to_hub m p q i v hv).trans (FacePath.reverse (path_to_hub m p q i w hw))

end
end TranslationTiling.FourLayer
