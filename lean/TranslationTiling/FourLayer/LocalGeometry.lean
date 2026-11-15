import TranslationTiling.FourLayer.Shape
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace TranslationTiling.FourLayer
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

theorem small_not_dent (c : Lattice 3) (hc : c∈Kim.cube 3) (i : Fin 3) :
    c≠dent (scales m) i := by
  have hm := NeZero.pos m
  have hi := (Kim.mem_cube_iff 3 _).mp hc i
  intro he
  have hh := congrFun he i
  fin_cases i <;> simp [dent,gridMap,scales,widths,Kim.bumpAt] at hh hi ⊢ <;> omega

private theorem relocate_corner (X : Fin m → Lattice 3) (hX : X 0=0)
    (p q : Equiv.Perm (Fin m)) {r : Lattice 3} {i : Fin 3} (hb : block r=corner m i) :
    relocate m X p q r=r := by simp [relocate,hb,corner_color,hX]

theorem raw_missing (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    {v : Lattice 3} (hv : v∈Raw m X p q) (hn : v∉Shape m X p q) :
    ∃ i, v=dent (scales m) i := by
  obtain ⟨r,rfl⟩ := hv
  by_cases h : ∃ i, r.val=dent (scales m) i
  · obtain ⟨i,hi⟩ := h
    refine ⟨i,?_⟩
    change relocate m X p q r.val=dent (scales m) i
    rw [hi,relocate_dent m X hX p q]
  · have h0 : r.val≠dent (scales m) 0 := fun he => h ⟨0,he⟩
    have h1 : r.val≠dent (scales m) 1 := fun he => h ⟨1,he⟩
    have h2 : r.val≠dent (scales m) 2 := fun he => h ⟨2,he⟩
    apply (hn ?_).elim
    exact ⟨r,by simp [modified,h0,h1,h2]⟩

theorem first_block (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    (c : Lattice 3) (hc : c∈Kim.cube 3) : c∈Shape m X p q := by
  have hr : Rect (scales m) c := by
    intro i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    have hw := widths_pos m i
    dsimp [scales]
    push_cast
    omega
  have hb : block c=0 := by
    ext i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    change c i/3=0
    omega
  refine ⟨⟨c,hr⟩,?_⟩
  change modified m X p q c=c
  simp [modified,small_not_dent m c hc,relocate,hb,color,hX]

theorem rim_mem (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    (i j : Fin 3) (hji : j≠i) (e : ℤ) (he : e=1 ∨ e=-1) :
    dent (scales m) i+Pi.single j e∈Shape m X p q := by
  let r := dent (scales m) i+Pi.single j e
  have hm := NeZero.pos m
  have hr : Rect (scales m) r := by
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [r,Rect,dent,gridMap,scales,widths,Kim.bumpAt] <;> omega
  have hb : block r=corner m i := by
    ext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [r,block,corner,dent,gridMap,scales,widths,Kim.bumpAt] <;> omega
  have hn (k : Fin 3) : r≠dent (scales m) k := by
    intro hk
    have hi : i=k := dents_close_unique m (by
      intro l
      rw [← hk]
      dsimp [r]
      simp only [Pi.add_apply,Pi.single_apply]
      split_ifs <;> rcases he with rfl | rfl <;> omega)
    subst k
    have hh := congrFun hk j
    dsimp [r] at hh
    simp at hh
    rcases he with rfl | rfl <;> omega
  refine ⟨⟨r,hr⟩,?_⟩
  change modified m X p q r=r
  simp only [modified,if_neg (hn 0),if_neg (hn 1),if_neg (hn 2)]
  exact relocate_corner m X hX p q hb

def localData (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m)) :
    LocalData (scales m) (Shape m X p q) where
  raw := Raw m X p q
  raw_or_bump := by
    rintro v ⟨r,rfl⟩
    unfold modified
    dsimp only
    split_ifs
    · exact Or.inr ⟨0,rfl⟩
    · exact Or.inr ⟨1,rfl⟩
    · exact Or.inr ⟨2,rfl⟩
    · exact Or.inl ⟨r,rfl⟩
  first_block := first_block m X hX p q
  dent_absent := dent_absent m X p q
  rim := rim_mem m X hX p q
  blocks := fun _ hv => raw_blocks m X p q hv
  missing_close := by
    intro u hu v hv hun hvn hnear
    obtain ⟨i,hi⟩ := raw_missing m X hX p q hu hun
    obtain ⟨j,hj⟩ := raw_missing m X hX p q hv hvn
    have he : i=j := dents_close_unique m (by simpa only [hi,hj] using hnear)
    rw [hi,hj,he]

theorem shape_upper (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) :
    ∃ upper : ℤ, ∀ v∈Shape m X p q, ∀ i, v i≤upper := by
  let F := shapeFinset m X p q
  let b := F.sup (fun v => ∑ i : Fin 3, (v i).natAbs)
  refine ⟨(b:ℤ),fun v hv i => ?_⟩
  have hvF : v∈F := (mem_shapeFinset m X p q v).mpr hv
  have h := Finset.le_sup (f:=fun v => ∑ i : Fin 3, (v i).natAbs) hvF
  have hh : (v i).natAbs≤∑ j : Fin 3, (v j).natAbs :=
    Finset.single_le_sum (f:=fun j : Fin 3 => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (Int.le_natAbs).trans (by exact_mod_cast hh.trans h)

theorem shape_rigidity (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    (A : Set (Lattice 3)) (hA : ExactTiling A (Shape m X p q)) :
    ∃ t, A=gridCoset (scales m) t :=
  coset_of_forward (scales_pos m) (localData m X hX p q)
    (shape_fundamental m X p q) (shape_upper m X p q) A hA

end
end TranslationTiling.FourLayer
