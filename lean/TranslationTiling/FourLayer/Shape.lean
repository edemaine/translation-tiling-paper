import TranslationTiling.FourLayer.Contacts
import Mathlib.Algebra.BigOperators.Fin
import TranslationTiling.FourLayer.Residues

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

def scales (i : Fin 3) : ℕ := 3*widths m i

theorem widths_pos (i : Fin 3) : 0<widths m i := by fin_cases i <;> simp [widths]
theorem scales_pos (i : Fin 3) : 0<scales m i := by exact Nat.mul_pos (by decide) (widths_pos m i)

def block (r : Lattice 3) : Lattice 3 := fun i => r i/3

theorem block_mem {r : Lattice 3} (hr : Rect (scales m) r) : InBox m (block r) := by
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2
  simp [Rect,scales,widths,block,InBox] at *
  omega

def relocate (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (r : Lattice 3) : Lattice 3 :=
  gridMap (scales m) (X (color m p q (block r)))+r

def modified (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (r : Lattice 3) : Lattice 3 :=
  if r=dent (scales m) 0 then Kim.bumpAt 0
  else if r=dent (scales m) 1 then Kim.bumpAt 1
  else if r=dent (scales m) 2 then Kim.bumpAt 2
  else relocate m X p q r

def Raw (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) : Set (Lattice 3) :=
  Set.range (fun r : {r : Lattice 3 // Rect (scales m) r} => relocate m X p q r.val)

def Shape (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) : Set (Lattice 3) :=
  Set.range (fun r : {r : Lattice 3 // Rect (scales m) r} => modified m X p q r.val)

theorem dent_mem_rect (i : Fin 3) : Rect (scales m) (dent (scales m) i) := by
  have hm := NeZero.pos m
  intro j
  fin_cases i <;> fin_cases j <;> simp [Rect,dent,gridMap,scales,widths,Kim.bumpAt] <;> omega

theorem residue_bump (i : Fin 3) : residue (scales m) (Kim.bumpAt i)=dent (scales m) i := by
  have h := residue_grid_add (scales m) (Pi.single i 1) (Kim.bumpAt i)
  change residue (scales m) (dent (scales m) i)=_ at h
  rw [residue_self (dent_mem_rect m i)] at h
  exact h.symm

theorem modified_residue (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m))
    (r : {r : Lattice 3 // Rect (scales m) r}) : residue (scales m) (modified m X p q r.val)=r.val := by
  unfold modified
  split_ifs with h0 h1 h2
  · rw [residue_bump,h0]
  · rw [residue_bump,h1]
  · rw [residue_bump,h2]
  · unfold relocate
    rw [residue_grid_add,residue_self r.property]

theorem shape_fundamental (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) :
    ExactTiling (Set.range (gridMap (scales m))) (Shape m X p q) :=
  representatives_fundamental (scales m) (scales_pos m) _ (modified_residue m X p q)

theorem modified_injective (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m))
    {r t : Lattice 3} (hr : Rect (scales m) r) (ht : Rect (scales m) t)
    (he : modified m X p q r=modified m X p q t) : r=t := by
  have h := congrArg (residue (scales m)) he
  rw [modified_residue m X p q ⟨r,hr⟩,modified_residue m X p q ⟨t,ht⟩] at h
  exact h

def corner (i : Fin 3) : Lattice 3 := fun j => if j=i then (widths m j:ℤ)-1 else 0

theorem corner_color (p q : Equiv.Perm (Fin m)) (i : Fin 3) : color m p q (corner m i)=0 := by
  have hm := NeZero.pos m
  fin_cases i <;> simp [corner,widths,color,NeZero.ne m]

theorem dent_block (i : Fin 3) : block (dent (scales m) i)=corner m i := by
  have hm := NeZero.pos m
  ext j
  fin_cases i <;> fin_cases j <;> simp [block,dent,gridMap,scales,widths,corner,Kim.bumpAt] <;> omega

theorem relocate_dent (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m)) (i : Fin 3) :
    relocate m X p q (dent (scales m) i)=dent (scales m) i := by
  simp [relocate,dent_block,corner_color,hX]

theorem dents_close_unique {i j : Fin 3}
    (h : ∀ k, -2≤dent (scales m) j k-dent (scales m) i k ∧
      dent (scales m) j k-dent (scales m) i k≤2) : i=j := by
  have hm := NeZero.pos m
  by_contra hij
  have hi := h i
  fin_cases i <;> fin_cases j <;> simp_all [dent,gridMap,scales,widths,Kim.bumpAt] <;> omega

theorem modified_dent (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (i : Fin 3) :
    modified m X p q (dent (scales m) i)=Kim.bumpAt i := by
  have hm := NeZero.pos m
  have hne (i j : Fin 3) (hij : i≠j) : dent (scales m) i≠dent (scales m) j := by
    intro h
    have hh := congrFun h i
    fin_cases i <;> fin_cases j <;> simp_all [dent,gridMap,scales,widths,Kim.bumpAt] <;> omega
  fin_cases i <;> simp [modified,hne _ _ (by decide : (1:Fin 3)≠0),
    hne _ _ (by decide : (2:Fin 3)≠0),hne _ _ (by decide : (2:Fin 3)≠1)]

theorem dent_absent (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (i : Fin 3) :
    dent (scales m) i∉Shape m X p q := by
  rintro ⟨r,hr⟩
  have hres := congrArg (residue (scales m)) hr
  rw [modified_residue m X p q r,residue_self (dent_mem_rect m i)] at hres
  change modified m X p q r.val=dent (scales m) i at hr
  rw [hres,modified_dent] at hr
  have hh := congrFun hr i
  have hs := scales_pos m i
  simp [dent,gridMap,Kim.bumpAt] at hh
  omega

theorem raw_blocks (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) {v : Lattice 3}
    (hv : v∈Raw m X p q) : ∃ b c : Lattice 3, c∈Kim.cube 3 ∧ v=3 • b+c ∧
      ∀ d∈Kim.cube 3, 3 • b+d∈Raw m X p q := by
  obtain ⟨r,rfl⟩ := hv
  let b := block r.val
  let c : Lattice 3 := fun i => r.val i%3
  have hb := block_mem m r.property
  change InBox m b at hb
  have hc : c∈Kim.cube 3 := (Kim.mem_cube_iff 3 _).mpr (fun i => ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩)
  have he : r.val=3 • b+c := by
    ext i
    exact (Int.mul_ediv_add_emod (r.val i) 3).symm
  let b' := gridMap (widths m) (X (color m p q b))+b
  have hscale : gridMap (scales m) (X (color m p q b))=3 • gridMap (widths m) (X (color m p q b)) := by
    ext i
    simp [gridMap,scales]; ring
  refine ⟨b',c,hc,?_,?_⟩
  · change gridMap (scales m) (X (color m p q b))+r.val=3 • (gridMap (widths m) (X (color m p q b))+b)+c
    rw [he,hscale,smul_add]
    abel
  · intro d hd
    let r' : Lattice 3 := 3 • b+d
    have hr' : Rect (scales m) r' := by
      intro i
      have hi := (Kim.mem_cube_iff 3 _).mp hd i
      have hh : 0≤b i ∧ b i<(widths m i:ℤ) := by
        fin_cases i <;> simp [widths,InBox] at hb ⊢ <;> omega
      dsimp [r',scales]
      push_cast
      change 0≤3*b i+d i ∧ 3*b i+d i<3*(widths m i:ℤ)
      omega
    have hblock : block r'=b := by
      ext i
      have hi := (Kim.mem_cube_iff 3 _).mp hd i
      simp [block,r']
      omega
    refine ⟨⟨r',hr'⟩,?_⟩
    change relocate m X p q r'=3 • b'+d
    unfold relocate
    rw [hblock,hscale]
    dsimp [r',b']
    rw [smul_add]
    abel

def shapeFinset (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) : Finset (Lattice 3) :=
  (boxFinset (scales m)).image (modified m X p q)

@[simp] theorem mem_shapeFinset (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (v : Lattice 3) :
    v∈shapeFinset m X p q ↔ v∈Shape m X p q := by
  simp only [shapeFinset,Finset.mem_image,mem_boxFinset,Shape,Set.mem_range]
  constructor
  · rintro ⟨r,hr,he⟩
    exact ⟨⟨r,hr⟩,he⟩
  · rintro ⟨r,he⟩
    exact ⟨r.val,r.property,he⟩

theorem shape_card_le (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) :
    (shapeFinset m X p q).card≤972*m^2 := by
  have hm := NeZero.pos m
  have hbox : (boxFinset (scales m)).card=108*(2*m+1)^2 := by
    unfold boxFinset
    rw [Fintype.card_piFinset]
    simp only [Int.card_Ico,sub_zero,Int.toNat_natCast]
    rw [Fin.prod_univ_three]
    simp [scales,widths]
    ring
  apply Finset.card_image_le.trans
  rw [hbox]
  nlinarith [Nat.mul_le_mul_left m hm]

end
end TranslationTiling.FourLayer
