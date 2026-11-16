import TranslationTiling.Rails.Ports
import Mathlib.Algebra.BigOperators.Fin
import TranslationTiling.FourLayer.Residues

namespace TranslationTiling.Rails
open FourLayer (Rect gridMap dent residue residue_grid_add residue_self representatives_fundamental boxFinset mem_boxFinset LocalData coset_of_forward gridCoset)
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (a B : ℕ) [NeZero a] [NeZero B]

def scales (i : Fin 3) : ℕ := 3*widths a B i

theorem scales_pos (i : Fin 3) : 0<scales a B i := by exact Nat.mul_pos (by decide) (widths_pos a B i)

def block (r : Lattice 3) : Lattice 3 := fun i => r i/3

theorem block_mem {r : Lattice 3} (hr : Rect (scales a B) r) : Box a B (block r) := by
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2
  simp [Rect,scales,widths,lengthX,lengthY,block,Box] at *
  omega

def relocate (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (r : Lattice 3) : Lattice 3 :=
  gridMap (scales a B) (X (color a B p q (block r)))+r

def modified (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (r : Lattice 3) : Lattice 3 :=
  if r=dent (scales a B) 0 then Kim.bumpAt 0
  else if r=dent (scales a B) 1 then Kim.bumpAt 1
  else if r=dent (scales a B) 2 then Kim.bumpAt 2
  else relocate a B X p q r

def Raw (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) : Set (Lattice 3) :=
  Set.range (fun r : {r : Lattice 3 // Rect (scales a B) r} => relocate a B X p q r.val)

def Shape (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) : Set (Lattice 3) :=
  Set.range (fun r : {r : Lattice 3 // Rect (scales a B) r} => modified a B X p q r.val)

theorem dent_mem_rect (i : Fin 3) : Rect (scales a B) (dent (scales a B) i) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos B
  intro j
  fin_cases i <;> fin_cases j <;> simp [Rect,dent,gridMap,scales,widths,lengthX,lengthY,Kim.bumpAt] <;> omega

theorem residue_bump (i : Fin 3) : residue (scales a B) (Kim.bumpAt i)=dent (scales a B) i := by
  have h := residue_grid_add (scales a B) (Pi.single i 1) (Kim.bumpAt i)
  change residue (scales a B) (dent (scales a B) i)=_ at h
  rw [residue_self (dent_mem_rect a B i)] at h
  exact h.symm

theorem modified_residue (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a))
    (r : {r : Lattice 3 // Rect (scales a B) r}) : residue (scales a B) (modified a B X p q r.val)=r.val := by
  unfold modified
  split_ifs with h0 h1 h2
  · rw [residue_bump,h0]
  · rw [residue_bump,h1]
  · rw [residue_bump,h2]
  · unfold relocate
    rw [residue_grid_add,residue_self r.property]

theorem shape_fundamental (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) :
    ExactTiling (Set.range (gridMap (scales a B))) (Shape a B X p q) :=
  representatives_fundamental (scales a B) (scales_pos a B) _ (modified_residue a B X p q)

theorem modified_injective (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a))
    {r t : Lattice 3} (hr : Rect (scales a B) r) (ht : Rect (scales a B) t)
    (he : modified a B X p q r=modified a B X p q t) : r=t := by
  have h := congrArg (residue (scales a B)) he
  rw [modified_residue a B X p q ⟨r,hr⟩,modified_residue a B X p q ⟨t,ht⟩] at h
  exact h

theorem dent_block (i : Fin 3) : block (dent (scales a B) i)=corner a B i := by
  have ha := NeZero.pos a
  have hb := NeZero.pos B
  ext j
  fin_cases i <;> fin_cases j <;> simp [block,dent,gridMap,scales,widths,lengthX,lengthY,corner,Kim.bumpAt] <;> omega

theorem relocate_dent (X : ℕ → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin a)) (i : Fin 3) :
    relocate a B X p q (dent (scales a B) i)=dent (scales a B) i := by
  simp [relocate,dent_block,corner_color,hX]

theorem dents_close_unique {i j : Fin 3}
    (h : ∀ k, -2≤dent (scales a B) j k-dent (scales a B) i k ∧
      dent (scales a B) j k-dent (scales a B) i k≤2) : i=j := by
  have ha := NeZero.pos a
  have hb := NeZero.pos B
  by_contra hij
  have hi := h i
  fin_cases i <;> fin_cases j <;> simp_all [dent,gridMap,scales,widths,lengthX,lengthY,Kim.bumpAt] <;> omega

theorem modified_dent (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (i : Fin 3) :
    modified a B X p q (dent (scales a B) i)=Kim.bumpAt i := by
  have ha := NeZero.pos a
  have hb := NeZero.pos B
  have hne (i j : Fin 3) (hij : i≠j) : dent (scales a B) i≠dent (scales a B) j := by
    intro h
    have hh := congrFun h i
    fin_cases i <;> fin_cases j <;> simp_all [dent,gridMap,scales,widths,lengthX,lengthY,Kim.bumpAt] <;> omega
  fin_cases i <;> simp [modified,hne _ _ (by decide : (1:Fin 3)≠0),
    hne _ _ (by decide : (2:Fin 3)≠0),hne _ _ (by decide : (2:Fin 3)≠1)]

theorem dent_absent (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (i : Fin 3) :
    dent (scales a B) i∉Shape a B X p q := by
  rintro ⟨r,hr⟩
  have hres := congrArg (residue (scales a B)) hr
  rw [modified_residue a B X p q r,residue_self (dent_mem_rect a B i)] at hres
  change modified a B X p q r.val=dent (scales a B) i at hr
  rw [hres,modified_dent] at hr
  have hh := congrFun hr i
  have hs := scales_pos a B i
  simp [dent,gridMap,Kim.bumpAt] at hh
  omega

theorem raw_blocks (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) {v : Lattice 3}
    (hv : v∈Raw a B X p q) : ∃ b c : Lattice 3, c∈Kim.cube 3 ∧ v=3 • b+c ∧
      ∀ d∈Kim.cube 3, 3 • b+d∈Raw a B X p q := by
  obtain ⟨r,rfl⟩ := hv
  let b := block r.val
  let c : Lattice 3 := fun i => r.val i%3
  have hb := block_mem a B r.property
  change Box a B b at hb
  have hc : c∈Kim.cube 3 := (Kim.mem_cube_iff 3 _).mpr (fun i => ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩)
  have he : r.val=3 • b+c := by
    ext i
    exact (Int.mul_ediv_add_emod (r.val i) 3).symm
  let b' := gridMap (widths a B) (X (color a B p q b))+b
  have hscale : gridMap (scales a B) (X (color a B p q b))=3 • gridMap (widths a B) (X (color a B p q b)) := by
    ext i
    simp [gridMap,scales]; ring
  refine ⟨b',c,hc,?_,?_⟩
  · change gridMap (scales a B) (X (color a B p q b))+r.val=3 • (gridMap (widths a B) (X (color a B p q b))+b)+c
    rw [he,hscale,smul_add]
    abel
  · intro d hd
    let r' : Lattice 3 := 3 • b+d
    have hr' : Rect (scales a B) r' := by
      intro i
      have hi := (Kim.mem_cube_iff 3 _).mp hd i
      have hh : 0≤b i ∧ b i<(widths a B i:ℤ) := by
        fin_cases i <;> simp [widths,Box,lengthX,lengthY] at hb ⊢ <;> omega
      dsimp [r',scales]
      push_cast
      change 0≤3*b i+d i ∧ 3*b i+d i<3*(widths a B i:ℤ)
      omega
    have hblock : block r'=b := by
      ext i
      have hi := (Kim.mem_cube_iff 3 _).mp hd i
      simp [block,r']
      omega
    refine ⟨⟨r',hr'⟩,?_⟩
    change relocate a B X p q r'=3 • b'+d
    unfold relocate
    rw [hblock,hscale]
    dsimp [r',b']
    rw [smul_add]
    abel

def shapeFinset (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) : Finset (Lattice 3) :=
  (boxFinset (scales a B)).image (modified a B X p q)

@[simp] theorem mem_shapeFinset (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (v : Lattice 3) :
    v∈shapeFinset a B X p q ↔ v∈Shape a B X p q := by
  simp only [shapeFinset,Finset.mem_image,mem_boxFinset,Shape,Set.mem_range]
  constructor
  · rintro ⟨r,hr,he⟩
    exact ⟨⟨r,hr⟩,he⟩
  · rintro ⟨r,he⟩
    exact ⟨r.val,r.property,he⟩

theorem shape_card_le (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) :
    (shapeFinset a B X p q).card≤216*(lengthX a B)*(lengthY a) := by
  have hbox : (boxFinset (scales a B)).card=216*(lengthX a B)*(lengthY a) := by
    unfold boxFinset
    rw [Fintype.card_piFinset]
    simp only [Int.card_Ico,sub_zero,Int.toNat_natCast]
    rw [Fin.prod_univ_three]
    simp [scales,widths]
    ring
  exact Finset.card_image_le.trans hbox.le

end
end TranslationTiling.Rails
