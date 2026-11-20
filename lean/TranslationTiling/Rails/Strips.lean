import TranslationTiling.Rails.SlotAssembly

namespace TranslationTiling.Rails.Strips
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def widthAt (M s : ℕ) : ℕ := if s=0 then 201*M+400 else 465*s+400

def radius (H : ℕ) : ℕ := 201*H+465

def bandAt (M H s : ℕ) (v : Lattice 3) : Prop :=
  v 2=0 ∧ (v 0).natAbs≤radius H ∧ (v 1+(s:ℤ)*v 0).natAbs≤widthAt M s

private def stripRows (M H s : ℕ) : Tile 3 :=
  (List.range (2*radius H+1)).flatMap fun (i : ℕ) =>
    (List.range (2*widthAt M s+1)).map fun (j : ℕ) =>
      let x := (i:ℤ)-radius H
      point x ((j:ℤ)-widthAt M s-(s:ℤ)*x) 0

private def stripEnum (M : ℕ) (H : ℕ → ℕ) : Tile 3 :=
  (List.range 17).flatMap fun s => stripRows M (H s) s

def slotsAt (M : ℕ) (H : ℕ → ℕ) : Tile 3 :=
  0 :: (stripEnum M H).dedup.filter (fun v => decide (v≠0))

instance (M : ℕ) (H : ℕ → ℕ) : NeZero (slotsAt M H).length := ⟨by simp [slotsAt]⟩

theorem mem_slotsAt (M : ℕ) (H : ℕ → ℕ) (v : Lattice 3) : v∈slotsAt M H ↔ ∃ s<17, bandAt M (H s) s v := by
  simp only [slotsAt,stripEnum,stripRows,List.mem_cons,List.mem_filter,List.mem_dedup,List.mem_flatMap,
    List.mem_range,List.mem_map,decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨⟨s,hs,i,hi,j,hj,rfl⟩,_⟩)
    · exact ⟨0,by decide,by simp [bandAt]⟩
    · have hi' : (i:ℤ) < 2*(radius (H s):ℤ)+1 := by exact_mod_cast hi
      have hj' : (j:ℤ) < 2*(widthAt M s:ℤ)+1 := by exact_mod_cast hj
      refine ⟨s,hs,rfl,?_,?_⟩
      · change ((i:ℤ)-radius (H s)).natAbs≤radius (H s)
        omega
      · change ((j:ℤ)-widthAt M s-(s:ℤ)*((i:ℤ)-radius (H s))+(s:ℤ)*((i:ℤ)-radius (H s))).natAbs≤widthAt M s
        rw [show (j:ℤ)-widthAt M s-(s:ℤ)*((i:ℤ)-radius (H s))+(s:ℤ)*((i:ℤ)-radius (H s))=(j:ℤ)-widthAt M s by ring]
        omega
  · rintro ⟨s,hs,hz,hx,hy⟩
    by_cases he : v=0
    · exact Or.inl he
    · have hx' : ( (v 0+radius (H s)).toNat : ℤ)=v 0+radius (H s) := Int.toNat_of_nonneg (by omega)
      have hy' : ((v 1+(s:ℤ)*v 0+widthAt M s).toNat:ℤ)=v 1+(s:ℤ)*v 0+widthAt M s :=
        Int.toNat_of_nonneg (by omega)
      have hi : (v 0+radius (H s)).toNat<2*radius (H s)+1 := by omega
      have hj : (v 1+(s:ℤ)*v 0+widthAt M s).toNat<2*widthAt M s+1 := by omega
      refine Or.inr ⟨⟨s,hs,_,hi,_,hj,?_⟩,he⟩
      ext k
      fin_cases k
      · change ((v 0+radius (H s)).toNat:ℤ)-radius (H s)=v 0
        omega
      · change ((v 1+(s:ℤ)*v 0+widthAt M s).toNat:ℤ)-widthAt M s-
          (s:ℤ)*(((v 0+radius (H s)).toNat:ℤ)-radius (H s))=v 1
        rw [hx',hy']
        ring
      · exact hz.symm

theorem validAt (M : ℕ) (H : ℕ → ℕ) : SlotAssembly.Valid (slotsAt M H) := by
  refine ⟨rfl,by simp [slotsAt],?_,fun v hv => ?_⟩
  · unfold slotsAt
    exact List.nodup_cons.mpr ⟨by simp, (List.nodup_dedup _).filter _⟩
  · obtain ⟨_,_,hv⟩ := (mem_slotsAt M H v).mp hv
    exact hv.1

private theorem vertical (M H s : ℕ) (x y : ℤ) (hx : x.natAbs≤radius H)
    (hy : (y+(s:ℤ)*x).natAbs≤widthAt M s) :
    FacePath (bandAt M H s) (point x y 0) (point x (-(s:ℤ)*x) 0) := by
  apply FacePath.box3 _ (point x (min y (-(s:ℤ)*x)) 0)
    (point x (max y (-(s:ℤ)*x)) 0)
  · intro i; fin_cases i <;> simp [point]
  · intro i; fin_cases i <;> simp [point]
  · intro v hv
    have h0 := hv 0; have h1 := hv 1; have h2 := hv 2
    simp [point] at h0 h1 h2
    have he : v 0=x := by omega
    refine ⟨by omega,by simpa [he] using hx,?_⟩
    rw [he]
    omega

private theorem center_path (M H s : ℕ) (hs : s<17) (x : ℤ) (hx : x.natAbs≤radius H) :
    FacePath (bandAt M H s) (point x (-(s:ℤ)*x) 0) 0 := by
  have hw : s≤widthAt M s := by unfold widthAt; split <;> omega
  induction hnEq : x.natAbs using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases h0 : x=0
    · subst x
      have he : point 0 0 0 = (0:Lattice 3) := by
        ext i; fin_cases i <;> rfl
      simpa [he] using (Relation.ReflTransGen.refl (a:=(0:Lattice 3)) :
        FacePath (bandAt M H s) 0 0)
    let x' := if 0<x then x-1 else x+1
    have hn : x'.natAbs<n := by dsimp only [x']; split <;> omega
    have hx' : x'.natAbs≤radius H := by omega
    have hstep : x'=x+1 ∨ x=x'+1 := by dsimp only [x']; split <;> omega
    have hy : (-(s:ℤ)*x+(s:ℤ)*x').natAbs≤widthAt M s := by
      rcases hstep with h | h
      · rw [h]
        rw [show -(s:ℤ)*x+(s:ℤ)*(x+1)=s by ring,Int.natAbs_natCast]
        exact hw
      · rw [h]
        rw [show -(s:ℤ)*(x'+1)+(s:ℤ)*x'=-(s:ℤ) by ring,Int.natAbs_neg,Int.natAbs_natCast]
        exact hw
    have hadj : FaceAdjacent (point x (-(s:ℤ)*x) 0) (point x' (-(s:ℤ)*x) 0) := by
      refine ⟨0,?_⟩
      rcases hstep with h | h
      · left
        ext i; fin_cases i <;> simp [point,h]
      · right
        ext i; fin_cases i <;> simp [point,h]
    exact (FacePath.step ⟨rfl,hx,by change (-(s:ℤ)*x+(s:ℤ)*x).natAbs≤_; rw [show -(s:ℤ)*x+(s:ℤ)*x=0 by ring]; simp⟩
      ⟨rfl,hx',hy⟩ hadj).trans ((vertical M H s x' _ hx' hy).trans (ih _ hn x' hx' rfl))

theorem pathAt (M : ℕ) (H : ℕ → ℕ) (v : Lattice 3) (hv : v∈slotsAt M H) :
    FacePath {v | v∈slotsAt M H} v 0 := by
  obtain ⟨s,hs,hz,hx,hy⟩ := (mem_slotsAt M H v).mp hv
  have he : point (v 0) (v 1) 0=v := by ext i; fin_cases i <;> simp [point,hz]
  exact FacePath.mono (he ▸ (vertical M (H s) s (v 0) (v 1) hx hy).trans
      (center_path M (H s) s hs (v 0) hx)) (fun w hw => (mem_slotsAt M H w).mpr ⟨s,hs,hw⟩)

def countCapAt (M : ℕ) (H : ℕ → ℕ) : ℕ :=
  ((List.range 17).map fun s => (2*radius (H s)+1)*(2*widthAt M s+1)).sum

theorem length_leAt (M : ℕ) (H : ℕ → ℕ) : (slotsAt M H).length≤countCapAt M H := by
  let l := stripEnum M H
  have hzero : (0:Lattice 3)∈l := by
    simp only [l,stripEnum,stripRows,List.mem_flatMap,List.mem_range,List.mem_map]
    exact ⟨0,by decide,radius (H 0),by omega,widthAt M 0,by omega,by
        ext i; fin_cases i <;> simp [point]⟩
  have he : (slotsAt M H).toFinset=l.toFinset := by
    ext v
    change v ∈ (0::l.dedup.filter (fun v => decide (v≠0))).toFinset ↔ v∈l.toFinset
    simp only [List.mem_toFinset,List.mem_cons,List.mem_filter,List.mem_dedup,decide_eq_true_eq]
    constructor
    · rintro (rfl|⟨hv,_⟩)
      · exact hzero
      · exact hv
    · intro hv
      by_cases h : v=0
      · exact Or.inl h
      · exact Or.inr ⟨hv,h⟩
  rw [←List.toFinset_card_of_nodup (validAt M H).2.2.1,he]
  apply (List.toFinset_card_le l).trans
  have inner (s : ℕ) : (stripRows M (H s) s).length=(2*radius (H s)+1)*(2*widthAt M s+1) := by
    rw [stripRows,List.length_flatMap]
    simp [List.length_map,List.sum_replicate,Function.comp_def]
  change (stripEnum M H).length≤_
  rw [stripEnum,List.length_flatMap]
  simp [countCapAt,inner]

abbrev width := widthAt 175
def slots (H : ℕ) := slotsAt 175 (fun _ => H)

instance (H : ℕ) : NeZero (slots H).length := by unfold slots; infer_instance

@[fun_prop] theorem slots_primrec : Primrec slots := by
  unfold slots slotsAt
  have he : Primrec (fun H => stripEnum 175 (fun _ => H)) := by
    unfold stripEnum stripRows widthAt radius point
    fun_prop
  exact Primrec.list_cons.comp (Primrec.const 0)
    (filterList (dedup_primrec.comp he) (by fun_prop))

abbrev mem_slots (H : ℕ) (v : Lattice 3) := mem_slotsAt 175 (fun _ => H) v
abbrev valid (H : ℕ) := validAt 175 (fun _ => H)
abbrev path (H : ℕ) := pathAt 175 (fun _ => H)

def countCap (H : ℕ) : ℕ := (402*H+931)*210447

theorem countCapAt_uniform (H : ℕ) : countCapAt 175 (fun _ => H)=countCap H := by
  unfold countCapAt
  rw [List.sum_map_mul_left]
  have he : ((List.range 17).map fun s => 2*widthAt 175 s+1).sum=210447 := by decide +kernel
  rw [he]
  unfold countCap radius
  have h : 2*(201*H+465)+1=402*H+931 := by omega
  rw [h]

theorem length_le (H : ℕ) : (slots H).length≤countCap H :=
  (length_leAt 175 (fun _ => H)).trans_eq (countCapAt_uniform H)

def railHeight (U : ℕ) : ℕ := 201*U+401

def assemble (E : Tile 3) (H U : ℕ) : Tile 3 :=
  SlotAssembly.assemble E (slots H) (railHeight U)

theorem assemble_computable : Computable (fun z : Tile 3 × ℕ × ℕ =>
    assemble z.1 z.2.1 z.2.2) := by
  have ht : Primrec (fun z : Tile 3 × ℕ × ℕ => (z.1,slots z.2.1,railHeight z.2.2)) := by
    unfold railHeight
    fun_prop
  exact Computable.comp
    (f:=fun z : Tile 3 × Tile 3 × ℕ => SlotAssembly.assemble z.1 z.2.1 z.2.2)
    (g:=fun z : Tile 3 × ℕ × ℕ => (z.1,slots z.2.1,railHeight z.2.2))
    SlotAssembly.assemble_computable ht.to_comp

end
end TranslationTiling.Rails.Strips
