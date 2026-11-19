import TranslationTiling.Rails.Assembly

namespace TranslationTiling.Rails.SlotAssembly
open FourLayer (gridMap gridCoset gridMap_injective matching matching_spec matching_computable
  tablePermutation tablePermutation_match)
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Valid (X : Tile 3) : Prop :=
  X.getD 0 0 = 0 ∧ 0 ∈ X ∧ X.Nodup ∧ ∀ v ∈ X, v 2 = 0

variable (X : Tile 3) (hX : Valid X)
include hX

variable [NeZero X.length]

private theorem required : FourLayer.Required X := by
  intro i hi j hj
  by_cases he : i=j
  · exact Or.inl he
  · right
    intro h
    rw [List.getD_eq_getElem _ _ (List.mem_range.mp hi),
      List.getD_eq_getElem _ _ (List.mem_range.mp hj)] at h
    exact he (hX.2.2.1.getElem_inj_iff.mp h)

private theorem slot_small (i : Fin X.length) :
    slotCode X i.val=FourLayer.slots X i := by simp [slotCode,i.isLt,FourLayer.slots]

private theorem slot_zero : slotCode X 0=0 := by
  rw [slotCode,if_pos (NeZero.pos X.length),hX.1]

private theorem slot_rail (i : ℕ) : slotCode X (railLabel X.length i)=point 0 0 i := by
  by_cases hi : i=0
  · subst i
    rw [show railLabel X.length 0=0 by simp [railLabel],slot_zero X hX]
    ext k
    fin_cases k <;> simp [point]
  · have hn : ¬X.length+i<X.length := by omega
    simp [slotCode,railLabel,hi,hn]

private theorem slot_plane (i : ℕ) (hi : i<X.length) : slotCode X i 2=0 := by
  simp only [slotCode,if_pos hi,List.getD_eq_getElem _ _ hi]
  exact hX.2.2.2 _ (List.getElem_mem hi)

theorem slot_injective (B i j : ℕ)
    (hi : Used X.length B i) (hj : Used X.length B j)
    (he : slotCode X i=slotCode X j) : i=j := by
  rcases hi with hi | ⟨k,hk,hkb,rfl⟩ <;> rcases hj with hj | ⟨l,hl,hlb,rfl⟩
  · have hh : FourLayer.slots X ⟨i,hi⟩=FourLayer.slots X ⟨j,hj⟩ := by
      rw [←slot_small X hX ⟨i,hi⟩,←slot_small X hX ⟨j,hj⟩]
      exact he
    exact congrArg Fin.val ((FourLayer.slots_injective _ (required X hX)) hh)
  · have h := slot_plane X hX i hi
    have hh := congrFun he 2
    simp only [show X.length+l=railLabel X.length l by simp [railLabel,show l≠0 by omega],slot_rail X hX] at hh
    simp [point] at hh
    omega
  · have h := slot_plane X hX j hj
    have hh := congrFun he 2
    simp only [show X.length+k=railLabel X.length k by simp [railLabel,show k≠0 by omega],slot_rail X hX] at hh
    simp [point] at hh
    omega
  · have hh := congrFun he 2
    simp only [show X.length+k=railLabel X.length k by simp [railLabel,show k≠0 by omega],
      show X.length+l=railLabel X.length l by simp [railLabel,show l≠0 by omega],slot_rail X hX] at hh
    simp [point] at hh
    omega

private theorem slot_large (k : ℕ) (hk : 0<k) :
    slotCode X (X.length+k)=point 0 0 k := by
  have he : X.length+k=railLabel X.length k := by simp [railLabel,show k≠0 by omega]
  rw [he,slot_rail X hX]

theorem slot_neighbor (B i j : ℕ)
    (hi : Used X.length B i) (hj : Used X.length B j)
    (k : Fin 3) (he : slotCode X j=slotCode X i+Pi.single k 1) :
    ((k=0 ∨ k=1) ∧ i<X.length ∧ j<X.length) ∨
    (k=2 ∧ ∃ r : ℕ, r<B ∧ r+1<B ∧
      i=railLabel X.length r ∧ j=railLabel X.length (r+1)) := by
  rcases hi with hi | ⟨r,hr,hrB,rfl⟩ <;> rcases hj with hj | ⟨s,hs,hsB,rfl⟩
  · have hiz := slot_plane X hX i hi
    have hjz := slot_plane X hX j hj
    fin_cases k
    · exact Or.inl ⟨Or.inl rfl,hi,hj⟩
    · exact Or.inl ⟨Or.inr rfl,hi,hj⟩
    · have hh := congrFun he 2
      simp at hh
      omega
  · have hiz := slot_plane X hX i hi
    have hz := congrFun he 2
    rw [slot_large X hX s hs] at hz
    fin_cases k
    · simp [point] at hz; omega
    · simp [point] at hz; omega
    · have hs1 : s=1 := by simp [point] at hz; omega
      have hi0 : i=0 := by
        apply slot_injective X hX B i 0 (Or.inl hi) (Or.inl (NeZero.pos _))
        rw [slot_zero X hX]
        ext l
        have hh := congrFun he l
        rw [slot_large X hX s hs] at hh
        fin_cases l <;> simp [point] at hh ⊢ <;> omega
      right
      refine ⟨rfl,0,by omega,by omega,?_,?_⟩
      · simpa [railLabel] using hi0
      · simp [railLabel,hs1]
  · have hjz := slot_plane X hX j hj
    have hz := congrFun he 2
    rw [slot_large X hX r hr] at hz
    fin_cases k <;> simp [point] at hz <;> omega
  · rw [slot_large X hX r hr,slot_large X hX s hs] at he
    fin_cases k
    · have hh := congrFun he 0; simp [point] at hh
    · have hh := congrFun he 1; simp [point] at hh
    · have hz := congrFun he 2
      have hrs : s=r+1 := by simp [point] at hz; omega
      right
      refine ⟨rfl,r,hrB,by omega,?_,?_⟩
      · simp [railLabel,show r≠0 by omega]
      · simp [railLabel,hrs]

private theorem slot_ports (B : ℕ) [NeZero B]
    (p q : Equiv.Perm (Fin X.length))
    (hp : ∀ i j, FourLayer.slots X j=FourLayer.slots X i+Pi.single 0 1 → p j=i)
    (hq : ∀ i j, FourLayer.slots X j=FourLayer.slots X i+Pi.single 1 1 → q j=i)
    (i j : ℕ) (hi : Used X.length B i) (hj : Used X.length B j)
    (k : Fin 3) (he : slotCode X j=slotCode X i+Pi.single k 1) :
    ∃ r t, MicroFiber X.length B p q i r ∧ MicroFiber X.length B p q j t ∧
      r+Pi.single k 1=gridMap (scales X.length B) (Pi.single k 1)+t := by
  rcases slot_neighbor X hX B i j hi hj k he with ⟨hk,hi,hj⟩ | ⟨rfl,r,hr,hr1,rfl,rfl⟩
  · have he' : FourLayer.slots X ⟨j,hj⟩=FourLayer.slots X ⟨i,hi⟩+Pi.single k 1 := by
      rw [←slot_small X hX ⟨i,hi⟩,←slot_small X hX ⟨j,hj⟩]
      exact he
    rcases hk with rfl | rfl
    · have hh := hp ⟨i,hi⟩ ⟨j,hj⟩ he'
      simpa only [hh] using x_micro_contact X.length B p q ⟨j,hj⟩
    · have hh := hq ⟨i,hi⟩ ⟨j,hj⟩ he'
      simpa only [hh] using y_micro_contact X.length B p q ⟨j,hj⟩
  · exact z_micro_contact X.length B p q ⟨r,hr⟩ hr1



omit hX

def shell (X : Tile 3) (B : ℕ) : Tile 3 :=
  shapeList X (B+1) (matching X).1 (matching X).2

def shellScales (X : Tile 3) (B : ℕ) := scales X.length (B+1)

set_option maxHeartbeats 6000000 in
theorem shell_computable : Computable (fun z : Tile 3 × ℕ => shell z.1 z.2) := by
  have hx : Primrec (Prod.fst : Tile 3 × ℕ → Tile 3) := Primrec.fst
  have hm := matching_computable.comp (f:=matching) (g:=Prod.fst) hx.to_comp
  have ht : Computable (fun z : Tile 3 × ℕ => (z.1,z.2+1,(matching z.1).1,(matching z.1).2)) :=
    hx.to_comp.pair ((show Primrec (fun z : Tile 3 × ℕ => z.2+1) by fun_prop).to_comp.pair
      ((Computable.fst.comp hm).pair (Computable.snd.comp hm)))
  exact Computable.comp
    (f:=fun z : Tile 3 × ℕ × List ℕ × List ℕ => shapeList z.1 z.2.1 z.2.2.1 z.2.2.2)
    (g:=fun z : Tile 3 × ℕ => (z.1,z.2+1,(matching z.1).1,(matching z.1).2))
    shapeList_primrec.to_comp ht

def assemble (E X : Tile 3) (B : ℕ) : Tile 3 :=
  (E.dedup.flatMap fun u => (shell X B).map fun v => gridMap (shellScales X B) u+v).dedup

theorem assemble_computable : Computable (fun z : Tile 3 × Tile 3 × ℕ =>
    assemble z.1 z.2.1 z.2.2) := by
  have ha : Primrec (fun z : Tile 3 × Tile 3 × (Fin 3 → ℕ) =>
      z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v) := by fun_prop
  have hs : Primrec (fun z : Tile 3 × ℕ => shellScales z.1 z.2) := by
    unfold shellScales
    fun_prop
  have ht : Computable (fun z : Tile 3 × Tile 3 × ℕ =>
      (z.1.dedup, shell z.2.1 z.2.2, shellScales z.2.1 z.2.2)) :=
    (dedup_primrec.to_comp.comp Computable.fst).pair
      ((shell_computable.pair hs.to_comp).comp Computable.snd)
  have hh := Computable.comp
    (f:=fun z : Tile 3 × Tile 3 × (Fin 3 → ℕ) =>
      z.1.flatMap fun u => z.2.1.map fun v => gridMap z.2.2 u+v)
    (g:=fun z : Tile 3 × Tile 3 × ℕ => (z.1.dedup, shell z.2.1 z.2.2, shellScales z.2.1 z.2.2))
    ha.to_comp ht
  exact (dedup_primrec (α:=Lattice 3)).to_comp.comp hh

theorem mem_assemble (E X : Tile 3) (B : ℕ) (x : Lattice 3) :
    x ∈ assemble E X B ↔ ∃ u ∈ E, ∃ v ∈ shell X B, x=gridMap (shellScales X B) u+v := by
  simp only [assemble,List.mem_dedup,List.mem_flatMap,List.mem_map,eq_comm]

include hX

private theorem shell_shape (B : ℕ) :
    {v | v∈shell X B}=Shape X.length (B+1) (slotCode X)
      (tablePermutation _ _ (matching_spec X (required X hX)).1)
      (tablePermutation _ _ (matching_spec X (required X hX)).2.1) := by
  ext v
  have hm := matching_spec X (required X hX)
  exact shapeList_mem X (B+1) (matching X).1 (matching X).2 hm.1 hm.2.1 v

theorem correct (E : Tile 3) (B : ℕ) :
    TranslationTiling.Tiles (assemble E X B) ↔ TranslationTiling.Tiles E := by
  have he : {x | x∈assemble E X B}=Assembly (gridMap (shellScales X B)) {u | u∈E}
      {v | v∈shell X B} := by
    ext x
    exact mem_assemble E X B x
  change (∃ C,ExactTiling C {x | x∈assemble E X B}) ↔ _
  rw [he]
  apply (shell_assembly_iff _ (gridMap_injective (scales_pos _ _)) _ _ ?_ ?_).symm
  · rw [shell_shape X hX]
    exact shape_fundamental X.length (B+1) _ _ _
  · intro C hC
    rw [shell_shape X hX] at hC
    exact shape_rigidity _ _ _ (slot_zero X hX) _ _ C hC

theorem nonempty (E : Tile 3) (B : ℕ) (hne : E≠[]) : assemble E X B≠[] := by
  have hf : ExactTiling (Set.range (gridMap (shellScales X B))) {v | v∈shell X B} := by
    rw [shell_shape X hX]
    exact shape_fundamental X.length (B+1) _ _ _
  obtain ⟨⟨_,v⟩,_⟩ := hf.2 0
  obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil E hne
  have hv := (mem_assemble E X B _).mpr ⟨u,hu,v.val,v.property,rfl⟩
  intro he
  rw [he] at hv
  exact List.not_mem_nil hv

theorem length_le (E : Tile 3) (B a : ℕ) (ha : X.length≤a) :
    (assemble E X B).length≤E.dedup.length*(216*(4*a+7*(B+2)+1)*(4*a+1)) := by
  have hm := matching_spec X (required X hX)
  have hs := shapeList_length_le X (B+1) (matching X).1 (matching X).2 hm.1 hm.2.1
  have ht : (shell X B).length≤216*(4*a+7*(B+2)+1)*(4*a+1) := by
    apply hs.trans
    unfold lengthX lengthY
    gcongr
  unfold assemble
  rw [←List.card_toFinset]
  apply (List.toFinset_card_le _).trans
  simp [List.length_flatMap,Function.comp_def,List.map_const,List.sum_replicate]
  exact Nat.mul_le_mul_left _ ht

/-! The permitted jumps are the differences represented by a horizontal and a vertical slot. -/
def Hop (B : ℕ) (u v : Lattice 3) : Prop :=
  (v 2-u 2).natAbs≤B ∧ point (u 0-v 0) (u 1-v 1) 0∈X ∧
    point (v 0-u 0) (v 1-u 1) 0∈X

omit hX in
theorem Hop.symm {B : ℕ} {u v : Lattice 3} (h : Hop X B u v) : Hop X B v u := by
  refine ⟨?_,h.2.2,h.2.1⟩
  rw [show u 2-v 2=-(v 2-u 2) by ring,Int.natAbs_neg]
  exact h.1

private theorem slotSet (B i : ℕ) :
    Used X.length (B+1) i → slotCode X i∈X ∨
      ∃ k : ℕ, k≤B ∧ slotCode X i=point 0 0 k := by
  rintro (hi | ⟨k,hk,hkb,rfl⟩)
  · left
    simp only [slotCode,if_pos hi,List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · right
    exact ⟨k,by omega,slot_large X hX _ hk⟩

private theorem slot_path (B : ℕ)
    (hconn : ∀ v∈X, FacePath {v | v∈X} v 0) (i j : ℕ)
    (hi : Used X.length (B+1) i) (hj : Used X.length (B+1) j) :
    FacePath (fun v => ∃ k, Used X.length (B+1) k ∧ slotCode X k=v)
      (slotCode X i) (slotCode X j) := by
  have hor (v : Lattice 3) (hv : v∈X) :
      ∃ k, Used X.length (B+1) k ∧ slotCode X k=v := by
    obtain ⟨k,hk⟩ := (FourLayer.mem_range_slots X v).mpr hv
    exact ⟨k.val,Or.inl k.isLt,(slot_small X hX k).trans hk⟩
  have vert (k : ℕ) (hk : k≤B) :
      ∃ j, Used X.length (B+1) j ∧ slotCode X j=point 0 0 k := by
    refine ⟨railLabel X.length k,?_,slot_rail X hX k⟩
    by_cases hz : k=0
    · subst k
      exact Or.inl (by simpa [railLabel] using NeZero.pos X.length)
    · exact Or.inr ⟨k,by omega,by omega,by simp [railLabel,hz]⟩
  have path (i : ℕ) (hi : Used X.length (B+1) i) :
      FacePath (fun v => ∃ k, Used X.length (B+1) k ∧ slotCode X k=v) (slotCode X i) 0 := by
    rcases slotSet X hX B i hi with hh | ⟨k,hk,he⟩
    · exact FacePath.mono (hconn _ hh) hor
    · rw [he]
      apply FacePath.box3 _ (0 : Lattice 3) ![0,0,(k:ℤ)]
      · intro j; fin_cases j <;> simp [point]
      · intro j; fin_cases j <;> simp
      · intro z hz
        have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
        simp at h0 h1 h2
        have he' : z=point 0 0 (z 2).toNat := by
          ext j; fin_cases j <;> simp [point] <;> omega
        rw [he']
        exact vert _ (by omega)
  exact (path i hi).trans (FacePath.reverse (path j hj))

private theorem shell_connected (B : ℕ)
    (hc : ∀ v∈X, FacePath {v | v∈X} v 0) : FaceConnected (shell X B) := by
  have hm := matching_spec X (required X hX)
  change ∀ v∈{v | v∈shell X B}, ∀ w∈{v | v∈shell X B}, FacePath {v | v∈shell X B} v w
  rw [shell_shape X hX]
  exact shape_connected _ _ _ (slot_zero X hX) (slot_injective X hX (B+1)) _ _
    (slot_ports X hX (B+1) _ _
      (tablePermutation_match _ _ hm.1 0 hm.2.2.1)
      (tablePermutation_match _ _ hm.2.1 1 hm.2.2.2))
    (slot_path X hX B hc)

private theorem contact (B : ℕ) {u v : Lattice 3} (h : Hop X B u v) :
    ∃ a∈shell X B, ∃ b∈shell X B,
      FaceAdjacent (gridMap (shellScales X B) u+a) (gridMap (shellScales X B) v+b) := by
  have hm := matching_spec X (required X hX)
  have forward (u v : Lattice 3) (h : Hop X B u v) (hle : u 2≤v 2) :
      ∃ a∈shell X B, ∃ b∈shell X B,
        FaceAdjacent (gridMap (shellScales X B) u+a) (gridMap (shellScales X B) v+b) := by
    obtain ⟨j,hj⟩ := (FourLayer.mem_range_slots X _).mpr h.2.1
    let k : Fin (B+1) := ⟨(v 2-u 2).toNat,by have := h.1; omega⟩
    have he : u+slotCode X (railLabel X.length k.val)=v+slotCode X j.val := by
      rw [slot_rail X hX,slot_small X hX,hj]
      ext i; fin_cases i <;> simp [point,k] <;> omega
    obtain ⟨a,ha,b,hb,hface⟩ := shape_contacts X.length (B+1) (slotCode X)
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) k j he
    exact ⟨a,(congrArg (fun S : Set (Lattice 3) => a∈S) (shell_shape X hX B)).mpr ha,
      b,(congrArg (fun S : Set (Lattice 3) => b∈S) (shell_shape X hX B)).mpr hb,hface⟩
  by_cases hle : u 2≤v 2
  · exact forward u v h hle
  · obtain ⟨b,hb,a,ha,hface⟩ := forward v u (h.symm) (by omega)
    exact ⟨a,ha,b,hb,FacePath.adjacent_symm hface⟩

theorem connected (E : Tile 3) (B : ℕ)
    (hc : ∀ v∈X, FacePath {v | v∈X} v 0)
    (hE : ∀ u∈E, ∀ v∈E, Relation.ReflTransGen
      (fun a b => a∈E ∧ b∈E ∧ Hop X B a b) u v) :
    FaceConnected (assemble E X B) := by
  intro x hx y hy
  obtain ⟨u,hu,a,ha,rfl⟩ := (mem_assemble E X B x).mp hx
  obtain ⟨v,hv,b,hb,rfl⟩ := (mem_assemble E X B y).mp hy
  have within (w : Lattice 3) (hw : w∈E) (c d : Lattice 3) (hc' : c∈shell X B) (hd : d∈shell X B) :
      FacePath {x | x∈assemble E X B} (gridMap (shellScales X B) w+c) (gridMap (shellScales X B) w+d) := by
    apply Relation.ReflTransGen.lift (fun z => gridMap (shellScales X B) w+z) _ c d
      (shell_connected X hX B hc c hc' d hd)
    intro a b hab
    exact ⟨(mem_assemble E X B _).mpr ⟨w,hw,a,hab.1,rfl⟩,
      (mem_assemble E X B _).mpr ⟨w,hw,b,hab.2.1,rfl⟩,Kim.adjacent_add_left _ hab.2.2⟩
  have route (w : Lattice 3) (hw : w∈E)
      (h : Relation.ReflTransGen (fun a b => a∈E ∧ b∈E ∧ Hop X B a b) u w) :
      ∀ d∈shell X B, FacePath {x | x∈assemble E X B}
        (gridMap (shellScales X B) u+a) (gridMap (shellScales X B) w+d) := by
    induction h with
    | refl => exact fun d hd => within u hu a d ha hd
    | @tail w w' h hstep ih =>
      intro d hd
      obtain ⟨c,hc',e,he,hface⟩ := contact X hX B hstep.2.2
      exact (ih hstep.1 c hc').trans ((FacePath.step
        ((mem_assemble E X B _).mpr ⟨w,hstep.1,c,hc',rfl⟩)
        ((mem_assemble E X B _).mpr ⟨w',hstep.2.1,e,he,rfl⟩) hface).trans
        (within w' hstep.2.1 e d he hd))
  exact route v hv (hE u hu v hv) b hb

end
end TranslationTiling.Rails.SlotAssembly
