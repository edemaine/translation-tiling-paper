import TranslationTiling.Rails.EffectiveShape
import TranslationTiling.Proofs.ShellAssembly
import TranslationTiling.Proofs.Translation

namespace TranslationTiling.Rails
open FourLayer (gridMap Rect gridCoset gridMap_injective matching matching_spec matching_computable tablePermutation tablePermutation_match)
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def shell (A B : ℕ) : Tile 3 :=
  let X := planeList A
  shapeList X (B+1) (matching X).1 (matching X).2

set_option maxHeartbeats 50000 in
theorem shell_computable : Computable (fun z : ℕ×ℕ => shell z.1 z.2) := by
  have hx : Primrec (fun z : ℕ×ℕ => planeList z.1) := planeList_primrec.comp Primrec.fst
  have hm := matching_computable.comp hx.to_comp
  have ht : Computable (fun z : ℕ×ℕ => (planeList z.1,z.2+1,(matching (planeList z.1)).1,(matching (planeList z.1)).2)) :=
    hx.to_comp.pair ((show Primrec (fun z : ℕ×ℕ => z.2+1) by fun_prop).to_comp.pair
      ((Computable.fst.comp hm).pair (Computable.snd.comp hm)))
  have hout := Computable.comp
    (f:=fun z : Tile 3×ℕ×List ℕ×List ℕ => shapeList z.1 z.2.1 z.2.2.1 z.2.2.2)
    (g:=fun z : ℕ×ℕ => (planeList z.1,z.2+1,(matching (planeList z.1)).1,(matching (planeList z.1)).2))
    shapeList_primrec.to_comp ht
  exact hout

def shellScales (A B : ℕ) := scales (planeList A).length (B+1)

@[fun_prop] theorem shellScales_primrec : Primrec (fun z : ℕ×ℕ => shellScales z.1 z.2) := by
  unfold shellScales; fun_prop

theorem shell_shape (A B : ℕ) :
    {v | v∈shell A B}=Shape (planeList A).length (B+1) (slot A)
      (tablePermutation _ _ (matching_spec (planeList A) (planeList_required A)).1)
      (tablePermutation _ _ (matching_spec (planeList A) (planeList_required A)).2.1) := by
  ext v
  have hm := matching_spec (planeList A) (planeList_required A)
  have hh := shapeList_mem (planeList A) (B+1) (matching (planeList A)).1 (matching (planeList A)).2 hm.1 hm.2.1 v
  have hs : slotCode (planeList A)=slot A := funext (slotCode_plane A)
  rw [hs] at hh
  exact hh

theorem shell_fundamental (A B : ℕ) :
    ExactTiling (Set.range (gridMap (shellScales A B))) {v | v∈shell A B} := by
  rw [shell_shape]
  exact shape_fundamental _ _ _ _ _

theorem shell_rigidity (A B : ℕ) (C : Set (Lattice 3))
    (hC : ExactTiling C {v | v∈shell A B}) : ∃ t, C=gridCoset (shellScales A B) t := by
  rw [shell_shape] at hC
  exact shape_rigidity _ _ _ (slot_zero A) _ _ C hC

theorem shell_connected (A B : ℕ) : FaceConnected (shell A B) := by
  have hm := matching_spec (planeList A) (planeList_required A)
  change ∀ v∈{v | v∈shell A B}, ∀ w∈{v | v∈shell A B}, FacePath {v | v∈shell A B} v w
  rw [shell_shape]
  exact shape_connected _ _ _ (slot_zero A) (slot_injective A (B+1)) _ _
    (slot_ports A (B+1) _ _
      (tablePermutation_match _ _ hm.1 0 hm.2.2.1)
      (tablePermutation_match _ _ hm.2.1 1 hm.2.2.2))
    (fun i j hi hj => slot_path A (B+1) i j (by omega) hi hj)

theorem shell_contacts (A B : ℕ) (hA : 0<A) (hAB : A^2≤B) {u v : Lattice 3}
    (hu : Rect ![A,A,B] u) (hv : Rect ![A,A,B] v) (hne : u≠v) :
    ∃ a∈shell A B, ∃ b∈shell A B,
      FaceAdjacent (gridMap (shellScales A B) u+a) (gridMap (shellScales A B) v+b) := by
  have hB : 0<B := by nlinarith
  have hm := matching_spec (planeList A) (planeList_required A)
  obtain ⟨i,j,he | he⟩ := slot_difference A B hA hB hu hv
  · obtain ⟨r,hr,t,ht,hadj⟩ := shape_contacts (planeList A).length (B+1) (slot A)
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) ⟨i.val,by omega⟩ j he
    exact ⟨r,(congrArg (fun S : Set (Lattice 3) => r∈S) (shell_shape A B)).mpr hr,
      t,(congrArg (fun S : Set (Lattice 3) => t∈S) (shell_shape A B)).mpr ht,hadj⟩
  · obtain ⟨r,hr,t,ht,hadj⟩ := shape_contacts (planeList A).length (B+1) (slot A)
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) ⟨i.val,by omega⟩ j he
    exact ⟨t,(congrArg (fun S : Set (Lattice 3) => t∈S) (shell_shape A B)).mpr ht,
      r,(congrArg (fun S : Set (Lattice 3) => r∈S) (shell_shape A B)).mpr hr,FacePath.adjacent_symm hadj⟩

theorem shell_length_le (A B : ℕ) (hA : 0<A) (hAB : A^2≤B) :
    (shell A B).length≤549072*A^2*B := by
  have hm := matching_spec (planeList A) (planeList_required A)
  have hlen := shapeList_length_le (planeList A) (B+1) (matching (planeList A)).1 (matching (planeList A)).2 hm.1 hm.2.1
  have ha := planeList_length_le A hA
  have hB : 1≤B := by nlinarith
  have hx : lengthX (planeList A).length (B+1)≤62*B := by unfold lengthX; omega
  have hy : lengthY (planeList A).length≤41*A^2 := by unfold lengthY; nlinarith
  calc
    _ ≤ 216*(lengthX (planeList A).length (B+1))*(lengthY (planeList A).length) := hlen
    _ ≤ 216*(62*B)*(41*A^2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hx) hy
    _ = _ := by ring

def assembly (E : Tile 3) (A B : ℕ) : Tile 3 :=
  E.flatMap fun u => (shell A B).map fun v => gridMap (shellScales A B) u+v

theorem mem_assembly (E : Tile 3) (A B : ℕ) (x : Lattice 3) :
    x∈assembly E A B ↔ ∃ u∈E, ∃ v∈shell A B, x=gridMap (shellScales A B) u+v := by
  simp only [assembly,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨u,hu,v,hv,he⟩; exact ⟨u,hu,v,hv,he.symm⟩
  · rintro ⟨u,hu,v,hv,he⟩; exact ⟨u,hu,v,hv,he.symm⟩

theorem assembly_correct (E : Tile 3) (A B : ℕ) :
    TranslationTiling.Tiles (assembly E A B) ↔ TranslationTiling.Tiles E := by
  have he : {x | x∈assembly E A B}=Assembly (gridMap (shellScales A B)) {u | u∈E} {v | v∈shell A B} := by
    ext x; exact mem_assembly E A B x
  change (∃ C,ExactTiling C {x | x∈assembly E A B}) ↔ _
  rw [he]
  exact (shell_assembly_iff _ (gridMap_injective (scales_pos _ _)) _ _ (shell_fundamental A B)
    (shell_rigidity A B)).symm

theorem assembly_connected (E : Tile 3) (A B : ℕ) (hA : 0<A) (hAB : A^2≤B)
    (hE : ∀ u∈E, Rect ![A,A,B] u) : FaceConnected (assembly E A B) := by
  intro x hx y hy
  obtain ⟨u,hu,a,ha,rfl⟩ := (mem_assembly E A B x).mp hx
  obtain ⟨v,hv,b,hb,rfl⟩ := (mem_assembly E A B y).mp hy
  have path (w : Lattice 3) (hw : w∈E) (c d : Lattice 3) (hc : c∈shell A B) (hd : d∈shell A B) :
      FacePath {x | x∈assembly E A B} (gridMap (shellScales A B) w+c) (gridMap (shellScales A B) w+d) := by
    apply Relation.ReflTransGen.lift (fun z => gridMap (shellScales A B) w+z) _ c d (shell_connected A B c hc d hd)
    intro a b hab
    exact ⟨(mem_assembly E A B _).mpr ⟨w,hw,a,hab.1,rfl⟩,
      (mem_assembly E A B _).mpr ⟨w,hw,b,hab.2.1,rfl⟩,Kim.adjacent_add_left _ hab.2.2⟩
  by_cases he : u=v
  · subst v; exact path u hu a b ha hb
  · obtain ⟨c,hc,d,hd,hadj⟩ := shell_contacts A B hA hAB (hE u hu) (hE v hv) he
    exact (path u hu a c ha hc).trans ((FacePath.step
      ((mem_assembly E A B _).mpr ⟨u,hu,c,hc,rfl⟩)
      ((mem_assembly E A B _).mpr ⟨v,hv,d,hd,rfl⟩) hadj).trans (path v hv d b hd hb))

theorem assembly_nonempty (E : Tile 3) (A B : ℕ) (hE : E≠[]) : assembly E A B≠[] := by
  obtain ⟨⟨_,v⟩,_⟩ := (shell_fundamental A B).2 0
  obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil E hE
  intro he
  have h := (mem_assembly E A B _).mpr ⟨u,hu,v.val,v.property,rfl⟩
  simp [he] at h

end
end TranslationTiling.Rails
