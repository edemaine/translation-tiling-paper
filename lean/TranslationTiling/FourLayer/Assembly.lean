import TranslationTiling.FourLayer.EffectiveShape
import TranslationTiling.Proofs.ShellAssembly
import TranslationTiling.Proofs.Translation

namespace TranslationTiling.FourLayer
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def shell (A B : ℕ) : Tile 3 :=
  let X := boundaryList A B
  shapeList X (matching X).1 (matching X).2

set_option maxHeartbeats 50000 in
theorem shell_computable : Computable (fun z : ℕ×ℕ => shell z.1 z.2) := by
  have h : Computable (fun X : Tile 3 => shapeList X (matching X).1 (matching X).2) := by
    have hf : Computable (fun X : Tile 3 => (X,(matching X).1,(matching X).2)) :=
      Computable.id.pair ((Computable.fst.comp matching_computable).pair (Computable.snd.comp matching_computable))
    exact Computable.comp (f:=fun z : Tile 3×List ℕ×List ℕ => shapeList z.1 z.2.1 z.2.2)
      (g:=fun X : Tile 3 => (X,(matching X).1,(matching X).2)) shapeList_primrec.to_comp hf
  exact Computable.comp (f:=fun X : Tile 3 => shapeList X (matching X).1 (matching X).2)
    (g:=fun z : ℕ×ℕ => boundaryList z.1 z.2) h boundaryList_primrec.to_comp

def shellScales (A B : ℕ) := scales (boundaryList A B).length

@[fun_prop] theorem shellScales_primrec : Primrec (fun z : ℕ×ℕ => shellScales z.1 z.2) := by
  unfold shellScales; fun_prop

theorem shell_fundamental (A B : ℕ) :
    ExactTiling (Set.range (gridMap (shellScales A B))) {v | v∈shell A B} := by
  have hm := matching_spec (boundaryList A B) (boundaryList_required A B)
  have he : {v | v∈shell A B}=Shape (boundaryList A B).length (slots (boundaryList A B))
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) := by
    ext v; exact shapeList_mem _ _ _ hm.1 hm.2.1 v
  rw [he]
  exact shape_fundamental _ _ _ _

theorem shell_rigidity (A B : ℕ) (C : Set (Lattice 3))
    (hC : ExactTiling C {v | v∈shell A B}) : ∃ t, C=gridCoset (shellScales A B) t := by
  have hm := matching_spec (boundaryList A B) (boundaryList_required A B)
  have he : {v | v∈shell A B}=Shape (boundaryList A B).length (slots (boundaryList A B))
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) := by
    ext v; exact shapeList_mem _ _ _ hm.1 hm.2.1 v
  rw [he] at hC
  exact shape_rigidity _ _ (boundary_slots_zero A B) _ _ C hC

theorem shell_connected (A B : ℕ) (hA : 0<A) (hAB : A≤B) : FaceConnected (shell A B) := by
  have hm := matching_spec (boundaryList A B) (boundaryList_required A B)
  have he : {v | v∈shell A B}=Shape (boundaryList A B).length (slots (boundaryList A B))
      (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) := by
    ext v; exact shapeList_mem _ _ _ hm.1 hm.2.1 v
  change ∀ v∈{v | v∈shell A B}, ∀ w∈{v | v∈shell A B}, FacePath {v | v∈shell A B} v w
  rw [he]
  exact shape_connected _ _ (boundary_slots_zero A B) (slots_injective _ (boundaryList_required A B)) _ _
    (tablePermutation_match _ _ hm.1 0 hm.2.2.1)
    (tablePermutation_match _ _ hm.2.1 1 hm.2.2.2) (boundary_slots_path A B hA hAB)

theorem shell_contacts (A B : ℕ) (hA : 0<A) (hAB : A≤B) {u v : Lattice 3}
    (hu : Rect ![A,A,B] u) (hv : Rect ![A,A,B] v) (hne : u≠v) :
    ∃ a∈shell A B, ∃ b∈shell A B,
      FaceAdjacent (gridMap (shellScales A B) u+a) (gridMap (shellScales A B) v+b) := by
  have hm := matching_spec (boundaryList A B) (boundaryList_required A B)
  obtain ⟨i,j,hij,he⟩ := boundary_slots_difference A B hA hAB hu hv hne
  obtain ⟨a,ha,b,hb,hadj⟩ := shape_contacts _ (slots (boundaryList A B))
    (tablePermutation _ _ hm.1) (tablePermutation _ _ hm.2.1) hij he
  exact ⟨a,(shapeList_mem _ _ _ hm.1 hm.2.1 a).mpr ha,
    b,(shapeList_mem _ _ _ hm.1 hm.2.1 b).mpr hb,hadj⟩

theorem shell_length_le (A B : ℕ) (hA : 0<A) (hAB : A≤B) :
    (shell A B).length≤972*(6*A*B)^2 := by
  have hm := matching_spec (boundaryList A B) (boundaryList_required A B)
  exact (shapeList_length_le _ _ _ hm.1 hm.2.1).trans
    (Nat.mul_le_mul_left 972 (Nat.pow_le_pow_left (boundaryList_length_le A B hA hAB) 2))

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
  exact (shell_assembly_iff _ (gridMap_injective (scales_pos _)) _ _ (shell_fundamental A B)
    (shell_rigidity A B)).symm

theorem assembly_connected (E : Tile 3) (A B : ℕ) (hA : 0<A) (hAB : A≤B)
    (hE : ∀ u∈E, Rect ![A,A,B] u) : FaceConnected (assembly E A B) := by
  intro x hx y hy
  obtain ⟨u,hu,a,ha,rfl⟩ := (mem_assembly E A B x).mp hx
  obtain ⟨v,hv,b,hb,rfl⟩ := (mem_assembly E A B y).mp hy
  have path (w : Lattice 3) (hw : w∈E) (c d : Lattice 3) (hc : c∈shell A B) (hd : d∈shell A B) :
      FacePath {x | x∈assembly E A B} (gridMap (shellScales A B) w+c) (gridMap (shellScales A B) w+d) := by
    apply Relation.ReflTransGen.lift (fun z => gridMap (shellScales A B) w+z) _ c d (shell_connected A B hA hAB c hc d hd)
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
end TranslationTiling.FourLayer
