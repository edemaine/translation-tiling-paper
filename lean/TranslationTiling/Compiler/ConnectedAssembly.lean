import TranslationTiling.Compiler.LatticeCompiler
import TranslationTiling.External.Kim
import TranslationTiling.Proofs.KimShellConnectivity
import TranslationTiling.Proofs.ShellAssembly
import TranslationTiling.Proofs.Translation
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases

namespace TranslationTiling.Compiler

open scoped Classical
noncomputable section

/-- Replace each lattice point by a translate of Kim's shell. -/
def connectedAssembly (E : Tile 3) (l : ℕ) : Tile 3 :=
  E.flatMap fun u => (Kim.shell l).map fun v =>
    (Kim.scale (Kim.boundary l).length : ℤ) • u + v

theorem mem_connectedAssembly (E : Tile 3) (l : ℕ) (x : Lattice 3) :
    x ∈ connectedAssembly E l ↔ ∃ u ∈ E, ∃ v ∈ Kim.shell l,
      x = (Kim.scale (Kim.boundary l).length : ℤ) • u + v := by
  simp only [connectedAssembly, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    exact ⟨u, hu, v, hv, he.symm⟩
  · rintro ⟨u, hu, v, hv, he⟩
    exact ⟨u, hu, v, hv, he.symm⟩

private def shellScaleHom (l : ℕ) : Lattice 3 →+ Lattice 3 where
  toFun u := (Kim.scale (Kim.boundary l).length : ℤ) • u
  map_zero' := smul_zero _
  map_add' := smul_add _

private theorem shellScaleHom_injective (l : ℕ) :
    Function.Injective (shellScaleHom l) := by
  intro u v h
  funext i
  have hi := congrFun h i
  change (Kim.scale (Kim.boundary l).length : ℤ) * u i =
    (Kim.scale (Kim.boundary l).length : ℤ) * v i at hi
  apply mul_left_cancel₀ _ hi
  have hp : 0 < Kim.scale (Kim.boundary l).length := by unfold Kim.scale; omega
  exact_mod_cast hp.ne'

/-- Coverage is proved; the tilability converse only needs coset rigidity. -/
theorem connectedAssembly_tiles_iff_of_cosets (E : Tile 3) (l : ℕ) (hl : 0 < l)
    (hcoset : ∀ A : Set (Lattice 3), ExactTiling A {x | x ∈ Kim.shell l} →
      ∃ t, A = Kim.gridCoset (Kim.scale (Kim.boundary l).length) t) :
    TranslationTiling.Tiles (connectedAssembly E l) ↔ TranslationTiling.Tiles E := by
  have hfund := Kim.shell_exactTiling l hl
  have hrange : Set.range (shellScaleHom l) =
      Kim.gridCoset (Kim.scale (Kim.boundary l).length) 0 := by
    ext x
    simp only [Set.mem_range, Kim.gridCoset, Set.mem_setOf_eq, zero_add]
    exact exists_congr fun z => eq_comm
  have hset : {x | x ∈ connectedAssembly E l} =
      Assembly (shellScaleHom l) {u | u ∈ E} {v | v ∈ Kim.shell l} := by
    ext x
    exact mem_connectedAssembly E l x
  change (∃ B, ExactTiling B {x | x ∈ connectedAssembly E l}) ↔ _
  rw [hset]
  exact (shell_assembly_iff (shellScaleHom l) (shellScaleHom_injective l)
    {u | u ∈ E} {v | v ∈ Kim.shell l} (hrange.symm ▸ hfund) hcoset).symm

theorem connectedAssembly_tiles_iff (rigid : Kim.Rigidity) (E : Tile 3)
    (l : ℕ) (hl : 3 ≤ l) :
    TranslationTiling.Tiles (connectedAssembly E l) ↔ TranslationTiling.Tiles E :=
  connectedAssembly_tiles_iff_of_cosets E l (by omega) (rigid l hl).2.2.2

private theorem adjacent_translate (t : Lattice 3) {a b : Lattice 3}
    (h : FaceAdjacent a b) : FaceAdjacent (t + a) (t + b) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl (by rw [hi, add_assoc])
  · exact Or.inr (by rw [hi, add_assoc])

/-- The contact property is proved; connectivity only needs a connected shell. -/
theorem connectedAssembly_connected_of_shell (E : Tile 3) (l : ℕ)
    (hconn : FaceConnected (Kim.shell l)) (hE : ∀ u ∈ E, u ∈ Kim.cube l) :
    FaceConnected (connectedAssembly E l) := by
  intro x hx y hy
  obtain ⟨u, hu, a, ha, rfl⟩ := (mem_connectedAssembly E l x).mp hx
  obtain ⟨v, hv, b, hb, rfl⟩ := (mem_connectedAssembly E l y).mp hy
  let s : ℤ := Kim.scale (Kim.boundary l).length
  have hpath (w : Lattice 3) (hw : w ∈ E) (c d : Lattice 3)
      (hc : c ∈ Kim.shell l) (hd : d ∈ Kim.shell l) :
      Relation.ReflTransGen (fun a b => a ∈ connectedAssembly E l ∧
        b ∈ connectedAssembly E l ∧ FaceAdjacent a b) (s • w + c) (s • w + d) := by
    apply Relation.ReflTransGen.lift (fun z => s • w + z) _ (hconn c hc d hd)
    intro a b hab
    exact ⟨(mem_connectedAssembly E l _).mpr ⟨w, hw, a, hab.1, rfl⟩,
      (mem_connectedAssembly E l _).mpr ⟨w, hw, b, hab.2.1, rfl⟩,
      adjacent_translate _ hab.2.2⟩
  by_cases huv : u = v
  · subst v
    exact hpath u hu a b ha hb
  · obtain ⟨c, hc, d, hd, hcd⟩ := Kim.shell_contacts l (hE u hu) (hE v hv) huv
    exact (hpath u hu a c ha hc).trans
      ((Relation.ReflTransGen.single
        ⟨(mem_connectedAssembly E l _).mpr ⟨u, hu, c, hc, rfl⟩,
          (mem_connectedAssembly E l _).mpr ⟨v, hv, d, hd, rfl⟩, hcd⟩).trans
        (hpath v hv d b hd hb))

theorem connectedAssembly_connected (E : Tile 3)
    (l : ℕ) (hl : 0 < l) (hE : ∀ u ∈ E, u ∈ Kim.cube l) :
    FaceConnected (connectedAssembly E l) :=
  connectedAssembly_connected_of_shell E l (Kim.shell_connected l hl) hE

theorem connectedAssembly_nonempty (E : Tile 3)
    (l : ℕ) (hl : 0 < l) (hE : E ≠ []) : connectedAssembly E l ≠ [] := by
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil (Kim.shell l) (Kim.shell_nonempty l hl)
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil E hE
  intro he
  have hm := (mem_connectedAssembly E l _).mpr ⟨u, hu, v, hv, rfl⟩
  simp [he] at hm

end
end TranslationTiling.Compiler
