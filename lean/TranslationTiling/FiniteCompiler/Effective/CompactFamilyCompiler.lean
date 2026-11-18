import TranslationTiling.FiniteCompiler.Effective.FamilyCompiler

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def familyTileAt (z : (ParameterData × List CyclicTile) × ℕ) : Tile 3 :=
  let c := familyCyclic z.1
  Rails.connectedTile (Compiler.integerTile c) z.2 (max (z.2^2) c.1)

theorem familyTileAt_computable : Computable familyTileAt := by
  have hc : Computable (fun z : (ParameterData × List CyclicTile) × ℕ => familyCyclic z.1) :=
    familyCyclic_computable.comp Computable.fst
  have hE := Compiler.integerTile_computable.comp hc
  have hp : Primrec (fun z : (ParameterData × List CyclicTile) × ℕ => z.2^2) := by fun_prop
  have hm : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  exact (Rails.connectedTile_computable.comp (hE.pair
    (Computable.snd.pair (hm.to_comp.comp (hp.to_comp.pair (Computable.fst.comp hc)))))).of_eq
    (fun _ => rfl)

theorem familyTileAt_facts (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) (hB : T.alphabet=3) (hw : 48≤T.width)
    (H : ℕ) (hH : 1≤H)
    (hxy : ∀ F∈G, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H) :
    familyTileAt ((parameterData T,G),H)≠[] ∧
    FaceConnected (familyTileAt ((parameterData T,G),H)) ∧
    ((∃ B : Set (Plane × ZMod (parameters T).cyclicOrder),
      ∀ i : Fin G.length, Tiles (cyclicTileSet (parameters T).cyclicOrder (G.getD i.val [])) B) ↔
      TranslationTiling.Tiles (familyTileAt ((parameterData T,G),H))) ∧
    (familyTileAt ((parameterData T,G),H)).length≤
      (2^24*(MassSize.mass (parameters T)*freshCap (max G.length (primeBudget T^2)) (primeBudget T^4)))*
      (549072*8003^4)*H^2*
      max (H^2) ((parameters T).cyclicOrder*freshCap (max G.length (primeBudget T^2)) (primeBudget T^4)) := by
  let C := primeBudget T
  let X := max G.length (C^2)
  have hP : C^4≤X^2 := by
    calc
      C^4 = (C^2)^2 := by ring
      _ ≤ X^2 := Nat.pow_le_pow_left (le_max_right G.length (C^2)) 2
  have hpr := BudgetSize.cyclicOrder_primeBound (parameters T) hB
    (parameters_bounded_budget T hB) (le_max_right _ _)
  have heq : familyCyclic (parameterData T,G)=freshStack (X,(parameters T).cyclicOrder,C^4,G) := by
    unfold familyCyclic; rw [rawOrder_eq]; rfl
  obtain ⟨hm,hne,hR,hiff⟩ := freshStack_facts X (parameters T).cyclicOrder (C^4) G
    (parameters T).cyclicOrder_pos hf.length_pos (le_max_left _ _) hP hpr hf.nonempty
  have hmass := freshStack_mass X (parameters T).cyclicOrder (C^4) G
    (parameters T).cyclicOrder_pos hf.length_pos (le_max_left _ _) hP hpr _ hf.mass
  have hstack : ∀ f∈(freshStack (X,(parameters T).cyclicOrder,C^4,G)).2,
      f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H := stackCodes_horizontal _ _ G H hxy
  unfold familyTileAt
  rw [heq]
  generalize hd : freshStack (X,(parameters T).cyclicOrder,C^4,G)=d at hm hne hR hiff hmass hstack ⊢
  have hM : d.1≤max (H^2) d.1 := le_max_right _ _
  have hrect := Compiler.Size.integerTile_rectangle_bound d H (max (H^2) d.1) hm hM hne hstack
  refine ⟨Rails.connectedTile_nonempty _ _ _ (Compiler.integerTile_nonempty d hne),
    Rails.connectedTile_connected _ _ _ hrect,?_,?_⟩
  · exact hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
      (Rails.connectedTile_correct _ H (max (H^2) d.1)).symm)
  · have hvol := Compiler.Size.integerTile_cubeCount_mass d hm
    have hh := Rails.connectedTile_length_mass (Compiler.integerTile d) H (max (H^2) d.1) hH (le_max_left _ _)
    apply hh.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hvol.trans (Nat.mul_le_mul_left _ hmass)))) (max_le_max_left _ hR)

end
end TranslationTiling.FiniteCompiler.Effective
