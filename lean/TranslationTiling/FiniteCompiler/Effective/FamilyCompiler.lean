import TranslationTiling.FiniteCompiler.Effective.SharpCompiler

/-! The quantitative geometric compiler for any bounded family of tests. -/
namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure FamilyBudget (T : System) (Fs : List CyclicTile) : Prop where
  length_pos : 0<Fs.length
  count : Fs.length≤3^(T.width+1)
  nonempty : ∀ F∈Fs, F≠[]
  horizontal : ∀ F∈Fs, ∀ f∈F,
    f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)
  mass : ∀ F∈Fs, (cyclicTileSet (parameters T).cyclicOrder F).card≤MassSize.mass (parameters T)

theorem budget_square_le_three_48 (w : ℕ) (hw : 48≤w) :
    (max (w+2) 256)^2≤3^(w+1) := by
  induction w,hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have hh : max (w+1+2) 256≤max (w+2) 256+1 := by omega
    have hp : 2≤max (w+2) 256 := by omega
    calc
      _ ≤ (max (w+2) 256+1)^2 := Nat.pow_le_pow_left hh _
      _ ≤ 3*(max (w+2) 256)^2 := by nlinarith
      _ ≤ 3*3^(w+1) := Nat.mul_le_mul_left _ ih
      _ = _ := (pow_succ' _ _).symm

def familyCyclic (d : ParameterData × List CyclicTile) : CyclicTileData :=
  let C := max (d.1.1+2) 256
  freshStack (max d.2.length (C^2),rawOrder d.1,C^4,d.2)

theorem familyCyclic_computable : Computable familyCyclic := by
  have hp : Primrec (fun d : ParameterData × List CyclicTile =>
      (max d.2.length ((max (d.1.1+2) 256)^2),rawOrder d.1,(max (d.1.1+2) 256)^4,d.2)) := by fun_prop
  exact freshStack_computable.comp hp.to_comp

def familyTile (d : ParameterData × List CyclicTile) : Tile 3 :=
  let c := familyCyclic d
  let H := rawHorizontal d.1
  Rails.connectedTile (Compiler.integerTile c) H (max (H^2) c.1)

theorem familyTile_computable : Computable familyTile := by
  have hE := Compiler.integerTile_computable.comp familyCyclic_computable
  have hH : Primrec (fun d : ParameterData × List CyclicTile => rawHorizontal d.1) := by fun_prop
  have hmax : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  have hM := hmax.to_comp.comp (((show Primrec (fun d : ParameterData × List CyclicTile => (rawHorizontal d.1)^2) by fun_prop).to_comp).pair (Computable.fst.comp familyCyclic_computable))
  have h := Rails.connectedTile_computable.comp (hE.pair (hH.to_comp.pair hM))
  dsimp only at h
  unfold familyTile
  exact h

theorem familyCyclic_facts (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hw : 48≤T.width) :
    0<(familyCyclic (parameterData T,G)).1 ∧ (familyCyclic (parameterData T,G)).2≠[] ∧
    (familyCyclic (parameterData T,G)).1^30≤primeBudget T^(630*T.width+930)*3^(60*T.width+60) ∧
    (∀ f ∈ (familyCyclic (parameterData T,G)).2,
      f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)) ∧
    ((∃ B : Set (Plane × ZMod (parameters T).cyclicOrder),
      ∀ i : Fin G.length, Tiles (cyclicTileSet (parameters T).cyclicOrder (G.getD i.val [])) B) ↔
      ∃ B : Set (Plane × ZMod (familyCyclic (parameterData T,G)).1),
        Tiles (cyclicTileSet (familyCyclic (parameterData T,G)).1 (familyCyclic (parameterData T,G)).2) B) := by
  let C := primeBudget T
  let Fs := G
  let X := max Fs.length (C^2)
  have hbig : 256≤C := le_max_right _ _
  have hcp : channelCount T≤C := le_max_left _ _
  have hsmall : BudgetPrimes (parameters T) C := parameters_bounded_budget T hB
  have hcount : Fs.length≤3^(T.width+1) := hf.count
  have hX3 : X≤3^(T.width+1) := max_le hcount
    (budget_square_le_three_48 T.width hw)
  have hXhi : X≤C^(8*C) := by
    apply hX3.trans
    apply (Nat.pow_le_pow_left (by omega : 3≤C) _).trans
    exact Nat.pow_le_pow_right (by omega) (by unfold channelCount at hcp; omega)
  have hXlo : C^2≤X := le_max_right _ _
  have hlen : 0<Fs.length := hf.length_pos
  have hP : C^4≤X^2 := by simpa only [← pow_mul] using Nat.pow_le_pow_left hXlo 2
  have hpr := BudgetSize.cyclicOrder_primeBound (parameters T) hB hsmall hbig
  have hraw : familyCyclic (parameterData T,G) = freshStack (X,(parameters T).cyclicOrder,C^4,Fs) := by
    unfold familyCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  obtain ⟨hm,hne,hcap,hiff⟩ := freshStack_facts _ _ _ Fs (parameters T).cyclicOrder_pos hlen
    (le_max_left _ _) hP hpr hf.nonempty
  refine ⟨hm,hne,?_,?_,?_⟩
  · have hv := BudgetSize.cyclicOrder_pow (parameters T) hB hsmall hbig
    have hv30 : (parameters T).cyclicOrder^30≤C^(630*T.width+840) := by
      convert Nat.pow_le_pow_left hv 3 using 1 <;> simp only [← pow_mul] <;> congr 1 <;> ring
    have hell : freshCap X (C^4)≤C^3*3^(2*T.width+2) := by
      apply (FixedSize.freshCap_le hbig hXlo hXhi).trans
      apply Nat.mul_le_mul_left
      convert Nat.pow_le_pow_left hX3 2 using 1 <;> rw [←pow_mul] <;> congr 1 <;> ring
    calc
      _ ≤ ((parameters T).cyclicOrder*freshCap X (C^4))^30 := Nat.pow_le_pow_left hcap _
      _ = (parameters T).cyclicOrder^30*freshCap X (C^4)^30 := by ring
      _ ≤ C^(630*T.width+840)*(C^3*3^(2*T.width+2))^30 :=
        Nat.mul_le_mul hv30 (Nat.pow_le_pow_left hell _)
      _ = C^(630*T.width+930)*3^(60*T.width+60) := by
        simp only [mul_pow,←pow_mul]
        rw [←mul_assoc,←pow_add]
        rw [show 630*T.width+840+3*30=630*T.width+930 by ring,
          show (2*T.width+2)*30=60*T.width+60 by ring]
  · exact stackCodes_horizontal _ _ Fs _ hf.horizontal
  · exact hiff

theorem familyCyclic_mass (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hw : 48≤T.width) :
    (cyclicTileSet (familyCyclic (parameterData T,G)).1 (familyCyclic (parameterData T,G)).2).card≤
      primeBudget T^(12*T.width+23)*3^(2*T.width+2) := by
  let C := primeBudget T
  let Fs := G
  let X := max Fs.length (C^2)
  have hbig : 256≤C := le_max_right _ _
  have hcp : channelCount T≤C := le_max_left _ _
  have hsmall : BudgetPrimes (parameters T) C := parameters_bounded_budget T hB
  have hcount : Fs.length≤3^(T.width+1) := hf.count
  have hX3 : X≤3^(T.width+1) := max_le hcount
    (budget_square_le_three_48 T.width hw)
  have hXhi : X≤C^(8*C) := by
    apply hX3.trans
    apply (Nat.pow_le_pow_left (by omega : 3≤C) _).trans
    exact Nat.pow_le_pow_right (by omega) (by unfold channelCount at hcp; omega)
  have hXlo : C^2≤X := le_max_right _ _
  have hlen : 0<Fs.length := hf.length_pos
  have hP : C^4≤X^2 := by simpa only [← pow_mul] using Nat.pow_le_pow_left hXlo 2
  have hpr := BudgetSize.cyclicOrder_primeBound (parameters T) hB hsmall hbig
  have hraw : familyCyclic (parameterData T,G) = freshStack (X,(parameters T).cyclicOrder,C^4,Fs) := by
    unfold familyCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  have hj := freshStack_mass X (parameters T).cyclicOrder (C^4) Fs
    (parameters T).cyclicOrder_pos hlen (le_max_left _ _) hP hpr _
    hf.mass
  have hell : freshCap X (C^4)≤C^3*3^(2*T.width+2) := by
    apply (FixedSize.freshCap_le hbig hXlo hXhi).trans
    apply Nat.mul_le_mul_left
    convert Nat.pow_le_pow_left hX3 2 using 1 <;> rw [←pow_mul] <;> congr 1 <;> ring
  calc
    _ ≤ MassSize.mass (parameters T)*freshCap X (C^4) := hj
    _ ≤ C^(12*T.width+20)*(C^3*3^(2*T.width+2)) :=
      Nat.mul_le_mul (MassSize.mass_bound (parameters T) hB hsmall) hell
    _ = C^(12*T.width+23)*3^(2*T.width+2) := by
      rw [←mul_assoc,←pow_add,show 12*T.width+20+3=12*T.width+23 by ring]

theorem familyTile_facts (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hw : 48≤T.width) :
    familyTile (parameterData T,G)≠[] ∧ FaceConnected (familyTile (parameterData T,G)) ∧
    ((∃ B : Set (Plane × ZMod (parameters T).cyclicOrder),
      ∀ i : Fin G.length, Tiles (cyclicTileSet (parameters T).cyclicOrder (G.getD i.val [])) B) ↔
      TranslationTiling.Tiles (familyTile (parameterData T,G))) ∧
    (familyTile (parameterData T,G)).length≤primeBudget T^(33*T.width+466)*3^(4*T.width+4) := by
  obtain ⟨hm,hne,hR30,hxy,hiff⟩ := familyCyclic_facts T G hf hS hB hw
  have hcard := familyCyclic_mass T G hf hS hB hw
  dsimp only [familyTile]
  generalize hd : familyCyclic (parameterData T,G)=d at hm hne hR30 hxy hiff hcard ⊢
  let H := rawHorizontal (parameterData T)
  let C := primeBudget T
  let M := max (H^2) d.1
  have hbig : 256≤C := le_max_right _ _
  have heq : rawBudget (parameterData T)=C^9 := by
    change (if T.alphabet=3 then (max (T.width+2) 256)^9 else _)=C^9
    rw [if_pos hB]
    rfl
  have hH : H≤C^200 := by
    change Size.horizontalCap (rawBudget (parameterData T))≤_
    rw [heq]
    exact Size.horizontalCap_channel_nine_le hbig
  have hH1 : 1≤H := by
    exact ((by unfold channelCount; omega : 1≤channelCount T).trans (parameters_rawBudget T hS).2.1).trans (Size.le_horizontalCap _)
  have hR : d.1≤C^(21*T.width+31)*3^(2*T.width+2) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 30≠0)).mp
    simpa only [mul_pow,←pow_mul,show (21*T.width+31)*30=630*T.width+930 by ring,
      show (2*T.width+2)*30=60*T.width+60 by ring] using hR30
  have hMc : M≤C^(21*T.width+31)*3^(2*T.width+2) := by
    apply max_le _ hR
    apply (Nat.pow_le_pow_left hH 2).trans
    rw [←pow_mul]
    apply (Nat.pow_le_pow_right (by omega : 1≤C) (by omega : 200*2≤21*T.width+31)).trans
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hM : d.1≤M := le_max_right _ _
  have hHM : H^2≤M := le_max_left _ _
  have hn := Compiler.integerTile_nonempty d hne
  have hrect := Compiler.Size.integerTile_rectangle_bound d H M hm hM hne hxy
  change Rails.connectedTile (Compiler.integerTile d) H M≠[] ∧ _
  refine ⟨Rails.connectedTile_nonempty _ H M hn,
    Rails.connectedTile_connected _ H M hrect,?_,?_⟩
  · exact hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
      (Rails.connectedTile_correct (Compiler.integerTile d) H M).symm)
  · have hvol := Compiler.Size.integerTile_cubeCount_mass d hm
    have hlen := Rails.connectedTile_length_mass (Compiler.integerTile d) H M hH1 hHM
    exact hlen.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ hvol))).trans (Rails.geometry_bound hbig hH hMc hcard))

end
end TranslationTiling.FiniteCompiler.Effective
