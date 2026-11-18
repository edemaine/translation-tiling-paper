import TranslationTiling.FiniteCompiler.Effective.JointFamily
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyBounds
import TranslationTiling.Compiler.JointLogBound
import TranslationTiling.Compiler.SingleInputBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def jointCompileCore (T : LeanWang.TileSet) : Tile 3 :=
  familyTileAt ((parameterData (jointSystem T),jointFamily T),compactHorizontal (parameterData (jointSystem T)))

theorem jointCompileCore_computable : Computable jointCompileCore := by
  have hd := jointParameterData_computable
  exact familyTileAt_computable.comp ((hd.pair jointFamily_computable).pair
    (compactHorizontal_primrec.to_comp.comp hd))

theorem jointFamily_compact_horizontal (T : LeanWang.TileSet) :
    ∀ F∈jointFamily T, ∀ f∈F,
      f.1.1.natAbs≤compactHorizontal (parameterData (jointSystem T)) ∧
      f.1.2.natAbs≤compactHorizontal (parameterData (jointSystem T)) := by
  intro F hF f hf
  have hm : F.toFinset.image (decodeNumericalPoint (parameters (jointSystem T))) ∈
      JointSystem.testTiles (jointCode T) (parameters (jointSystem T)) := by
    rw [←jointFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  have hS : ∀ n, ((jointSystem T).slope n).natAbs≤16 := jointSystem_slope_bound T
  exact CompactSupport.joint_test_horizontal (jointCode T) _
    (compactHorizontal_support _ rfl hS) hS hm
    (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)

theorem jointCompileCore_channel_bound (T : LeanWang.TileSet) (hn : 0<T.length) :
    jointCompileCore T≠[] ∧ FaceConnected (jointCompileCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (jointCompileCore T)) ∧
    (jointCompileCore T).length≤primeBudget (jointSystem T)^(33*(jointSystem T).width+98)*
      3^(4*(jointSystem T).width+4) := by
  have hw : 48≤(jointSystem T).width := by
    have hk := jointWidth_three hn
    change 48≤Sudoku.Width*jointWidth T.length
    norm_num [Sudoku.Width,Sudoku.q]
    omega
  have hf := jointFamily_budget T hn
  have hs := jointSystem_slope_bound T
  have hsupport := compactHorizontal_support (jointSystem T) rfl hs
  have hH : 1≤compactHorizontal (parameterData (jointSystem T)) :=
    (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 1≤residueModulus).trans hsupport.modulus
  obtain ⟨hne,hconn,hiff,_⟩ := familyTileAt_facts (jointSystem T) (jointFamily T)
    hf hs rfl hw _ hH (jointFamily_compact_horizontal T)
  have hbound := family_compact_bound (jointSystem T) (jointFamily T) hf hs rfl hw _ hH
    (compactHorizontal_le _) (jointFamily_compact_horizontal T)
  have hwang := JointSystem.finite_system_iff_wang (jointCode T) (parameters (jointSystem T))
  exact ⟨hne,hconn,hwang.trans ((joint_family_solution_iff T).trans hiff),hbound⟩

theorem jointCompileCore_small_bound (T : LeanWang.TileSet) (hn : 0<T.length)
    (i : Fin 5) (hk : jointWidth T.length=3+i.val) :
    (jointCompileCore T).length≤2^SmallProfiles.exponent i := by
  have hw : (jointSystem T).width=SmallProfiles.width i := by
    change Sudoku.Width*jointWidth T.length=48+16*i.val
    rw [hk]
    norm_num [Sudoku.Width,Sudoku.q]
    ring
  have hH := compactHorizontal_small (jointSystem T) i hw rfl
  have hxy := jointFamily_compact_horizontal T
  rw [hH] at hxy
  unfold jointCompileCore
  rw [hH]
  exact family_small_bound (jointSystem T) (jointFamily T) (jointFamily_budget T hn)
    (jointSystem_slope_bound T) rfl i hw hxy


def jointCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T=[] then Compiler.Size.emptyTile else
  if T.length=1 then Compiler.Size.singleTile (T.getD 0 ⟨0,0,0,0⟩) else
  if T.length=2 then MixedCompiler.compile 0 T else
  if T.length=4 then MixedCompiler.compile 1 T else
  if T.length=5 then MixedCompiler.compile 2 T else jointCompileCore T

theorem jointCompile_computable : Computable jointCompile := by
  have hs : Computable (fun T : LeanWang.TileSet => Compiler.Size.singleTile (T.getD 0 ⟨0,0,0,0⟩)) :=
    Compiler.Size.singleTile_computable.comp ((Primrec.list_getD (⟨0,0,0,0⟩ : LeanWang.WangTile)).comp Primrec.id (Primrec.const 0)).to_comp
  have hlen (n : ℕ) : Primrec (fun T : LeanWang.TileSet => decide (T.length=n)) := by fun_prop
  have hd : Primrec (fun T : LeanWang.TileSet => decide (T=[])) := by fun_prop
  exact (hd.to_comp.cond (Computable.const Compiler.Size.emptyTile)
    ((hlen 1).to_comp.cond hs
      ((hlen 2).to_comp.cond (MixedCompiler.compile_computable 0)
        ((hlen 4).to_comp.cond (MixedCompiler.compile_computable 1)
          ((hlen 5).to_comp.cond (MixedCompiler.compile_computable 2) jointCompileCore_computable))))).of_eq
    (fun T => by simp only [jointCompile,Bool.cond_decide])

private theorem list_of_length_one {α : Type*} (xs : List α) (h : xs.length=1) : ∃ x, xs=[x] := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => exact ⟨x,rfl⟩
    | cons y ys => simp only [List.length_cons] at h; omega

theorem jointCompile_single_bound (T : LeanWang.TileSet) (hn : T.length=1) :
    (jointCompile T).length≤2^250 := by
  obtain ⟨t,rfl⟩ := list_of_length_one T hn
  simpa only [jointCompile,List.cons_ne_self,List.cons_ne_nil,if_false,List.length_singleton,
    if_true,List.getD_cons_zero] using (Compiler.Size.singleTile_facts t).2.2.2

theorem jointCompile_facts (T : LeanWang.TileSet) :
    jointCompile T ≠ [] ∧ FaceConnected (jointCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (jointCompile T)) ∧
    ((jointCompile T).length : ℝ) ≤ ((T.length:ℝ)+4) ^
      (2200 * Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases ht : T=[]
  · subst T
    simp only [jointCompile,if_pos rfl,List.length_nil,Nat.cast_zero,zero_add]
    obtain ⟨hn,hc,ht,hb⟩ := Compiler.Size.emptyTile_facts
    refine ⟨hn,hc,⟨fun h => (Compiler.Size.empty_wang_not_tiles h).elim,fun h => (ht h).elim⟩,?_⟩
    have hlog4 : Real.logb 2 (4:ℝ)=2 := by
      rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
      norm_num [Real.logb_self_eq_one]
    rw [hlog4,show Real.logb 2 (2:ℝ)=1 from Real.logb_self_eq_one (by norm_num),mul_one]
    have hcast : (Compiler.Size.emptyTile.length:ℝ)≤(2:ℝ)^250 := by exact_mod_cast hb
    apply hcast.trans
    calc
      (2:ℝ)^250 ≤ (4:ℝ)^250 := by norm_num
      _ = (4:ℝ)^(250:ℝ) := (Real.rpow_natCast (4:ℝ) 250).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · by_cases h1 : T.length=1
    · obtain ⟨t,rfl⟩ := list_of_length_one T h1
      simp only [jointCompile,if_neg ht,List.length_singleton,if_pos rfl,List.getD_cons_zero]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.Size.singleTile_facts t
      exact ⟨hn,hc,hi,Compiler.Size.dyadic_compact_real_bound hb
        (by simpa only [Nat.cast_ofNat,Nat.cast_one] using Compiler.Size.single_compact_exponent)⟩
    · by_cases h2 : T.length=2
      · simp only [jointCompile,if_neg ht,if_neg h1,if_pos h2]
        obtain ⟨hn,hc,hi,hb⟩ := MixedCompiler.compile_facts 0 T h2
        exact ⟨hn,hc,hi,Compiler.Size.dyadic_compact_real_bound hb (Compiler.Size.mixed_compact_exponent 0 h2)⟩
      · by_cases h4 : T.length=4
        · simp only [jointCompile,if_neg ht,if_neg h1,if_neg h2,if_pos h4]
          obtain ⟨hn,hc,hi,hb⟩ := MixedCompiler.compile_facts 1 T h4
          exact ⟨hn,hc,hi,Compiler.Size.dyadic_compact_real_bound hb (Compiler.Size.mixed_compact_exponent 1 h4)⟩
        · by_cases h5 : T.length=5
          · simp only [jointCompile,if_neg ht,if_neg h1,if_neg h2,if_neg h4,if_pos h5]
            obtain ⟨hn,hc,hi,hb⟩ := MixedCompiler.compile_facts 2 T h5
            exact ⟨hn,hc,hi,Compiler.Size.dyadic_compact_real_bound hb (Compiler.Size.mixed_compact_exponent 2 h5)⟩
          · have hn : 0<T.length := List.length_pos_iff_ne_nil.mpr ht
            have hn3 : 3≤T.length := by omega
            obtain ⟨hne,hconn,hiff,hbound⟩ := jointCompileCore_channel_bound T hn
            simp only [jointCompile,if_neg ht,if_neg h1,if_neg h2,if_neg h4,if_neg h5]
            refine ⟨hne,hconn,hiff,?_⟩
            by_cases hsmall : T.length<92
            · have hklo := jointWidth_three hn
              have hkhi : jointWidth T.length≤7 := by
                have hh := Nat.add_le_add_right (Nat.log_mono_right (b:=3)
                  (Nat.mul_le_mul_left 24 (show T.length≤91 by omega))) 1
                exact hh.trans (by decide : Nat.log 3 (24*91)+1≤7)
              let i : Fin 5 := ⟨jointWidth T.length-3,by omega⟩
              have hi : jointWidth T.length=3+i.val := by dsimp [i]; omega
              exact Compiler.Size.dyadic_compact_real_bound (jointCompileCore_small_bound T hn i hi)
                (Compiler.Size.joint_compact_small_exponent hn3 h4 h5 i hi)
            · exact Compiler.Size.joint_compact_bulk_real_bound (by omega) hbound

theorem jointCompile_real_bound (T : LeanWang.TileSet) :
    ((jointCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (2200*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (jointCompile_facts T).2.2.2

end
end TranslationTiling.FiniteCompiler.Effective
