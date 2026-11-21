import TranslationTiling.FiniteCompiler.Effective.JointFamily
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyBounds
import TranslationTiling.Compiler.JointLogBound

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

end
end TranslationTiling.FiniteCompiler.Effective
