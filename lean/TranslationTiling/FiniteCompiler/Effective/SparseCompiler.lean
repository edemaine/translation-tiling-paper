import TranslationTiling.FiniteCompiler.Effective.SparseFamily
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyBounds
import TranslationTiling.Compiler.SparseLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sparseCompileCore (T : LeanWang.TileSet) : Tile 3 :=
  familyTileAt ((parameterData (SparseTernary.system T),sparseFamily T),compactHorizontal (parameterData (SparseTernary.system T)))

theorem sparseCompileCore_computable : Computable sparseCompileCore := by
  have hd := sparseParameterData_computable
  exact familyTileAt_computable.comp ((hd.pair sparseFamily_computable).pair
    (compactHorizontal_primrec.to_comp.comp hd))

theorem sparseFamily_compact_horizontal (T : LeanWang.TileSet) :
    ∀ F∈sparseFamily T, ∀ f∈F,
      f.1.1.natAbs≤compactHorizontal (parameterData (SparseTernary.system T)) ∧
      f.1.2.natAbs≤compactHorizontal (parameterData (SparseTernary.system T)) := by
  intro F hF f hf
  have hm : F.toFinset.image (decodeNumericalPoint (parameters (SparseTernary.system T))) ∈
      SparseTernary.testFamily (parameters (SparseTernary.system T)) := by
    rw [←sparseFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  have hS : ∀ n, ((SparseTernary.system T).slope n).natAbs≤16 := SparseTernary.slope_bound T
  exact SparseTernary.test_horizontal _
    (compactHorizontal_support _ rfl hS) hm
    (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)

theorem sparseCompileCore_channel_bound (T : LeanWang.TileSet) (hn : 0<T.length) :
    sparseCompileCore T≠[] ∧ FaceConnected (sparseCompileCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sparseCompileCore T)) ∧
    (sparseCompileCore T).length≤primeBudget (SparseTernary.system T)^(33*(SparseTernary.system T).width+98)*
      3^(4*(SparseTernary.system T).width+4) := by
  have hw : 48≤(SparseTernary.system T).width := by
    have hh := SparseTernary.raw_width_le T.length
    change 48≤SparseTernary.width T.length
    omega
  have hf := sparseFamily_budget T hn
  have hs := SparseTernary.slope_bound T
  have hsupport := compactHorizontal_support (SparseTernary.system T) rfl hs
  have hH : 1≤compactHorizontal (parameterData (SparseTernary.system T)) :=
    (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 1≤residueModulus).trans hsupport.modulus
  obtain ⟨hne,hconn,hiff,_⟩ := familyTileAt_facts (SparseTernary.system T) (sparseFamily T)
    hf hs rfl hw _ hH (sparseFamily_compact_horizontal T)
  have hbound := family_compact_bound (SparseTernary.system T) (sparseFamily T) hf hs rfl hw _ hH
    (compactHorizontal_le _) (sparseFamily_compact_horizontal T)
  have hwang := SparseTernary.finite_system_iff_wang (parameters (SparseTernary.system T))
  exact ⟨hne,hconn,hwang.trans ((sparse_family_solution_iff T).trans hiff),hbound⟩

theorem sparseCompileCore_small_bound (T : LeanWang.TileSet) (hn : 0<T.length)
    (i : Fin 5) (hw : (SparseTernary.system T).width=SmallProfiles.width i) :
    (sparseCompileCore T).length≤2^SmallProfiles.exponent i := by
  have hH := compactHorizontal_small (SparseTernary.system T) i hw rfl
  have hxy := sparseFamily_compact_horizontal T
  rw [hH] at hxy
  unfold sparseCompileCore
  rw [hH]
  exact family_small_bound (SparseTernary.system T) (sparseFamily T) (sparseFamily_budget T hn)
    (SparseTernary.slope_bound T) rfl i hw hxy

 theorem sparseCompileCore_real_bound (T : LeanWang.TileSet) (hn : 11≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (1350*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 252≤T.length
  · exact Compiler.Size.sparse_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.sparse_width64 hn hm
      exact Compiler.Size.sparse_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Compiler.Size.sparse_medium_exponent hn)
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.sparse_width80 (by omega : 243≤T.length) (by omega : T.length≤251)
      exact Compiler.Size.sparse_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Compiler.Size.sparse_later_exponent (by omega))

end
end TranslationTiling.FiniteCompiler.Effective
