import TranslationTiling.FiniteCompiler.Effective.SparseFamily
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyBounds
import TranslationTiling.Compiler.SparseLogBound
import TranslationTiling.Compiler.SmallInputBound

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

def sparseCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length=0 then Compiler.Size.emptyTile else
  if T.length=1 then Compiler.SmallTile.compile 1 (by decide) T else
  if T.length=2 then Compiler.SmallTile.compile 2 (by decide) T else
  if T.length=3 then Compiler.SmallTile.compile 3 (by decide) T else
  if T.length=4 then SparseSmallCompiler.compile 0 T else
  if T.length=5 then SparseSmallCompiler.compile 1 T else
  if T.length=6 then SparseSmallCompiler.compile 2 T else
  if T.length=7 then SparseSmallCompiler.compile 3 T else
  if T.length=8 then SparseSmallCompiler.compile 4 T else
  if T.length=9 then SparseSmallCompiler.compile 5 T else
  if T.length=10 then SparseSmallCompiler.compile 6 T else
  sparseCompileCore T

theorem sparseCompile_computable : Computable sparseCompile := by
  have hlen (n : ℕ) : Primrec (fun T : LeanWang.TileSet => decide (T.length=n)) := by fun_prop
  exact ((hlen 0).to_comp.cond (Computable.const Compiler.Size.emptyTile) ((hlen 1).to_comp.cond (Compiler.SmallTile.compile_computable 1 (by decide)) ((hlen 2).to_comp.cond (Compiler.SmallTile.compile_computable 2 (by decide)) ((hlen 3).to_comp.cond (Compiler.SmallTile.compile_computable 3 (by decide)) ((hlen 4).to_comp.cond (SparseSmallCompiler.compile_computable 0) ((hlen 5).to_comp.cond (SparseSmallCompiler.compile_computable 1) ((hlen 6).to_comp.cond (SparseSmallCompiler.compile_computable 2) ((hlen 7).to_comp.cond (SparseSmallCompiler.compile_computable 3) ((hlen 8).to_comp.cond (SparseSmallCompiler.compile_computable 4) ((hlen 9).to_comp.cond (SparseSmallCompiler.compile_computable 5) ((hlen 10).to_comp.cond (SparseSmallCompiler.compile_computable 6) sparseCompileCore_computable))))))))))).of_eq (fun T => by simp only [sparseCompile,Bool.cond_decide])

theorem sparseCompile_small_bound (T : LeanWang.TileSet) (hs : T.length≤3) :
    (sparseCompile T).length≤2^250 := by
  generalize he : T.length=n at hs
  interval_cases n
  · have hf : sparseCompile T=Compiler.Size.emptyTile := by simp [sparseCompile,he]
    rw [hf]
    exact Compiler.Size.emptyTile_facts.2.2.2
  · have hf : sparseCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [sparseCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he).2.2.2
  · have hf : sparseCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [sparseCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he).2.2.2
  · have hf : sparseCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [sparseCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he).2.2.2

theorem sparseCompile_facts (T : LeanWang.TileSet) :
    sparseCompile T≠[] ∧ FaceConnected (sparseCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sparseCompile T)) ∧
    ((sparseCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (1350*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hs : T.length≤10
  · generalize he : T.length=n at hs
    interval_cases n
    · have hf : sparseCompile T=Compiler.Size.emptyTile := by simp [sparseCompile,he]
      rw [hf]
      have hz : T=[] := by cases T <;> simp_all
      subst T
      obtain ⟨hn,hc,ht,hb⟩ := Compiler.Size.emptyTile_facts
      exact ⟨hn,hc,iff_of_false Compiler.Size.empty_wang_not_tiles ht,
        Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_tiny_exponent 0)⟩
    · have hf : sparseCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [sparseCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_tiny_exponent 1)⟩
    · have hf : sparseCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [sparseCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_tiny_exponent 2)⟩
    · have hf : sparseCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [sparseCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_tiny_exponent 3)⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 0 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 0 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 0 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 0 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 1 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 1 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 1 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 1 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 2 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 2 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 2 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 2 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 3 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 3 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 3 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 3 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 4 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 4 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 4 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 4 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 5 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 5 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 5 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 5 (by rfl))⟩
    · have hf : sparseCompile T=SparseSmallCompiler.compile 6 T := by simp [sparseCompile,he]
      rw [hf]
      have hlen : T.length=SparseSmallCompiler.Profiles.count 6 := by simpa [SparseSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := SparseSmallCompiler.compile_facts 6 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.sparse_dyadic_real_bound hb (Compiler.Size.sparse_small_exponent 6 (by rfl))⟩
  · have hn : 11≤T.length := by omega
    have hf : sparseCompile T=sparseCompileCore T := by
      simp only [sparseCompile,if_neg (show T.length≠0 by omega),if_neg (show T.length≠1 by omega),if_neg (show T.length≠2 by omega),if_neg (show T.length≠3 by omega),if_neg (show T.length≠4 by omega),if_neg (show T.length≠5 by omega),if_neg (show T.length≠6 by omega),if_neg (show T.length≠7 by omega),if_neg (show T.length≠8 by omega),if_neg (show T.length≠9 by omega),if_neg (show T.length≠10 by omega)]
    rw [hf]
    obtain ⟨h0,hc,hi,_⟩ := sparseCompileCore_channel_bound T (by omega)
    exact ⟨h0,hc,hi,sparseCompileCore_real_bound T hn⟩

 theorem sparseCompile_real_bound (T : LeanWang.TileSet) :
    ((sparseCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (1350*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (sparseCompile_facts T).2.2.2

theorem sparseCompile_single_bound (T : LeanWang.TileSet) (hn : T.length=1) :
    (sparseCompile T).length≤2^250 := sparseCompile_small_bound T (by omega)

end
end TranslationTiling.FiniteCompiler.Effective
