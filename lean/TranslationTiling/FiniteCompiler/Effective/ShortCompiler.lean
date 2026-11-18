import TranslationTiling.FiniteCompiler.Effective.SparseCompiler
import TranslationTiling.Compiler.ShortLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

 theorem shortCompileCore_real_bound (T : LeanWang.TileSet) (hn : 21≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (1000*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 252≤T.length
  · exact Compiler.Size.short_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.short_width64 (by omega : 11≤T.length) hm
      exact Compiler.Size.short_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Compiler.Size.short_medium_exponent hn)
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.short_width80 (by omega : 243≤T.length) (by omega : T.length≤251)
      exact Compiler.Size.short_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Compiler.Size.short_later_exponent (by omega))


def shortCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length=0 then Compiler.Size.emptyTile else
  if T.length=1 then Compiler.SmallTile.compile 1 (by decide) T else
  if T.length=2 then Compiler.SmallTile.compile 2 (by decide) T else
  if T.length=3 then Compiler.SmallTile.compile 3 (by decide) T else
  if T.length=4 then ShortSmallCompiler.compile 0 T else
  if T.length=5 then ShortSmallCompiler.compile 1 T else
  if T.length=6 then ShortSmallCompiler.compile 2 T else
  if T.length=7 then ShortSmallCompiler.compile 3 T else
  if T.length=8 then ShortSmallCompiler.compile 4 T else
  if T.length=9 then ShortSmallCompiler.compile 5 T else
  if T.length=10 then ShortSmallCompiler.compile 6 T else
  if T.length=11 then ShortSmallCompiler.compile 7 T else
  if T.length=12 then ShortSmallCompiler.compile 8 T else
  if T.length=13 then ShortSmallCompiler.compile 9 T else
  if T.length=14 then ShortSmallCompiler.compile 10 T else
  if T.length=15 then ShortSmallCompiler.compile 11 T else
  if T.length=16 then ShortSmallCompiler.compile 12 T else
  if T.length=17 then ShortSmallCompiler.compile 13 T else
  if T.length=18 then ShortSmallCompiler.compile 14 T else
  if T.length=19 then ShortSmallCompiler.compile 15 T else
  if T.length=20 then ShortSmallCompiler.compile 16 T else
  sparseCompileCore T

theorem shortCompile_computable : Computable shortCompile := by
  have hlen (n : ℕ) : Primrec (fun T : LeanWang.TileSet => decide (T.length=n)) := by fun_prop
  exact ((hlen 0).to_comp.cond (Computable.const Compiler.Size.emptyTile) ((hlen 1).to_comp.cond (Compiler.SmallTile.compile_computable 1 (by decide)) ((hlen 2).to_comp.cond (Compiler.SmallTile.compile_computable 2 (by decide)) ((hlen 3).to_comp.cond (Compiler.SmallTile.compile_computable 3 (by decide)) ((hlen 4).to_comp.cond (ShortSmallCompiler.compile_computable 0) ((hlen 5).to_comp.cond (ShortSmallCompiler.compile_computable 1) ((hlen 6).to_comp.cond (ShortSmallCompiler.compile_computable 2) ((hlen 7).to_comp.cond (ShortSmallCompiler.compile_computable 3) ((hlen 8).to_comp.cond (ShortSmallCompiler.compile_computable 4) ((hlen 9).to_comp.cond (ShortSmallCompiler.compile_computable 5) ((hlen 10).to_comp.cond (ShortSmallCompiler.compile_computable 6) ((hlen 11).to_comp.cond (ShortSmallCompiler.compile_computable 7) ((hlen 12).to_comp.cond (ShortSmallCompiler.compile_computable 8) ((hlen 13).to_comp.cond (ShortSmallCompiler.compile_computable 9) ((hlen 14).to_comp.cond (ShortSmallCompiler.compile_computable 10) ((hlen 15).to_comp.cond (ShortSmallCompiler.compile_computable 11) ((hlen 16).to_comp.cond (ShortSmallCompiler.compile_computable 12) ((hlen 17).to_comp.cond (ShortSmallCompiler.compile_computable 13) ((hlen 18).to_comp.cond (ShortSmallCompiler.compile_computable 14) ((hlen 19).to_comp.cond (ShortSmallCompiler.compile_computable 15) ((hlen 20).to_comp.cond (ShortSmallCompiler.compile_computable 16) sparseCompileCore_computable))))))))))))))))))))).of_eq (fun T => by simp only [shortCompile,Bool.cond_decide])

theorem shortCompile_small_bound (T : LeanWang.TileSet) (hs : T.length≤3) :
    (shortCompile T).length≤2^250 := by
  generalize he : T.length=n at hs
  interval_cases n
  · have hf : shortCompile T=Compiler.Size.emptyTile := by simp [shortCompile,he]
    rw [hf]
    exact Compiler.Size.emptyTile_facts.2.2.2
  · have hf : shortCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [shortCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he).2.2.2
  · have hf : shortCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [shortCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he).2.2.2
  · have hf : shortCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [shortCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he).2.2.2

theorem shortCompile_facts (T : LeanWang.TileSet) :
    shortCompile T≠[] ∧ FaceConnected (shortCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (shortCompile T)) ∧
    ((shortCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (1000*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hs : T.length≤20
  · generalize he : T.length=n at hs
    interval_cases n
    · have hf : shortCompile T=Compiler.Size.emptyTile := by simp [shortCompile,he]
      rw [hf]
      have hz : T=[] := by cases T <;> simp_all
      subst T
      obtain ⟨hn,hc,ht,hb⟩ := Compiler.Size.emptyTile_facts
      exact ⟨hn,hc,iff_of_false Compiler.Size.empty_wang_not_tiles ht,
        Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_tiny_exponent 0)⟩
    · have hf : shortCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [shortCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_tiny_exponent 1)⟩
    · have hf : shortCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [shortCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_tiny_exponent 2)⟩
    · have hf : shortCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [shortCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_tiny_exponent 3)⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 0 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 0 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 0 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 0 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 1 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 1 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 1 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 1 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 2 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 2 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 2 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 2 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 3 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 3 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 3 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 3 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 4 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 4 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 4 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 4 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 5 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 5 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 5 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 5 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 6 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 6 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 6 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 6 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 7 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 7 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 7 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 7 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 8 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 8 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 8 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 8 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 9 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 9 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 9 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 9 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 10 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 10 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 10 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 10 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 11 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 11 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 11 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 11 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 12 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 12 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 12 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 12 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 13 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 13 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 13 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 13 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 14 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 14 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 14 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 14 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 15 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 15 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 15 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 15 (by rfl))⟩
    · have hf : shortCompile T=ShortSmallCompiler.compile 16 T := by simp [shortCompile,he]
      rw [hf]
      have hlen : T.length=ShortSmallCompiler.Profiles.count 16 := by simpa [ShortSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := ShortSmallCompiler.compile_facts 16 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.short_dyadic_real_bound hb (Compiler.Size.short_small_exponent 16 (by rfl))⟩
  · have hn : 21≤T.length := by omega
    have hf : shortCompile T=sparseCompileCore T := by
      simp only [shortCompile,if_neg (show T.length≠0 by omega),if_neg (show T.length≠1 by omega),if_neg (show T.length≠2 by omega),if_neg (show T.length≠3 by omega),if_neg (show T.length≠4 by omega),if_neg (show T.length≠5 by omega),if_neg (show T.length≠6 by omega),if_neg (show T.length≠7 by omega),if_neg (show T.length≠8 by omega),if_neg (show T.length≠9 by omega),if_neg (show T.length≠10 by omega),if_neg (show T.length≠11 by omega),if_neg (show T.length≠12 by omega),if_neg (show T.length≠13 by omega),if_neg (show T.length≠14 by omega),if_neg (show T.length≠15 by omega),if_neg (show T.length≠16 by omega),if_neg (show T.length≠17 by omega),if_neg (show T.length≠18 by omega),if_neg (show T.length≠19 by omega),if_neg (show T.length≠20 by omega)]
    rw [hf]
    obtain ⟨h0,hc,hi,_⟩ := sparseCompileCore_channel_bound T (by omega)
    exact ⟨h0,hc,hi,shortCompileCore_real_bound T hn⟩

 theorem shortCompile_real_bound (T : LeanWang.TileSet) :
    ((shortCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (1000*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (shortCompile_facts T).2.2.2

theorem shortCompile_single_bound (T : LeanWang.TileSet) (hn : T.length=1) :
    (shortCompile T).length≤2^250 := shortCompile_small_bound T (by omega)

end
end TranslationTiling.FiniteCompiler.Effective
