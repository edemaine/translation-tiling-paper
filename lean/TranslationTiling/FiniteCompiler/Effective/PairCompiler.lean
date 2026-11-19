import TranslationTiling.FiniteCompiler.Effective.SparseCompiler
import TranslationTiling.Compiler.PairLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

 theorem pairCompileCore_real_bound (T : LeanWang.TileSet) (hn : 31≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (800*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 2044≤T.length
  · exact Compiler.Size.pair_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.pair_width64 (by omega : 11≤T.length) hm
      exact Compiler.Size.pair_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Compiler.Size.pair_medium_exponent hn)
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.pair_width80 (by omega : 243≤T.length) (by omega : T.length≤2043)
      exact Compiler.Size.pair_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Compiler.Size.pair_later_exponent (by omega))


def pairCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length=0 then Compiler.Size.emptyTile else
  if T.length=1 then Compiler.SmallTile.compile 1 (by decide) T else
  if T.length=2 then Compiler.SmallTile.compile 2 (by decide) T else
  if T.length=3 then Compiler.SmallTile.compile 3 (by decide) T else
  if T.length=4 then PairSmallCompiler.compile 0 T else
  if T.length=5 then PairSmallCompiler.compile 1 T else
  if T.length=6 then PairSmallCompiler.compile 2 T else
  if T.length=7 then PairSmallCompiler.compile 3 T else
  if T.length=8 then PairSmallCompiler.compile 4 T else
  if T.length=9 then PairSmallCompiler.compile 5 T else
  if T.length=10 then PairSmallCompiler.compile 6 T else
  if T.length=11 then PairSmallCompiler.compile 7 T else
  if T.length=12 then PairSmallCompiler.compile 8 T else
  if T.length=13 then PairSmallCompiler.compile 9 T else
  if T.length=14 then PairSmallCompiler.compile 10 T else
  if T.length=15 then PairSmallCompiler.compile 11 T else
  if T.length=16 then PairSmallCompiler.compile 12 T else
  if T.length=17 then PairSmallCompiler.compile 13 T else
  if T.length=18 then PairSmallCompiler.compile 14 T else
  if T.length=19 then PairSmallCompiler.compile 15 T else
  if T.length=20 then PairSmallCompiler.compile 16 T else
  if T.length=21 then PairSmallCompiler.compile 17 T else
  if T.length=22 then PairSmallCompiler.compile 18 T else
  if T.length=23 then PairSmallCompiler.compile 19 T else
  if T.length=24 then PairSmallCompiler.compile 20 T else
  if T.length=25 then PairSmallCompiler.compile 21 T else
  if T.length=26 then PairSmallCompiler.compile 22 T else
  if T.length=27 then PairSmallCompiler.compile 23 T else
  if T.length=28 then PairSmallCompiler.compile 24 T else
  if T.length=29 then PairSmallCompiler.compile 25 T else
  if T.length=30 then PairSmallCompiler.compile 26 T else
  sparseCompileCore T

theorem pairCompile_computable : Computable pairCompile := by
  have hlen (n : ℕ) : Primrec (fun T : LeanWang.TileSet => decide (T.length=n)) := by fun_prop
  exact ((hlen 0).to_comp.cond (Computable.const Compiler.Size.emptyTile) ((hlen 1).to_comp.cond (Compiler.SmallTile.compile_computable 1 (by decide)) ((hlen 2).to_comp.cond (Compiler.SmallTile.compile_computable 2 (by decide)) ((hlen 3).to_comp.cond (Compiler.SmallTile.compile_computable 3 (by decide)) ((hlen 4).to_comp.cond (PairSmallCompiler.compile_computable 0) ((hlen 5).to_comp.cond (PairSmallCompiler.compile_computable 1) ((hlen 6).to_comp.cond (PairSmallCompiler.compile_computable 2) ((hlen 7).to_comp.cond (PairSmallCompiler.compile_computable 3) ((hlen 8).to_comp.cond (PairSmallCompiler.compile_computable 4) ((hlen 9).to_comp.cond (PairSmallCompiler.compile_computable 5) ((hlen 10).to_comp.cond (PairSmallCompiler.compile_computable 6) ((hlen 11).to_comp.cond (PairSmallCompiler.compile_computable 7) ((hlen 12).to_comp.cond (PairSmallCompiler.compile_computable 8) ((hlen 13).to_comp.cond (PairSmallCompiler.compile_computable 9) ((hlen 14).to_comp.cond (PairSmallCompiler.compile_computable 10) ((hlen 15).to_comp.cond (PairSmallCompiler.compile_computable 11) ((hlen 16).to_comp.cond (PairSmallCompiler.compile_computable 12) ((hlen 17).to_comp.cond (PairSmallCompiler.compile_computable 13) ((hlen 18).to_comp.cond (PairSmallCompiler.compile_computable 14) ((hlen 19).to_comp.cond (PairSmallCompiler.compile_computable 15) ((hlen 20).to_comp.cond (PairSmallCompiler.compile_computable 16) ((hlen 21).to_comp.cond (PairSmallCompiler.compile_computable 17) ((hlen 22).to_comp.cond (PairSmallCompiler.compile_computable 18) ((hlen 23).to_comp.cond (PairSmallCompiler.compile_computable 19) ((hlen 24).to_comp.cond (PairSmallCompiler.compile_computable 20) ((hlen 25).to_comp.cond (PairSmallCompiler.compile_computable 21) ((hlen 26).to_comp.cond (PairSmallCompiler.compile_computable 22) ((hlen 27).to_comp.cond (PairSmallCompiler.compile_computable 23) ((hlen 28).to_comp.cond (PairSmallCompiler.compile_computable 24) ((hlen 29).to_comp.cond (PairSmallCompiler.compile_computable 25) ((hlen 30).to_comp.cond (PairSmallCompiler.compile_computable 26) sparseCompileCore_computable))))))))))))))))))))))))))))))).of_eq (fun T => by simp only [pairCompile,Bool.cond_decide])

theorem pairCompile_small_bound (T : LeanWang.TileSet) (hs : T.length≤3) :
    (pairCompile T).length≤2^250 := by
  generalize he : T.length=n at hs
  interval_cases n
  · have hf : pairCompile T=Compiler.Size.emptyTile := by simp [pairCompile,he]
    rw [hf]
    exact Compiler.Size.emptyTile_facts.2.2.2
  · have hf : pairCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [pairCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he).2.2.2
  · have hf : pairCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [pairCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he).2.2.2
  · have hf : pairCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [pairCompile,he]
    rw [hf]
    exact (Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he).2.2.2

theorem pairCompile_facts (T : LeanWang.TileSet) :
    pairCompile T≠[] ∧ FaceConnected (pairCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (pairCompile T)) ∧
    ((pairCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (800*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hs : T.length≤30
  · generalize he : T.length=n at hs
    interval_cases n
    · have hf : pairCompile T=Compiler.Size.emptyTile := by simp [pairCompile,he]
      rw [hf]
      have hz : T=[] := by cases T <;> simp_all
      subst T
      obtain ⟨hn,hc,ht,hb⟩ := Compiler.Size.emptyTile_facts
      exact ⟨hn,hc,iff_of_false Compiler.Size.empty_wang_not_tiles ht,
        Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_tiny_exponent 0)⟩
    · have hf : pairCompile T=Compiler.SmallTile.compile 1 (by decide) T := by simp [pairCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 1 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_tiny_exponent 1)⟩
    · have hf : pairCompile T=Compiler.SmallTile.compile 2 (by decide) T := by simp [pairCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 2 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_tiny_exponent 2)⟩
    · have hf : pairCompile T=Compiler.SmallTile.compile 3 (by decide) T := by simp [pairCompile,he]
      rw [hf]
      obtain ⟨hn,hc,hi,hb⟩ := Compiler.SmallTile.compile_facts 3 (by decide) (by decide) T he
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_tiny_exponent 3)⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 0 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 0 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 0 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 0 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 1 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 1 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 1 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 1 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 2 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 2 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 2 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 2 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 3 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 3 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 3 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 3 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 4 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 4 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 4 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 4 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 5 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 5 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 5 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 5 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 6 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 6 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 6 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 6 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 7 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 7 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 7 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 7 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 8 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 8 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 8 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 8 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 9 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 9 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 9 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 9 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 10 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 10 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 10 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 10 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 11 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 11 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 11 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 11 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 12 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 12 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 12 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 12 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 13 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 13 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 13 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 13 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 14 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 14 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 14 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 14 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 15 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 15 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 15 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 15 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 16 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 16 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 16 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 16 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 17 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 17 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 17 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 17 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 18 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 18 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 18 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 18 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 19 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 19 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 19 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 19 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 20 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 20 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 20 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 20 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 21 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 21 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 21 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 21 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 22 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 22 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 22 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 22 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 23 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 23 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 23 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 23 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 24 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 24 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 24 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 24 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 25 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 25 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 25 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 25 (by rfl))⟩
    · have hf : pairCompile T=PairSmallCompiler.compile 26 T := by simp [pairCompile,he]
      rw [hf]
      have hlen : T.length=PairSmallCompiler.Profiles.count 26 := by simpa [PairSmallCompiler.Profiles.count] using he
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 26 T hlen
      exact ⟨hn,hc,hi,Compiler.Size.pair_dyadic_real_bound hb (Compiler.Size.pair_small_exponent 26 (by rfl))⟩
  · have hn : 31≤T.length := by omega
    have hf : pairCompile T=sparseCompileCore T := by
      simp only [pairCompile,if_neg (show T.length≠0 by omega),if_neg (show T.length≠1 by omega),if_neg (show T.length≠2 by omega),if_neg (show T.length≠3 by omega),if_neg (show T.length≠4 by omega),if_neg (show T.length≠5 by omega),if_neg (show T.length≠6 by omega),if_neg (show T.length≠7 by omega),if_neg (show T.length≠8 by omega),if_neg (show T.length≠9 by omega),if_neg (show T.length≠10 by omega),if_neg (show T.length≠11 by omega),if_neg (show T.length≠12 by omega),if_neg (show T.length≠13 by omega),if_neg (show T.length≠14 by omega),if_neg (show T.length≠15 by omega),if_neg (show T.length≠16 by omega),if_neg (show T.length≠17 by omega),if_neg (show T.length≠18 by omega),if_neg (show T.length≠19 by omega),if_neg (show T.length≠20 by omega),if_neg (show T.length≠21 by omega),if_neg (show T.length≠22 by omega),if_neg (show T.length≠23 by omega),if_neg (show T.length≠24 by omega),if_neg (show T.length≠25 by omega),if_neg (show T.length≠26 by omega),if_neg (show T.length≠27 by omega),if_neg (show T.length≠28 by omega),if_neg (show T.length≠29 by omega),if_neg (show T.length≠30 by omega)]
    rw [hf]
    obtain ⟨h0,hc,hi,_⟩ := sparseCompileCore_channel_bound T (by omega)
    exact ⟨h0,hc,hi,pairCompileCore_real_bound T hn⟩

 theorem pairCompile_real_bound (T : LeanWang.TileSet) :
    ((pairCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (800*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (pairCompile_facts T).2.2.2

theorem pairCompile_single_bound (T : LeanWang.TileSet) (hn : T.length=1) :
    (pairCompile T).length≤2^250 := pairCompile_small_bound T (by omega)

end
end TranslationTiling.FiniteCompiler.Effective
