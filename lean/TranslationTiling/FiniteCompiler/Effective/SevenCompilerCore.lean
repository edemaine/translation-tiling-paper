import TranslationTiling.FiniteCompiler.Effective.PairCompiler
import TranslationTiling.FiniteCompiler.FortySmallCompiler
import TranslationTiling.Compiler.FiveInputBound
import TranslationTiling.Compiler.SevenLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler
noncomputable section
set_option maxHeartbeats 4000000

private theorem core_bound (T : LeanWang.TileSet) (hn : 41≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (700*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 8188≤T.length
  · exact Size.seven_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Size.pair_width64 (by omega : 11≤T.length) hm
      exact Size.seven_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Size.seven_exponent (a:=49) (b:=9) (c:=12) (d:=5) hn (by decide) (by decide)
          (by norm_num) (by norm_num) (by norm_num) (by change (9124:ℝ)≤_; norm_num))
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Size.seven_width80 (by omega : 243≤T.length) (by omega : T.length≤8187)
      exact Size.seven_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Size.seven_exponent (m:=243) (a:=7) (b:=1) (c:=12) (d:=5) (by omega) (by decide) (by decide)
          (by norm_num) (by norm_num) (by norm_num) (by change (11678:ℝ)≤_; norm_num))

def sevenCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length=0 then Size.emptyTile else
  if T.length=1 then FiveTile.compile 1 (by decide) T else
  if T.length=2 then FiveTile.compile 2 (by decide) T else
  if T.length=3 then FiveTile.compile 3 (by decide) T else
  if T.length=4 then FiveTile.compile 4 (by decide) T else
  if T.length=5 then FiveTile.compile 5 (by decide) T else
  if T.length≤30 then pairCompile T else
  if T.length=31 then FortySmallCompiler.compile 0 T else
  if T.length=32 then FortySmallCompiler.compile 1 T else
  if T.length=33 then FortySmallCompiler.compile 2 T else
  if T.length=34 then FortySmallCompiler.compile 3 T else
  if T.length=35 then FortySmallCompiler.compile 4 T else
  if T.length=36 then FortySmallCompiler.compile 5 T else
  if T.length=37 then FortySmallCompiler.compile 6 T else
  if T.length=38 then FortySmallCompiler.compile 7 T else
  if T.length=39 then FortySmallCompiler.compile 8 T else
  if T.length=40 then FortySmallCompiler.compile 9 T else
  sparseCompileCore T

theorem sevenCompile_computable : Computable sevenCompile := by
  have hlen (n : ℕ) : Primrec (fun T : LeanWang.TileSet => decide (T.length=n)) := by fun_prop
  have h30 : Primrec (fun T : LeanWang.TileSet => decide (T.length≤30)) := by fun_prop
  exact ((hlen 0).to_comp.cond (Computable.const Size.emptyTile) ((hlen 1).to_comp.cond (FiveTile.compile_computable 1 (by decide)) ((hlen 2).to_comp.cond (FiveTile.compile_computable 2 (by decide)) ((hlen 3).to_comp.cond (FiveTile.compile_computable 3 (by decide)) ((hlen 4).to_comp.cond (FiveTile.compile_computable 4 (by decide)) ((hlen 5).to_comp.cond (FiveTile.compile_computable 5 (by decide)) (h30.to_comp.cond pairCompile_computable ((hlen 31).to_comp.cond (FortySmallCompiler.compile_computable 0) ((hlen 32).to_comp.cond (FortySmallCompiler.compile_computable 1) ((hlen 33).to_comp.cond (FortySmallCompiler.compile_computable 2) ((hlen 34).to_comp.cond (FortySmallCompiler.compile_computable 3) ((hlen 35).to_comp.cond (FortySmallCompiler.compile_computable 4) ((hlen 36).to_comp.cond (FortySmallCompiler.compile_computable 5) ((hlen 37).to_comp.cond (FortySmallCompiler.compile_computable 6) ((hlen 38).to_comp.cond (FortySmallCompiler.compile_computable 7) ((hlen 39).to_comp.cond (FortySmallCompiler.compile_computable 8) ((hlen 40).to_comp.cond (FortySmallCompiler.compile_computable 9) sparseCompileCore_computable))))))))))))))))).of_eq (fun T => by simp only [sevenCompile,Bool.cond_decide])

variable (classification : ∀ {H : ℕ} {V : FiveTile.Matrix} {W : ℕ → ℕ → FiveTile.Letter},
  FiveTile.Rectangular (FiveTile.edge H) → FiveTile.Rectangular V → FiveTile.Patch H V W → FiveTile.Plane H V)

include classification in
private theorem tiny_facts (T : LeanWang.TileSet) (h : T.length≤5) :
    sevenCompile T≠[] ∧ FaceConnected (sevenCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sevenCompile T)) ∧
    (sevenCompile T).length≤2^250 := by
  by_cases h0 : T.length=0
  · have hf : sevenCompile T=Size.emptyTile := by simp [sevenCompile,h0]
    rw [hf]
    have hz : T=[] := by cases T <;> simp_all
    subst T
    obtain ⟨hn,hc,ht,hb⟩ := Size.emptyTile_facts
    exact ⟨hn,hc,iff_of_false Size.empty_wang_not_tiles ht,hb⟩
  · generalize he : T.length=n at h h0
    interval_cases n
    · contradiction
    · rw [show sevenCompile T=FiveTile.compile 1 (by decide) T by simp [sevenCompile,he]]
      exact FiveTile.compile_facts classification 1 (by decide) (by decide) T he
    · rw [show sevenCompile T=FiveTile.compile 2 (by decide) T by simp [sevenCompile,he]]
      exact FiveTile.compile_facts classification 2 (by decide) (by decide) T he
    · rw [show sevenCompile T=FiveTile.compile 3 (by decide) T by simp [sevenCompile,he]]
      exact FiveTile.compile_facts classification 3 (by decide) (by decide) T he
    · rw [show sevenCompile T=FiveTile.compile 4 (by decide) T by simp [sevenCompile,he]]
      exact FiveTile.compile_facts classification 4 (by decide) (by decide) T he
    · rw [show sevenCompile T=FiveTile.compile 5 (by decide) T by simp [sevenCompile,he]]
      exact FiveTile.compile_facts classification 5 (by decide) (by decide) T he

include classification in
theorem sevenCompile_small_bound (T : LeanWang.TileSet) (h : T.length≤5) :
    (sevenCompile T).length≤2^250 := (tiny_facts classification T h).2.2.2

include classification in
theorem sevenCompile_facts (T : LeanWang.TileSet) :
    sevenCompile T≠[] ∧ FaceConnected (sevenCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sevenCompile T)) ∧
    ((sevenCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (700*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases ht : T.length≤5
  · obtain ⟨hn,hc,hi,hb⟩ := tiny_facts classification T ht
    exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
      (Size.seven_exponent (m:=0) (a:=2) (b:=1) (c:=1) (d:=1) (by omega)
        (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))⟩
  by_cases hm : T.length≤30
  · have hf : sevenCompile T=pairCompile T := by
      simp [sevenCompile,hm,show T.length≠0 by omega, show T.length≠1 by omega, show T.length≠2 by omega, show T.length≠3 by omega, show T.length≠4 by omega, show T.length≠5 by omega]
    rw [hf]
    generalize he : T.length=n at ht hm
    interval_cases n
    · rw [show pairCompile T=PairSmallCompiler.compile 2 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 2 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=6) (a:=33) (b:=10) (c:=12) (d:=7)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (3950:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 3 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 3 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=7) (a:=69) (b:=20) (c:=7) (d:=4)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4220:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 4 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 4 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=7) (a:=69) (b:=20) (c:=7) (d:=4)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4220:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 5 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 5 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=7) (a:=69) (b:=20) (c:=7) (d:=4)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4220:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 6 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 6 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=7) (a:=69) (b:=20) (c:=7) (d:=4)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4220:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 7 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 7 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 8 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 8 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 9 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 9 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 10 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 10 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 11 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 11 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 12 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 12 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 13 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 13 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 14 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 14 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 15 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 15 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 16 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 16 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (4980:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 17 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 17 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 18 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 18 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 19 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 19 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 20 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 20 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 21 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 21 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 22 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 22 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 23 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 23 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 24 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 24 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 25 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 25 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩
    · rw [show pairCompile T=PairSmallCompiler.compile 26 T by simp [pairCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := PairSmallCompiler.compile_facts 26 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (5780:ℝ)≤_; norm_num))⟩

  by_cases h40 : T.length<41
  · generalize he : T.length=n at ht hm h40
    interval_cases n
    · rw [show sevenCompile T=FortySmallCompiler.compile 0 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 0 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 1 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 1 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 2 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 2 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 3 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 3 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 4 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 4 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 5 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 5 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 6 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 6 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 7 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 7 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 8 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 8 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
    · rw [show sevenCompile T=FortySmallCompiler.compile 9 T by simp [sevenCompile,he]]
      obtain ⟨hn,hc,hi,hb⟩ := FortySmallCompiler.compile_facts 9 T he
      exact ⟨hn,hc,hi,Size.seven_dyadic_real_bound hb
        (Size.seven_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
          (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by change (6586:ℝ)≤_; norm_num))⟩
  · rw [show sevenCompile T=sparseCompileCore T by
      simp only [sevenCompile,if_neg (show T.length≠0 by omega), if_neg (show T.length≠1 by omega), if_neg (show T.length≠2 by omega), if_neg (show T.length≠3 by omega), if_neg (show T.length≠4 by omega), if_neg (show T.length≠5 by omega), if_neg (show T.length≠31 by omega), if_neg (show T.length≠32 by omega), if_neg (show T.length≠33 by omega), if_neg (show T.length≠34 by omega), if_neg (show T.length≠35 by omega), if_neg (show T.length≠36 by omega), if_neg (show T.length≠37 by omega), if_neg (show T.length≠38 by omega), if_neg (show T.length≠39 by omega), if_neg (show T.length≠40 by omega),if_neg hm]]
    obtain ⟨hn,hc,hi,_⟩ := sparseCompileCore_channel_bound T (by omega)
    exact ⟨hn,hc,hi,core_bound T (by omega)⟩

include classification in
theorem sevenCompile_real_bound (T : LeanWang.TileSet) :
    ((sevenCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (700*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (sevenCompile_facts classification T).2.2.2

include classification in
theorem sevenCompile_single_bound (T : LeanWang.TileSet) (h : T.length=1) :
    (sevenCompile T).length≤2^250 := sevenCompile_small_bound classification T (by omega)
end
end TranslationTiling.FiniteCompiler.Effective
