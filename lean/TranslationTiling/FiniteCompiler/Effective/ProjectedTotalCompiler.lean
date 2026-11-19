import TranslationTiling.FiniteCompiler.Effective.SevenCompiler
import TranslationTiling.FiniteCompiler.ProjectedCompiler
import TranslationTiling.Compiler.ProjectedLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler
noncomputable section
set_option maxHeartbeats 4000000

private theorem core_bound (T : LeanWang.TileSet) (hn : 45≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (660*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 8188≤T.length
  · exact Size.projected_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Size.pair_width64 (by omega : 11≤T.length) hm
      exact Size.projected_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Size.projected_exponent (a:=28) (b:=5) (c:=247) (d:=100) hn (by decide) (by decide)
          (by norm_num) (by norm_num) (by norm_num) (by change (9124:ℝ)≤_; norm_num))
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Size.seven_width80 (by omega : 243≤T.length) (by omega : T.length≤8187)
      exact Size.projected_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Size.projected_exponent (m:=243) (a:=7) (b:=1) (c:=11) (d:=4) (by omega) (by decide) (by decide)
          (by norm_num) (by norm_num) (by norm_num) (by change (11678:ℝ)≤_; norm_num))


private def projectionIndex (T : LeanWang.TileSet) : Fin 39 :=
  ⟨(T.length-6)%39,Nat.mod_lt _ (by decide)⟩

def projectedCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T.length≤5 then sevenCompile T
  else if T.length≤44 then ProjectedCompiler.compile (projectionIndex T) T
  else sparseCompileCore T

theorem projectedCompile_computable : Computable projectedCompile := by
  have hfixed (k : Fin 39) : Primrec (ProjectedCompiler.compile k) :=
    (Compiler.Effective.finFunction_primrec (ProjectedCompiler.finiteTile k)).comp
      (Size.inputIndex_primrec _ (ProjectedCompiler.Profiles.count_pos k))
  have hix : Primrec projectionIndex := by
    apply Primrec.fin_val_iff.mp
    unfold projectionIndex
    fun_prop
  have hmid := (Primrec.fin_curry₁.mpr hfixed).comp hix Primrec.id
  have hs : Primrec (fun T : LeanWang.TileSet => decide (T.length≤5)) := by fun_prop
  have hm : Primrec (fun T : LeanWang.TileSet => decide (T.length≤44)) := by fun_prop
  exact (hs.to_comp.cond sevenCompile_computable (hm.to_comp.cond hmid.to_comp sparseCompileCore_computable)).of_eq
    (fun T => by simp only [projectedCompile,Bool.cond_decide,id_eq])

theorem projectedCompile_small_bound (T : LeanWang.TileSet) (h : T.length≤5) :
    (projectedCompile T).length≤2^250 := by
  simpa only [projectedCompile,if_pos h] using sevenCompile_checked_small_bound T h

private theorem profile_exponent (k : Fin 39) (n : ℕ)
    (hn : n=ProjectedCompiler.Profiles.count k) :
    (ProjectedCompiler.Profiles.exponent k : ℝ)≤
      660*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  fin_cases k
  · change n=6 at hn
    change (3788:ℝ)≤_
    exact Size.projected_exponent (m:=6) (a:=83) (b:=25) (c:=173) (d:=100)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=7 at hn
    change (3912:ℝ)≤_
    exact Size.projected_exponent (m:=7) (a:=17) (b:=5) (c:=7) (d:=4)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=8 at hn
    change (4065:ℝ)≤_
    exact Size.projected_exponent (m:=8) (a:=7) (b:=2) (c:=9) (d:=5)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=9 at hn
    change (4065:ℝ)≤_
    exact Size.projected_exponent (m:=8) (a:=7) (b:=2) (c:=9) (d:=5)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=10 at hn
    change (4065:ℝ)≤_
    exact Size.projected_exponent (m:=8) (a:=7) (b:=2) (c:=9) (d:=5)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=11 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=12 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=13 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=14 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=15 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=16 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=17 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=18 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=19 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=20 at hn
    change (4862:ℝ)≤_
    exact Size.projected_exponent (m:=11) (a:=39) (b:=10) (c:=49) (d:=25)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=21 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=22 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=23 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=24 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=25 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=26 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=27 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=28 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=29 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=30 at hn
    change (5663:ℝ)≤_
    exact Size.projected_exponent (m:=21) (a:=9) (b:=2) (c:=13) (d:=6)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=31 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=32 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=33 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=34 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=35 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=36 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=37 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=38 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=39 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=40 at hn
    change (6476:ℝ)≤_
    exact Size.projected_exponent (m:=31) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=41 at hn
    change (6807:ℝ)≤_
    exact Size.projected_exponent (m:=41) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=42 at hn
    change (6807:ℝ)≤_
    exact Size.projected_exponent (m:=41) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=43 at hn
    change (6807:ℝ)≤_
    exact Size.projected_exponent (m:=41) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · change n=44 at hn
    change (6807:ℝ)≤_
    exact Size.projected_exponent (m:=41) (a:=5) (b:=1) (c:=23) (d:=10)
      (by omega) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem projectedCompile_facts (T : LeanWang.TileSet) :
    projectedCompile T≠[] ∧ FaceConnected (projectedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (projectedCompile T)) ∧
    ((projectedCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (660*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases ht : T.length≤5
  · rw [show projectedCompile T=sevenCompile T by simp [projectedCompile,ht]]
    obtain ⟨hn,hc,hi,_⟩ := sevenCompile_checked_facts T
    exact ⟨hn,hc,hi,Size.projected_dyadic_real_bound (sevenCompile_checked_small_bound T ht)
      (Size.projected_exponent (m:=0) (a:=2) (b:=1) (c:=1) (d:=1) (by omega)
        (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))⟩
  by_cases hm : T.length≤44
  · rw [show projectedCompile T=ProjectedCompiler.compile (projectionIndex T) T by simp [projectedCompile,ht,hm]]
    have hlen : T.length=ProjectedCompiler.Profiles.count (projectionIndex T) := by
      have hlt : T.length-6<39 := by omega
      simp only [ProjectedCompiler.Profiles.count,projectionIndex,Nat.mod_eq_of_lt hlt]
      omega
    obtain ⟨hn,hc,hi,hb⟩ := ProjectedCompiler.compile_facts _ T hlen
    exact ⟨hn,hc,hi,Size.projected_dyadic_real_bound hb (profile_exponent _ _ hlen)⟩
  · rw [show projectedCompile T=sparseCompileCore T by simp [projectedCompile,ht,hm]]
    obtain ⟨hn,hc,hi,_⟩ := sparseCompileCore_channel_bound T (by omega)
    exact ⟨hn,hc,hi,core_bound T (by omega)⟩

theorem projectedCompile_real_bound (T : LeanWang.TileSet) :
    ((projectedCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (660*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (projectedCompile_facts T).2.2.2

theorem projectedCompile_single_bound (T : LeanWang.TileSet) (h : T.length=1) :
    (projectedCompile T).length≤2^250 := projectedCompile_small_bound T (by omega)

end
end TranslationTiling.FiniteCompiler.Effective
