import TranslationTiling.Compiler.EmptyInputBound
import TranslationTiling.Examples

/-! A direct edge test handles a Wang input consisting of one tile. -/
namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

def selfMatching (t : LeanWang.WangTile) : Prop := t.e=t.w ∧ t.n=t.s
instance (t : LeanWang.WangTile) : Decidable (selfMatching t) := by unfold selfMatching; infer_instance

theorem singleton_wang_iff (t : LeanWang.WangTile) : LeanWang.TilesPlane [t] ↔ selfMatching t := by
  constructor
  · rintro ⟨x,hx⟩
    have he (p : ℤ×ℤ) : (x p).val=t := List.mem_singleton.mp (x p).property
    have hh := hx.1 (0,0)
    have hv := hx.2 (0,0)
    simpa only [LeanWang.WangTile.HMatches,LeanWang.WangTile.VMatches,he,selfMatching] using And.intro hh hv
  · intro h
    refine ⟨fun _ => ⟨t,by simp⟩,?_,?_⟩
    · intro p; exact h.1
    · intro p; exact h.2

def singleTile (t : LeanWang.WangTile) : Tile 3 := if selfMatching t then [0] else emptyTile

theorem singleTile_facts (t : LeanWang.WangTile) :
    singleTile t≠[] ∧ FaceConnected (singleTile t) ∧
    (LeanWang.TilesPlane [t] ↔ TranslationTiling.Tiles (singleTile t)) ∧
    (singleTile t).length≤2^250 := by
  by_cases h : selfMatching t
  · simp only [singleTile,if_pos h]
    refine ⟨by simp,?_,iff_of_true ((singleton_wang_iff t).mpr h) (tiles_singleton 0),by norm_num⟩
    intro p hp q hq
    have hp' : p=0 := List.mem_singleton.mp hp
    have hq' : q=0 := List.mem_singleton.mp hq
    rw [hp',hq']
  · simp only [singleTile,if_neg h]
    obtain ⟨hn,hc,ht,hb⟩ := emptyTile_facts
    exact ⟨hn,hc,iff_of_false (fun hh => h ((singleton_wang_iff t).mp hh)) ht,hb⟩

theorem singleTile_computable : Computable singleTile := by
  unfold singleTile
  have hd : Primrec (fun t : LeanWang.WangTile => decide (selfMatching t)) := by
    unfold selfMatching
    fun_prop
  exact (hd.to_comp.cond (Computable.const [0]) (Computable.const emptyTile)).of_eq
    (fun t => by simp [Bool.cond_decide])

end
end TranslationTiling.Compiler.Size
