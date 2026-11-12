import TranslationTiling.FiniteCompiler.Effective.BoundedStack
import TranslationTiling.FiniteCompiler.Effective.Canonical

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem getD_mem_of_lt {α : Type*} (xs : List α) (n : ℕ) (d : α) (hn : n < xs.length) :
    xs.getD n d ∈ xs := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem stackCodes_horizontal (N : ℕ) (c : PartitionCertificate) (Fs : List CyclicTile) (H : ℕ)
    (hb : ∀ F ∈ Fs, ∀ f ∈ F, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    ∀ f ∈ stackCodes (N,c,Fs), f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H := by
  intro f hf
  obtain ⟨i,hi,p,hp,j,hj,rfl⟩ := (by
    simpa only [stackCodes,List.mem_flatMap,List.mem_map] using hf :
      ∃ i ∈ List.range Fs.length, ∃ p ∈ Fs.getD i [],
        ∃ j ∈ (List.range c.1).filter (fun j => decide (c.2.getD j 0 = i)),
          (p.1,mergeResidues N c.1 p.2 j) = f)
  exact hb _ (getD_mem_of_lt Fs i [] (List.mem_range.mp hi)) p hp

theorem stackCodes_nonempty (N : ℕ) (c : PartitionCertificate) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (hc : PartitionValid (Fs.length-1) N c)
    (hne : ∀ F ∈ Fs, F ≠ []) : stackCodes (N,c,Fs) ≠ [] := by
  have hF : Fs.getD 0 [] ∈ Fs := getD_mem_of_lt Fs 0 [] hs
  have hp : (Fs.getD 0 []).headD ((0,0),0) ∈ Fs.getD 0 [] := by
    have hn := hne _ hF
    cases he : Fs.getD 0 [] with
    | nil => exact False.elim (hn he)
    | cons f fs => simp
  obtain ⟨x,hx,y,hy,hcol,_,_⟩ := hc.2.2.2.2 0 (List.mem_range.mpr (by omega))
    0 (List.mem_range.mpr hc.1.pos)
  have hm : ((Fs.getD 0 []).headD ((0,0),0)).1 = ((Fs.getD 0 []).headD ((0,0),0)).1 := rfl
  have hout : (((Fs.getD 0 []).headD ((0,0),0)).1,
      mergeResidues N c.1 ((Fs.getD 0 []).headD ((0,0),0)).2 x) ∈ stackCodes (N,c,Fs) := by
    apply List.mem_flatMap.mpr
    refine ⟨0,List.mem_range.mpr hs,List.mem_flatMap.mpr ⟨_,hp,List.mem_map.mpr ⟨x,?_,rfl⟩⟩⟩
    exact List.mem_filter.mpr ⟨hx,decide_eq_true hcol⟩
  intro he
  simp only [he,List.not_mem_nil] at hout

theorem canonicalFamily_horizontal (H N : ℕ) (Fs : List CyclicTile) :
    ∀ F ∈ canonicalFamily H N Fs, ∀ f ∈ F,
      f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hF)
  have h := (mem_pointUniverse H N f).mp (List.mem_filter.mp hf).1
  exact ⟨Compiler.Size.natAbs_le_of_bounds h.1,Compiler.Size.natAbs_le_of_bounds h.2.1⟩

end
end TranslationTiling.FiniteCompiler.Effective
