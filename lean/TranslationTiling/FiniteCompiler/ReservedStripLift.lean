import TranslationTiling.FiniteCompiler.Effective.ReservedStack
import TranslationTiling.FiniteCompiler.StripLift

namespace TranslationTiling.Compiler.StripLift
open Rails Rails.Strips FiniteCompiler.Effective
open scoped Classical
noncomputable section

private theorem samples (Q U : ℕ) (hU : U<2*Q) (P : ℕ → Prop)
    (h : ∀ z, ∃ v, z≤v ∧ v≤z+U ∧ P (v%Q)) :
    ∃ a : Fin (2*Q) → ℕ,
      (∀ k, a k<2*Q ∧ P (a k%Q)) ∧
      (∀ k l, l.val=k.val+1 → ((a l:ℤ)-a k).natAbs≤U+1) ∧
      ∀ k, ((a k:ℤ)-k.val).natAbs≤U := by
  have hex (z : ℕ) : ∃ v, z≤v ∧ P (v%Q) := (h z).imp fun _ hv => ⟨hv.1,hv.2.2⟩
  let f (z : ℕ) := Nat.find (hex z)
  have hf (z : ℕ) : z≤f z ∧ f z≤z+U ∧ P (f z%Q) := by
    obtain ⟨v,hv,hvu,hp⟩ := h z
    exact ⟨(Nat.find_spec (hex z)).1,(Nat.find_min' (hex z) ⟨hv,hp⟩).trans hvu,
      (Nat.find_spec (hex z)).2⟩
  let S := (Finset.range (2*Q)).filter (fun v => P (v%Q))
  have hS : S.Nonempty := ⟨f 0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by have := (hf 0).2.1; omega),(hf 0).2.2⟩⟩
  let last := S.max' hS
  have hlast : last<2*Q ∧ P (last%Q) :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp (S.max'_mem hS)).1,
      (Finset.mem_filter.mp (S.max'_mem hS)).2⟩
  have hlastU : 2*Q-1≤last+U := by
    let z := 2*Q-1-U
    have ht : f z < 2*Q := by have := (hf z).2.1; dsimp [z] at *; omega
    have hl := S.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,(hf z).2.2⟩)
    have := (hf z).1
    dsimp [z] at *
    omega
  let a (z : ℕ) := min (f z) last
  refine ⟨fun k => a k.val,?_,?_,?_⟩
  · intro k
    obtain ⟨h₁,h₂⟩ := hlast
    dsimp only [a]
    rw [min_def]
    split
    · exact ⟨by omega,(hf k.val).2.2⟩
    · exact ⟨h₁,h₂⟩
  · intro k l hkl
    have hk := (hf k.val)
    have hl := (hf l.val)
    have hmin : f k.val≤f l.val := Nat.find_min' (hex k.val) ⟨by omega,hl.2.2⟩
    have hmon : a k.val≤a l.val := min_le_min hmin (le_refl last)
    have hstep : a l.val≤a k.val+(U+1) := by
      by_cases hh : f k.val≤last
      · dsimp only [a]
        rw [min_eq_left hh]
        have hm : min (f l.val) last≤f l.val := min_le_left _ _
        omega
      · dsimp only [a]
        rw [min_eq_right (by omega : last≤f k.val)]
        exact (min_le_right _ _).trans (by omega)
    change ((a l.val:ℤ)-(a k.val:ℤ)).natAbs≤U+1
    omega
  · intro k
    obtain ⟨hk,hku,_⟩ := hf k.val
    have hi := k.isLt
    change (((min (f k.val) last:ℕ):ℤ)-(k.val:ℤ)).natAbs≤U
    rw [min_def]
    split <;> omega

theorem connected_forward (d : CyclicTileData) (M : ℕ) (H : ℕ → ℕ) (U : ℕ)
    (hQ : 0<d.1) (hU : U<2*d.1) (hc : HasForwardColumn d U)
    (hsup : ∀ f∈d.2, TestSupportAt M H f.1) :
    FaceConnected (SlotAssembly.assemble (integerTile d) (slotsAt M H) (railHeight (U+1))) := by
  letI : NeZero d.1 := ⟨hQ.ne'⟩
  let f₀ := cyclicPoint d.1 (d.2.headD ((0,0),0))
  let P (z : ℕ) := (((0:Plane),(z:ZMod d.1)+f₀.2) : Plane × ZMod d.1)∈cyclicTileSet d.1 d.2
  have hP (z : ℕ) : ∃ v, z≤v ∧ v≤z+U ∧ P (v%d.1) := by
    obtain ⟨v,hlo,hhi,hmem⟩ := hc (z+f₀.2.val)
    let t := v-f₀.2.val
    have ht : t+f₀.2.val=v := by dsimp [t]; omega
    have he : ((t%d.1:ℕ):ZMod d.1)+f₀.2=(v:ZMod d.1) := by
      rw [←ZMod.val_natCast,ZMod.natCast_zmod_val,←ZMod.natCast_zmod_val f₀.2,←Nat.cast_add,ht]
    refine ⟨t,by dsimp [t]; omega,by dsimp [t]; omega,?_⟩
    change ((0:Plane),_)∈_
    rwa [he]
  obtain ⟨a,ha,hstep,hnear⟩ := samples d.1 U hU P hP
  apply connectedAt d M H (U+1) hQ (2*d.1) (by omega) a (fun k => (ha k).1)
  · intro k
    let z := a k%d.1
    have hm : ((0:Plane),(z:ZMod d.1)+f₀.2)-f₀ ∈
        (cyclicTileSet d.1 d.2).image (fun f => f-f₀) :=
      Finset.mem_image.mpr ⟨_,(ha k).2,rfl⟩
    have hx := CyclicQuotient.lift_mem_representatives d.1 hm
    have he : CyclicQuotient.lift d.1 (((0:Plane),(z:ZMod d.1)+f₀.2)-f₀) =
        Rails.point (-(d.2.headD ((0,0),0)).1.1) (-(d.2.headD ((0,0),0)).1.2) z := by
      ext i
      fin_cases i
      · change 0-f₀.1.1= -f₀.1.1
        simp
      · change 0-f₀.1.2= -f₀.1.2
        simp
      · change (((z:ZMod d.1)+f₀.2-f₀.2).val:ℤ)=(z:ℤ)
        rw [add_sub_cancel_right,ZMod.val_natCast_of_lt (Nat.mod_lt _ hQ)]
    rw [he] at hx
    exact hx
  · exact hstep
  · intro z hz
    exact ⟨⟨z,hz⟩,(hnear ⟨z,hz⟩).trans (by omega)⟩
  · exact hsup

end
end TranslationTiling.Compiler.StripLift
