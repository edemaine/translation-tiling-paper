import TranslationTiling.Rails.Micro

namespace TranslationTiling.Rails
open FourLayer (gridMap dent Rect)
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable (a B : ℕ) [NeZero a] [NeZero B]

private theorem zero_offset_safe (v : Lattice 3) (k : Fin 3) :
    ∀ j, 3 • v+Pi.single k 2≠dent (scales a B) j := by
  intro j he
  have hh := congrFun he (if k=0 then 1 else 0)
  fin_cases k <;> fin_cases j <;>
    simp [dent,gridMap,scales,widths,Kim.bumpAt] at hh <;> omega

private theorem all_zero_safe (v : Lattice 3) :
    ∀ j, 3 • v+(0 : Lattice 3)≠dent (scales a B) j := by
  intro j he
  have hh := congrFun he 0
  fin_cases j <;> simp [dent,gridMap,scales,widths,Kim.bumpAt] at hh <;> omega

private theorem micro_mem (p q : Equiv.Perm (Fin a)) (i : ℕ) (v c : Lattice 3)
    (hv : Fiber a B p q i v) (hc : c∈Kim.cube 3)
    (hn : ∀ j, 3 • v+c≠dent (scales a B) j) : MicroFiber a B p q i (3 • v+c) := by
  have hh := micro_box a B v c hv.1 hc
  exact ⟨hh.1,by rw [hh.2]; exact hv.2,hn⟩

theorem lift_contact (p q : Equiv.Perm (Fin a)) (i j : ℕ) (k : Fin 3)
    {v w : Lattice 3} (hv : Fiber a B p q i v) (hw : Fiber a B p q j w)
    (he : v+Pi.single k 1=gridMap (widths a B) (Pi.single k 1)+w) :
    ∃ r t, MicroFiber a B p q i r ∧ MicroFiber a B p q j t ∧
      r+Pi.single k 1=gridMap (scales a B) (Pi.single k 1)+t := by
  refine ⟨3 • v+Pi.single k 2,3 • w+0,?_,?_,?_⟩
  · apply micro_mem a B p q i v _ hv
    · apply (Kim.mem_cube_iff 3 _).mpr
      intro l; by_cases hl : l=k <;> simp [Pi.single_apply,hl]
    · exact zero_offset_safe a B v k
  · exact micro_mem a B p q j w 0 hw (by decide) (all_zero_safe a B w)
  · have hh := congrArg (fun x : Lattice 3 => 3 • x) he
    ext l
    have h := congrFun hh l
    simp [gridMap,scales,Pi.single_apply,Pi.smul_apply,nsmul_eq_mul] at h ⊢
    split_ifs at h ⊢ <;> omega

theorem x_micro_contact (p q : Equiv.Perm (Fin a)) (j : Fin a) :
    ∃ r t, MicroFiber a B p q (p j).val r ∧ MicroFiber a B p q j.val t ∧
      r+Pi.single 0 1=gridMap (scales a B) (Pi.single 0 1)+t := by
  obtain ⟨v,w,hv,hw,he⟩ := x_contact a B p q j
  exact lift_contact a B p q _ _ 0 hv hw he

theorem y_micro_contact (p q : Equiv.Perm (Fin a)) (j : Fin a) :
    ∃ r t, MicroFiber a B p q (q j).val r ∧ MicroFiber a B p q j.val t ∧
      r+Pi.single 1 1=gridMap (scales a B) (Pi.single 1 1)+t := by
  obtain ⟨v,w,hv,hw,he⟩ := y_contact a B p q j
  exact lift_contact a B p q _ _ 1 hv hw he

theorem z_micro_contact (p q : Equiv.Perm (Fin a)) (i : Fin B) (hi : i.val+1<B) :
    ∃ r t, MicroFiber a B p q (railLabel a i.val) r ∧
      MicroFiber a B p q (railLabel a (i.val+1)) t ∧
      r+Pi.single 2 1=gridMap (scales a B) (Pi.single 2 1)+t := by
  obtain ⟨v,w,hv,hw,he⟩ := z_contact a B p q i hi
  exact lift_contact a B p q _ _ 2 hv hw he

theorem internal_micro_contact (p q : Equiv.Perm (Fin a)) (i : Fin B) (j : Fin a) :
    ∃ r t, MicroFiber a B p q (railLabel a i.val) r ∧ MicroFiber a B p q j.val t ∧
      t=r+Pi.single 2 1 := by
  obtain ⟨v,w,hv,hw,he⟩ := internal_contact a B p q i j
  refine ⟨3 • v+Pi.single 2 2,3 • w+0,?_,?_,?_⟩
  · exact micro_mem a B p q _ v _ hv (by decide) (zero_offset_safe a B v 2)
  · exact micro_mem a B p q _ w 0 hw (by decide) (all_zero_safe a B w)
  · rw [he]; ext k; fin_cases k <;> simp <;> ring

end
end TranslationTiling.Rails
