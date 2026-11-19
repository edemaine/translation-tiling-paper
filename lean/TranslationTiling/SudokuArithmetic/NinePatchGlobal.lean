import TranslationTiling.SudokuArithmetic.NinePatchField

namespace TranslationTiling.Sudoku.NinePatch
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000

def LineRule {p : Nat} (W : Fin 9 → Int → (ZMod p)ˣ) : Prop :=
  ∀ d e : Int, ∃ a b : ZMod p, (a≠0 ∨ b≠0) ∧ ∀ n,
    a*(position p n.val:ZMod p)+b≠0 →
      (W n (d*(position p n.val:Int)+e)).val=a*(position p n.val:ZMod p)+b

theorem global_affine {p : Nat} [Fact p.Prime] (hp : p=5 ∨ p=7)
    (W : Fin 9 → Int → (ZMod p)ˣ) (hW : LineRule W) :
    ∃ A B C : ZMod p, (A≠0 ∨ B≠0 ∨ C≠0) ∧ ∀ n (m : Int),
      A*(position p n.val:ZMod p)+B*(m:ZMod p)+C≠0 →
        (W n m).val=A*(position p n.val:ZMod p)+B*(m:ZMod p)+C := by
  have hlarge : 4≤p := by rcases hp with rfl|rfl <;> decide
  have hx : Function.Injective (fun i : Fin 4 => (position p i.val:ZMod p)) := by
    simpa only [position,show ∀ i : Fin 4, i.val<5 by intro i; omega,
      if_true,zero_add,Int.cast_natCast] using ArithmeticRule.four_residues_injective hlarge 0
  obtain ⟨abc,hn,h⟩ := glue_patches
    (fun n : Fin 9 => (position p n.val:ZMod p)) (fun m : Int => (m:ZMod p)) hx
    (fun t => ArithmeticRule.four_residues_injective hlarge t) (fun n m => (W n m).val) (by
      intro t
      let V : Nat → Nat → ZMod p := fun n y => if hn : n<9 then (W ⟨n,hn⟩ (t+y)).val else 1
      have hV : ∀ n<9, ∀ y<7, V n y≠0 := by
        intro n hn y _
        simpa only [V,dif_pos hn] using Units.ne_zero (W ⟨n,hn⟩ (t+y))
      have hl : PatchLines V := by
        intro i _
        let l := lineAt p i
        obtain ⟨a,b,hab,hm⟩ := hW l.1 (t+l.2)
        refine ⟨a,b,hab,?_⟩
        intro n y hny hv
        have he := entries_spec hny
        have htime : (t+y:Int)=l.1*(position p n:Int)+(t+l.2) := by
          have hyy := he.2.2
          change (y:Int)=l.1*(position p n:Int)+l.2 at hyy
          omega
        simpa only [V,dif_pos he.1,htime] using hm ⟨n,he.1⟩ hv
      obtain ⟨A,B,C,hn,ha⟩ := field_patch hp V hV hl
      refine ⟨(A,B,C-B*(t:ZMod p)),?_,?_⟩
      · by_contra hz
        push Not at hz
        change A=0 ∧ B=0 ∧ C-B*(t:ZMod p)=0 at hz
        rcases hn with ha|hb|hc
        · exact ha hz.1
        · exact hb hz.2.1
        · exact hc (by simpa [hz.2.1] using hz.2.2)
      · intro n m htm hmt hv
        let y := (m-t).toNat
        have hy : y<7 := by dsimp [y]; omega
        have he : (t+y:Int)=m := by dsimp [y]; omega
        have hform : A*(position p n.val:ZMod p)+B*(y:ZMod p)+C=
            A*(position p n.val:ZMod p)+B*(m:ZMod p)+(C-B*(t:ZMod p)) := by
          have hcast := congrArg (fun z : Int => (z:ZMod p)) he
          push_cast at hcast
          linear_combination B*hcast
        have hh := ha n.val n.isLt y hy (by rwa [hform])
        simpa only [V,dif_pos n.isLt,he,hform] using hh)
  exact ⟨abc.1,abc.2.1,abc.2.2,hn,h⟩

end
end TranslationTiling.Sudoku.NinePatch
