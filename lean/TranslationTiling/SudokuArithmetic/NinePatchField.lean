import TranslationTiling.SudokuArithmetic.NinePatchLocal
import TranslationTiling.SudokuArithmetic.NinePatchOverlap

namespace TranslationTiling.Sudoku.NinePatch
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000

variable {p : Nat} [Fact p.Prime]

theorem entries_spec {l : Int × Int} {n y : Nat} (h : (n,y)∈entries p l) :
    n<9 ∧ y<7 ∧ (y:Int)=l.1*(position p n:Int)+l.2 := by
  obtain ⟨n',hn',he⟩ := List.mem_filterMap.mp h
  dsimp only at he
  split at he
  next hy =>
    cases Option.some.inj he
    exact ⟨List.mem_range.mp hn', by omega, Int.toNat_of_nonneg hy.1⟩
  next => contradiction

private theorem cast_value (a b : ZMod p) (n : Nat) :
    (value p (a.val,b.val) n : ZMod p)=a*(position p n:ZMod p)+b := by
  simp [value,ZMod.natCast_mod]

private theorem cast_affine (abc : Nat × Nat × Nat) (n y : Nat) :
    (affineValue p abc n y : ZMod p)=
      (abc.1:ZMod p)*(position p n:ZMod p)+(abc.2.1:ZMod p)*y+abc.2.2 := by
  simp [affineValue,ZMod.natCast_mod]

def PatchLines (W : Nat → Nat → ZMod p) : Prop :=
  ∀ i<(lines p).length, ∃ a b : ZMod p, (a≠0 ∨ b≠0) ∧
    ∀ n y, (n,y)∈entries p (lineAt p i) → a*(position p n:ZMod p)+b≠0 →
      W n y=a*(position p n:ZMod p)+b

theorem normalized_field_patch (hp : p=5 ∨ p=7) (W : Nat → Nat → ZMod p)
    (hw : ∀ n<9, ∀ (y : Nat), y<7 → W n y≠0) (hnorm : W 0 0=1) (hl : PatchLines W) :
    ∃ A B C : ZMod p, (A≠0 ∨ B≠0 ∨ C≠0) ∧
      ∀ n<9, ∀ (y : Nat), y<7 → A*(position p n:ZMod p)+B*(y:ZMod p)+C≠0 →
        W n y=A*(position p n:ZMod p)+B*(y:ZMod p)+C := by
  have hpos : 0<p := (Fact.out : p.Prime).pos
  obtain ⟨abc,habc,h⟩ := normalized_patch_affine hp (fun n y => (W n y).val)
    (fun n hn y hy => ⟨Nat.pos_of_ne_zero (by simpa using hw n hn y hy),ZMod.val_lt _⟩)
    (by rw [hnorm,ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by rcases hp with rfl|rfl <;> decide)]) (by
      intro i hi
      obtain ⟨a,b,hab,hm⟩ := hl i hi
      refine ⟨(a.val,b.val), mem_forms.mpr ⟨ZMod.val_lt _,ZMod.val_lt _,?_⟩, ?_⟩
      · simpa only [ne_eq,ZMod.val_eq_zero] using hab
      · intro n y hny hv
        have hv' : a*(position p n:ZMod p)+b≠0 := by
          rw [← cast_value a b n]
          exact fun hz => hv (by
            have := congrArg ZMod.val hz
            simpa only [value,ZMod.val_natCast,ZMod.val_zero,Nat.mod_mod] using this)
        have he := congrArg ZMod.val (hm n y hny hv')
        rw [← cast_value a b n] at he
        simpa only [value,ZMod.val_natCast,Nat.mod_mod] using he)
  rcases abc with ⟨aa,bb,cc⟩
  let abc := (aa,bb,cc)
  have htr : abc.1<p ∧ abc.2.1<p ∧ abc.2.2<p ∧
      (abc.1≠0 ∨ abc.2.1≠0 ∨ abc.2.2≠0) := by
    simpa [triples,List.mem_flatMap,List.mem_map,List.mem_filter,Prod.mk.injEq,abc,or_assoc] using habc
  refine ⟨abc.1,abc.2.1,abc.2.2,?_,?_⟩
  · simpa only [ne_eq,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero,
      Nat.mod_eq_of_lt htr.1,Nat.mod_eq_of_lt htr.2.1,Nat.mod_eq_of_lt htr.2.2.1] using htr.2.2.2
  · intro n hn y hy hv
    have hz : affineValue p abc n y≠0 := by
      intro he
      apply hv
      rw [← cast_affine abc n y,he,Nat.cast_zero]
    have hh := congrArg (fun k : Nat => (k:ZMod p)) (h n hn y hy hz)
    simpa only [ZMod.natCast_zmod_val,cast_affine] using hh

theorem field_patch (hp : p=5 ∨ p=7) (W : Nat → Nat → ZMod p)
    (hw : ∀ n<9, ∀ (y : Nat), y<7 → W n y≠0) (hl : PatchLines W) :
    ∃ A B C : ZMod p, (A≠0 ∨ B≠0 ∨ C≠0) ∧
      ∀ n<9, ∀ (y : Nat), y<7 → A*(position p n:ZMod p)+B*(y:ZMod p)+C≠0 →
        W n y=A*(position p n:ZMod p)+B*(y:ZMod p)+C := by
  let u := W 0 0
  have hu : u≠0 := hw 0 (by decide) 0 (by decide)
  obtain ⟨A,B,C,hn,h⟩ := normalized_field_patch hp (fun n y => u⁻¹*W n y)
    (fun n hn y hy => mul_ne_zero (inv_ne_zero hu) (hw n hn y hy))
    (inv_mul_cancel₀ hu) (by
      intro i hi
      obtain ⟨a,b,hab,hm⟩ := hl i hi
      refine ⟨u⁻¹*a,u⁻¹*b,hab.imp (mul_ne_zero (inv_ne_zero hu)) (mul_ne_zero (inv_ne_zero hu)),?_⟩
      intro n y hny hv
      have hv' : a*(position p n:ZMod p)+b≠0 := by
        intro hz
        apply hv
        calc
          _ = u⁻¹*(a*(position p n:ZMod p)+b) := by ring
          _ = 0 := by rw [hz,mul_zero]
      dsimp only
      rw [hm n y hny hv']
      ring)
  refine ⟨u*A,u*B,u*C,hn.imp (mul_ne_zero hu)
    (Or.imp (mul_ne_zero hu) (mul_ne_zero hu)),?_⟩
  intro n hn y hy hv
  have he : u*A*(position p n:ZMod p)+u*B*(y:ZMod p)+u*C=
      u*(A*(position p n:ZMod p)+B*(y:ZMod p)+C) := by ring
  have hz : A*(position p n:ZMod p)+B*(y:ZMod p)+C≠0 := by
    intro hz
    apply hv
    rw [he,hz,mul_zero]
  have hh := congrArg (fun z => u*z) (h n hn y hy hz)
  rw [← mul_assoc,mul_inv_cancel₀ hu,one_mul] at hh
  exact hh.trans he.symm

end
end TranslationTiling.Sudoku.NinePatch
