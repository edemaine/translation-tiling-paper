import TranslationTiling.FiniteCompiler.SharedActivation
import Mathlib.Logic.Equiv.Sum

namespace TranslationTiling.FiniteCompiler.FourValueShift

open scoped BigOperators

noncomputable section

/-- The shared output and the four outputs that mark values of a digit. -/
abbrev Index := ZMod 5
abbrev Shift (m : Index → ℕ) := ∀ j, ZMod (m j)
abbrev Bits := Index → Bool

variable {m : Index → ℕ}

def bitPoint (z : Bits) : Shift m := fun j => if z j then 1 else 0

def changeBits (z : Bits) : Bits := fun j => xor (z j) (z (j+1))

/-- Restore the coordinate that is read by the current block. -/
def restore (i : Index) (z : Bits) : Bits :=
  Function.update (changeBits z) i (z i)

theorem restore_bijective (i : Index) : Function.Bijective (restore i) := by
  revert i
  decide +kernel

theorem bitPoint_injective (hm : ∀ j, 1 < m j) : Function.Injective (bitPoint (m := m)) := by
  intro x y h
  funext j
  have : Fact (1 < m j) := ⟨hm j⟩
  have hj := congrFun h j
  cases hx : x j <;> cases hy : y j <;> simp_all [bitPoint]

/-- The shift is the identity outside the binary cube. -/
def shift (z : Shift m) : Shift m :=
  if h : ∃ w : Bits, bitPoint w = z then bitPoint (changeBits h.choose) else z

theorem shift_bitPoint (hm : ∀ j, 1 < m j) (z : Bits) :
    shift (bitPoint (m := m) z) = bitPoint (changeBits z) := by
  have h : ∃ w : Bits, bitPoint (m := m) w = bitPoint z := ⟨z,rfl⟩
  rw [shift,dite_eq_left h,(bitPoint_injective hm) h.choose_spec]

/-- The ranks are unchanged outside the binary cube and bijective on it. -/
theorem rank_bijective (hm : ∀ j, 1 < m j) (i : Index) :
    Function.Bijective (fun z : Shift m => Function.update (shift z) i (z i)) := by
  let r := fun z : Shift m => Function.update (shift z) i (z i)
  change Function.Bijective r
  have hin (w : Bits) : r (bitPoint w) = bitPoint (restore i w) := by
    dsimp only [r]
    rw [shift_bitPoint hm]
    funext j
    by_cases hj : j = i
    · subst j
      simp [restore,bitPoint]
    · simp [restore,bitPoint,Function.update_of_ne hj]
  have hout (z : Shift m) (hz : ¬ ∃ w : Bits, bitPoint w = z) : r z = z := by
    simp [r,shift,hz]
  constructor
  · intro a b he
    by_cases ha : ∃ w : Bits, bitPoint w = a
    · obtain ⟨u,rfl⟩ := ha
      rw [hin] at he
      by_cases hb : ∃ w : Bits, bitPoint w = b
      · obtain ⟨v,rfl⟩ := hb
        rw [hin] at he
        exact congrArg bitPoint ((restore_bijective i).1 ((bitPoint_injective hm) he))
      · rw [hout b hb] at he
        exact (hb ⟨_,he⟩).elim
    · rw [hout a ha] at he
      by_cases hb : ∃ w : Bits, bitPoint w = b
      · obtain ⟨v,rfl⟩ := hb
        rw [hin] at he
        exact (ha ⟨_,he.symm⟩).elim
      · rwa [hout b hb] at he
  · intro z
    by_cases hz : ∃ w : Bits, bitPoint w = z
    · obtain ⟨w,rfl⟩ := hz
      obtain ⟨v,hv⟩ := (restore_bijective i).2 w
      exact ⟨bitPoint v,by rw [hin,hv]⟩
    · exact ⟨z,hout z hz⟩

/-- The output of the block whose label lies in coordinate `i`. -/
def blockOutput (i : Index) (y : ZMod (m i)) : Shift m :=
  Function.update 0 i y

/-- Restoring one coordinate determines the entire shift index, so the
output and rotated label together determine both the index and input label. -/
theorem block_bijective (hm : ∀ j, 1 < m j) (i : Index) (x : ZMod (m i)) :
    Function.Bijective (fun (v : Shift m × ZMod (m i)) =>
      (blockOutput i v.2 + shift v.1,
        v.2 + x - (v.1 i - shift v.1 i))) := by
  let forward := fun (v : Shift m × ZMod (m i)) =>
    (blockOutput i v.2 + shift v.1, v.2 + x - (v.1 i - shift v.1 i))
  let r := fun z : Shift m => Function.update (shift z) i (z i)
  let rank := Equiv.ofBijective r (rank_bijective hm i)
  let observe (v : Shift m × ZMod (m i)) := Function.update v.1 i (v.1 i + x - v.2)
  have hob (v : Shift m × ZMod (m i)) : observe (forward v) = r v.1 := by
    funext j
    by_cases hj : j = i
    · subst j
      dsimp [observe,forward,r,blockOutput]
      simp only [Function.update_self]
      abel
    · simp [observe,forward,r,blockOutput,Function.update_of_ne hj]
  change Function.Bijective forward
  constructor
  · intro a b hab
    have he : a.1 = b.1 := (rank_bijective hm i).1 (show r a.1 = r b.1 from
      (hob a).symm.trans ((congrArg observe hab).trans (hob b)))
    have hlabel := congrFun (congrArg Prod.fst hab) i
    dsimp [forward,blockOutput] at hlabel
    simp only [Function.update_self,he,add_left_inj] at hlabel
    exact Prod.ext he hlabel
  · intro v
    let z := rank.symm (observe v)
    have hr : r z = observe v := rank.apply_symm_apply _
    refine ⟨(z,v.1 i - shift z i),Prod.ext ?_ ?_⟩
    · funext j
      by_cases hj : j = i
      · subst j
        simp [forward,blockOutput]
      · have he := congrFun hr j
        simpa [r,observe,forward,blockOutput,Function.update_of_ne hj] using he
    · have he := congrFun hr i
      simp only [r,observe,Function.update_self] at he
      dsimp [forward]
      rw [he]
      abel

private def shuffle (C : Type*) (j : Index) : (C × ZMod (m j)) × Shift m ≃
      C × (Shift m × ZMod (m j)) :=
  (Equiv.prodAssoc _ _ _).trans ((Equiv.refl _).prodCongr (Equiv.prodComm _ _))

/-- Lift the block permutation to the low coordinate, using the shared
output on the first kind of block and the selected value on the second. -/
theorem partition_bijective (hm : ∀ j, 1 < m j)
    {K A B : Type*} [AddCommGroup K] (i : Index)
    (D : LabeledBlocks K A B (m 0) (m i)) (x : ℤ) (k : K)
    (H : K × Shift m → ℤ)
    (hH : ∀ (v : K × Shift m) j, (H v : ZMod (m j)) = v.2 j - shift v.2 j) :
    Function.Bijective (fun v : K × Shift m =>
      ((match D.decode (k-v.1) with
        | .inl (_,y) => blockOutput 0 y
        | .inr (_,y) => blockOutput i y) + shift v.2,
        D.T (x-H v) (k-v.1))) := by
  let perm (j : Index) : (Shift m × ZMod (m j)) ≃ (Shift m × ZMod (m j)) :=
    Equiv.ofBijective _ (block_bijective hm j (x : ZMod (m j)))
  let e₁ : (K × Shift m) ≃ ((A × (Shift m × ZMod (m 0))) ⊕
      (B × (Shift m × ZMod (m i)))) :=
    ((Equiv.subLeft k).prodCongr (.refl _)).trans
      ((D.decode.prodCongr (.refl _)).trans
        ((Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr (shuffle A 0) (shuffle B i))))
  let e₂ : ((A × (Shift m × ZMod (m 0))) ⊕ (B × (Shift m × ZMod (m i)))) ≃ (Shift m × K) :=
    (Equiv.sumCongr ((shuffle A 0).symm.trans (Equiv.prodComm _ _))
      ((shuffle B i).symm.trans (Equiv.prodComm _ _))).trans
      ((Equiv.prodSumDistrib _ _ _).symm.trans ((Equiv.refl _).prodCongr D.decode.symm))
  let e := e₁.trans ((Equiv.sumCongr ((Equiv.refl _).prodCongr (perm 0))
    ((Equiv.refl _).prodCongr (perm i))).trans e₂)
  have he (v : K × Shift m) : e v =
      ((match D.decode (k-v.1) with
        | .inl (_,y) => blockOutput 0 y
        | .inr (_,y) => blockOutput i y) + shift v.2,
        D.T (x-H v) (k-v.1)) := by
    have hr : Equiv.subLeft k v.1 = k-v.1 := rfl
    cases h : D.decode (k-v.1) with
    | inl v₁ =>
        rcases v₁ with ⟨a,y⟩
        have he₁ : e₁ v = .inl (a,v.2,y) := by
          have hp : D.decode (Equiv.subLeft k v.1) = .inl (a,y) := hr.symm ▸ h
          change (Equiv.sumCongr (shuffle A 0) (shuffle B i))
            (Equiv.sumProdDistrib _ _ _ (D.decode (Equiv.subLeft k v.1),v.2)) = _
          rw [hp]
          rfl
        change e₂ ((Equiv.sumCongr ((Equiv.refl _).prodCongr (perm 0))
          ((Equiv.refl _).prodCongr (perm i))) (e₁ v)) = _
        rw [he₁]
        change (blockOutput 0 y + shift v.2,
          D.decode.symm (.inl (a,y+(x : ZMod (m 0))-(v.2 0 - shift v.2 0)))) = _
        simp only [LabeledBlocks.T,Equiv.trans_apply,h,LabeledBlocks.labelRotation,
          Equiv.coe_fn_mk,Int.cast_sub,hH]
        congr 3
        abel
    | inr v₁ =>
        rcases v₁ with ⟨b,y⟩
        have he₁ : e₁ v = .inr (b,v.2,y) := by
          have hp : D.decode (Equiv.subLeft k v.1) = .inr (b,y) := hr.symm ▸ h
          change (Equiv.sumCongr (shuffle A 0) (shuffle B i))
            (Equiv.sumProdDistrib _ _ _ (D.decode (Equiv.subLeft k v.1),v.2)) = _
          rw [hp]
          rfl
        change e₂ ((Equiv.sumCongr ((Equiv.refl _).prodCongr (perm 0))
          ((Equiv.refl _).prodCongr (perm i))) (e₁ v)) = _
        rw [he₁]
        change (blockOutput i y + shift v.2,
          D.decode.symm (.inr (b,y+(x : ZMod (m i))-(v.2 i - shift v.2 i)))) = _
        simp only [LabeledBlocks.T,Equiv.trans_apply,h,LabeledBlocks.labelRotation,
          Equiv.coe_fn_mk,Int.cast_sub,hH]
        congr 3
        abel
  rw [← funext he]
  exact e.bijective

private def zeroSlice (t : ZMod (m 0)) : Shift m :=
  if t = 1 then bitPoint (fun _ => true) else Function.update (0 : Shift m) 0 t

private theorem zeroSlice_shift (hm : ∀ j, 1 < m j) (t : ZMod (m 0)) :
    shift (zeroSlice t) = Function.update (0 : Shift m) 0 (if t = 1 then 0 else t) := by
  by_cases h1 : t = 1
  · subst t
    rw [zeroSlice,ite_eq_left rfl,shift_bitPoint hm]
    rw [ite_eq_left rfl]
    have hz : (0 : Shift m) 0 = 0 := rfl
    rw [← hz,Function.update_eq_self]
    funext j
    rfl
  · rw [zeroSlice,ite_eq_right h1,ite_eq_right h1]
    by_cases h0 : t = 0
    · subst t
      have hbit : Function.update (0 : Shift m) 0 0 = bitPoint (fun _ => false) := by
        funext j
        simp [bitPoint]
      rw [hbit,shift_bitPoint hm]
      rfl
    · unfold shift
      refine dite_eq_right (fun ⟨w, hw⟩ => ?_)
      have hh := congrFun hw 0
      cases hw0 : w 0
      · exact h0 (by simpa [bitPoint,hw0] using hh.symm)
      · exact h1 (by simpa [bitPoint,hw0] using hh.symm)

private theorem zeroSlice_self (t : ZMod (m 0)) : zeroSlice t 0 = t := by
  by_cases h : t = 1 <;> simp [zeroSlice,bitPoint,h]

private theorem zeroSlice_rank (hm : ∀ j, 1 < m j) (t : ZMod (m 0)) :
    Function.update (shift (zeroSlice t)) 0 (zeroSlice t 0) = Function.update (0 : Shift m) 0 t := by
  rw [zeroSlice_shift hm,zeroSlice_self,Function.update_idem]

private theorem shift_eq_zeroSlice (hm : ∀ j, 1 < m j) (z : Shift m)
    (hz : ∀ j ≠ 0, shift z j = 0) : z = zeroSlice (z 0) := by
  apply (rank_bijective hm 0).1
  change Function.update (shift z) 0 (z 0) =
    Function.update (shift (zeroSlice (z 0))) 0 (zeroSlice (z 0) 0)
  rw [zeroSlice_rank hm]
  funext j
  by_cases hj : j = 0
  · subst j
    simp
  · simp [Function.update_of_ne hj,hz j hj]

variable [∀ j, NeZero (m j)]

/-- If every value output is constant, uniform coverage would force a uniform
histogram in the shared output, whose cardinality is a multiple of its modulus. -/
theorem activation_nonconstant (hm : ∀ j, 1 < m j) {K : Type*} [Fintype K]
    (hdiv : ¬ m 0 ∣ Fintype.card K) (c : K → Shift m) (high : K × Shift m → K)
    (hcover : Function.Bijective (fun v : K × Shift m => (c v.1 + shift v.2,high v))) :
    ∃ j ≠ 0, ¬ ∃ t, ∀ k, c k j = t := by
  classical
  by_contra hn
  push Not at hn
  choose d hd using hn
  let u : Shift m := fun j => if hj : j = 0 then 0 else d j hj
  let out : K × Shift m → Shift m × K := fun v => (c v.1 + shift v.2 - u,high v)
  have hout : Function.Bijective out :=
    ((Equiv.subRight u).prodCongr (.refl K)).bijective.comp hcover
  let target (a : ZMod (m 0)) : Shift m := Function.update (0 : Shift m) 0 a
  let Q (a : ZMod (m 0)) := ∑ k : K, if c k 0 = a then (1 : ℤ) else 0
  have hslice (k : K) (a : ZMod (m 0)) :
      (∑ z : Shift m, if (out (k,z)).1 = target a then (1 : ℤ) else 0) =
        ∑ t : ZMod (m 0), if c k 0 + (if t = 1 then 0 else t) = a
          then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter,← Finset.sum_filter]
    have onSlice (z : Shift m) (hz : (out (k,z)).1 = target a) (j : Index)
        (hj : j ≠ 0) : shift z j = 0 := by
      have hh := congrFun hz j
      simpa [out,u,hj,target,Function.update_of_ne hj,hd j hj,add_comm (c k j)] using hh
    refine Finset.sum_bij (fun z _ => z 0) ?_ ?_ ?_ (by intros; rfl)
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      have hh := congrFun hz' 0
      change (c k + shift z - u) 0 = target a 0 at hh
      rw [show shift z = shift (zeroSlice (z 0)) from congrArg shift (shift_eq_zeroSlice hm z (onSlice z hz')),
        zeroSlice_shift hm] at hh
      simpa [u,target] using hh
    · intro z hz w hw h
      exact (shift_eq_zeroSlice hm z (onSlice z (Finset.mem_filter.mp hz).2)).trans
        ((congrArg zeroSlice h).trans
          (shift_eq_zeroSlice hm w (onSlice w (Finset.mem_filter.mp hw).2)).symm)
    · intro t ht
      refine ⟨zeroSlice t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,zeroSlice_self t⟩
      funext j
      by_cases hj : j = 0
      · subst j
        simpa [out,u,target,zeroSlice_shift hm] using (Finset.mem_filter.mp ht).2
      · simp [out,u,hj,target,zeroSlice_shift hm,hd j hj]
  have hdif (a : ZMod (m 0)) : Q a = Q (a-1) := by
    have hcount := sum_firstCoordinate_of_bijective out hout (target a)
    have hh : (∑ v : K × Shift m, if (out v).1 = target a then (1 : ℤ) else 0) =
        (Fintype.card K : ℤ) := by
      exact_mod_cast hcount
    rw [Fintype.sum_prod_type] at hh
    simp_rw [hslice] at hh
    have hlocal (k : K) :
        (∑ t : ZMod (m 0), if c k 0 + (if t = 1 then 0 else t) = a
            then (1 : ℤ) else 0) =
          1 + (if c k 0 = a then 1 else 0) - (if c k 0 = a-1 then 1 else 0) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : ZMod (m 0)))]
      simp only [ite_true,add_zero]
      have he : (∑ t ∈ (Finset.univ.erase (1 : ZMod (m 0))),
          if c k 0 + (if t = 1 then 0 else t) = a then (1 : ℤ) else 0) =
          ∑ t ∈ (Finset.univ.erase (1 : ZMod (m 0))), if c k 0 + t = a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [ite_eq_right (Finset.ne_of_mem_erase hv)]
      rw [he]
      have hb : (∑ t : ZMod (m 0), if c k 0 + t = a then (1 : ℤ) else 0) = 1 := by
        simp_rw [show ∀ t : ZMod (m 0), c k 0 + t = a ↔ t = a - c k 0 by
          intro t; rw [eq_sub_iff_add_eq,add_comm]]
        simp
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : ZMod (m 0)))] at hb
      simp only [show c k 0 + 1 = a ↔ c k 0 = a - 1 by rw [eq_sub_iff_add_eq]] at hb
      linarith
    simp_rw [hlocal] at hh
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ] at hh
    simp only [nsmul_eq_mul,mul_one] at hh
    exact (sub_eq_iff_eq_add.mp (by linarith : Q a - Q (a-1) = 0)).trans (zero_add _)
  have hconst (a : ZMod (m 0)) : Q a = Q 0 := by
    have hiter (v : ℕ) : Q (v : ZMod (m 0)) = Q 0 := by
      induction v with
      | zero => simp
      | succ v ih => rw [hdif (↑(v+1)),Nat.cast_add,Nat.cast_one,add_sub_cancel_right,ih]
    simpa only [ZMod.natCast_zmod_val] using hiter a.val
  have hmass : (∑ a, Q a) = Fintype.card K := by
    unfold Q
    rw [Finset.sum_comm]
    simp
  simp_rw [hconst] at hmass
  rw [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] at hmass
  exact hdiv (by exact_mod_cast (show (m 0 : ℤ) ∣ (Fintype.card K : ℤ) from
    ⟨Q 0,hmass.symm⟩))

end
end TranslationTiling.FiniteCompiler.FourValueShift
