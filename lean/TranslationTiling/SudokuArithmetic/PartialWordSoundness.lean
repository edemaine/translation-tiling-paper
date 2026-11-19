import TranslationTiling.SudokuArithmetic.PartialWordFormula

namespace TranslationTiling.Sudoku.PartialWord
open Mathlib.Tactic

noncomputable section

def Matches (W : ℕ → ℕ) (p : Pattern) : Prop := ∀ iv ∈ p, W iv.1 = iv.2

theorem mem_coordinates_iff {r : ℕ} {digit : ℕ → ℕ} {i v : ℕ} :
    (i,v) ∈ coordinates r digit ↔ i < 9 ∧ digit i ≠ 0 ∧ v = digit i := by
  unfold coordinates
  simp only [List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    split at h <;> simp_all
    simpa [h.1] using h.2.symm
  · rintro ⟨hi,hn,rfl⟩
    exact ⟨i,hi,by simp [hn]⟩

theorem mem_residues_iff {r a b : ℕ} :
    (a,b) ∈ residues r ↔ a < r^2 ∧ b < r^2 ∧ (a%r ≠ 0 ∨ b%r ≠ 0) := by
  simp [residues, and_assoc]

theorem mem_legal {r : ℕ} {p : Pattern} :
    p ∈ legal r ↔ ∃ a b : ℕ, (a,b) ∈ residues r ∧ p=coordinates r (predicted r a b) := by
  simp only [legal,List.mem_eraseDups,List.mem_map]
  constructor
  · rintro ⟨⟨a,b⟩,h,rfl⟩
    exact ⟨a,b,h,rfl⟩
  · rintro ⟨a,b,h,rfl⟩
    exact ⟨(a,b),h,rfl⟩

private theorem satisfies_iff (v : Sat.Valuation) (c : List Sat.Literal) :
    v.satisfies c ↔ ∃ l ∈ c, ¬ v.neg l := by
  classical
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    simp only [Sat.Valuation.satisfies, ih, List.mem_cons]
    by_cases h : v.neg l <;> simp_all

theorem covers_of_unsat {r : ℕ} {cs : List Pattern}
    (hu : Sat.Fmla.proof (formula r cs) []) (W : ℕ → ℕ)
    (hW : ∀ i<9, 0<W i ∧ W i<r)
    (hvalid : ∀ p∈cs++legal r, ∀ (iv : ℕ × ℕ), iv ∈ p → iv.1 < 9 ∧ 0 < iv.2 ∧ iv.2 < r)
    (havoid : ∀ p∈cs, ¬ Matches W p) :
    ∃ p∈legal r, Matches W p := by
  classical
  by_contra hn
  let val : Sat.Valuation := fun k => ∃ i<9, k=cell r i (W i)
  have hread (i v : ℕ) (hi : i<9) (hv : 0<v) (hvr : v<r) :
      val (cell r i v) ↔ W i=v := by
    constructor
    · rintro ⟨j,hj,he⟩
      have hp : 0<r-1 := by omega
      have hdiv (k a : ℕ) (ha : 0<a) (hb : a<r) : cell r k a / (r-1) = k := by
        rw [cell,Nat.mul_comm k, Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega)]
        omega
      have e := congrArg (· / (r-1)) he
      rw [hdiv i v hv hvr,hdiv j (W j) (hW j hj).1 (hW j hj).2] at e
      subst j
      unfold cell at he
      have hw := (hW i hi).1
      omega
    · intro he
      exact ⟨i,hi,by rw [he]⟩
  apply hu val
  constructor
  intro c hc
  rcases List.mem_append.mp hc with hh | hh
  · obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hh
    have hi := List.mem_range.mp hi
    have hm (v : ℕ) : v ∈ digits r ↔ 0<v ∧ v<r := by
      simp only [digits,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨j,hj,rfl⟩; omega
      · intro hv; exact ⟨v-1,by omega,by omega⟩
    apply (satisfies_iff _ _).mpr
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨.pos (cell r i (W i)),List.mem_map.mpr ⟨_,(hm (W i)).mpr (hW i hi),rfl⟩,
        by change ¬ ¬ val _; exact not_not_intro ⟨i,hi,rfl⟩⟩
    · obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hc
      have hw' := List.mem_filter.mp hw
      by_cases he : W i=v
      · refine ⟨.neg (cell r i w),by simp,?_⟩
        intro hx
        have hh := (hread i w hi ((hm w).mp hw'.1).1 ((hm w).mp hw'.1).2).mp hx
        exact (Nat.ne_of_lt (of_decide_eq_true hw'.2)) (he.symm.trans hh)
      · exact ⟨.neg (cell r i v),by simp,fun hx =>
          he ((hread i v hi ((hm v).mp hv).1 ((hm v).mp hv).2).mp hx)⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hh
    have hbad : ¬ Matches W p := by
      rcases List.mem_append.mp hp with hs|hs
      · exact havoid p hs
      · exact fun h => hn ⟨p,hs,h⟩
    unfold Matches at hbad
    push Not at hbad
    obtain ⟨⟨i,v⟩,hi,he⟩ := hbad
    obtain ⟨hi',hv,hvr⟩ := hvalid p hp (i,v) hi
    exact (satisfies_iff _ _).mpr ⟨.neg (cell r i v),List.mem_map.mpr ⟨(i,v),hi,rfl⟩,
      fun h => he ((hread i v hi' hv hvr).mp h)⟩

theorem incompatible_of_clashes {W : ℕ → ℕ} {p q : Pattern}
    (h : clashes p q = true) (hp : Matches W p) (hq : Matches W q) : False := by
  unfold clashes at h
  obtain ⟨⟨i,v⟩,hi,h⟩ := List.any_eq_true.mp h
  obtain ⟨⟨j,w⟩,hj,h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at h
  exact h.2 ((hp _ hi).symm.trans ((congrArg W h.1).trans (hq _ hj)))

def values (r : ℕ) (V : NineArithmetic.Column r → (ZMod r)ˣ) (i : ℕ) : ℕ :=
  if hi : i<9 then (V ⟨i,hi⟩).val.val else 0

theorem values_pos_lt {r : ℕ} (hr : r.Prime) (V : NineArithmetic.Column r → (ZMod r)ˣ)
    (i : ℕ) (hi : i<9) : 0 < values r V i ∧ values r V i < r := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  rw [values,dif_pos hi]
  exact ⟨Nat.pos_of_ne_zero (fun h => Units.ne_zero _ (ZMod.val_injective r (h.trans ZMod.val_zero.symm))),
    ZMod.val_lt _⟩

theorem pattern_bounds {r : ℕ} (hr : r.Prime) (codes : List ℕ) :
    ∀ p ∈ codes.map (decode r) ++ legal r, ∀ (iv : ℕ × ℕ), iv ∈ p →
      iv.1 < 9 ∧ 0 < iv.2 ∧ iv.2 < r := by
  letI : NeZero r := ⟨hr.ne_zero⟩
  intro p hp iv hiv
  rcases List.mem_append.mp hp with h|h
  · obtain ⟨m,_,rfl⟩ := List.mem_map.mp h
    have ⟨hi,hn,he⟩ := mem_coordinates_iff.mp hiv
    refine ⟨hi,Nat.pos_of_ne_zero (he.symm ▸ hn),?_⟩
    rw [he]
    exact Nat.mod_lt _ hr.pos
  · obtain ⟨a,b,_,rfl⟩ := mem_legal.mp h
    have ⟨hi,hn,he⟩ := mem_coordinates_iff.mp hiv
    refine ⟨hi,Nat.pos_of_ne_zero (he.symm ▸ hn),?_⟩
    rw [he]
    unfold predicted
    dsimp only
    split
    · exact ZMod.val_lt _
    · exact hr.pos

private theorem arithmetic_digit_ne_zero {r : ℕ} (hr : r.Prime) {z : ℤ} {u : ℕ}
    (hu : lowValuation r z = some u) : (lowDigit r z).val ≠ 0 := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  intro h
  have h' := ZMod.val_injective r (h.trans ZMod.val_zero.symm)
  exact Units.ne_zero _ ((lastDigit_eq_lowDigit r hr z u hu).trans h')

def IsArithmetic (r : ℕ) (V : NineArithmetic.Column r → (ZMod r)ˣ) : Prop :=
  ∃ a b : ℤ, (¬ (r:ℤ) ∣ a ∨ ¬ (r:ℤ) ∣ b) ∧
    ∀ i u, lowValuation r (a*NineArithmetic.position r i+b)=some u → u≤threshold r a →
      (V i).val=lowDigit r (a*NineArithmetic.position r i+b)

theorem arithmetic_of_match {r : ℕ} (hr : r.Prime) (V : NineArithmetic.Column r → (ZMod r)ˣ)
    {p : Pattern} (hp : p∈legal r) (hm : Matches (values r V) p) :
    IsArithmetic r V := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨a,b,hab,rfl⟩ := mem_legal.mp hp
  have hprim := (mem_residues_iff.mp hab).2.2
  refine ⟨a,b,?_,fun i u hu _ => ?_⟩
  · simpa only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] using hprim
  apply ZMod.val_injective r
  have hd : predicted r a b i.val = (lowDigit r ((a:ℤ)*NineArithmetic.position r i+b)).val := by
    unfold predicted
    dsimp only
    change lowValuation r ((a:ℤ)*NinePatch.position r i.val+b)=some u at hu
    simp only [hu,Option.isSome_some,ite_true,NineArithmetic.position]
  have hi := hm (i.val, (lowDigit r ((a:ℤ)*NineArithmetic.position r i+b)).val)
    (mem_coordinates_iff.mpr ⟨i.isLt,by rw [hd]; exact arithmetic_digit_ne_zero hr hu,hd.symm⟩)
  simpa [values,i.isLt] using hi

private theorem bounded_repr (r : ℕ) (hr : r.Prime) (v : ℤ) :
    ∃ n : ℕ, n<r^2 ∧ SqCongr r v n := by
  have hm : 0 < (r:ℤ)^2 := by positivity [hr.pos]
  let u := v % (r:ℤ)^2
  have hn : 0≤u := Int.emod_nonneg _ (ne_of_gt hm)
  refine ⟨u.toNat,?_,?_⟩
  · exact_mod_cast (show (u.toNat:ℤ)<(r:ℤ)^2 from by
      rw [Int.toNat_of_nonneg hn]; exact Int.emod_lt_of_pos _ hm)
  · unfold SqCongr
    rw [Int.toNat_of_nonneg hn]
    exact ⟨v / (r:ℤ)^2,by dsimp [u]; have := Int.emod_add_mul_ediv v ((r:ℤ)^2); omega⟩

theorem match_of_arithmetic {r : ℕ} (hr : r.Prime) (V : NineArithmetic.Column r → (ZMod r)ˣ)
    (h : IsArithmetic r V) : ∃ p ∈ legal r, Matches (values r V) p := by
  obtain ⟨a,b,hab,hV⟩ := h
  obtain ⟨a',ha,hca⟩ := bounded_repr r hr a
  obtain ⟨b',hb,hcb⟩ := bounded_repr r hr b
  have hprim : ¬ (r:ℤ) ∣ (a':ℤ) ∨ ¬ (r:ℤ) ∣ (b':ℤ) := by
    simpa only [←hca.dvd_iff,←hcb.dvd_iff] using hab
  have hres : (a',b') ∈ residues r := mem_residues_iff.mpr
    ⟨ha,hb,by simpa only [Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero] using hprim⟩
  refine ⟨_,mem_legal.mpr ⟨a',b',hres,rfl⟩,?_⟩
  rintro ⟨i,v⟩ hv
  obtain ⟨hi,hn,rfl⟩ := mem_coordinates_iff.mp hv
  let k : NineArithmetic.Column r := ⟨i,hi⟩
  have hc := hca.affine hcb (NineArithmetic.position r k)
  have hh : lowValuation r ((a':ℤ)*NineArithmetic.position r k+b') ≠ none := by
    intro hz
    have h0 : lowValuation r ((a':ℤ)*NinePatch.position r i+b')=none := hz
    exact hn (by simp [predicted,h0])
  cases he : lowValuation r ((a':ℤ)*NineArithmetic.position r k+b') with
  | none => exact (hh he).elim
  | some u =>
    have hu : lowValuation r (a*NineArithmetic.position r k+b)=some u := hc.lowValuation_eq.trans he
    have hbound : u ≤ threshold r a := by
      by_cases hnd : ¬(r:ℤ)∣a*NineArithmetic.position r k+b
      · simp [lowValuation,hnd] at hu
        simp [←hu]
      · have ha := NineArithmetic.primitive_slope_not_dvd r a b (NineArithmetic.position r k) hab (not_not.mp hnd)
        unfold lowValuation at hu
        rw [if_neg hnd] at hu
        split at hu <;> simp_all [threshold]
    have hd := (hV k u hu hbound).trans (hc.lowDigit_eq hr.ne_zero)
    simpa only [values,dif_pos hi,predicted,←show NineArithmetic.position r k=NinePatch.position r i from rfl,
      he,Option.isSome_some,if_true] using congrArg ZMod.val hd

theorem avoids_of_safe {r : ℕ} {cs : List Pattern} (hr : r.Prime)
    (hsafe : cs.all (fun p => (legal r).all (clashes p)) = true)
    (V : NineArithmetic.Column r → (ZMod r)ˣ) (h : IsArithmetic r V) :
    ∀ p∈cs, ¬ Matches (values r V) p := by
  obtain ⟨q,hq,hm⟩ := match_of_arithmetic hr V h
  intro p hp hp'
  exact incompatible_of_clashes (List.all_eq_true.mp (List.all_eq_true.mp hsafe p hp) q hq) hp' hm

theorem arithmetic_of_covers {r : ℕ} {codes : List ℕ} (hr : r.Prime)
    (hu : Sat.Fmla.proof (formula r (codes.map (decode r))) [])
    (V : NineArithmetic.Column r → (ZMod r)ˣ)
    (h : ∀ p∈codes.map (decode r), ¬ Matches (values r V) p) :
    IsArithmetic r V := by
  obtain ⟨p,hp,hm⟩ := covers_of_unsat hu _ (values_pos_lt hr V) (pattern_bounds hr codes) h
  exact arithmetic_of_match hr V hp hm


end
end TranslationTiling.Sudoku.PartialWord
