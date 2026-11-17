import TranslationTiling.SudokuArithmetic.SmallPrimeFormula
namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

variable {p : Nat} [Fact p.Prime] {W : WordArray p}
def model (hW : LineRule p W) : Atom p → Bool
  | .inl (n,y,v) => decide ((W n y.val : ZMod p).val = v.val)
  | .inr (.inl (d,e,a,b)) =>
    let L := chooseLine hW (direction (d,e)) (intercept (d,e))
    decide (L.a.val=a.val ∧ L.b.val=b.val)
  | .inr (.inr (d,e,n)) =>
    let L := chooseLine hW (direction (d,e)) (intercept (d,e))
    decide (L.a*(n.val:ZMod p)+L.b=0)

def Holds (m : Atom p → Bool) (c : Clause p) : Prop := ∃ z∈c, m z.1=z.2

theorem cellChoices_hold (hW : LineRule p W) (c : Clause p) (hc : c∈cellChoices p) : Holds (model hW) c := by
  simp only [cellChoices,List.mem_flatMap,List.mem_finRange,List.mem_map,true_and] at hc
  obtain ⟨n,y,_,rfl⟩ := hc
  let v : Fin p := ⟨(W n y.val : ZMod p).val, ZMod.val_lt _⟩
  have hv : v.val≠0 := by
    intro h
    have he : (W n y.val : ZMod p)=0 := (ZMod.val_eq_zero _).mp h
    exact Units.ne_zero _ he
  refine ⟨(cell n y v,true),List.mem_map.mpr ⟨v,?_,rfl⟩,?_⟩
  · simpa only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] using hv
  · simp [model,cell,v]

theorem cellUnique_hold (hW : LineRule p W) (c : Clause p) (hc : c∈cellUnique p) : Holds (model hW) c := by
  simp only [cellUnique,List.mem_flatMap,List.mem_finRange,List.mem_map,true_and,List.mem_filter] at hc
  obtain ⟨n,y,u,v,hv,rfl⟩ := hc
  have huv : u.val<v.val := of_decide_eq_true hv
  dsimp [Holds,model,cell]
  by_cases h : (W n y.val : ZMod p).val=u.val
  · refine ⟨(cell n y v,false),by simp [cell,coeff,bad],?_⟩
    change decide ((W n y.val : ZMod p).val=v.val)=false
    simp only [decide_eq_false_iff_not]
    omega
  · exact ⟨(cell n y u,false),by simp [cell,coeff,bad],by simp [model,cell,h]⟩

theorem lineChoices_hold (hW : LineRule p W) (c : Clause p) (hc : c∈lineChoices p) : Holds (model hW) c := by
  simp only [lineChoices,List.mem_map] at hc
  obtain ⟨l,_,rfl⟩ := hc
  let L := chooseLine hW (direction l) (intercept l)
  let a : Fin p := ⟨L.a.val,ZMod.val_lt _⟩
  let b : Fin p := ⟨L.b.val,ZMod.val_lt _⟩
  have hnz : a.val≠0 ∨ b.val≠0 := by
    simpa only [a,b,ZMod.val_eq_zero,ne_eq] using L.nonzero
  refine ⟨(coeff l a b,true),List.mem_map.mpr ⟨(a,b),?_,rfl⟩,?_⟩
  · simpa [forms,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and,Prod.mk.injEq,exists_eq_right,decide_eq_true_eq] using hnz
  · simp [model,coeff,a,b,L]


theorem consistency_hold (hW : LineRule p W) (c : Clause p) (hc : c∈consistency p) : Holds (model hW) c := by
  simp only [consistency,List.mem_flatMap] at hc
  obtain ⟨l,_,n,_,hc⟩ := hc
  split at hc
  next hy =>
    simp only [List.mem_map,List.mem_filter] at hc
    obtain ⟨⟨a,b⟩,⟨_,hab⟩,rfl⟩ := hc
    have hv : value (a,b) n≠0 := of_decide_eq_true hab
    let L := chooseLine hW (direction l) (intercept l)
    by_cases hs : L.a.val=a.val ∧ L.b.val=b.val
    · have ha : L.a=(a.val:ZMod p) := (ZMod.val_injective p) (by simpa [ZMod.val_natCast_of_lt a.isLt] using hs.1)
      have hb : L.b=(b.val:ZMod p) := (ZMod.val_injective p) (by simpa [ZMod.val_natCast_of_lt b.isLt] using hs.2)
      have he : L.a*(n.val:ZMod p)+L.b=(value (a,b) n:ZMod p) := by
        rw [ha,hb]; simp [value,ZMod.natCast_mod]
      have hv' : L.a*(n.val:ZMod p)+L.b≠0 := by
        rw [he]; intro hz
        have hh := congrArg ZMod.val hz
        have hval : value (a,b) n<p := Nat.mod_lt _ (by have := a.isLt; omega)
        rw [ZMod.val_natCast_of_lt hval,ZMod.val_zero] at hh
        exact hv hh
      have hag := L.agrees n hv'
      change (W n (height l n) : ZMod p)=_ at hag
      have hheight : ((height l n).toNat:ℤ)=height l n := Int.toNat_of_nonneg hy.1
      refine ⟨(cell n ⟨(height l n).toNat,by omega⟩ ⟨value (a,b) n,Nat.mod_lt _ (by have := a.isLt; omega)⟩,true),by simp,?_⟩
      change decide ((W n ((height l n).toNat:ℤ):ZMod p).val=value (a,b) n)=true
      rw [hheight,hag,he]
      simp only [decide_eq_true_eq]
      exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by have := a.isLt; omega))
    · exact ⟨(coeff l a b,false),by simp [cell,coeff,bad],by simpa [model,coeff,L] using hs⟩
  next hy => simp at hc

theorem badLinks_hold (hW : LineRule p W) (c : Clause p) (hc : c∈badLinks p) : Holds (model hW) c := by
  simp only [badLinks,List.mem_flatMap] at hc
  obtain ⟨l,_,n,_,hc⟩ := hc
  split at hc
  next hy =>
    simp only [List.mem_map,List.mem_filter] at hc
    obtain ⟨⟨a,b⟩,⟨_,hab⟩,rfl⟩ := hc
    have hv : value (a,b) n≠0 := of_decide_eq_true hab
    let L := chooseLine hW (direction l) (intercept l)
    by_cases hs : L.a.val=a.val ∧ L.b.val=b.val
    · have ha : L.a=(a.val:ZMod p) := (ZMod.val_injective p) (by simpa [ZMod.val_natCast_of_lt a.isLt] using hs.1)
      have hb : L.b=(b.val:ZMod p) := (ZMod.val_injective p) (by simpa [ZMod.val_natCast_of_lt b.isLt] using hs.2)
      refine ⟨(bad l n,false),by simp [cell,coeff,bad],?_⟩
      change decide (L.a*(n.val:ZMod p)+L.b=0)=false
      rw [decide_eq_false_iff_not,ha,hb]
      intro hz
      have hh := congrArg ZMod.val hz
      have hh' : (a.val*n.val+b.val)%p=0 := by simpa [ZMod.val_add,ZMod.val_mul,ZMod.val_natCast] using hh
      exact hv hh'
    · exact ⟨(coeff l a b,false),by simp [cell,coeff,bad],by simpa [model,coeff,L] using hs⟩
  next hy => simp at hc


def total (p : Nat) := width p*(13*p)+(9*(extent p*(p*p))+9*(extent p*width p))
def assignment (m : Atom p → Bool) (k : Nat) : Bool :=
  if hk : k<total p then m ((atomEquiv p).symm ⟨k,hk⟩) else false
@[simp] theorem assignment_key (m : Atom p → Bool) (a : Atom p) : assignment m (key a)=m a := by
  unfold assignment
  rw [dif_pos (show key a<total p from (atomEquiv p a).isLt)]
  exact congrArg m ((atomEquiv p).symm_apply_apply a)

theorem formula_sat (m : Atom p → Bool) (hm : ∀ c∈clauses p, Holds m c) : (formula p).Sat (assignment m) := by
  apply Std.Sat.CNF.sat_of_all_mem_sat
  intro c hc
  simp only [formula,Std.Sat.CNF.Internal.mem_iff,List.mem_toArray,List.mem_map] at hc
  obtain ⟨c,hc,rfl⟩ := hc
  obtain ⟨⟨a,b⟩,ha,hb⟩ := hm c hc
  apply Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mpr
  refine ⟨(key a,b),?_,?_⟩
  · change (key a,b)∈(Std.Sat.CNF.Clause.ofLiterals (c.map fun ab => (key ab.1,ab.2))).literals
    rw [Std.Sat.CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨(a,b),ha,rfl⟩
  · simpa using hb

theorem baseClauses_hold (hW : LineRule p W) (c : Clause p)
    (hc : c∈cellChoices p ++ cellUnique p ++ lineChoices p ++ consistency p ++ badLinks p) : Holds (model hW) c := by
  simp only [List.mem_append] at hc
  rcases hc with (((h|h)|h)|h)|h
  · exact cellChoices_hold hW c h
  · exact cellUnique_hold hW c h
  · exact lineChoices_hold hW c h
  · exact consistency_hold hW c h
  · exact badLinks_hold hW c h

theorem exists_clean_seed (hW : LineRule p W) (hu : (formula p).Unsat) :
    ∃ h∈[2,4], ∃ r∈List.range (width p-4), ∃ q∈List.range (13-2*h),
      ∀ z∈seedClause p r q h, model hW z.1=false := by
  by_contra hn
  have hsat : (formula p).Sat (assignment (model hW)) := by
    apply formula_sat
    intro c hc
    simp only [clauses,List.mem_append] at hc
    rcases hc with hc|hc
    · exact baseClauses_hold hW c (by simpa only [List.mem_append] using hc)
    · simp only [seedFailures,List.mem_flatMap,List.mem_map] at hc
      obtain ⟨h,hh,r,hr,q,hq,rfl⟩ := hc
      have h : ¬∀ z∈seedClause p r q h, model hW z.1=false := by
        intro hz
        exact hn ⟨h,hh,r,hr,q,hq,hz⟩
      push_neg at h
      obtain ⟨z,hz,hv⟩ := h
      refine ⟨z,hz,?_⟩
      have hb : z.2=true := by
        simp only [seedClause,List.mem_map] at hz
        obtain ⟨a,_,rfl⟩ := hz
        rfl
      rw [hb]
      exact Bool.eq_true_of_not_eq_false hv
  exact Std.Sat.CNF.unsat_iff_not_sat.mp hu _ hsat
end
end TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
