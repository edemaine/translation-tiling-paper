import TranslationTiling.Proofs.ReservedDifferenceBound
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TranslationTiling.Stacking

open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

private def avoidsEdges {s : ℕ} (c : Fin 4 → Fin s) (ν : Fin s)
    (E : Finset (Fin 3)) : Prop :=
  ∀ j ∈ E, ¬ (c j.castSucc = ν ∧ c j.succ = ν)

/-- A block of four vertices has at least one disjoint family of successful
colorings for each retained edge. -/
private theorem block_bad_add_le {s : ℕ} (ν : Fin s) (E : Finset (Fin 3)) :
    Fintype.card {c : Fin 4 → Fin s // avoidsEdges c ν E} + E.card*s*(s-1) ≤ s^4 := by
  let C := {c : Fin s // c ≠ ν}
  let q (j : Fin 3) (z : Fin s × C) : Fin 4 → Fin s :=
    ![![ν,ν,z.2.val,z.1], ![z.1,ν,ν,z.2.val], ![z.2.val,z.1,ν,ν]] j
  have good (j : Fin 3) (z : Fin s × C) :
      q j z j.castSucc = ν ∧ q j z j.succ = ν := by
    fin_cases j <;> exact ⟨rfl,rfl⟩
  have hq : Function.Injective (fun p : Fin 3 × (Fin s × C) => q p.1 p.2) := by
    rintro ⟨i,x,y⟩ ⟨j,z,t⟩ h
    fin_cases i <;> fin_cases j
    · exact Prod.ext rfl (Prod.ext (congrFun h 3) (Subtype.ext (congrFun h 2)))
    · exact (y.property (congrFun h 2)).elim
    · exact (y.property (congrFun h 2)).elim
    · exact (t.property (congrFun h 2).symm).elim
    · exact Prod.ext rfl (Prod.ext (congrFun h 0) (Subtype.ext (congrFun h 3)))
    · exact (y.property (congrFun h 3)).elim
    · exact (t.property (congrFun h 2).symm).elim
    · exact (t.property (congrFun h 3).symm).elim
    · exact Prod.ext rfl (Prod.ext (congrFun h 1) (Subtype.ext (congrFun h 0)))
  let f (p : ↥E × (Fin s × C)) : {c : Fin 4 → Fin s // ¬ avoidsEdges c ν E} :=
    ⟨q p.1 p.2,fun h => h p.1 p.1.property (good p.1 p.2)⟩
  have hf : Function.Injective f := by
    intro i j h
    have he : (i.1.val,i.2) = (j.1.val,j.2) := hq (show q i.1.val i.2 = q j.1.val j.2 from congrArg Subtype.val h)
    have hv₁ := congrArg (fun z : Fin 3 × (Fin s × C) => z.1) he
    have hv₂ := congrArg (fun z : Fin 3 × (Fin s × C) => z.2) he
    exact Prod.ext (Subtype.ext hv₁) hv₂
  have hc : Fintype.card C = s-1 := by
    dsimp [C]
    rw [Fintype.card_subtype_compl]
    simp
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_fin,hc, Fintype.card_coe,
    Fintype.card_subtype_compl,Fintype.card_fun,Fintype.card_fin] at h
  simp only [Fintype.card_fin] at h
  rw [mul_assoc]
  have hbound := Fintype.card_subtype_le (fun c : Fin 4 → Fin s => avoidsEdges c ν E)
  simp only [Fintype.card_fun,Fintype.card_fin] at hbound
  omega

private theorem bad_block_fraction {s : ℕ} (hs : 2 ≤ s) (ν : Fin s)
    (E : Finset (Fin 3)) :
    (Fintype.card {c : Fin 4 → Fin s // avoidsEdges c ν E} : ℝ) ≤
      (s:ℝ)^4 * Real.exp (-(E.card:ℝ)*(((s:ℝ)-1)/(s:ℝ)^3)) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hc := block_bad_add_le ν E
  have hcast : (Fintype.card {c : Fin 4 → Fin s // avoidsEdges c ν E} : ℝ) +
      (E.card:ℝ)*s*((s:ℝ)-1) ≤ (s:ℝ)^4 := by
    have he : ((s-1:ℕ):ℝ) = (s:ℝ)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub (R:=ℝ) (show 1 ≤ s by omega))
    rw [←he]
    exact_mod_cast hc
  let p := (E.card:ℝ)*(((s:ℝ)-1)/(s:ℝ)^3)
  have hp : (s:ℝ)^4*p = (E.card:ℝ)*s*((s:ℝ)-1) := by
    dsimp [p]
    field_simp
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg p)
    (show 0 ≤ (s:ℝ)^4 by positivity)
  rw [neg_mul]
  change _ ≤ (s:ℝ)^4 * Real.exp (-p)
  rw [mul_sub,mul_one,hp] at h
  linarith

private theorem blockCover {q : ℕ} (a i : ℕ) (hi : a ≤ i)
    (hj : i+1 < a+4*((q-a)/4)) (hr : (i-a)%4 ≠ 3) :
    ∃ j : Fin ((q-a)/4), ∃ t : Fin 3, a+4*j.val+t.val=i := by
  have hmod := Nat.mod_add_div (i-a) 4
  have ht := Nat.mod_lt (i-a) (by decide : 0<4)
  refine ⟨⟨(i-a)/4,by omega⟩,⟨(i-a)%4,by omega⟩,?_⟩
  dsimp
  omega

private theorem manyBlocks {q : ℕ} [Fact q.Prime] (D : Finset (ZMod q))
    (hD : D.card≤(q+2)/3) (d : ZMod q) (hd : d≠0) :
    ∃ (B : ℕ) (f : (Fin B × Fin 4) ↪ ZMod q) (E : Fin B → Finset (Fin 3)),
      (∀ j t, t ∈ E j → f (j,t.castSucc) ∉ D ∧ f (j,t.succ) ∉ D ∧
        f (j,t.succ) - f (j,t.castSucc) = d) ∧
      q ≤ 4*(∑ j, (E j).card)+40 := by
  by_cases hq : 3 ≤ q
  swap
  · refine ⟨0,⟨fun p => Fin.elim0 p.1,fun p => Fin.elim0 p.1⟩,fun j => Fin.elim0 j,?_,?_⟩
    · intro j; exact Fin.elim0 j
    · omega
  let v (i : ℕ) : ZMod q := i*d
  have hv {i j : ℕ} (hi : i<q) (hj : j<q) (h : v i=v j) : i=j := by
    have he : (i : ZMod q) = j := mul_right_cancel₀ hd h
    simpa only [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] using congrArg ZMod.val he
  let R := Finset.range (q-1)
  let bad₀ := R.filter (fun i => v i ∈ D)
  let bad₁ := R.filter (fun i => v (i+1) ∈ D)
  let G := R \ (bad₀ ∪ bad₁)
  have hbad₀ : bad₀.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn v
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj he
      have h₁ := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have h₂ := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      exact hv (by omega) (by omega) he
  have hbad₁ : bad₁.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun i => v (i+1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj he
      have h₁ := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have h₂ := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have := hv (by omega : i+1<q) (by omega : j+1<q) he
      omega
  have hG : q-1 ≤ G.card+2*D.card := by
    have hs : bad₀ ∪ bad₁ ⊆ R := Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..)
    have h₁ := Finset.card_sdiff_add_card_eq_card hs
    have h₂ := Finset.card_union_le bad₀ bad₁
    rw [Finset.card_range] at h₁
    change G.card + _ = _ at h₁
    omega
  let residue (i : ℕ) : Fin 4 := ⟨i%4,Nat.mod_lt _ (by decide)⟩
  let F (r : Fin 4) := G.filter (fun i => residue i=r)
  have hsum : ∑ r, (F r).card = G.card :=
    Finset.sum_card_fiberwise_eq_card_filter _ _ _ |>.trans (by simp)
  have hmin : ∃ r : Fin 4, 4*(F r).card≤G.card := by
    by_contra! h
    have hlt : (∑ _r : Fin 4, G.card) < ∑ r, 4*(F r).card :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => h r)
    rw [←Finset.mul_sum,hsum] at hlt
    simp at hlt
  obtain ⟨r,hr⟩ := hmin
  let a := (r.val+1)%4
  let B := (q-a)/4
  have ha : a<4 := Nat.mod_lt _ (by decide)
  have hab : a+4*B≤q ∧ q<a+4*B+4 := by
    have h₁ := Nat.mod_add_div (q-a) 4
    have h₂ := Nat.mod_lt (q-a) (by decide : 0<4)
    dsimp [B]
    omega
  let index (p : Fin B × Fin 4) := a+4*p.1.val+p.2.val
  have hi (p : Fin B × Fin 4) : index p<q := by
    have := p.1.isLt
    have := p.2.isLt
    dsimp [index]
    omega
  let f : (Fin B × Fin 4) ↪ ZMod q := ⟨fun p => v (index p),by
    intro p p' h
    have h' := hv (hi p) (hi p') h
    have h₁ := p.2.isLt
    have h₂ := p'.2.isLt
    dsimp [index] at h'
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩
  let E (j : Fin B) := Finset.univ.filter (fun t : Fin 3 => a+4*j.val+t.val∈G)
  refine ⟨B,f,E,?_,?_⟩
  · intro j t ht
    have h := Finset.mem_sdiff.mp ((Finset.mem_filter.mp ht).2)
    have he₀ : v (a+4*j.val+t.val)∉D := fun he => h.2 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h.1,he⟩))
    have he₁ : v (a+4*j.val+t.val+1)∉D := fun he => h.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h.1,he⟩))
    refine ⟨he₀,he₁,?_⟩
    change v (a+4*j.val+t.val+1)-v (a+4*j.val+t.val)=d
    simp only [v,Nat.cast_add,Nat.cast_one]
    ring
  let L := Finset.range a
  let U := (Finset.range (q-1)).filter (fun i => a+4*B ≤ i+1)
  let J := (Finset.univ : Finset (Fin B)).sigma E
  let I (p : Σ _ : Fin B, Fin 3) := a+4*p.1.val+p.2.val
  have hU : U.card ≤ 3 := by
    apply Finset.card_le_card_of_injOn (fun i => i+1-(a+4*B)) (t := Finset.range 3)
    · intro i hi
      obtain ⟨hm,hb⟩ := Finset.mem_filter.mp hi
      have hq' := Finset.mem_range.mp hm
      change i+1-(a+4*B) ∈ Finset.range 3
      rw [Finset.mem_range]
      omega
    · intro i hi j hj he
      have h₁ := (Finset.mem_filter.mp hi).2
      have h₂ := (Finset.mem_filter.mp hj).2
      dsimp at he
      omega
  have hG' : G ⊆ F r ∪ L ∪ U ∪ J.image I := by
    intro i hg
    by_cases hres : residue i=r
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,hres⟩)))
    by_cases hlow : i<a
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_range.mpr hlow)))
    by_cases hhigh : a+4*B ≤ i+1
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hg).1,hhigh⟩))
    have hne : (i-a)%4 ≠ 3 := by
      intro h
      apply hres
      apply Fin.ext
      dsimp [residue,a] at *
      have := r.isLt
      omega
    obtain ⟨j,t,he⟩ := blockCover (q:=q) a i (by omega) (by omega) hne
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨⟨j,t⟩,Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,he⟩
    rwa [he]
  have hJ := Finset.card_sigma (s := (Finset.univ : Finset (Fin B))) (t := E)
  have hcnt := Finset.card_le_card hG'
  have h₁ := Finset.card_union_le (F r ∪ L ∪ U) (J.image I)
  have h₂ := Finset.card_union_le (F r ∪ L) U
  have h₃ := Finset.card_union_le (F r) L
  have h₄ := Finset.card_image_le (s := J) (f := I)
  have hL : L.card=a := Finset.card_range _
  change J.card = _ at hJ
  omega

private theorem badColorings_le {q s B : ℕ} [NeZero q] (hs : 2 ≤ s) (ν : Fin s)
    (f : (Fin B × Fin 4) ↪ ZMod q) (E : Fin B → Finset (Fin 3)) :
    (Fintype.card {c : ZMod q → Fin s // ∀ j, avoidsEdges (fun t => c (f (j,t))) ν (E j)} : ℝ)
      ≤ (s:ℝ)^q * Real.exp (-(∑ j, ((E j).card:ℝ))*(((s:ℝ)-1)/(s:ℝ)^3)) := by
  let Outside := {x : ZMod q // x ∉ Set.range f}
  let A (j : Fin B) := {c : Fin 4 → Fin s // avoidsEdges c ν (E j)}
  let extract (c : {c : ZMod q → Fin s // ∀ j, avoidsEdges (fun t => c (f (j,t))) ν (E j)}) :
      (∀ j, A j) × (Outside → Fin s) :=
    (fun j => ⟨fun t => c.val (f (j,t)), c.property j⟩, fun x => c.val x.val)
  have hinj : Function.Injective extract := by
    intro c c' he
    apply Subtype.ext
    funext x
    by_cases h : x ∈ Set.range f
    · obtain ⟨⟨j,t⟩,rfl⟩ := h
      exact congrArg (fun z : (∀ j, A j) × (Outside → Fin s) => (z.1 j).val t) he
    · exact congrArg (fun z : (∀ j, A j) × (Outside → Fin s) => z.2 ⟨x,h⟩) he
  let decomp : ((Fin B × Fin 4) ⊕ Outside) ≃ ZMod q :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range f))
  have hsplit : B*4+Fintype.card Outside = q := by
    simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,ZMod.card] using
      Fintype.card_congr decomp
  have hcard := Fintype.card_le_of_injective extract hinj
  rw [Fintype.card_prod,Fintype.card_pi,Fintype.card_fun,Fintype.card_fin] at hcard
  have hprod := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin B)))
    (fun _ _ => Nat.cast_nonneg (α := ℝ) _)
    (fun j _ => bad_block_fraction hs ν (E j))
  have hp : (∏ j : Fin B, (s:ℝ)^4 * Real.exp (-((E j).card:ℝ)*(((s:ℝ)-1)/(s:ℝ)^3))) =
      (s:ℝ)^(B*4) * Real.exp (-(∑ j, ((E j).card:ℝ))*(((s:ℝ)-1)/(s:ℝ)^3)) := by
    rw [Finset.prod_mul_distrib,←Real.exp_sum,←Finset.sum_mul,Finset.sum_neg_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,mul_comm 4 B]
  rw [hp] at hprod
  calc
    _ ≤ (∏ j, (Fintype.card (A j):ℝ)) * (s:ℝ)^(Fintype.card Outside) := by exact_mod_cast hcard
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hprod (show (0:ℝ) ≤ (s:ℝ)^Fintype.card Outside by positivity)
      rwa [mul_right_comm,←pow_add,hsplit] at h

private theorem labelCount_lt_exp {s X P q : ℕ} (hsX : s ≤ X) (hX : 2313≤X)
    (hP : P+3≤2*X^2) (hhi : q≤2*(10*X^2*differenceLog X+P+3)) :
    ((s*(q-1):ℕ):ℝ) < Real.exp ((249:ℝ)/100 * differenceLog X) := by
  let L := differenceLog X
  have hL : 13≤L := by
    have h : 12≤Nat.log 2 (2*X) := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega)).mpr (by norm_num; omega)
    exact Nat.succ_le_succ h
  have hb : ∀ l≥13, (20*l+4)^2≤2^(l+4) := by
    intro l hl
    induction l,hl using Nat.le_induction with
    | base => decide
    | succ l hl ih =>
        rw [show l+1+4=l+4+1 by omega,pow_succ]
        have h : (20*(l+1)+4)^2≤2*(20*l+4)^2 := by
          nlinarith only [hl, Nat.mul_le_mul_right l hl]
        exact h.trans (by omega)
  have hX' : X≤2^(L-1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) (2*X)
    rw [Nat.pow_succ] at h
    simpa [L,differenceLog] using (show X≤2^Nat.log 2 (2*X) by omega)
  have hq : q ≤ (20*L+4)*X^2 := by
    calc
      q ≤ 2*(10*X^2*L+P+3) := hhi
      _ = 20*L*X^2+2*(P+3) := by ring
      _ ≤ 20*L*X^2+2*(2*X^2) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hP) _
      _ = _ := by ring
  have hs : s*(q-1) ≤ (20*L+4)*X^3 := by
    calc
      _ ≤ X*((20*L+4)*X^2) := Nat.mul_le_mul hsX ((Nat.sub_le ..).trans hq)
      _ = _ := by ring
  have hpow : (s*(q-1))^2 ≤ 2^(7*L) := by
    calc
      _ ≤ ((20*L+4)*X^3)^2 := Nat.pow_le_pow_left hs _
      _ = (20*L+4)^2 * X^6 := by ring
      _ ≤ 2^(L+4) * (2^(L-1))^6 := Nat.mul_le_mul (hb L hL) (Nat.pow_le_pow_left hX' _)
      _ ≤ 2^(7*L) := by
        rw [←pow_mul,←pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  have hc : (((s*(q-1):ℕ):ℝ)^2) ≤ 2^(7*L) := by exact_mod_cast hpow
  have ht : (2:ℝ)^(7*L) < (Real.exp ((249:ℝ)/100*L))^2 := by
    calc
      _ = Real.exp ((7*L:ℕ)*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ < _ := by
        rw [←Real.exp_nat_mul]
        apply Real.exp_lt_exp.mpr
        push_cast
        have hh : Real.log 2 < (7:ℝ)/10 := Real.log_two_lt_d9.trans (by norm_num)
        have hl : (0:ℝ)<L := by exact_mod_cast (by omega : 0<L)
        nlinarith only [mul_lt_mul_of_pos_right hh hl,hl]
  exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 2≠0)).mp (hc.trans_lt ht)

private theorem blockDecay {s X P q e : ℕ} (hs : 2≤s) (hsX : s≤X) (hX : 2313≤X)
    (hlo : 10*X^2*differenceLog X+P+3<q) (he : q≤4*e+40) :
    (249:ℝ)/100*differenceLog X ≤ (e:ℝ)*(((s:ℝ)-1)/(s:ℝ)^3) := by
  let x := (X:ℝ)
  let y := (s:ℝ)
  let L := (differenceLog X:ℝ)
  have hx : (2313:ℝ)≤x := by dsimp [x]; exact_mod_cast hX
  have hy : (2:ℝ)≤y := by dsimp [y]; exact_mod_cast hs
  have hyx : y≤x := by dsimp [x,y]; exact_mod_cast hsX
  have hL : 1≤L := by dsimp [L]; exact_mod_cast (by unfold differenceLog; omega : 1≤differenceLog X)
  have hlarge : 10000≤x^2*L := by
    have h₁ : (100:ℝ)^2≤x^2 := by gcongr; linarith
    have h₂ : x^2*1≤x^2*L := mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have he' : 10*x^2*L≤4*(e:ℝ)+40 := by
    dsimp [x,L]
    exact_mod_cast (show 10*X^2*differenceLog X≤4*e+40 from by omega)
  have hbase : (2499:ℝ)/1000*x^2*L≤e := by nlinarith only [he',hlarge]
  have hratio : ((x-1)/x^3)≤(y-1)/y^3 := by
    apply (div_le_div_iff₀ (by positivity : 0<x^3) (by positivity : 0<y^3)).mpr
    have hp : 0≤(y-1)*x^2+(y*(y-1))*x-y^2 := by
      have h₁ : y^2 ≤ x^2 := by gcongr
      have h₂ := mul_le_mul_of_nonneg_right (show (1:ℝ)≤y-1 by linarith) (sq_nonneg x)
      have h₃ : 0≤(y*(y-1))*x := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr hyx) hp]
  have hx' : (999:ℝ)/1000*x≤x-1 := by linarith
  calc
    _ ≤ ((2499:ℝ)/1000*x^2*L)*(x-1)/x^3 := by
      apply (le_div_iff₀ (by positivity : 0<x^3)).mpr
      have hc : 0≤(x-1-(999:ℝ)/1000*x)*(x^2*L) :=
        mul_nonneg (sub_nonneg.mpr hx') (by positivity)
      have hd : 0≤x^3*L := by positivity
      nlinarith only [hc,hd]
    _ = ((2499:ℝ)/1000*x^2*L)*((x-1)/x^3) := by ring
    _ ≤ (e:ℝ)*((y-1)/y^3) :=
      mul_le_mul hbase hratio (div_nonneg (by linarith) (by positivity)) (by positivity)

/-- Use disjoint four-vertex blocks from a cyclic progression of a given
difference. The reserved vertices may all be assigned to the seed color. -/
theorem partition_reserved_blocks (s X P q : ℕ) (hs : 0<s) (hsX : s≤X)
    (hX : 2313≤X) (hP : P+3≤2*X^2) (hq : q.Prime)
    (hlo : 10*X^2*differenceLog X+P+3<q)
    (hhi : q≤2*(10*X^2*differenceLog X+P+3))
    (D : Finset (ZMod q)) (hD : D.card≤(q+2)/3) (seed : Fin s) :
    ∃ E : Fin s → Finset (ZMod q), IsColorPartition E ∧ HasFullDifferences E ∧ D⊆E seed := by
  let _ : Fact q.Prime := ⟨hq⟩
  let extend (f : ZMod q → Fin s) (x : ZMod q) : Fin s := if x∈D then seed else f x
  suffices h : ∃ f, ∀ ν d, d≠0 → ∃ x y, extend f x=ν ∧ extend f y=ν ∧ x-y=d by
    obtain ⟨f,hf⟩ := h
    let E (ν : Fin s) := (Finset.univ : Finset (ZMod q)).filter (fun x => extend f x=ν)
    refine ⟨E,?_,?_,fun x hx => by simp [E,extend,hx]⟩
    · intro x
      exact ⟨extend f x,by simp [E],fun ν hν => by simpa [E] using (Finset.mem_filter.mp hν).2.symm⟩
    · intro ν d
      by_cases hd : d=0
      · obtain ⟨x,y,hx,hy,_⟩ := hf ν 1 one_ne_zero
        exact ⟨x,by simp [E,hx],x,by simp [E,hx],by simp [hd]⟩
      · obtain ⟨x,y,hx,hy,he⟩ := hf ν d hd
        exact ⟨x,by simp [E,hx],y,by simp [E,hy],he⟩
  by_cases hs1 : s=1
  · subst s
    refine ⟨fun _ => seed,fun ν d _ => ⟨d,0,?_,?_,sub_zero _⟩⟩ <;>
      exact Subsingleton.elim (α:=Fin 1) _ _
  let bad (p : Fin s × ZMod q) : Finset (ZMod q → Fin s) :=
    Finset.univ.filter fun f => BadDifference (extend f) p.1 p.2
  let all := (badDifferenceLabels q s).biUnion bad
  let u := (249:ℝ)/100 * differenceLog X
  have hbound (p : Fin s × ZMod q) (hp : p ∈ badDifferenceLabels q s) :
      ((bad p).card:ℝ) ≤ (s:ℝ)^q * Real.exp (-u) := by
    have hd := (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1
    obtain ⟨B,f,E,hE,hB⟩ := manyBlocks D hD p.2 hd
    let good := {c : ZMod q → Fin s // ∀ j, avoidsEdges (fun t => c (f (j,t))) p.1 (E j)}
    let res (c : ↥(bad p)) : good := ⟨c.val,by
      intro j t ht h
      obtain ⟨h₀,h₁,he⟩ := hE j t ht
      exact (Finset.mem_filter.mp c.property).2 ⟨f (j,t.succ),f (j,t.castSucc),
        by simpa [extend,h₁] using h.2,by simpa [extend,h₀] using h.1,he⟩⟩
    have hc : (bad p).card ≤ Fintype.card good := by
      rw [←Fintype.card_coe]
      exact Fintype.card_le_of_injective res (fun c c' h => Subtype.ext (congrArg (fun x : good => x.val) h))
    refine (show ((bad p).card:ℝ) ≤ Fintype.card good by exact_mod_cast hc).trans
      ((badColorings_le (by omega) p.1 f E).trans ?_)
    have he := blockDecay (by omega : 2≤s) hsX hX hlo hB
    push_cast at he
    have hh := Real.exp_le_exp.mpr (neg_le_neg he)
    rw [←neg_mul] at hh
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hlabel : (((badDifferenceLabels q s).card:ℕ):ℝ) < Real.exp u := by
    simpa only [badDifferenceLabels_card] using labelCount_lt_exp hsX hX hP hhi
  have hall : all.card<(Finset.univ : Finset (ZMod q → Fin s)).card := by
    have hc : (all.card:ℝ) ≤ ∑ p ∈ badDifferenceLabels q s, ((bad p).card:ℝ) := by
      exact_mod_cast (show all.card ≤ ∑ p ∈ badDifferenceLabels q s, (bad p).card from Finset.card_biUnion_le)
    have hm : (all.card:ℝ) ≤ ((badDifferenceLabels q s).card:ℝ)*((s:ℝ)^q*Real.exp (-u)) := by
      exact hc.trans (by simpa [nsmul_eq_mul] using Finset.sum_le_sum hbound)
    have hh := mul_lt_mul_of_pos_right hlabel (show 0<(s:ℝ)^q*Real.exp (-u) by positivity)
    have cancel : Real.exp u * ((s:ℝ)^q * Real.exp (-u)) = (s:ℝ)^q := by
      rw [mul_left_comm,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
    rw [cancel] at hh
    have hlt : (all.card:ℝ)<(s:ℝ)^q := hm.trans_lt hh
    rw [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card]
    exact_mod_cast hlt
  obtain ⟨f,_,hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hall
  refine ⟨f,fun ν d hd => ?_⟩
  by_contra h
  exact hf (Finset.mem_biUnion.mpr
    ⟨(ν,d),Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_erase.mpr ⟨hd,Finset.mem_univ _⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

end
end TranslationTiling.Stacking
