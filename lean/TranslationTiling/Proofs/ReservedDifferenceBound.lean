import TranslationTiling.Proofs.TightDifferenceBound

namespace TranslationTiling.Stacking

open scoped Classical BigOperators
noncomputable section

private theorem pairs_avoiding {q : ℕ} [Fact q.Prime]
    (hodd : q=2*(q/2)+1) (D : Finset (ZMod q)) (d : ZMod q) (hd : d≠0)
    (k : ℕ) (hk : k+D.card≤q/2) :
    ∃ f : (Fin k × Fin 2) ↪ {x : ZMod q // x ∉ D},
      ∀ j, (f (j,1)).val-(f (j,0)).val=d := by
  let f := primeDifferencePairs q (q/2) hodd d hd
  let good (j : Fin (q/2)) := ∀ t : Fin 2, f (j,t) ∉ D
  let bad := {j : Fin (q/2) // ¬ good j}
  have hw (j : bad) : ∃ t : Fin 2, f (j.val,t) ∈ D := by
    have h := j.property
    change ¬ ∀ t : Fin 2, f (j.val,t) ∉ D at h
    push_neg at h
    exact h
  let g (j : bad) : {x // x ∈ D} := ⟨_,(hw j).choose_spec⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact Subtype.ext (congrArg Prod.fst (f.injective (congrArg Subtype.val hij)))
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_fin] at hc
  have hcard : k≤Fintype.card {j // good j} := by
    have hsub := Fintype.card_subtype_le good
    simp only [Fintype.card_fin] at hsub
    omega
  let e := (Fintype.equivFin {j // good j}).symm
  let i (j : Fin k) := e (Fin.castLE hcard j)
  have hi : Function.Injective i := e.injective.comp (Fin.castLE_injective hcard)
  refine ⟨⟨fun p => ⟨f ((i p.1).val,p.2),(i p.1).property p.2⟩,?_⟩,?_⟩
  · intro x y h
    have he := f.injective (congrArg Subtype.val h)
    have hs : x.2=y.2 := congrArg (fun z : Fin (q/2) × Fin 2 => z.2) he
    exact Prod.ext (hi (Subtype.ext (congrArg Prod.fst he))) hs
  · intro j
    exact primeDifferencePairs_step q _ hodd d hd _

/-- A prescribed set of layers may all be assigned to one color. -/
theorem partition_reserved (s X P q : ℕ) (hs : 0<s) (hsX : s≤X)
    (hP : P+3≤2*X^2) (hL : 5≤differenceLog X) (hq : q.Prime)
    (hlo : 20*X^2*differenceLog X+P+3<q)
    (hhi : q≤2*(20*X^2*differenceLog X+P+3))
    (D : Finset (ZMod q)) (hD : D.card≤(q+2)/3) (seed : Fin s) :
    ∃ E : Fin s → Finset (ZMod q), IsColorPartition E ∧ HasFullDifferences E ∧ D⊆E seed := by
  letI : Fact q.Prime := ⟨hq⟩
  let free := {x : ZMod q // x ∉ D}
  let extend (f : free → Fin s) (x : ZMod q) : Fin s := if h : x∈D then seed else f ⟨x,h⟩
  suffices h : ∃ f, ∀ ν d, d≠0 → ∃ x y, extend f x=ν ∧ extend f y=ν ∧ x-y=d by
    obtain ⟨f,hf⟩ := h
    let E (ν : Fin s) := (Finset.univ : Finset (ZMod q)).filter (fun x => extend f x=ν)
    refine ⟨E,?_,?_,fun x hx => by simp [E,extend,hx]⟩
    · intro x
      exact ⟨extend f x,by simp [E],fun ν hν => by simpa [E] using (Finset.mem_filter.mp hν).2.symm⟩
    · intro ν d
      by_cases hd : d=0
      · obtain ⟨x,y,hx,hy,_⟩ := hf ν 1 (by have : 1<q := hq.one_lt; exact one_ne_zero)
        exact ⟨x,by simp [E,hx],x,by simp [E,hx],by simp [hd]⟩
      · obtain ⟨x,y,hx,hy,he⟩ := hf ν d hd
        exact ⟨x,by simp [E,hx],y,by simp [E,hy],he⟩
  by_cases hs1 : s=1
  · subst s
    refine ⟨fun _ => seed,fun ν d _ => ⟨d,0,?_,?_,sub_zero _⟩⟩ <;>
      exact Subsingleton.elim (α:=Fin 1) _ _
  let L := differenceLog X
  let k := 3*X^2*L
  have hq2 : 2<q := by omega
  have hodd : q=2*(q/2)+1 := by have := hq.eq_two_or_odd.resolve_left (by omega); omega
  have hk : k+D.card≤q/2 := by
    have hX : 1≤X := by omega
    have hXL : 5≤X^2*L := by nlinarith only [hX,hL,show 1≤X^2 by nlinarith]
    have hl : 20*(X^2*L)+P+3<q := by linarith only [hlo]
    dsimp [k]
    have h1 : 6*(3*X^2*L)+7≤q := by linarith
    omega
  have hlabels : s*(q-1)<16^L := by
    apply bad_label_bound _ _ X L (40*L+4) hsX (by omega)
    · exact Nat.lt_pow_succ_log_self (by decide) _
    · change _≤(40*differenceLog X+4)*X^2
      calc
        q-1 ≤ q := Nat.sub_le _ _
        _ ≤ 2*(20*X^2*differenceLog X+P+3) := hhi
        _ = 40*differenceLog X*X^2+2*(P+3) := by ring
        _ ≤ 40*differenceLog X*X^2+2*(2*X^2) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 hP) _
        _ = (40*differenceLog X+4)*X^2 := by ring
    · omega
    · have h : ∀ l≥5, 40*l+4≤8*2^l := by
        intro l hl
        induction l,hl using Nat.le_induction with
        | base => decide
        | succ l hl ih => rw [pow_succ]; omega
      exact h L hL
  have hbad := tight_bad_bound_of_labels s k (q-1) X L (by omega) hsX (le_refl _) hlabels
  let bad (p : Fin s × ZMod q) : Finset (free → Fin s) :=
    Finset.univ.filter fun f => BadDifference (extend f) p.1 p.2
  let all := (badDifferenceLabels q s).biUnion bad
  have hfree : 2*k≤Fintype.card free := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, ZMod.card]
    omega
  have hcard (p : Fin s × ZMod q) (hp : p ∈ badDifferenceLabels q s) :
      (bad p).card≤(s^2-1)^k*s^(Fintype.card free-2*k) := by
    have hd := (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1
    obtain ⟨pair,hpair⟩ := pairs_avoiding hodd D p.2 hd k hk
    let G (_ : Fin k) : Finset (Fin s × Fin s) := {(p.1,p.1)}
    refine (Finset.card_le_card (show bad p⊆allBadAssignments pair G from ?_)).trans ?_
    · intro f hf
      have hf' := (Finset.mem_filter.mp hf).2
      apply (mem_allBadAssignments pair G f).mpr
      intro j hj
      have he : (f (pair (j,0)),f (pair (j,1)))=(p.1,p.1) := Finset.mem_singleton.mp hj
      exact hf' ⟨(pair (j,1)).val,(pair (j,0)).val,
        by simpa [extend,(pair (j,1)).property] using congrArg Prod.snd he,
        by simpa [extend,(pair (j,0)).property] using congrArg Prod.fst he, hpair j⟩
    · simpa only [Fintype.card_fin] using allBadAssignments_card_le pair G 1 (by simp [G])
  have hall : all.card<(Finset.univ : Finset (free → Fin s)).card := by
    calc
      _ ≤ ∑ p ∈ badDifferenceLabels q s, (bad p).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ badDifferenceLabels q s, (s^2-1)^k*s^(Fintype.card free-2*k) :=
        Finset.sum_le_sum hcard
      _ = (s*(q-1)*(s^2-1)^k)*s^(Fintype.card free-2*k) := by simp [mul_assoc]
      _ < s^(2*k)*s^(Fintype.card free-2*k) := Nat.mul_lt_mul_of_pos_right hbad (by positivity)
      _ = _ := by rw [←pow_add,Nat.add_sub_of_le hfree]; simp
  obtain ⟨f,_,hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hall
  refine ⟨f,fun ν d hd => ?_⟩
  by_contra h
  exact hf (Finset.mem_biUnion.mpr
    ⟨(ν,d),Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_erase.mpr ⟨hd,Finset.mem_univ _⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

end
end TranslationTiling.Stacking
