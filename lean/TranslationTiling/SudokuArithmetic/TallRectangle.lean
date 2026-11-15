import TranslationTiling.SudokuArithmetic.WordAffineAlgebra
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Sudoku.ArithmeticRule
noncomputable section
attribute [local instance] Classical.propDecidable

private def lineBlockedOrigins (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d e : ℤ) :=
  (Finset.univ : Finset (Fin 4 × Fin 4)).biUnion fun o =>
    (((Finset.Ico (0 : ℤ) (N-3 : ℕ)).filter (fun x => bad d e (x+o.1.val))).image
      fun x => (x,d*(x+o.1.val)+e-o.2.val))

private theorem lineBlockedOrigins_card (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d e : ℤ)
    (hbad : ∀ i : Fin 4,
      ((Finset.Ico (0 : ℤ) (N-3 : ℕ)).filter (fun x => bad d e (x+i.val))).card ≤ 2) :
    (lineBlockedOrigins N bad d e).card ≤ 32 := by
  have h : (lineBlockedOrigins N bad d e).card ≤
      (Finset.univ : Finset (Fin 4 × Fin 4)).card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro o _
    exact Finset.card_image_le.trans (hbad o.1)
  simpa using h

private theorem mem_lineBlockedOrigins (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (x y d e : ℤ) (i j : Fin 4) (hx : x ∈ Finset.Ico (0 : ℤ) (N-3 : ℕ))
    (he : e=y+j.val-d*(x+i.val)) (hb : bad d e (x+i.val)) :
    (x,y) ∈ lineBlockedOrigins N bad d e := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,j),Finset.mem_univ _,Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hb⟩,?_⟩⟩
  exact Prod.ext rfl (by dsimp only; rw [he]; ring)

private def blockedAlong (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d : ℤ) (E : Finset ℤ) :=
  E.biUnion (lineBlockedOrigins N bad d)

private theorem blockedAlong_card (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d : ℤ) (E : Finset ℤ)
    (hbad : ∀ e, ∀ i : Fin 4,
      ((Finset.Ico (0 : ℤ) (N-3 : ℕ)).filter (fun x => bad d e (x+i.val))).card ≤ 2) :
    (blockedAlong N bad d E).card ≤ E.card*32 := by
  apply Finset.card_biUnion_le_card_mul
  intro e _
  exact lineBlockedOrigins_card N bad d e (hbad e)

/-- Search vertically as far as needed; only the horizontal width is restricted. -/
theorem exists_clean_four_rectangle (p : ℕ) (hp : 48 < p)
    (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d=-1 ∨ d=0 ∨ d=1) → ∀ i : Fin 4,
      ((Finset.Ico (0 : ℤ) (wordWidth p-3 : ℕ)).filter
        (fun x => bad d e (x+i.val))).card ≤ 2) :
    ∃ r q : ℤ, 0≤r ∧ r+3<(wordWidth p : ℕ) ∧
      0≤q ∧ q+3<(100*wordWidth p : ℕ) ∧
      ∀ i j : Fin 4, ∀ d : ℤ, (d=-1 ∨ d=0 ∨ d=1) →
        ¬bad d ((q+j.val)-d*(r+i.val)) (r+i.val) := by
  let N := wordWidth p
  let T := 100*N
  have hN : 100≤N := by dsimp [N,wordWidth]; omega
  let C := (Finset.Ico (0 : ℤ) (N-3 : ℕ)).product (Finset.Ico (0 : ℤ) (T-3 : ℕ))
  let B₀ := blockedAlong N bad (-1) (Finset.Ico 0 (T+N : ℕ))
  let B₁ := blockedAlong N bad 0 (Finset.Ico 0 (T : ℕ))
  let B₂ := blockedAlong N bad 1 (Finset.Ico (-(N:ℤ)) T)
  let B := B₀ ∪ B₁ ∪ B₂
  have h0 : B₀.card≤(T+N)*32 := by
    have h := blockedAlong_card N bad (-1) (Finset.Ico 0 (T+N : ℕ))
      (fun e i => hbad _ e (Or.inl rfl) i)
    simpa only [Int.card_Ico,sub_zero,Int.toNat_natCast] using h
  have h1 : B₁.card≤T*32 := by
    have h := blockedAlong_card N bad 0 (Finset.Ico 0 (T : ℕ))
      (fun e i => hbad _ e (Or.inr (Or.inl rfl)) i)
    simpa only [Int.card_Ico,sub_zero,Int.toNat_natCast] using h
  have h2 : B₂.card≤(T+N)*32 := by
    have h := blockedAlong_card N bad 1 (Finset.Ico (-(N:ℤ)) T)
      (fun e i => hbad _ e (Or.inr (Or.inr rfl)) i)
    have hc : (Finset.Ico (-(N:ℤ)) T).card=T+N := by rw [Int.card_Ico]; omega
    simpa only [hc] using h
  have hB : B.card≤32*(3*T+2*N) := by
    have h := Finset.card_union_le (B₀ ∪ B₁) B₂
    have h' := Finset.card_union_le B₀ B₁
    dsimp only [B]
    omega
  have hC : C.card=(N-3)*(T-3) := by
    have h := Finset.card_product (Finset.Ico (0 : ℤ) (N-3 : ℕ))
      (Finset.Ico (0 : ℤ) (T-3 : ℕ))
    simpa [C] using h
  have hlt : B.card<C.card := by
    rw [hC]
    apply hB.trans_lt
    have hn : N-3+3=N := Nat.sub_add_cancel (by omega)
    have ht : T-3+3=T := Nat.sub_add_cancel (by dsimp [T]; omega)
    dsimp [T] at *
    nlinarith
  obtain ⟨⟨r,q⟩,hc,hnb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hc
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  refine ⟨r,q,hr'.1,by omega,hq'.1,by change q+3<(T:ℕ); omega,?_⟩
  intro i j d hd hb
  have hi := i.isLt
  have hj := j.isLt
  let e := (q+j.val)-d*(r+i.val)
  have hm (E : Finset ℤ) (he : e∈E) : (r,q)∈blockedAlong N bad d E := by
    apply Finset.mem_biUnion.mpr
    exact ⟨e,he,mem_lineBlockedOrigins N bad r q d e i j hr rfl hb⟩
  apply hnb
  rcases hd with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hm _ (by
      dsimp [e]; simp only [Finset.mem_Ico,neg_one_mul]; constructor <;> omega)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hm _ (by
      dsimp [e]; simp only [Finset.mem_Ico,zero_mul,sub_zero]; constructor <;> omega)))
  · exact Finset.mem_union_right _ (hm _ (by
      dsimp [e]; simp only [Finset.mem_Ico,one_mul]; constructor <;> omega))

end
end TranslationTiling.Sudoku.ArithmeticRule
