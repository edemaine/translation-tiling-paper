/-
Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Copyright and license: see third_party/openai-math.LICENSE (Apache-2.0).
-/
import TranslationTiling.SudokuArithmetic.WordRule
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TranslationTiling.Sudoku

namespace ArithmeticRule

noncomputable section

attribute [local instance] Classical.propDecidable

private def exceptionalAlong (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d : ℤ) (E : Finset ℤ) :=
  E.biUnion fun e => ((Finset.Ico (0:ℤ) N).filter (bad d e)).image fun n => (n,d*n+e)

def wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) : Finset (ℤ × ℤ) :=
  exceptionalAlong N bad (-1) (Finset.Ico 0 (2*(N:ℤ))) ∪
  exceptionalAlong N bad 0 (Finset.Ico 0 (N:ℤ)) ∪
  exceptionalAlong N bad 1 (Finset.Ico (-(N:ℤ)) N)

private theorem card_exceptionalAlong (N k : ℕ) (bad : ℤ → ℤ → ℤ → Prop) (d : ℤ) (E : Finset ℤ)
    (h : ∀ e, ((Finset.Ico (0:ℤ) N).filter (bad d e)).card≤k) :
    (exceptionalAlong N bad d E).card≤E.card*k := by
  apply Finset.card_biUnion_le_card_mul
  intro e _
  exact Finset.card_image_le.trans (h e)

theorem card_wordExceptionalCells_le (N k : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d=-1 ∨ d=0 ∨ d=1) →
      ((Finset.Ico (0:ℤ) N).filter (bad d e)).card≤k) :
    (wordExceptionalCells N bad).card≤5*N*k := by
  have h0 := card_exceptionalAlong N k bad (-1) (Finset.Ico 0 (2*(N:ℤ))) (fun e => hbad _ e (Or.inl rfl))
  have h1 := card_exceptionalAlong N k bad 0 (Finset.Ico 0 (N:ℤ)) (fun e => hbad _ e (Or.inr (Or.inl rfl)))
  have h2 := card_exceptionalAlong N k bad 1 (Finset.Ico (-(N:ℤ)) N) (fun e => hbad _ e (Or.inr (Or.inr rfl)))
  simp only [Int.card_Ico,sub_zero,Int.toNat_natCast] at h0 h1
  have ht : (2*(N:ℤ)).toNat=2*N := by omega
  rw [ht] at h0
  have hc : (Finset.Ico (-(N:ℤ)) N).card=2*N := by rw [Int.card_Ico]; omega
  rw [hc] at h2
  have hu := Finset.card_union_le (exceptionalAlong N bad (-1) (Finset.Ico 0 (2*(N:ℤ))) ∪
    exceptionalAlong N bad 0 (Finset.Ico 0 (N:ℤ))) (exceptionalAlong N bad 1 (Finset.Ico (-(N:ℤ)) N))
  have hv := Finset.card_union_le (exceptionalAlong N bad (-1) (Finset.Ico 0 (2*(N:ℤ))))
    (exceptionalAlong N bad 0 (Finset.Ico 0 (N:ℤ)))
  change _≤5*N*k
  unfold wordExceptionalCells
  nlinarith

theorem mem_wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (n m d : ℤ) (hn0 : 0≤n) (hnN : n<N) (hm0 : 0≤m) (hmN : m<N)
    (hd : d=-1 ∨ d=0 ∨ d=1) (hb : bad d (m-d*n) n) :
    (n,m)∈wordExceptionalCells N bad := by
  have hmem (E : Finset ℤ) (he : m-d*n∈E) : (n,m)∈exceptionalAlong N bad d E := by
    apply Finset.mem_biUnion.mpr
    refine ⟨m-d*n,he,Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn0,hnN⟩,hb⟩,?_⟩⟩
    exact Prod.ext rfl (by ring)
  rcases hd with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hmem _ (by simp only [Finset.mem_Ico,neg_one_mul]; constructor <;> omega)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hmem _ (by simp [hm0,hmN])))
  · exact Finset.mem_union_right _ (hmem _ (by simp only [Finset.mem_Ico,one_mul]; constructor <;> omega))

def wordBlockedOrigins (B : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  B.biUnion fun c =>
    ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).image
      fun o => (c.1 - o.1, c.2 - o.2)

theorem card_wordBlockedOrigins_le (B : Finset (ℤ × ℤ)) :
    (wordBlockedOrigins B).card ≤ B.card * 16 := by
  apply Finset.card_biUnion_le_card_mul
  intro c _hc
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).card :=
      Finset.card_image_le
    _ = 16 := by norm_num [Finset.card_product, Int.card_Icc]

theorem mem_wordBlockedOrigins (B : Finset (ℤ × ℤ)) (r q : ℤ)
    (i j : Fin 4) (hc : (r + i.val, q + j.val) ∈ B) :
    (r, q) ∈ wordBlockedOrigins B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(r + i.val, q + j.val), hc, Finset.mem_image.mpr ?_⟩
  refine ⟨((i.val : ℤ), (j.val : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
  · apply Prod.ext <;> simp

private theorem four_square_count_inequality (p : ℕ) (hp : 200<p) :
    240*wordWidth p<(wordWidth p-3)^2 := by
  have hs : 3≤wordWidth p := by change 3≤2*p+2; omega
  have he := Nat.sub_add_cancel hs
  dsimp [wordWidth] at *
  nlinarith

theorem exists_clean_four_square (p : ℕ) (hp : 200 < p)
    (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      ((Finset.Ico (0 : ℤ) (wordWidth p : ℕ)).filter (bad d e)).card ≤ 3) :
    ∃ r q : ℤ, 0 ≤ r ∧ r + 3 < (wordWidth p : ℕ) ∧
      0 ≤ q ∧ q + 3 < (wordWidth p : ℕ) ∧
      ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
        ¬ bad d ((q + j.val) - d * (r + i.val)) (r + i.val) := by
  let N : ℕ := wordWidth p
  have hN : 3 ≤ N := by dsimp [N]; nlinarith
  let C : Finset (ℤ × ℤ) :=
    (Finset.Ico (0 : ℤ) (N - 3 : ℕ)).product
      (Finset.Ico (0 : ℤ) (N - 3 : ℕ))
  let B := wordBlockedOrigins (wordExceptionalCells N bad)
  have hC : C.card = (N - 3) ^ 2 := by
    simp [C, Finset.card_product, Int.card_Ico, pow_two]
  have hB : B.card ≤ 240 * N := by
    calc
      B.card ≤ (wordExceptionalCells N bad).card * 16 :=
        card_wordBlockedOrigins_le _
      _ ≤ (5 * N * 3) * 16 :=
        Nat.mul_le_mul_right 16 (card_wordExceptionalCells_le N 3 bad hbad)
      _ = 240 * N := by ring
  have hlt : B.card < C.card := by
    rw [hC]
    exact hB.trans_lt (four_square_count_inequality p hp)
  obtain ⟨⟨r, q⟩, hc, hnblocked⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr, hq⟩ := Finset.mem_product.mp hc
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  have hr0 : 0 ≤ r := hr'.1
  have hq0 : 0 ≤ q := hq'.1
  have hr3 : r + 3 < (N : ℤ) := by omega
  have hq3 : q + 3 < (N : ℤ) := by omega
  refine ⟨r, q, hr0, hr3, hq0, hq3, ?_⟩
  intro i j d hd hb
  apply hnblocked
  apply mem_wordBlockedOrigins _ r q i j
  apply mem_wordExceptionalCells N bad (r + i.val) (q + j.val) d
  · omega
  · omega
  · omega
  · omega
  · exact hd
  · exact hb

end

end ArithmeticRule

end TranslationTiling.Sudoku
