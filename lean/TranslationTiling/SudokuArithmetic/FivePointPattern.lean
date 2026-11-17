import TranslationTiling.SudokuArithmetic.WordAffineAlgebra
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Sudoku.ArithmeticRule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Four horizontal checks and two diagonal triples. -/
def fivePattern (d : ℤ) : Finset (ℤ×ℤ) :=
  if d=0 then {(0,0),(2,0),(2,6),(3,6)}
  else if d=3 then {(0,0),(2,6),(4,12)}
  else if d=6 then {(2,0),(3,6),(4,12)} else ∅

private def blockedLine (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d e : ℤ) :=
  (fivePattern d).biUnion fun o =>
    (((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+o.1))).image
      fun x => (x,d*(x+o.1)+e-o.2))

private theorem blockedLine_card (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d e : ℤ)
    (hb : ∀ i : ℤ, ((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+i))).card≤1) :
    (blockedLine p bad d e).card≤(fivePattern d).card := by
  have h : (blockedLine p bad d e).card≤(fivePattern d).card*1 := by
    apply Finset.card_biUnion_le_card_mul
    intro o _
    exact Finset.card_image_le.trans (hb o.1)
  simpa using h

private def blocked (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d : ℤ) (E : Finset ℤ) :=
  E.biUnion (blockedLine p bad d)

private theorem blocked_card (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d : ℤ) (E : Finset ℤ)
    (hb : ∀ e i : ℤ, ((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+i))).card≤1) :
    (blocked p bad d E).card≤E.card*(fivePattern d).card := by
  apply Finset.card_biUnion_le_card_mul
  exact fun e _ => blockedLine_card p bad d e (hb e)

/-- The five-point seed exists already at prime 11. -/
theorem exists_clean_five_pattern (p : ℕ) (hp : 11≤p)
    (bad : ℤ→ℤ→ℤ→Prop)
    (hb : ∀ d e i : ℤ, ((Finset.Ico (0:ℤ) p).filter
      (fun x => bad d e (x+i))).card≤1) :
    ∃ r q : ℤ, 0≤r ∧ r<(p:ℤ) ∧ 0≤q ∧ q+12<(100*p:ℕ) ∧
      ∀ d o, o∈fivePattern d → ¬bad d (q+o.2-d*(r+o.1)) (r+o.1) := by
  let T := 100*p
  let origins := (Finset.Ico (0:ℤ) p).product (Finset.Ico (0:ℤ) (T-12:ℕ))
  let E (d : ℤ) := Finset.Ico (-d*((p:ℤ)+4)) T
  let B₀ := blocked p bad 0 (E 0)
  let B₃ := blocked p bad 3 (E 3)
  let B₆ := blocked p bad 6 (E 6)
  let B := B₀ ∪ B₃ ∪ B₆
  have hcount (d : ℤ) (hd : d=0 ∨ d=3 ∨ d=6) :
      (blocked p bad d (E d)).card≤(T+d.toNat*(p+4))*(fivePattern d).card := by
    have h := blocked_card p bad d (E d) (hb d)
    have he : (E d).card=T+d.toNat*(p+4) := by
      rcases hd with rfl | rfl | rfl <;> simp [E,Int.card_Ico] <;> omega
    simpa only [he] using h
  have h0 : B₀.card≤4*T := by simpa [B₀,fivePattern,Nat.mul_comm] using hcount 0 (by tauto)
  have h3 : B₃.card≤3*(T+3*(p+4)) := by simpa [B₃,fivePattern,Nat.mul_comm] using hcount 3 (by tauto)
  have h6 : B₆.card≤3*(T+6*(p+4)) := by simpa [B₆,fivePattern,Nat.mul_comm] using hcount 6 (by tauto)
  have hB : B.card≤10*T+27*(p+4) := by
    have h := Finset.card_union_le (B₀ ∪ B₃) B₆
    have h' := Finset.card_union_le B₀ B₃
    dsimp only [B]
    omega
  have hO : origins.card=p*(T-12) := by simp [origins]
  have hlt : B.card<origins.card := by
    apply hB.trans_lt
    rw [hO]
    have ht : T-12+12=T := Nat.sub_add_cancel (by dsimp [T]; omega)
    have hm := Nat.mul_le_mul_right (100*p+61) hp
    dsimp [T] at *
    nlinarith
  obtain ⟨⟨r,q⟩,ho,hnb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp ho
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  refine ⟨r,q,hr'.1,hr'.2,hq'.1,by change q+12<(T:ℤ); omega,?_⟩
  intro d o ho hbad
  have hd : d=0 ∨ d=3 ∨ d=6 := by
    by_contra hn
    simp [fivePattern,show d≠0 by tauto,
      show d≠3 by tauto,show d≠6 by tauto] at ho
  have hob : 0≤o.1 ∧ o.1≤4 ∧ 0≤o.2 ∧ o.2≤12 := by
    rcases hd with rfl | rfl | rfl <;> simp [fivePattern] at ho <;>
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  let e := q+o.2-d*(r+o.1)
  have he : e∈E d := by
    rcases hd with rfl | rfl | rfl <;> simp only [E,Finset.mem_Ico] <;> dsimp [e] <;> constructor <;> omega
  have hm : (r,q)∈blocked p bad d (E d) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨e,he,Finset.mem_biUnion.mpr ⟨o,ho,Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hbad⟩,?_⟩⟩⟩
    apply Prod.ext
    · rfl
    · dsimp [e]
      ring
  apply hnb
  rcases hd with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
  · exact Finset.mem_union_right _ hm

end
end TranslationTiling.Sudoku.ArithmeticRule
