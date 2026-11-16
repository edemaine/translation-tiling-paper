import TranslationTiling.SudokuArithmetic.WordAffineAlgebra
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Sudoku.ArithmeticRule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Six horizontal checks and three diagonal triples. -/
def sixPattern (d : ℤ) : Finset (ℤ×ℤ) :=
  if d=0 then {(0,0),(2,0),(3,6),(4,6),(4,12),(6,12)}
  else if d=2 then {(0,0),(3,6),(6,12)}
  else if d=3 then {(2,0),(4,6),(6,12)}
  else if d=6 then {(2,0),(3,6),(4,12)} else ∅

private def blockedLine (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d e : ℤ) :=
  (sixPattern d).biUnion fun o =>
    (((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+o.1))).image
      fun x => (x,d*(x+o.1)+e-o.2))

private theorem blockedLine_card (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d e : ℤ)
    (hb : ∀ i : ℤ, ((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+i))).card≤1) :
    (blockedLine p bad d e).card≤(sixPattern d).card := by
  have h : (blockedLine p bad d e).card≤(sixPattern d).card*1 := by
    apply Finset.card_biUnion_le_card_mul
    intro o _
    exact Finset.card_image_le.trans (hb o.1)
  simpa using h

private def blocked (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d : ℤ) (E : Finset ℤ) :=
  E.biUnion (blockedLine p bad d)

private theorem blocked_card (p : ℕ) (bad : ℤ→ℤ→ℤ→Prop) (d : ℤ) (E : Finset ℤ)
    (hb : ∀ e i : ℤ, ((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+i))).card≤1) :
    (blocked p bad d E).card≤E.card*(sixPattern d).card := by
  apply Finset.card_biUnion_le_card_mul
  exact fun e _ => blockedLine_card p bad d e (hb e)

/-- The six-point seed exists already at prime 17. -/
theorem exists_clean_six_pattern (p : ℕ) (hp : 17≤p)
    (bad : ℤ→ℤ→ℤ→Prop)
    (hb : ∀ d e i : ℤ, ((Finset.Ico (0:ℤ) p).filter
      (fun x => bad d e (x+i))).card≤1) :
    ∃ r q : ℤ, 0≤r ∧ r<(p:ℤ) ∧ 0≤q ∧ q+12<(100*p:ℕ) ∧
      ∀ d o, o∈sixPattern d → ¬bad d (q+o.2-d*(r+o.1)) (r+o.1) := by
  let T := 100*p
  let origins := (Finset.Ico (0:ℤ) p).product (Finset.Ico (0:ℤ) (T-12:ℕ))
  let E (d : ℤ) := Finset.Ico (-d*((p:ℤ)+6)) T
  let B₀ := blocked p bad 0 (E 0)
  let B₂ := blocked p bad 2 (E 2)
  let B₃ := blocked p bad 3 (E 3)
  let B₆ := blocked p bad 6 (E 6)
  let B := B₀ ∪ B₂ ∪ B₃ ∪ B₆
  have hcount (d : ℤ) (hd : d=0 ∨ d=2 ∨ d=3 ∨ d=6) :
      (blocked p bad d (E d)).card≤(T+d.toNat*(p+6))*(sixPattern d).card := by
    have h := blocked_card p bad d (E d) (hb d)
    have he : (E d).card=T+d.toNat*(p+6) := by
      rcases hd with rfl | rfl | rfl | rfl <;> simp [E,Int.card_Ico] <;> omega
    simpa only [he] using h
  have h0 : B₀.card≤6*T := by simpa [B₀,sixPattern,Nat.mul_comm] using hcount 0 (by tauto)
  have h2 : B₂.card≤3*(T+2*(p+6)) := by simpa [B₂,sixPattern,Nat.mul_comm] using hcount 2 (by tauto)
  have h3 : B₃.card≤3*(T+3*(p+6)) := by simpa [B₃,sixPattern,Nat.mul_comm] using hcount 3 (by tauto)
  have h6 : B₆.card≤3*(T+6*(p+6)) := by simpa [B₆,sixPattern,Nat.mul_comm] using hcount 6 (by tauto)
  have hB : B.card≤15*T+33*(p+6) := by
    have h := Finset.card_union_le (B₀ ∪ B₂ ∪ B₃) B₆
    have h' := Finset.card_union_le (B₀ ∪ B₂) B₃
    have h'' := Finset.card_union_le B₀ B₂
    dsimp only [B]
    omega
  have hO : origins.card=p*(T-12) := by simp [origins]
  have hlt : B.card<origins.card := by
    apply hB.trans_lt
    rw [hO]
    have ht : T-12+12=T := Nat.sub_add_cancel (by dsimp [T]; omega)
    have hm := Nat.mul_le_mul_right (100*p+155) hp
    dsimp [T] at *
    nlinarith
  obtain ⟨⟨r,q⟩,ho,hnb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp ho
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  refine ⟨r,q,hr'.1,hr'.2,hq'.1,by change q+12<(T:ℤ); omega,?_⟩
  intro d o ho hbad
  have hd : d=0 ∨ d=2 ∨ d=3 ∨ d=6 := by
    by_contra hn
    simp [sixPattern,show d≠0 by tauto,show d≠2 by tauto,
      show d≠3 by tauto,show d≠6 by tauto] at ho
  have hob : 0≤o.1 ∧ o.1≤6 ∧ 0≤o.2 ∧ o.2≤12 := by
    rcases hd with rfl | rfl | rfl | rfl <;> simp [sixPattern] at ho <;>
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  let e := q+o.2-d*(r+o.1)
  have he : e∈E d := by
    rcases hd with rfl | rfl | rfl | rfl <;> simp only [E,Finset.mem_Ico] <;> dsimp [e] <;> constructor <;> omega
  have hm : (r,q)∈blocked p bad d (E d) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨e,he,Finset.mem_biUnion.mpr ⟨o,ho,Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hbad⟩,?_⟩⟩⟩
    apply Prod.ext
    · rfl
    · dsimp [e]
      ring
  apply hnb
  rcases hd with rfl | rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
  · exact Finset.mem_union_right _ hm

section Field
variable {K : Type*} [Field K]

theorem six_point_row_coefficients (h2 : (2:K)≠0) (U V : Fin 3→K)
    (h3 : 2*U 0+V 0-2*(4*U 1+V 1)+6*U 2+V 2=0)
    (h6 : 2*U 0+V 0-2*(3*U 1+V 1)+4*U 2+V 2=0)
    (h2' : V 0-2*(3*U 1+V 1)+6*U 2+V 2=0) :
    (∀ j, U j=U 0) ∧ ∀ j, V j=V 0+(V 1-V 0)*(j.val:K) := by
  have hu21 : U 2=U 1 := by
    apply mul_left_cancel₀ h2
    linear_combination h3-h6
  have hu02 : U 0=U 2 := by
    apply mul_left_cancel₀ h2
    linear_combination h6-h2'
  have hv : V 2=2*V 1-V 0 := by linear_combination h2'-6*hu21
  constructor
  · intro j; fin_cases j <;> simp_all
  · intro j; fin_cases j <;> simp [hv] <;> ring

theorem two_nonzero_of_three (x : Fin 3→K) (hx : Function.Injective x)
    (a b : K) (hab : a≠0 ∨ b≠0) :
    ∃ i j, i≠j ∧ a*x i+b≠0 ∧ a*x j+b≠0 := by
  let bad := Finset.univ.filter (fun i => a*x i+b=0)
  have hb : bad.card≤1 := affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) a b hab
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  have hgood : 1<(Finset.univ\bad).card := by simp only [Finset.card_univ,Fintype.card_fin] at hc; omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hgood
  exact ⟨i,j,hij,by simpa [bad] using hi,by simpa [bad] using hj⟩

theorem two_good_of_five_affines (x : Fin 7→K) (hx : Function.Injective x)
    (a b : Fin 5→K) (hab : ∀ k, a k≠0 ∨ b k≠0) :
    ∃ i j, i≠j ∧ (∀ k, a k*x i+b k≠0) ∧ ∀ k, a k*x j+b k≠0 := by
  let bad := Finset.univ.biUnion fun k : Fin 5 => Finset.univ.filter (fun i => a k*x i+b k=0)
  have hb : bad.card≤5 := by
    have h : bad.card≤(Finset.univ : Finset (Fin 5)).card*1 := by
      apply Finset.card_biUnion_le_card_mul
      exact fun k _ => affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ (hab k)
    simpa using h
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  have hgood : 1<(Finset.univ\bad).card := by simp only [Finset.card_univ,Fintype.card_fin] at hc; omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hgood
  exact ⟨i,j,hij,by simpa [bad] using hi,by simpa [bad] using hj⟩

end Field
end
end TranslationTiling.Sudoku.ArithmeticRule
