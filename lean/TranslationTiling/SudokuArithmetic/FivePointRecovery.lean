import TranslationTiling.SudokuArithmetic.FivePointRows
import TranslationTiling.SudokuArithmetic.FivePointPattern
import Mathlib.Tactic.FieldSimp

namespace TranslationTiling.Sudoku.ArithmeticRule
open scoped Classical
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The five-point argument lowers the prime requirement to 11. -/
theorem global_affine_approximation {p : ℕ} (hp : p.Prime) (hlarge : 10<p)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let bad : ℤ→ℤ→ℤ→Prop := fun d e n =>
    (chooseLine hW d e).a*(n:ZMod p)+(chooseLine hW d e).b=0
  have hbad : ∀ d e i : ℤ, ((Finset.Ico (0:ℤ) p).filter (fun x => bad d e (x+i))).card≤1 := by
    intro d e i
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
    have hy' := Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1
    have he := affine_root_unique (chooseLine hW d e).nonzero
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have he' : (x:ZMod p)=(y:ZMod p) := by simpa only [Int.cast_add,add_left_inj] using he
    have hm := (ZMod.intCast_eq_intCast_iff' x y p).mp he'
    rw [Int.emod_eq_of_lt hx'.1 hx'.2,Int.emod_eq_of_lt hy'.1 hy'.2] at hm
    exact hm
  obtain ⟨r,q,hr0,hrp,hq0,hqmax,hclean⟩ := exists_clean_five_pattern p (by omega) bad (by
    intro d e i
    have hf := @Finset.filter_congr_decidable ℤ (Finset.Ico (0:ℤ) p)
      (fun x => bad d e (x+i))
      (fun x => Classical.propDecidable (bad d e (x+i)))
      (fun x => ZMod.decidableEq p
        ((chooseLine hW d e).a*((x+i:ℤ):ZMod p)+(chooseLine hW d e).b) 0)
    exact (congrArg (fun s : Finset ℤ => s.card≤1) hf).mpr (hbad d e i))
  have point_agrees (d i j : ℤ) (ho : (i,j)∈fivePattern d) :
      rawArray W (r+i) (q+j)=(chooseLine hW d (q+j-d*(r+i))).a*((r+i:ℤ):ZMod p)+
        (chooseLine hW d (q+j-d*(r+i))).b := by
    have hi : (0:ℤ) ≤ i ∧ i ≤ 4 := by
      by_cases h0 : d=0
      · subst d; simp [fivePattern] at ho; omega
      · by_cases h3 : d=3
        · subst d; simp [fivePattern] at ho; omega
        · by_cases h6 : d=6
          · subst d; simp [fivePattern] at ho; omega
          · simp [fivePattern,h0,h3,h6] at ho
    have hb : 0≤r+i ∧ r+i<(wordWidth p:ℕ) := by dsimp [wordWidth]; omega
    have hh := (chooseLine hW d (q+j-d*(r+i))).raw_agrees (r+i) hb (hclean d (i,j) ho)
    simpa only [show d*(r+i)+(q+j-d*(r+i))=q+j by ring] using hh
  let U : Fin 2→ZMod p := fun j => (chooseLine hW 0 (q+6*j.val)).a
  let V : Fin 2→ZMod p := fun j => U j*(r:ZMod p)+(chooseLine hW 0 (q+6*j.val)).b
  have row (i : ℤ) (j : Fin 2) (ho : (i,(6:ℤ)*j.val)∈fivePattern 0) :
      rawArray W (r+i) (q+6*j.val)=U j*(i:ZMod p)+V j := by
    have hh := point_agrees 0 i (6*j.val) ho
    rw [show q+6*j.val-0*(r+i)=q+6*j.val by ring] at hh
    rw [hh]
    dsimp [U,V]; push_cast; ring
  have diag (d x y : ℤ) (h0 : (x,0)∈fivePattern d) (h1 : (x+y,6)∈fivePattern d)
      (h2 : (x+2*y,12)∈fivePattern d) (hdy : d*y=6) :
      rawArray W (r+x) q-2*rawArray W (r+(x+y)) (q+6)+rawArray W (r+(x+2*y)) (q+12)=0 := by
    have h0' := point_agrees d x 0 h0
    have h1' := point_agrees d (x+y) 6 h1
    have h2' := point_agrees d (x+2*y) 12 h2
    have e1 : q+6-d*(r+(x+y))=q-d*(r+x) := by linear_combination -hdy
    have e2 : q+12-d*(r+(x+2*y))=q-d*(r+x) := by linear_combination -2*hdy
    rw [show q+0-d*(r+x)=q-d*(r+x) by ring] at h0'
    simp only [add_zero] at h0'
    rw [e1] at h1'; rw [e2] at h2'
    rw [h0',h1',h2']; push_cast; ring
  have hd3 := diag 3 0 2 (by decide) (by decide) (by decide) (by norm_num)
  have hd6 := diag 6 2 1 (by decide) (by decide) (by decide) (by norm_num)
  have hr00 := row 0 0 (by decide)
  have hr20 := row 2 0 (by decide)
  have hr26 := row 2 1 (by decide)
  have hr36 := row 3 1 (by decide)
  norm_num at hr00 hr20 hr26 hr36
  have h2 : (2:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) hd
  have h3 : (3:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<3) (by omega : 3<p) hd
  have h6 : (6:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<6) (by omega : 6<p) hd
  let T0 := rawArray W (r+4) (q+12)
  have hcoeff := five_point_coefficients h2 (U 0) (V 0) (U 1) (V 1) T0
    (by norm_num at hd3; rw [hr00,hr26] at hd3; dsimp [T0]; linear_combination hd3)
    (by norm_num at hd6; rw [hr20,hr36] at hd6; dsimp [T0]; linear_combination hd6)
  let A := U 0
  let B := (V 1-V 0)/6
  let C := V 0-A*(r:ZMod p)-B*(q:ZMod p)
  have hB : 6*B=V 1-V 0 := by dsimp [B]; field_simp [h6]
  have hu (j : Fin 2) : U j=U 0 := by fin_cases j; rfl; exact hcoeff.1.symm
  have hv (j : Fin 2) : V j=V 0+(V 1-V 0)*(j.val:ZMod p) := by fin_cases j <;> simp <;> ring
  have form (j : Fin 2) (n : ℤ) :
      A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C=
        (chooseLine hW 0 (q+6*j.val)).a*(n:ZMod p)+(chooseLine hW 0 (q+6*j.val)).b := by
    calc
      _ = U 0*((n:ZMod p)-(r:ZMod p))+V 0+(V 1-V 0)*(j.val:ZMod p) := by
        change U 0*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+
          (V 0-U 0*(r:ZMod p)-B*(q:ZMod p))=_
        push_cast; linear_combination (j.val:ZMod p)*hB
      _ = U j*((n:ZMod p)-(r:ZMod p))+V j := by rw [hu j,hv j]; ring
      _ = _ := by dsimp [V]; ring
  let D0 := B*(q:ZMod p)+C
  let D1 := B*((q+6:ℤ):ZMod p)+C
  have hf2 : 2*D1-D0=B*((q+12:ℤ):ZMod p)+C := by dsimp [D0,D1]; push_cast; ring
  have hnz (j : Fin 2) : A≠0 ∨ B*((q+6*j.val:ℤ):ZMod p)+C≠0 := by
    by_cases ha : A=0
    · right
      have hnonzero := (chooseLine hW 0 (q+6*j.val)).nonzero
      have hj : (chooseLine hW 0 (q+6*j.val)).a=0 := (hu j).trans ha
      have hb := hnonzero.resolve_left (not_not.mpr hj)
      have he := form j 0
      simp only [Int.cast_zero,mul_zero,zero_add] at he
      exact ne_of_eq_of_ne he hb
    · exact Or.inl ha
  have hT : A*((r+4:ℤ):ZMod p)+(2*D1-D0)=T0 := by
    change U 0*((r+4:ℤ):ZMod p)+(2*(B*((q+6:ℤ):ZMod p)+(V 0-U 0*(r:ZMod p)-B*(q:ZMod p)))-
      (B*(q:ZMod p)+(V 0-U 0*(r:ZMod p)-B*(q:ZMod p))))=T0
    push_cast
    linear_combination 2*hB-hcoeff.2
  have hrbound : 0≤r+4 ∧ r+4<(wordWidth p:ℕ) := by dsimp [wordWidth]; omega
  have hTnz : T0≠0 := rawArray_ne_zero W (r+4) (q+12) hrbound
  have hnz2 : A≠0 ∨ 2*D1-D0≠0 := by
    by_cases ha : A=0
    · right; intro hh; apply hTnz; rw [ha,hh] at hT; simpa using hT.symm
    · exact Or.inl ha
  have hrow0 (n : ℤ) (hn0 : 0≤n) (hnN : n<(wordWidth p:ℕ)) (hn : A*(n:ZMod p)+D0≠0) :
      rawArray W n q=A*(n:ZMod p)+D0 := by
    have he : A*(n:ZMod p)+D0=(chooseLine hW 0 q).a*(n:ZMod p)+(chooseLine hW 0 q).b := by
      have hh := form 0 n
      rw [show (q+6*(0:Fin 2).val:ℤ)=q by simp] at hh
      simpa [D0,add_assoc] using hh
    have h := (chooseLine hW 0 q).raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; exact hn)
    simpa only [zero_mul,zero_add] using h.trans he.symm
  have hrow1 (n : ℤ) (hn0 : 0≤n) (hnN : n<(wordWidth p:ℕ)) (hn : A*(n:ZMod p)+D1≠0) :
      rawArray W n (q+6)=A*(n:ZMod p)+D1 := by
    have he : A*(n:ZMod p)+D1=(chooseLine hW 0 (q+6)).a*(n:ZMod p)+(chooseLine hW 0 (q+6)).b := by
      simpa [D1,add_assoc] using form 1 n
    have h := (chooseLine hW 0 (q+6)).raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; exact hn)
    simpa only [zero_mul,zero_add] using h.trans he.symm
  have h0 : A≠0 ∨ D0≠0 := by simpa [D0] using hnz 0
  have h1 : A≠0 ∨ D1≠0 := by simpa [D1] using hnz 1
  let H := chooseLine hW 0 (q+12)
  have hc1 := third_row_candidate hp hlarge hW A D0 D1 q 1 (Or.inl rfl) h0 h1 hnz2 hrow0 hrow1
  have hc2 := third_row_candidate hp hlarge hW A D0 D1 q 2 (Or.inr rfl) h0 h1 hnz2 hrow0 hrow1
  norm_num only [Int.cast_one,Int.cast_ofNat] at hc1 hc2
  have hH : H.a=A ∧ H.b=2*D1-D0 := by
    by_cases ha : A=0
    · have hHa : H.a=0 := by
        rcases hc1 with hh | hh | hh <;> simpa [H,ha] using hh.1
      have hHb : H.b≠0 := H.nonzero.resolve_left (not_not.mpr hHa)
      have hv := H.raw_agrees (r+4) hrbound (by rw [hHa]; simpa using hHb)
      simp only [zero_mul,zero_add,hHa] at hv
      refine ⟨hHa.trans ha.symm,?_⟩
      have ht : 2*D1-D0=T0 := by simpa only [ha,zero_mul,zero_add] using hT
      exact hv.symm.trans ht.symm
    · exact intersect_row_candidates h2 h3 A D0 D1 H.a H.b ha hc1 hc2
  have hknown : ∀ j : Fin 3, ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) →
      A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0 →
      rawArray W n (q+6*j.val)=A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C := by
    intro j n hn0 hnN hn
    fin_cases j
    · simpa [D0,add_assoc] using hrow0 n hn0 hnN (by simpa [D0,add_assoc] using hn)
    · simpa [D1,add_assoc] using hrow1 n hn0 hnN (by simpa [D1,add_assoc] using hn)
    · have he : A*(n:ZMod p)+B*((q+12:ℤ):ZMod p)+C=H.a*(n:ZMod p)+H.b := by
        rw [hH.1,hH.2,hf2]; ring
      have hh := H.raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; simpa using hn)
      simpa [←he] using hh
  have hnz3 : ∀ j : Fin 3, A≠0 ∨ A*((6*j.val:ℤ):ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0 := by
    intro j
    by_cases ha : A=0
    · right
      fin_cases j
      · simpa [ha,D0] using h0.resolve_left (not_not.mpr ha)
      · simpa [ha,D1] using h1.resolve_left (not_not.mpr ha)
      · have hh := hnz2.resolve_left (not_not.mpr ha)
        rw [hf2] at hh
        simpa [ha] using hh
    · exact Or.inl ha
  have hrows := three_spaced_rows_four hp hlarge hW A B C q hknown hnz3
  have hglobal := good_everywhere_of_four_square (wordWidth p:ℕ) (by dsimp [wordWidth]; omega)
    (fun n m => A*(n:ZMod p)+B*(m:ZMod p)+C=0 ∨ rawArray W n m=A*(n:ZMod p)+B*(m:ZMod p)+C)
    (affine_four_line_closure hp hlarge hW A B C) 0 q (by omega) (by dsimp [wordWidth]; omega)
    (fun i j => by simpa only [zero_add] using hrows (q+j.val) (by omega) (by have := j.isLt; omega) i.val (by omega) (by have := i.isLt; dsimp [wordWidth]; omega))
  have hnonzero : A≠0 ∨ B≠0 ∨ C≠0 := by
    by_contra hh
    push_neg at hh
    apply hTnz
    rw [hf2] at hT
    simpa [hh.1,hh.2.1,hh.2.2] using hT.symm
  refine ⟨A,B,C,hnonzero,?_⟩
  intro n m hn
  have hh := hglobal n.val m (Int.natCast_nonneg _) (by exact_mod_cast n.isLt)
  rw [rawArray_column] at hh
  simpa only [affineValue,Int.cast_natCast] using hh.resolve_left (by simpa only [affineValue,Int.cast_natCast] using hn)

end
end TranslationTiling.Sudoku.ArithmeticRule
