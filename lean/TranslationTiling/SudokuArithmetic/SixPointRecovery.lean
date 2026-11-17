import TranslationTiling.SudokuArithmetic.WordAffine
import TranslationTiling.SudokuArithmetic.SixPointPattern
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp

namespace TranslationTiling.Sudoku.ArithmeticRule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem int_residues_injective {p k : ℕ} (hk : k≤p) :
    Function.Injective (fun i : Fin k => (i.val:ZMod p)) := by
  intro i j he
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (i.isLt.trans_le hk),ZMod.val_natCast_of_lt (j.isLt.trans_le hk)] at hv
  exact Fin.ext hv

/-- Recover the intervening rows before applying four-row propagation. -/
theorem three_spaced_rows_four {p : ℕ} (hp : p.Prime) (hlarge : 10<p)
    {W : WordArray p} (hW : LineRule p W) (A B C : ZMod p) (q : ℤ)
    (hknown : ∀ j : Fin 3, ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) →
      A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0 →
      rawArray W n (q+6*j.val)=A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C)
    (hnz : ∀ j : Fin 3, A≠0 ∨ A*((6*j.val:ℤ):ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0) :
    FourGoodRows (wordWidth p:ℕ)
      (fun n m => A*(n:ZMod p)+B*(m:ZMod p)+C=0 ∨ rawArray W n m=A*(n:ZMod p)+B*(m:ZMod p)+C) q := by
  let : Fact p.Prime := ⟨hp⟩
  let F (n m : ℤ) := A*(n:ZMod p)+B*(m:ZMod p)+C
  have h6 : (6:ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 6 p).mp he
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  have hx : Function.Injective (fun i : Fin 7 => (i.val:ZMod p)) := int_residues_injective (by omega)
  intro m hm0 hm3
  let t := m-q
  have ht : 0≤t ∧ t≤3 := by dsimp [t]; omega
  have hm : m=q+t := by dsimp [t]; omega
  rw [hm]
  by_cases hz : A=0 ∧ B*((q+t:ℤ):ZMod p)+C=0
  · intro n _ _
    left
    simp only [hz.1,zero_mul,zero_add]
    exact hz.2
  let H := chooseLine hW 0 (q+t)
  let a : Fin 5→ZMod p := ![A,A,A,A,H.a]
  let b : Fin 5→ZMod p := ![F 0 q,F 6 (q+6),F 12 (q+12),F t (q+t),H.a*(t:ZMod p)+H.b]
  have hab : ∀ k, a k≠0 ∨ b k≠0 := by
    intro k
    fin_cases k
    · simpa [a,b,F] using hnz 0
    · simpa [a,b,F] using hnz 1
    · simpa [a,b,F] using hnz 2
    · by_cases hA : A=0
      · right
        have hh : B*((q+t:ℤ):ZMod p)+C≠0 := fun he => hz ⟨hA,he⟩
        simpa [a,b,F,hA] using hh
      · exact Or.inl hA
    · dsimp [a,b]
      rcases H.nonzero with ha | hb
      · exact Or.inl ha
      · by_cases ha : H.a=0
        · exact Or.inr (by simpa [ha] using hb)
        · exact Or.inl ha
  obtain ⟨x,y,hxy,hxgood,hygood⟩ := two_good_of_five_affines _ hx a b hab
  have known_nonzero (x : Fin 7) (hg : ∀ k, a k*(x.val:ZMod p)+b k≠0) (j : Fin 3) :
      F ((x.val:ℤ)+6*j.val) (q+6*j.val)≠0 := by
    fin_cases j
    · convert hg 0 using 1 <;> dsimp [a,b,F] <;> push_cast <;> ring
    · convert hg 1 using 1 <;> dsimp [a,b,F] <;> push_cast <;> ring
    · convert hg 2 using 1 <;> dsimp [a,b,F] <;> push_cast <;> ring
  have endpoint (x : Fin 7) (hg : ∀ k, a k*(x.val:ZMod p)+b k≠0) :
      A*(((x.val:ℤ)+t:ℤ):ZMod p)+B*((q+t:ℤ):ZMod p)+C=
        H.a*(((x.val:ℤ)+t:ℤ):ZMod p)+H.b := by
    let L := chooseLine hW 1 (q-x.val)
    let z (j : Fin 3) : ℤ := x.val+6*j.val
    have hzbound (j) : 0≤z j ∧ z j<(wordWidth p:ℕ) := by
      have hxv := x.isLt; have hj := j.isLt
      dsimp [z,wordWidth]
      omega
    have hzinj : Function.Injective (fun j : Fin 3 => (z j:ZMod p)) := by
      intro i j he
      have hh : (i.val:ZMod p)=(j.val:ZMod p) := by
        apply mul_left_cancel₀ h6
        dsimp [z] at he
        push_cast at he
        linear_combination he
      exact int_residues_injective (by omega : 3≤p) hh
    obtain ⟨i,j,hij,hi,hj⟩ := two_nonzero_of_three _ hzinj L.a L.b L.nonzero
    have agree (k : Fin 3) (hk : L.a*(z k:ZMod p)+L.b≠0) :
        L.a*(z k:ZMod p)+L.b=(A+B)*(z k:ZMod p)+(B*((q-x.val:ℤ):ZMod p)+C) := by
      have hl := L.raw_agrees (z k) (hzbound k) hk
      have hv := hknown k (z k) (hzbound k).1 (hzbound k).2 (known_nonzero x hg k)
      have he : 1*z k+(q-x.val)=q+6*k.val := by dsimp [z]; ring
      rw [he] at hl
      rw [hv] at hl
      rw [← hl]
      dsimp [z]
      push_cast
      ring
    obtain ⟨hla,hlb⟩ := affine_coefficients_eq_of_two (fun he => hij (hzinj he)) (agree i hi) (agree j hj)
    have hnt : 0≤(x.val:ℤ)+t ∧ (x.val:ℤ)+t<(wordWidth p:ℕ) := by
      have hxv := x.isLt
      dsimp [wordWidth]
      omega
    have htarget : F ((x.val:ℤ)+t) (q+t)≠0 := by
      convert hg 3 using 1 <;> dsimp [a,b,F] <;> push_cast <;> ring
    have hhor : H.a*(((x.val:ℤ)+t:ℤ):ZMod p)+H.b≠0 := by
      convert hg 4 using 1 <;> dsimp [a,b] <;> push_cast <;> ring
    have hline : L.a*(((x.val:ℤ)+t:ℤ):ZMod p)+L.b=F ((x.val:ℤ)+t) (q+t) := by
      rw [hla,hlb]
      dsimp [F]
      push_cast
      ring
    have hs := L.raw_agrees ((x.val:ℤ)+t) hnt (by rw [hline]; exact htarget)
    have hh := H.raw_agrees ((x.val:ℤ)+t) hnt hhor
    rw [show 1*((x.val:ℤ)+t)+(q-x.val)=q+t by ring,hline] at hs
    simp only [zero_mul,zero_add] at hh
    exact hs.symm.trans hh
  have hdistinct : (((x.val:ℤ)+t:ℤ):ZMod p)≠(((y.val:ℤ)+t:ℤ):ZMod p) := by
    intro he
    apply hxy
    apply hx
    simpa only [Int.cast_add,Int.cast_natCast,add_left_inj] using he
  obtain ⟨ha,hb⟩ := affine_coefficients_eq_of_two (a:=A) (b:=B*((q+t:ℤ):ZMod p)+C)
    (c:=H.a) (d:=H.b) hdistinct
    (by simpa only [add_assoc] using endpoint x hxgood)
    (by simpa only [add_assoc] using endpoint y hygood)
  intro n hn0 hnN
  by_cases hF : F n (q+t)=0
  · exact Or.inl hF
  · right
    have hFnz : A*(n:ZMod p)+(B*((q+t:ℤ):ZMod p)+C)≠0 := by simpa only [F,add_assoc] using hF
    have hh := H.raw_agrees n ⟨hn0,hnN⟩ (by rw [← ha,← hb]; exact hFnz)
    simp only [zero_mul,zero_add] at hh
    simpa only [ha,hb,F,add_assoc] using hh

/-- The six-point argument lowers the prime requirement to 17. -/
theorem global_affine_approximation_six {p : ℕ} (hp : p.Prime) (hlarge : 16<p)
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
  obtain ⟨r,q,hr0,hrp,hq0,hqmax,hclean⟩ := exists_clean_six_pattern p (by omega) bad (by
    intro d e i
    have hf := @Finset.filter_congr_decidable ℤ (Finset.Ico (0:ℤ) p)
      (fun x => bad d e (x+i))
      (fun x => Classical.propDecidable (bad d e (x+i)))
      (fun x => ZMod.decidableEq p
        ((chooseLine hW d e).a*((x+i:ℤ):ZMod p)+(chooseLine hW d e).b) 0)
    exact (congrArg (fun s : Finset ℤ => s.card≤1) hf).mpr (hbad d e i))
  have point_agrees (d i j : ℤ) (ho : (i,j)∈sixPattern d) :
      rawArray W (r+i) (q+j)=(chooseLine hW d (q+j-d*(r+i))).a*((r+i:ℤ):ZMod p)+
        (chooseLine hW d (q+j-d*(r+i))).b := by
    have hi : (0:ℤ) ≤ i ∧ i ≤ 6 := by
      by_cases h0 : d=0
      · subst d; simp [sixPattern] at ho; omega
      · by_cases h2 : d=2
        · subst d; simp [sixPattern] at ho; omega
        · by_cases h3 : d=3
          · subst d; simp [sixPattern] at ho; omega
          · by_cases h6 : d=6
            · subst d; simp [sixPattern] at ho; omega
            · simp [sixPattern,h0,h2,h3,h6] at ho
    have hb : 0≤r+i ∧ r+i<(wordWidth p:ℕ) := by dsimp [wordWidth]; omega
    have hh := (chooseLine hW d (q+j-d*(r+i))).raw_agrees (r+i) hb (hclean d (i,j) ho)
    simpa only [show d*(r+i)+(q+j-d*(r+i))=q+j by ring] using hh
  let U : Fin 3→ZMod p := fun j => (chooseLine hW 0 (q+6*j.val)).a
  let V : Fin 3→ZMod p := fun j => U j*(r:ZMod p)+(chooseLine hW 0 (q+6*j.val)).b
  have row (i : ℤ) (j : Fin 3) (ho : (i,(6:ℤ)*j.val)∈sixPattern 0) :
      rawArray W (r+i) (q+6*j.val)=U j*(i:ZMod p)+V j := by
    have hh := point_agrees 0 i (6*j.val) ho
    rw [show q+6*j.val-0*(r+i)=q+6*j.val by ring] at hh
    rw [hh]
    dsimp [U,V]
    push_cast
    ring
  have diag (d x y : ℤ) (h0 : (x,0)∈sixPattern d) (h1 : (x+y,6)∈sixPattern d)
      (h2 : (x+2*y,12)∈sixPattern d) (hdy : d*y=6) :
      rawArray W (r+x) q-2*rawArray W (r+(x+y)) (q+6)+rawArray W (r+(x+2*y)) (q+12)=0 := by
    have h0' := point_agrees d x 0 h0
    have h1' := point_agrees d (x+y) 6 h1
    have h2' := point_agrees d (x+2*y) 12 h2
    have e1 : q+6-d*(r+(x+y))=q-d*(r+x) := by linear_combination -hdy
    have e2 : q+12-d*(r+(x+2*y))=q-d*(r+x) := by linear_combination -2*hdy
    rw [show q+0-d*(r+x)=q-d*(r+x) by ring] at h0'
    simp only [add_zero] at h0'
    rw [e1] at h1'
    rw [e2] at h2'
    rw [h0',h1',h2']
    push_cast
    ring
  have hd3 := diag 3 2 2 (by decide) (by decide) (by decide) (by norm_num)
  have hd6 := diag 6 2 1 (by decide) (by decide) (by decide) (by norm_num)
  have hd2 := diag 2 0 3 (by decide) (by decide) (by decide) (by norm_num)
  have hr00 := row 0 0 (by decide)
  have hr20 := row 2 0 (by decide)
  have hr36 := row 3 1 (by decide)
  have hr46 := row 4 1 (by decide)
  have hr412 := row 4 2 (by decide)
  have hr612 := row 6 2 (by decide)
  norm_num at hr00 hr20 hr36 hr46 hr412 hr612
  have h2 : (2:ZMod p)≠0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) ((ZMod.natCast_eq_zero_iff 2 p).mp he)
  have h6 : (6:ZMod p)≠0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<6) (by omega : 6<p) ((ZMod.natCast_eq_zero_iff 6 p).mp he)
  have hcoeff := six_point_row_coefficients h2 U V
    (by norm_num only [show (2:ℤ)+2=4 by norm_num,show (2:ℤ)+2*2=6 by norm_num] at hd3; rw [hr20,hr46,hr612] at hd3; norm_num at hd3 ⊢; linear_combination hd3)
    (by norm_num only [show (2:ℤ)+1=3 by norm_num,show (2:ℤ)+2*1=4 by norm_num] at hd6; rw [hr20,hr36,hr412] at hd6; norm_num at hd6 ⊢; linear_combination hd6)
    (by norm_num only [zero_add,add_zero,show (2:ℤ)*3=6 by norm_num] at hd2; rw [hr00,hr36,hr612] at hd2; norm_num at hd2 ⊢; linear_combination hd2)
  let A := U 0
  let B := (V 1-V 0)/6
  let C := V 0-A*(r:ZMod p)-B*(q:ZMod p)
  have hB : 6*B=V 1-V 0 := by dsimp [B]; field_simp [h6]
  have form (j : Fin 3) (n : ℤ) :
      A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C=
        (chooseLine hW 0 (q+6*j.val)).a*(n:ZMod p)+(chooseLine hW 0 (q+6*j.val)).b := by
    calc
      _ = U 0*((n:ZMod p)-(r:ZMod p))+V 0+(V 1-V 0)*(j.val:ZMod p) := by
        change U 0*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+
          (V 0-U 0*(r:ZMod p)-B*(q:ZMod p))=_
        push_cast
        linear_combination (j.val:ZMod p)*hB
      _ = U j*((n:ZMod p)-(r:ZMod p))+V j := by rw [hcoeff.1 j,hcoeff.2 j]; ring
      _ = _ := by dsimp [V]; ring
  have hknown : ∀ j : Fin 3, ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) →
      A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0 →
      rawArray W n (q+6*j.val)=A*(n:ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C := by
    intro j n hn0 hnN hn
    rw [form j n] at hn ⊢
    have hh := (chooseLine hW 0 (q+6*j.val)).raw_agrees n ⟨hn0,hnN⟩ hn
    simpa only [zero_mul,zero_add] using hh
  have hnz : ∀ j : Fin 3, A≠0 ∨ A*((6*j.val:ℤ):ZMod p)+B*((q+6*j.val:ℤ):ZMod p)+C≠0 := by
    intro j
    by_cases ha : A=0
    · right
      have hnonzero := (chooseLine hW 0 (q+6*j.val)).nonzero
      have hj : (chooseLine hW 0 (q+6*j.val)).a=0 := (hcoeff.1 j).trans ha
      have hb := hnonzero.resolve_left (not_not.mpr hj)
      rw [form]
      simpa only [hj,zero_mul,zero_add] using hb
    · exact Or.inl ha
  have hrows := three_spaced_rows_four hp (by omega) hW A B C q hknown hnz
  have hglobal := good_everywhere_of_four_square (wordWidth p:ℕ) (by dsimp [wordWidth]; omega)
    (fun n m => A*(n:ZMod p)+B*(m:ZMod p)+C=0 ∨ rawArray W n m=A*(n:ZMod p)+B*(m:ZMod p)+C)
    (affine_four_line_closure hp (by omega) hW A B C) 0 q (by omega) (by dsimp [wordWidth]; omega)
    (fun i j => by simpa only [zero_add] using hrows (q+j.val) (by omega) (by have := j.isLt; omega) i.val (by omega) (by have := i.isLt; dsimp [wordWidth]; omega))
  have hnonzero : A≠0 ∨ B≠0 ∨ C≠0 := by
    by_cases ha : A=0
    · by_cases hb : B=0
      · right; right; intro hc
        have he := form 0 0
        have hu := (chooseLine hW 0 (q+0)).nonzero
        have hua : (chooseLine hW 0 (q+0)).a=0 := by
          have hh := (hcoeff.1 0).trans ha
          change (chooseLine hW 0 (q+6*(0:ℤ))).a=0 at hh
          rw [mul_zero] at hh
          exact hh
        have hub := hu.resolve_left (not_not.mpr hua)
        simp [ha,hb,hc] at he
        exact hub (by simpa using he.symm)
      · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
  refine ⟨A,B,C,hnonzero,?_⟩
  intro n m hn
  have hh := hglobal n.val m (Int.natCast_nonneg _) (by exact_mod_cast n.isLt)
  rw [rawArray_column] at hh
  simpa only [affineValue,Int.cast_natCast] using hh.resolve_left (by simpa only [affineValue,Int.cast_natCast] using hn)

end
end TranslationTiling.Sudoku.ArithmeticRule
