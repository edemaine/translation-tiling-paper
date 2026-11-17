import TranslationTiling.SudokuArithmetic.SmallPrimeRows
import TranslationTiling.SudokuArithmetic.SmallPrimeGeometry
import Mathlib.Tactic.FieldSimp
namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
open Mathlib.Tactic
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem affine_four_line_closure_small {p : ℕ} (hp : p.Prime) (hlarge : 4 < p)
    {W : WordArray p} (hW : LineRule p W) (A B C : ZMod p) :
    FourLineClosure (wordWidth p : ℕ)
      (fun n m => A * (n : ZMod p) + B * (m : ZMod p) + C = 0 ∨
        rawArray W n m = A * (n : ZMod p) + B * (m : ZMod p) + C) := by
  let : Fact p.Prime := ⟨hp⟩
  intro d e hd r hr₀ hr₃ hgood n hn₀ hn
  let a : ZMod p := A + B * (d : ZMod p)
  let b : ZMod p := B * (e : ZMod p) + C
  let L := chooseLine hW d e
  have hrest (k : ℤ) : A * (k : ZMod p) + B * ((d * k + e : ℤ) : ZMod p) + C =
      a * (k : ZMod p) + b := by
    dsimp [a, b]
    push_cast
    ring
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · left
      rw [hrest, ha, hb]
      simp
    · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inr hb
      obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
        (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
        (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
      have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
          (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
          a * ((r + k.val : ℤ) : ZMod p) + b =
            L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
        have hk := hgood k
        dsimp only at hk
        rw [hrest] at hk
        have hk' := hk.resolve_left hkA
        have hbound : 0 ≤ r + k.val ∧ r + k.val < (wordWidth p : ℕ) := by
          have := k.isLt
          omega
        exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
      have hcoef := affine_coefficients_eq_of_two
        (fun h => hij ((four_residues_injective (by omega) r) h))
        (heq i hiA hiL) (heq j hjA hjL)
      by_cases hz : a * (n : ZMod p) + b = 0
      · left
        rw [hrest]
        exact hz
      · right
        rw [hrest]
        rw [hcoef.1, hcoef.2] at hz ⊢
        exact L.raw_agrees n ⟨hn₀, hn⟩ hz
  · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inl ha
    obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
      (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
      (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
    have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
        (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
        a * ((r + k.val : ℤ) : ZMod p) + b =
          L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
      have hk := hgood k
      dsimp only at hk
      rw [hrest] at hk
      have hk' := hk.resolve_left hkA
      have hbound : 0 ≤ r + k.val ∧ r + k.val < (wordWidth p : ℕ) := by
        have := k.isLt
        omega
      exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
    have hcoef := affine_coefficients_eq_of_two
      (fun h => hij ((four_residues_injective (by omega) r) h))
      (heq i hiA hiL) (heq j hjA hjL)
    by_cases hz : a * (n : ZMod p) + b = 0
    · left
      rw [hrest]
      exact hz
    · right
      rw [hrest]
      rw [hcoef.1, hcoef.2] at hz ⊢
      exact L.raw_agrees n ⟨hn₀, hn⟩ hz



theorem global_affine_of_certificates {p : Nat} (hp : p.Prime) (hlarge : 4<p)
    (hseed : Sat.Fmla.proof (satFormula p) []) (hthird : ThirdTest p)
    (hmid1 : MidTest p 1) (hmid3 : MidTest p 3)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h,hh,r,q,hr0,hr4,hclean⟩ := clean_seed_coordinates hW hseed
  have point_agrees (d : Int) (i j : Nat) (ho : (d,i,j)∈pattern h) :
      rawArray W (r+i) (q+j)=(chooseLine hW d (q+j-d*(r+i))).a*((r+i:Int):ZMod p)+
        (chooseLine hW d (q+j-d*(r+i))).b := by
    have hi := pattern_bounds h hh d i j ho
    have hb : 0≤r+i ∧ r+i<(wordWidth p:Nat) := by omega
    have hc := (chooseLine hW d (q+j-d*(r+i))).raw_agrees (r+i) hb (hclean d i j ho)
    simpa only [show d*(r+i)+(q+j-d*(r+i))=q+j by ring] using hc
  let U : Fin 2→ZMod p := fun j => (chooseLine hW 0 (q+h*j.val)).a
  let V : Fin 2→ZMod p := fun j => U j*(r:ZMod p)+(chooseLine hW 0 (q+h*j.val)).b
  have row (i : Nat) (j : Fin 2) (ho : (0,i,h*j.val)∈pattern h) :
      rawArray W (r+i) (q+h*j.val)=U j*(i:ZMod p)+V j := by
    have hc := point_agrees 0 i (h*j.val) ho
    rw [show q+(h*j.val:Nat)-0*(r+i)=q+h*j.val by push_cast; ring] at hc
    push_cast at hc
    rw [hc]
    dsimp [U,V]; push_cast; ring
  have diag (d : Int) (x y : Nat) (h0 : (d,x,0)∈pattern h)
      (h1 : (d,x+y,h)∈pattern h) (h2 : (d,x+2*y,2*h)∈pattern h) (hdy : d*y=h) :
      rawArray W (r+x) q-2*rawArray W (r+(x+y)) (q+h)+rawArray W (r+(x+2*y)) (q+2*h)=0 := by
    have h0' := point_agrees d x 0 h0
    have h1' := point_agrees d (x+y) h h1
    have h2' := point_agrees d (x+2*y) (2*h) h2
    have e1 : q+h-d*(r+(x+y:Nat))=q-d*(r+x) := by push_cast; linear_combination -hdy
    have e2 : q+(2*h:Nat)-d*(r+(x+2*y:Nat))=q-d*(r+x) := by push_cast; linear_combination -2*hdy
    rw [show q+(0:Nat)-d*(r+x)=q-d*(r+x) by ring] at h0'
    simp only [Nat.cast_zero,add_zero] at h0'
    push_cast at h0' h1' h2' e1 e2
    rw [e1] at h1'; rw [e2] at h2'
    rw [h0',h1',h2']; push_cast; ring
  have hd3 := diag (h/2) 0 2 (by rcases hh with rfl|rfl <;> decide)
    (by rcases hh with rfl|rfl <;> decide) (by rcases hh with rfl|rfl <;> decide)
    (by rcases hh with rfl|rfl <;> norm_num)
  have hd6 := diag h 2 1 (by rcases hh with rfl|rfl <;> decide)
    (by rcases hh with rfl|rfl <;> decide) (by rcases hh with rfl|rfl <;> decide) (by ring)
  have hr00 := row 0 0 (by rcases hh with rfl|rfl <;> decide)
  have hr20 := row 2 0 (by rcases hh with rfl|rfl <;> decide)
  have hr26 := row 2 1 (by rcases hh with rfl|rfl <;> decide)
  have hr36 := row 3 1 (by rcases hh with rfl|rfl <;> decide)
  norm_num only [Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.mul_one,Nat.cast_zero,Nat.cast_ofNat,Nat.cast_one,mul_zero,mul_one,add_zero,zero_add] at hr00 hr20 hr26 hr36
  have h2 : (2:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) hd
  have h3 : (3:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<3) (by omega : 3<p) hd
  have h6 : (h:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ h := (ZMod.natCast_eq_zero_iff h p).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hd
  let T0 := rawArray W (r+4) (q+2*h)
  have hcoeff := five_point_coefficients h2 (U 0) (V 0) (U 1) (V 1) T0
    (by norm_num only [Nat.zero_add,Nat.mul_one,Nat.cast_ofNat,Nat.cast_zero,mul_zero,add_zero] at hd3; rw [hr00,hr26] at hd3; dsimp [T0]; linear_combination hd3)
    (by norm_num only [Nat.zero_add,Nat.mul_one,Nat.cast_ofNat,Nat.cast_zero,mul_zero,add_zero] at hd6; rw [hr20,hr36] at hd6; dsimp [T0]; linear_combination hd6)
  let A := U 0
  let B := (V 1-V 0)/(h:ZMod p)
  let C := V 0-A*(r:ZMod p)-B*(q:ZMod p)
  have hB : (h:ZMod p)*B=V 1-V 0 := by dsimp [B]; field_simp [h6]
  have hu (j : Fin 2) : U j=U 0 := by fin_cases j; rfl; exact hcoeff.1.symm
  have hv (j : Fin 2) : V j=V 0+(V 1-V 0)*(j.val:ZMod p) := by fin_cases j <;> simp <;> ring
  have form (j : Fin 2) (n : ℤ) :
      A*(n:ZMod p)+B*((q+h*j.val:ℤ):ZMod p)+C=
        (chooseLine hW 0 (q+h*j.val)).a*(n:ZMod p)+(chooseLine hW 0 (q+h*j.val)).b := by
    calc
      _ = U 0*((n:ZMod p)-(r:ZMod p))+V 0+(V 1-V 0)*(j.val:ZMod p) := by
        change U 0*(n:ZMod p)+B*((q+h*j.val:ℤ):ZMod p)+
          (V 0-U 0*(r:ZMod p)-B*(q:ZMod p))=_
        push_cast; linear_combination (j.val:ZMod p)*hB
      _ = U j*((n:ZMod p)-(r:ZMod p))+V j := by rw [hu j,hv j]; ring
      _ = _ := by dsimp [V]; ring
  let D0 := B*(q:ZMod p)+C
  let D1 := B*((q+h:ℤ):ZMod p)+C
  have hf2 : 2*D1-D0=B*((q+2*h:ℤ):ZMod p)+C := by dsimp [D0,D1]; push_cast; ring
  have hnz (j : Fin 2) : A≠0 ∨ B*((q+h*j.val:ℤ):ZMod p)+C≠0 := by
    by_cases ha : A=0
    · right
      have hnonzero := (chooseLine hW 0 (q+h*j.val)).nonzero
      have hj : (chooseLine hW 0 (q+h*j.val)).a=0 := (hu j).trans ha
      have hb := hnonzero.resolve_left (not_not.mpr hj)
      have he := form j 0
      simp only [Int.cast_zero,mul_zero,zero_add] at he
      exact ne_of_eq_of_ne he hb
    · exact Or.inl ha
  have hT : A*((r+4:ℤ):ZMod p)+(2*D1-D0)=T0 := by
    change U 0*((r+4:ℤ):ZMod p)+(2*(B*((q+h:ℤ):ZMod p)+(V 0-U 0*(r:ZMod p)-B*(q:ZMod p)))-
      (B*(q:ZMod p)+(V 0-U 0*(r:ZMod p)-B*(q:ZMod p))))=T0
    push_cast
    linear_combination 2*hB-hcoeff.2
  have hrbound : 0≤r+4 ∧ r+4<(wordWidth p:ℕ) := by dsimp [wordWidth] at *; omega
  have hTnz : T0≠0 := rawArray_ne_zero W (r+4) (q+2*h) hrbound
  have hnz2 : A≠0 ∨ 2*D1-D0≠0 := by
    by_cases ha : A=0
    · right; intro hh; apply hTnz; rw [ha,hh] at hT; simpa using hT.symm
    · exact Or.inl ha
  have hrow0 (n : ℤ) (hn0 : 0≤n) (hnN : n<(wordWidth p:ℕ)) (hn : A*(n:ZMod p)+D0≠0) :
      rawArray W n q=A*(n:ZMod p)+D0 := by
    have he : A*(n:ZMod p)+D0=(chooseLine hW 0 q).a*(n:ZMod p)+(chooseLine hW 0 q).b := by
      have hh := form 0 n
      rw [show (q+h*(0:Fin 2).val:ℤ)=q by simp] at hh
      simpa [D0,add_assoc] using hh
    have h := (chooseLine hW 0 q).raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; exact hn)
    simpa only [zero_mul,zero_add] using h.trans he.symm
  have hrow1 (n : ℤ) (hn0 : 0≤n) (hnN : n<(wordWidth p:ℕ)) (hn : A*(n:ZMod p)+D1≠0) :
      rawArray W n (q+h)=A*(n:ZMod p)+D1 := by
    have he : A*(n:ZMod p)+D1=(chooseLine hW 0 (q+h)).a*(n:ZMod p)+(chooseLine hW 0 (q+h)).b := by
      have hf := form 1 n
      rw [show (q+h*(1:Fin 2).val:Int)=q+h by norm_num] at hf
      simpa [D1,add_assoc] using hf
    have h := (chooseLine hW 0 (q+h)).raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; exact hn)
    simpa only [zero_mul,zero_add] using h.trans he.symm
  have h0 : A≠0 ∨ D0≠0 := by simpa [D0] using hnz 0
  have h1 : A≠0 ∨ D1≠0 := by simpa [D1] using hnz 1

  have hT' : A*((r+4:Int):ZMod p)+2*D1-D0=T0 := by linear_combination hT
  have hH := third_row hp hlarge hW hthird A D0 D1 q h (by omega) h0 h1 hnz2 hrow0 hrow1
    ⟨r+4,hrbound.1,hrbound.2,by simpa [T0] using hT'.symm,by rw [hT']; exact hTnz⟩
  let H := chooseLine hW 0 (q+2*h)
  have hknown : ∀ j : Fin 3, ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) →
      A*(n:ZMod p)+B*((q+h*j.val:ℤ):ZMod p)+C≠0 →
      rawArray W n (q+h*j.val)=A*(n:ZMod p)+B*((q+h*j.val:ℤ):ZMod p)+C := by
    intro j n hn0 hnN hn
    fin_cases j
    · simpa [D0,add_assoc] using hrow0 n hn0 hnN (by simpa [D0,add_assoc] using hn)
    · simpa [D1,add_assoc] using hrow1 n hn0 hnN (by simpa [D1,add_assoc] using hn)
    · have he : A*(n:ZMod p)+B*((q+2*h:ℤ):ZMod p)+C=H.a*(n:ZMod p)+H.b := by
        rw [hH.1,hH.2,hf2]; ring
      have hh := H.raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; simpa [mul_comm] using hn)
      simp only [zero_mul,zero_add] at hh
      change rawArray W n (q+(h:Int)*2)=A*(n:ZMod p)+B*((q+(h:Int)*2:Int):ZMod p)+C
      rw [mul_comm (h:Int) 2]
      exact hh.trans he.symm
  have hnz3 : ∀ j : Fin 3, A≠0 ∨ A*((h*j.val:ℤ):ZMod p)+B*((q+h*j.val:ℤ):ZMod p)+C≠0 := by
    intro j
    by_cases ha : A=0
    · right
      fin_cases j
      · simpa [ha,D0] using h0.resolve_left (not_not.mpr ha)
      · simpa [ha,D1] using h1.resolve_left (not_not.mpr ha)
      · have hh := hnz2.resolve_left (not_not.mpr ha)
        rw [hf2] at hh
        simpa [ha,mul_comm] using hh
    · exact Or.inl ha

  have hknown' : KnownRows W A B C q h := by
    intro j n hn0 hnN
    by_cases hz : A*(n:ZMod p)+B*((q+h*j.val:Int):ZMod p)+C=0
    · exact Or.inl hz
    · exact Or.inr (hknown j n hn0 hnN hz)
  have hnz' : NonzeroRows A B C q h := by
    intro j
    by_cases ha : A=0
    · simpa [ha] using hnz3 j
    · exact Or.inl ha
  obtain ⟨q',hrows⟩ := four_rows_of_spaced hp hlarge hW hmid1 hmid3 A B C q h (by omega) hknown' hnz'
  have hglobal := good_everywhere_of_four_square (wordWidth p:Nat) (by dsimp [wordWidth]; omega)
    (Good W A B C)
    (affine_four_line_closure_small hp hlarge hW A B C) 0 q' (by omega) (by dsimp [wordWidth]; omega)
    (fun i j => by simpa only [zero_add] using hrows (q'+j.val) (by omega) (by have := j.isLt; omega) i.val (by omega) (by have := i.isLt; dsimp [wordWidth]; omega))
  have hnonzero : A≠0 ∨ B≠0 ∨ C≠0 := by
    by_contra hn
    push Not at hn
    apply hTnz
    rw [hf2] at hT
    simpa [hn.1,hn.2.1,hn.2.2] using hT.symm
  refine ⟨A,B,C,hnonzero,?_⟩
  intro n m hn
  have hg := hglobal n.val m (Int.natCast_nonneg _) (by exact_mod_cast n.isLt)
  rw [Good,rawArray_column] at hg
  simpa only [affineValue,Int.cast_natCast] using hg.resolve_left (by simpa only [affineValue,Int.cast_natCast] using hn)
end
end TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
