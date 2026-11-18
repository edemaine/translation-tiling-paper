import TranslationTiling.SudokuArithmetic.ShortFields
import TranslationTiling.SudokuArithmetic.ShortWordAffine
namespace TranslationTiling.Sudoku.ShortRule.Seed
open ArithmeticRule
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable {p : Nat} (hp : p.Prime) (hlarge : 4<p)
include hp hlarge

theorem third_row {W : WordArray p} (hW : LineRule p W)
    (htest : ThirdTest p) (A D0 D1 : ZMod p) (q h : Int)
    (hh : h=2 ∨ h=4)
    (h0 : A≠0 ∨ D0≠0) (h1 : A≠0 ∨ D1≠0) (h2 : A≠0 ∨ 2*D1-D0≠0)
    (row0 : ∀ n : Int, 0≤n → n<(wordWidth p:Nat) → A*(n:ZMod p)+D0≠0 →
      rawArray W n q=A*(n:ZMod p)+D0)
    (row1 : ∀ n : Int, 0≤n → n<(wordWidth p:Nat) → A*(n:ZMod p)+D1≠0 →
      rawArray W n (q+h)=A*(n:ZMod p)+D1)
    (seed : ∃ n : Int, 0≤n ∧ n<(wordWidth p:Nat) ∧
      rawArray W n (q+2*h)=A*(n:ZMod p)+2*D1-D0 ∧ A*(n:ZMod p)+2*D1-D0≠0) :
    (chooseLine hW 0 (q+2*h)).a=A ∧ (chooseLine hW 0 (q+2*h)).b=2*D1-D0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let H := chooseLine hW 0 (q+2*h)
  have htwo : (2:ZMod p)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  apply htest A D0 D1 H.a H.b h0 h1 h2 H.nonzero
  · by_cases hHa : H.a=0
    · right
      obtain ⟨n,hn0,hnN,he,hne⟩ := seed
      have hHb := H.nonzero.resolve_left (not_not.mpr hHa)
      have hv := H.raw_agrees n ⟨hn0,hnN⟩ (by simpa [hHa] using hHb)
      simp only [zero_mul,zero_add] at hv
      have hncast : (n.toNat:ZMod p)=(n:ZMod p) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ZMod p)) (Int.toNat_of_nonneg hn0)
      exact ⟨⟨n.toNat,by omega⟩,by simpa only [hncast] using hv.symm.trans he,by simpa only [hncast] using hne⟩
    · exact Or.inl hHa
  · intro si nn hn20 hn2N hn10 hn1N hf0 hf1 hf2 hhx
    let s := step si
    have hs' : s=-2 ∨ s=-1 ∨ s=1 ∨ s=2 := by fin_cases si <;> simp [s,step]
    let n : Int := nn.val
    let x : ZMod p := nn.val
    have hncast : (n:ZMod p)=x := by simp [n,x]
    have bounds : 0≤n ∧ n<(wordWidth p:Nat) ∧ 0≤n-s ∧ n-s<(wordWidth p:Nat) ∧
        0≤n-2*s ∧ n-2*s<(wordWidth p:Nat) := by
      have hn := nn.isLt
      dsimp [n,s]
      exact ⟨by omega,by omega,hn10,hn1N,hn20,hn2N⟩
    let d : Int := h/s
    have hds : d*s=h := by
      rcases hh with rfl|rfl <;> fin_cases si <;> norm_num [d,s,step]
    let z0 := n-2*s
    let z1 := n-s
    let L := chooseLine hW d (q-d*z0)
    let l0 := L.a*(z0:ZMod p)+L.b
    let l1 := L.a*(z1:ZMod p)+L.b
    let l2 := L.a*(n:ZMod p)+L.b
    have he0 : d*z0+(q-d*z0)=q := by ring
    have he1 : d*z1+(q-d*z0)=q+h := by dsimp [z0,z1]; linear_combination hds
    have he2 : d*n+(q-d*z0)=q+2*h := by dsimp [z0]; linear_combination 2*hds
    have hl : l2-2*l1+l0=0 := by dsimp [l0,l1,l2,z0,z1]; push_cast; ring
    have hsnz : (s:ZMod p)≠0 := by
      fin_cases si <;> first | simpa [s,step] using htwo | simp [s,step]
    have hl01 : l0≠0 ∨ l1≠0 := by
      by_contra hz
      push Not at hz
      have he := affine_root_unique L.nonzero hz.1 hz.2
      apply hsnz
      dsimp [z0,z1] at he
      push_cast at he
      linear_combination -he
    have ha : l0≠0 → l0=A*(x-2*(s:ZMod p))+D0 := by
      intro hz
      have hr := row0 z0 bounds.2.2.2.2.1 bounds.2.2.2.2.2 (by simpa [z0,Int.cast_sub,Int.cast_mul,hncast] using hf0)
      have hd := L.raw_agrees z0 ⟨bounds.2.2.2.2.1,bounds.2.2.2.2.2⟩ hz
      rw [he0] at hd
      simpa [l0,z0,Int.cast_sub,Int.cast_mul,hncast] using hd.symm.trans hr
    have hb : l1≠0 → l1=A*(x-(s:ZMod p))+D1 := by
      intro hz
      have hr := row1 z1 bounds.2.2.1 bounds.2.2.2.1 (by simpa [z1,Int.cast_sub,hncast] using hf1)
      have hd := L.raw_agrees z1 ⟨bounds.2.2.1,bounds.2.2.2.1⟩ hz
      rw [he1] at hd
      simpa [l1,z1,Int.cast_sub,hncast] using hd.symm.trans hr
    have hc : l2≠0 → l2=H.a*x+H.b := by
      intro hz
      have hd := L.raw_agrees n ⟨bounds.1,bounds.2.1⟩ hz
      rw [he2] at hd
      have hr := H.raw_agrees n ⟨bounds.1,bounds.2.1⟩ (by simpa [hncast] using hhx)
      simp only [zero_mul,zero_add] at hr
      simpa [l2,hncast] using hd.symm.trans hr
    have hf : 2*(A*(x-(s:ZMod p))+D1)-(A*(x-2*(s:ZMod p))+D0)≠0 := by
      convert hf2 using 1 <;> ring
    have he := three_point_alternatives htwo l0 l1 l2 _ _ _ hl hl01 ha hb hc hf
    rcases he with he|he|he
    · left; convert he using 1 <;> ring
    · exact Or.inr (Or.inl (by simpa [x,s] using he))
    · exact Or.inr (Or.inr (by simpa [x,s] using he))


theorem mid_row {W : WordArray p} (hW : LineRule p W) (A B C : ZMod p) (q s : Int)
    (hs : s=1 ∨ s=2) (t : Nat) (ht : t=1 ∨ t=3) (htest : MidTest p t)
    (hknown : ∀ j : Fin 3, ∀ n : Int, 0≤n → n<(wordWidth p:Nat) →
      A*(n:ZMod p)+B*((q+s*(2*j.val):Int):ZMod p)+C≠0 →
      rawArray W n (q+s*(2*j.val))=A*(n:ZMod p)+B*((q+s*(2*j.val):Int):ZMod p)+C)
    (hnz : ∀ j : Fin 3, A≠0 ∨ B*((q+s*(2*j.val):Int):ZMod p)+C≠0) :
    ∀ n : Int, 0≤n → n<(wordWidth p:Nat) →
      A*(n:ZMod p)+B*((q+s*t:Int):ZMod p)+C=0 ∨
      rawArray W n (q+s*t)=A*(n:ZMod p)+B*((q+s*t:Int):ZMod p)+C := by
  letI : Fact p.Prime := ⟨hp⟩
  let D := B*(q:ZMod p)+C
  let B' := B*(s:ZMod p)
  by_cases hF : A=0 ∧ B'*t+D=0
  · intro n _ _
    left
    dsimp [B',D] at hF
    push_cast
    linear_combination hF.2+(n:ZMod p)*hF.1
  let H := chooseLine hW 0 (q+s*t)
  have hcoeff : H.a=A ∧ H.b=B'*t+D := by
    have hf := htest A B' D
    simp only [ZMod.natCast_zmod_val] at hf
    apply hf H.a H.b
    · intro j
      have he : B'*(2*j.val:ZMod p)+D=B*((q+s*(2*j.val):Int):ZMod p)+C := by
        dsimp [B',D]; push_cast; ring
      simpa only [he] using hnz j
    · tauto
    · exact H.nonzero
    · intro zi xx hxs hxt0 hxtN
      let z := sign zi
      have hz' : z=1 ∨ z=-1 := by fin_cases zi <;> simp [z,sign]
      let x' : Int := xx.val
      have hxc : (x':ZMod p)=(xx.val:ZMod p) := by simp [x']
      let d := z*s
      let L := chooseLine hW d (q-d*x')
      refine ⟨L.a,L.b,L.nonzero,?_,?_⟩
      · intro j hnzL hnzF
        let n : Int := x'+z*(2*j.val)
        have hn : 0≤n ∧ n<(wordWidth p:Nat) := by
          exact hxs j
        have he : d*n+(q-d*x')=q+s*(2*j.val) := by
          fin_cases zi <;> dsimp [n,d,z,sign] <;> ring
        have hL := L.raw_agrees n hn (by simpa [n,Int.cast_add,Int.cast_mul,hxc] using hnzL)
        rw [he] at hL
        have hK := hknown j n hn.1 hn.2 (by
          convert hnzF using 1 <;> dsimp [n,B',D] <;> push_cast <;> rw [hxc] <;> ring)
        convert hL.symm.trans hK using 1 <;> dsimp [n,B',D] <;> push_cast <;> rw [hxc] <;> ring
      · let n : Int := x'+z*t
        intro hnzL hnzH
        have hn : 0≤n ∧ n<(wordWidth p:Nat) := by
          exact ⟨hxt0,hxtN⟩
        have he : d*n+(q-d*x')=q+s*t := by
          fin_cases zi <;> dsimp [n,d,z,sign] <;> ring
        have hL := L.raw_agrees n hn (by simpa [n,Int.cast_add,Int.cast_mul,hxc] using hnzL)
        rw [he] at hL
        have hH := H.raw_agrees n hn (by simpa [n,Int.cast_add,Int.cast_mul,hxc] using hnzH)
        simp only [zero_mul,zero_add] at hH
        simpa [n,Int.cast_add,Int.cast_mul,hxc] using hL.symm.trans hH
  intro n hn0 hnN
  by_cases hf : A*(n:ZMod p)+B*((q+s*t:Int):ZMod p)+C=0
  · exact Or.inl hf
  right
  have he : A*(n:ZMod p)+B*((q+s*t:Int):ZMod p)+C=H.a*(n:ZMod p)+H.b := by
    rw [hcoeff.1,hcoeff.2]; dsimp [B',D]; push_cast; ring
  have hval := H.raw_agrees n ⟨hn0,hnN⟩ (by rw [←he]; exact hf)
  simpa [←he] using hval


def Good {p : Nat} (W : WordArray p) (A B C : ZMod p) (n m : Int) : Prop :=
  A*(n:ZMod p)+B*(m:ZMod p)+C=0 ∨ rawArray W n m=A*(n:ZMod p)+B*(m:ZMod p)+C

def KnownRows {p : Nat} (W : WordArray p) (A B C : ZMod p) (q h : Int) : Prop :=
  ∀ j : Fin 3, ∀ n : Int, 0≤n → n<(wordWidth p:Nat) → Good W A B C n (q+h*j.val)
def NonzeroRows {p : Nat} (A B C : ZMod p) (q h : Int) : Prop :=
  ∀ j : Fin 3, A≠0 ∨ B*((q+h*j.val:Int):ZMod p)+C≠0

theorem four_rows_of_two_spaced {W : WordArray p} (hW : LineRule p W)
    (htest1 : MidTest p 1) (htest3 : MidTest p 3) (A B C : ZMod p) (q : Int)
    (hknown : KnownRows W A B C q 2) (hnz : NonzeroRows A B C q 2) :
    FourGoodRows (wordWidth p:Nat) (Good W A B C) q := by
  have mid (t : Nat) (ht : t=1 ∨ t=3) : ∀ n : Int, 0≤n → n<(wordWidth p:Nat) → Good W A B C n (q+t) := by
    have htest : MidTest p t := by
      rcases ht with rfl|rfl
      · exact htest1
      · exact htest3
    have hk : ∀ j : Fin 3, ∀ n : Int, 0≤n → n<(wordWidth p:Nat) →
        A*(n:ZMod p)+B*((q+1*(2*j.val):Int):ZMod p)+C≠0 →
        rawArray W n (q+1*(2*j.val))=A*(n:ZMod p)+B*((q+1*(2*j.val):Int):ZMod p)+C := by
      intro j n hn0 hnN hn
      simpa only [one_mul] using (hknown j n hn0 hnN).resolve_left (by simpa using hn)
    have hz : ∀ j : Fin 3, A≠0 ∨ B*((q+1*(2*j.val):Int):ZMod p)+C≠0 := by
      simpa [NonzeroRows] using hnz
    simpa only [one_mul,Good] using mid_row hp hlarge hW A B C q 1 (Or.inl rfl) t ht htest hk hz
  intro m hm0 hm3 n hn0 hnN
  have ht : m=q ∨ m=q+1 ∨ m=q+2 ∨ m=q+3 := by omega
  rcases ht with rfl|rfl|rfl|rfl
  · simpa using hknown 0 n hn0 hnN
  · exact mid 1 (Or.inl rfl) n hn0 hnN
  · simpa using hknown 1 n hn0 hnN
  · exact mid 3 (Or.inr rfl) n hn0 hnN

theorem four_rows_of_spaced {W : WordArray p} (hW : LineRule p W)
    (htest1 : MidTest p 1) (htest3 : MidTest p 3) (A B C : ZMod p) (q h : Int)
    (hh : h=2 ∨ h=4) (hknown : KnownRows W A B C q h) (hnz : NonzeroRows A B C q h) :
    ∃ q' : Int, FourGoodRows (wordWidth p:Nat) (Good W A B C) q' := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hh with rfl|rfl
  · exact ⟨q,four_rows_of_two_spaced hp hlarge hW htest1 htest3 A B C q hknown hnz⟩
  have even (t : Nat) (ht : t=1 ∨ t=3) : ∀ n : Int, 0≤n → n<(wordWidth p:Nat) → Good W A B C n (q+2*t) := by
    apply mid_row hp hlarge hW A B C q 2 (Or.inr rfl) t ht
    · rcases ht with rfl|rfl
      · exact htest1
      · exact htest3
    · intro j n hn0 hnN hn
      have hj : 2*(2*(j.val:Int))=4*j.val := by ring
      rw [hj] at hn ⊢
      exact (hknown j n hn0 hnN).resolve_left hn
    · intro j
      simpa only [show (2:Int)*(2*j.val)=4*j.val by ring] using hnz j
  have hr2 := even 1 (Or.inl rfl)
  have hr6 := even 3 (Or.inr rfl)
  by_cases hn2 : A≠0 ∨ B*((q+2:Int):ZMod p)+C≠0
  · refine ⟨q,four_rows_of_two_spaced hp hlarge hW htest1 htest3 A B C q ?_ ?_⟩
    · intro j n hn0 hnN
      fin_cases j
      · simpa using hknown 0 n hn0 hnN
      · simpa using hr2 n hn0 hnN
      · simpa using hknown 1 n hn0 hnN
    · intro j
      fin_cases j
      · simpa using hnz 0
      · simpa using hn2
      · simpa using hnz 1
  · have hn6 : A≠0 ∨ B*((q+6:Int):ZMod p)+C≠0 := by
      push Not at hn2
      right
      intro hz
      have hn4 := (hnz 1).resolve_left (not_not.mpr hn2.1)
      apply hn4
      have htwo : (2:ZMod p)≠0 := by
        intro hz
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
      have he : (2:ZMod p)*(B*((q+4:Int):ZMod p)+C)=0 := by
        push_cast at hn2 hz ⊢
        linear_combination hn2.2+hz
      simpa using (mul_eq_zero.mp he).resolve_left htwo
    refine ⟨q+4,four_rows_of_two_spaced hp hlarge hW htest1 htest3 A B C (q+4) ?_ ?_⟩
    · intro j n hn0 hnN
      fin_cases j
      · simpa using hknown 1 n hn0 hnN
      · simpa [add_assoc] using hr6 n hn0 hnN
      · simpa [add_assoc] using hknown 2 n hn0 hnN
    · intro j
      fin_cases j
      · simpa using hnz 1
      · simpa [add_assoc] using hn6
      · simpa [add_assoc] using hnz 2
end
end TranslationTiling.Sudoku.ShortRule.Seed
