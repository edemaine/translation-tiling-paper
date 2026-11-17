import TranslationTiling.SudokuArithmetic.FivePointCandidates
import TranslationTiling.SudokuArithmetic.SixPointRecovery

namespace TranslationTiling.Sudoku.ArithmeticRule
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem third_row_candidate {p : ℕ} (hp : p.Prime) (hlarge : 10<p)
    {W : WordArray p} (hW : LineRule p W) (A D0 D1 : ZMod p) (q s : ℤ)
    (hs : s=1 ∨ s=2)
    (h0 : A≠0 ∨ D0≠0) (h1 : A≠0 ∨ D1≠0) (h2 : A≠0 ∨ 2*D1-D0≠0)
    (row0 : ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) → A*(n:ZMod p)+D0≠0 →
      rawArray W n q=A*(n:ZMod p)+D0)
    (row1 : ∀ n : ℤ, 0≤n → n<(wordWidth p:ℕ) → A*(n:ZMod p)+D1≠0 →
      rawArray W n (q+6)=A*(n:ZMod p)+D1) :
    RowCandidate A D0 D1 (chooseLine hW 0 (q+12)).a (chooseLine hW 0 (q+12)).b (s:ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  let H := chooseLine hW 0 (q+12)
  let x : Fin 8→ZMod p := fun i => ((4+(i.val:ℤ):ℤ):ZMod p)
  have hinj : Function.Injective x := by
    intro i j he
    have hh : (i.val:ZMod p)=(j.val:ZMod p) := by simpa only [x,Int.cast_add,Int.cast_ofNat,Int.cast_natCast,add_right_inj] using he
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega),
      ZMod.val_natCast_of_lt (by have := j.isLt; omega)] at hv
    exact Fin.ext hv
  apply row_candidate_of_values x hinj A D0 D1 H.a H.b (s:ZMod p) h0 h1 h2 H.nonzero
  intro i hf0 hf1 hf2 hh
  let n : ℤ := 4+i.val
  let z0 : ℤ := n-2*s
  let z1 : ℤ := n-s
  let d : ℤ := if s=1 then 6 else 3
  have hds : d*s=6 := by rcases hs with rfl | rfl <;> norm_num [d]
  have hsnz : (s:ZMod p)≠0 := by
    rcases hs with rfl | rfl
    · norm_num
    · intro hz
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) hd
  have hn : 0≤n ∧ n<(wordWidth p:ℕ) := by have hi := i.isLt; dsimp [n,wordWidth]; omega
  have hn0 : 0≤z0 ∧ z0<(wordWidth p:ℕ) := by
    have hi := i.isLt; rcases hs with hs | hs <;> dsimp [z0,n,wordWidth] <;> rw [hs] <;> omega
  have hn1 : 0≤z1 ∧ z1<(wordWidth p:ℕ) := by
    have hi := i.isLt; rcases hs with hs | hs <;> dsimp [z1,n,wordWidth] <;> rw [hs] <;> omega
  let L := chooseLine hW d (q-d*z0)
  let l0 : ZMod p := L.a*(z0:ZMod p)+L.b
  let l1 : ZMod p := L.a*(z1:ZMod p)+L.b
  let l2 : ZMod p := L.a*(n:ZMod p)+L.b
  have he0 : d*z0+(q-d*z0)=q := by ring
  have he1 : d*z1+(q-d*z0)=q+6 := by dsimp [z0,z1]; linear_combination hds
  have he2 : d*n+(q-d*z0)=q+12 := by dsimp [z0]; linear_combination 2*hds
  have hl : l2-2*l1+l0=0 := by dsimp [l0,l1,l2,z0,z1]; push_cast; ring
  have hl01 : l0≠0 ∨ l1≠0 := by
    by_contra hz
    push_neg at hz
    have he := affine_root_unique L.nonzero hz.1 hz.2
    apply hsnz
    dsimp [z0,z1] at he
    push_cast at he
    linear_combination -he
  have ha : l0≠0 → l0=A*(x i-2*(s:ZMod p))+D0 := by
    intro hz
    have hv := L.raw_agrees z0 hn0 hz
    rw [he0] at hv
    have hf : A*(z0:ZMod p)+D0≠0 := by simpa [z0,n,x,Int.cast_sub,Int.cast_mul] using hf0
    have hr := row0 z0 hn0.1 hn0.2 hf
    calc
      l0 = rawArray W z0 q := hv.symm
      _ = A*(z0:ZMod p)+D0 := hr
      _ = _ := by dsimp [z0,n,x]; push_cast; ring
  have hb : l1≠0 → l1=A*(x i-(s:ZMod p))+D1 := by
    intro hz
    have hv := L.raw_agrees z1 hn1 hz
    rw [he1] at hv
    have hf : A*(z1:ZMod p)+D1≠0 := by simpa [z1,n,x,Int.cast_sub] using hf1
    have hr := row1 z1 hn1.1 hn1.2 hf
    calc
      l1 = rawArray W z1 (q+6) := hv.symm
      _ = A*(z1:ZMod p)+D1 := hr
      _ = _ := by dsimp [z1,n,x]; push_cast; ring
  have hc : l2≠0 → l2=H.a*x i+H.b := by
    intro hz
    have hv := L.raw_agrees n hn hz
    rw [he2] at hv
    have hh' : H.a*(n:ZMod p)+H.b≠0 := by simpa [n,x] using hh
    have hr := H.raw_agrees n hn hh'
    simp only [zero_mul,zero_add] at hr
    exact hv.symm.trans hr
  have hf : 2*(A*(x i-(s:ZMod p))+D1)-(A*(x i-2*(s:ZMod p))+D0)≠0 := by
    convert hf2 using 1 <;> ring
  have htwo : (2:ZMod p)≠0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) hd
  have hh' := three_point_alternatives htwo l0 l1 l2 _ _ _ hl hl01 ha hb hc hf
  rcases hh' with he | he | he
  · left; convert he using 1 <;> ring
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

end
end TranslationTiling.Sudoku.ArithmeticRule
