import TranslationTiling.SudokuArithmetic.ShortArithmetic
import TranslationTiling.SudokuArithmetic.Soundness

/-! The word rule with Wang decorations retained only at columns 1, 5, 7. -/
namespace TranslationTiling.Sudoku.ShortBoard
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev PColumn := ShortArithmetic.Column 5
abbrev QColumn := ShortArithmetic.Column 7
abbrev TileColumn := Fin 3

def position (i : TileColumn) : ℕ := ![1,5,7] i

def pPosition (i : TileColumn) : PColumn :=
  ⟨position i, by fin_cases i <;> decide⟩
def qPosition (i : TileColumn) : QColumn :=
  ⟨position i, by fin_cases i <;> decide⟩

def originalP (n : PColumn) : Sudoku.Column :=
  ⟨ShortArithmetic.position 5 n,by fin_cases n <;> decide⟩
def originalQ (n : QColumn) : Sudoku.Column :=
  ⟨ShortArithmetic.position 7 n,by fin_cases n <;> decide⟩
def originalC (n : TileColumn) : Sudoku.Column := ⟨position n,by fin_cases n <;> decide⟩

structure Board (T : LeanWang.TileSet) where
  p : PColumn → ℤ → (ZMod 5)ˣ
  q : QColumn → ℤ → (ZMod 7)ˣ
  tile : TileColumn → ℤ → LeanWang.TileIn T

def Allowed (T : LeanWang.TileSet)
    (P : PColumn → (ZMod 5)ˣ) (Q : QColumn → (ZMod 7)ˣ)
    (C : TileColumn → LeanWang.TileIn T) : Prop :=
  ∃ a b : ℤ, (¬ (5:ℤ) ∣ a ∨ ¬ (5:ℤ) ∣ b) ∧
    (¬ (7:ℤ) ∣ a ∨ ¬ (7:ℤ) ∣ b) ∧
    ∃ σ : Fin (threshold 5 a+1) → Fin (threshold 7 a+1) → LeanWang.TileIn T,
      ValidRectangle T _ _ σ ∧
      (∀ n u, lowValuation 5 (a*ShortArithmetic.position 5 n+b)=some u → u≤threshold 5 a →
        (P n).val=lowDigit 5 (a*ShortArithmetic.position 5 n+b)) ∧
      (∀ n v, lowValuation 7 (a*ShortArithmetic.position 7 n+b)=some v → v≤threshold 7 a →
        (Q n).val=lowDigit 7 (a*ShortArithmetic.position 7 n+b)) ∧
      ∀ n u v, lowValuation 5 (a*position n+b)=some u →
        lowValuation 7 (a*position n+b)=some v →
        ∀ (hu : u≤threshold 5 a) (hv : v≤threshold 7 a),
          C n=σ ⟨u,Nat.lt_succ_iff.mpr hu⟩ ⟨v,Nat.lt_succ_iff.mpr hv⟩

def LineRule {T : LeanWang.TileSet} (W : Board T) : Prop :=
  ∀ d e : ℤ, Allowed T (fun n => W.p n (d*ShortArithmetic.position 5 n+e))
    (fun n => W.q n (d*ShortArithmetic.position 7 n+e)) (fun n => W.tile n (d*position n+e))

def Nonconstant {T : LeanWang.TileSet} (W : Board T) : Prop :=
  (∀ n, ∃ m m', W.p n m≠W.p n m') ∧
    (∀ n, ∃ m m', W.q n m≠W.q n m')

theorem arithmetic_p {T : LeanWang.TileSet} {W : Board T} (hW : LineRule W) :
    ShortArithmetic.ArithmeticLineRule 5 W.p := by
  intro d e
  obtain ⟨a,b,hp,_,σ,_,ht,_,_⟩ := hW d e
  exact ⟨a,b,hp,ht⟩

theorem arithmetic_q {T : LeanWang.TileSet} {W : Board T} (hW : LineRule W) :
    ShortArithmetic.ArithmeticLineRule 7 W.q := by
  intro d e
  obtain ⟨a,b,_,hq,σ,_,_,ht,_⟩ := hW d e
  exact ⟨a,b,hq,ht⟩

def reparametrize {T : LeanWang.TileSet} (W : Board T) (a D E : ℤ) : Board T where
  p n m := W.p n (a*m+D*ShortArithmetic.position 5 n+E)
  q n m := W.q n (a*m+D*ShortArithmetic.position 7 n+E)
  tile n m := W.tile n (a*m+D*position n+E)

theorem reparametrize_lineRule {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) (a D E : ℤ) : LineRule (reparametrize W a D E) := by
  intro d e
  convert hW (a*d+D) (a*e+E) using 1 <;>
    first | (funext n; dsimp [reparametrize]; congr 1; ring) | rfl

/-- Independent arithmetic boards admit one common shear at every finite depth. -/
theorem finite_structure {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) (hc : Nonconstant W) (k l : ℕ) :
    ∃ (D E : ℤ) (Bp : ZMod 5) (Bq : ZMod 7), Bp≠0 ∧ Bq≠0 ∧
      (∀ n m, m≠0 → padicValInt 5 m≤k →
        ((reparametrize W 1 D E).p n m).val=Bp*(lastDigit 5 (by decide) m).val) ∧
      (∀ n m, m≠0 → padicValInt 7 m≤l →
        ((reparametrize W 1 D E).q n m).val=Bq*(lastDigit 7 (by decide) m).val) := by
  obtain ⟨Dp,Ep,Bp,hBp,hp⟩ := ShortArithmetic.arithmetic_finite_structure
    (by decide : Nat.Prime 5) (by decide) (by decide) _ (arithmetic_p hW) hc.1 k
  obtain ⟨Dq,Eq,Bq,hBq,hq⟩ := ShortArithmetic.arithmetic_finite_structure
    (by decide : Nat.Prime 7) (by decide) (by decide) _ (arithmetic_q hW) hc.2 l
  obtain ⟨D,hDp,hDq⟩ := exists_twoPrime_power_residue (k+1) (l+1) Dp Dq
  obtain ⟨E,hEp,hEq⟩ := exists_twoPrime_power_residue (k+1) (l+1) Ep Eq
  have affine_congr (r K : ℕ) (Dr Er : ℤ)
      (hD : (r:ℤ)^K ∣ D-Dr) (hE : (r:ℤ)^K ∣ E-Er) (n m : ℤ) :
      (r:ℤ)^K ∣ (m+D*n+E-Dr*n-Er)-m := by
    rw [show (m+D*n+E-Dr*n-Er)-m=(D-Dr)*n+(E-Er) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hD n) hE
  refine ⟨D,E,Bp,Bq,hBp,hBq,?_,?_⟩
  · intro n m hm hv
    obtain ⟨hnz,hval,hdigit⟩ := digit_congr_bounded 5 (by decide) k hm hv
      (affine_congr 5 (k+1) Dp Ep hDp hEp (ShortArithmetic.position 5 n) m)
    have hh := hp n (m+D*ShortArithmetic.position 5 n+E) hnz (by rwa [hval])
    simpa only [reparametrize,one_mul,hdigit] using hh
  · intro n m hm hv
    obtain ⟨hnz,hval,hdigit⟩ := digit_congr_bounded 7 (by decide) l hm hv
      (affine_congr 7 (l+1) Dq Eq hDq hEq (ShortArithmetic.position 7 n) m)
    have hh := hq n (m+D*ShortArithmetic.position 7 n+E) hnz (by rwa [hval])
    simpa only [reparametrize,one_mul,hdigit] using hh

def restrict {T : LeanWang.TileSet} (W : Array T) : Board T where
  p n m := (W (originalP n) m).1
  q n m := (W (originalQ n) m).2.1
  tile n m := (W (originalC n) m).2.2

theorem restrict_lineRule {T : LeanWang.TileSet} {W : Array T}
    (hW : Sudoku.LineRule W) : LineRule (restrict W) := by
  intro d e
  obtain ⟨a,b,hp,hq,σ,hσ,ht⟩ := hW d e
  refine ⟨a,b,hp,hq,σ,hσ,?_,?_,?_⟩
  · intro n u hu hs
    exact (ht (originalP n)).1 u hu hs
  · intro n v hv hs
    exact (ht (originalQ n)).2.1 v hv hs
  · intro n u v hu hv hs ht'
    exact (ht (originalC n)).2.2 u v hu hv hs ht'

end
end TranslationTiling.Sudoku.ShortBoard
