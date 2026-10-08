import TranslationTiling.SudokuArithmetic.InitialStructure
import TranslationTiling.Proofs.WordResidues

/-! Affine changes of height preserve the decorated rule. -/

namespace TranslationTiling.Sudoku

def reparametrize {T : LeanWang.TileSet} (W : Array T) (a u v : ℤ) : Array T :=
  fun n m => W n (a * m + u * n.val + v)

theorem reparametrize_lineRule {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) (a u v : ℤ) : LineRule (reparametrize W a u v) := by
  intro d e
  have he : (fun n => reparametrize W a u v n (d * n.val + e)) =
      (fun n => W n ((a * d + u) * n.val + (a * e + v))) := by
    funext n
    unfold reparametrize
    congr 1
    ring
  rw [he]
  exact hW (a * d + u) (a * e + v)

theorem reparametrize_one_nonconstant {T : LeanWang.TileSet} {W : Array T}
    (hcols : NonconstantColumns W) (u v : ℤ) :
    NonconstantColumns (reparametrize W 1 u v) := by
  constructor
  · intro n
    obtain ⟨m, m', hm⟩ := hcols.1 n
    refine ⟨m - u * n.val - v, m' - u * n.val - v, ?_⟩
    have hh (z : ℤ) : z - u * n.val - v + u * n.val + v = z := by ring
    simpa only [reparametrize, one_mul, hh] using hm
  · intro n
    obtain ⟨m, m', hm⟩ := hcols.2 n
    refine ⟨m - u * n.val - v, m' - u * n.val - v, ?_⟩
    have hh (z : ℤ) : z - u * n.val - v + u * n.val + v = z := by ring
    simpa only [reparametrize, one_mul, hh] using hm

def arithmeticReparametrize {r : ℕ} (V : Column → ℤ → (ZMod r)ˣ)
    (a u v : ℤ) : Column → ℤ → (ZMod r)ˣ :=
  fun n m => V n (a * m + u * n.val + v)

theorem arithmeticReparametrize_lineRule {r : ℕ} {V : Column → ℤ → (ZMod r)ˣ}
    (hV : ArithmeticLineRule r V) (a u v : ℤ) :
    ArithmeticLineRule r (arithmeticReparametrize V a u v) := by
  intro d e
  obtain ⟨b, c, hbc, ht⟩ := hV (a * d + u) (a * e + v)
  refine ⟨b, c, hbc, ?_⟩
  intro n t hn hs
  have he : a * (d * (n.val : ℤ) + e) + u * n.val + v =
      (a * d + u) * n.val + (a * e + v) := by ring
  simpa only [arithmeticReparametrize, he] using ht n t hn hs

theorem FullAffineApproximation.reparametrize {r : ℕ} {V : Column → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (hp : r.Prime) (hH : FullAffineApproximation V A B C) (a u v : ℤ)
    (hB : B ≠ 0) (ha : (a : ZMod r) ≠ 0) :
    FullAffineApproximation (arithmeticReparametrize V a u v)
      (A + B * (u : ZMod r)) (B * (a : ZMod r)) (C + B * (v : ZMod r)) := by
  let : Fact r.Prime := ⟨hp⟩
  refine ⟨Or.inr (Or.inl (mul_ne_zero hB ha)), ?_⟩
  intro n m hm
  have he : A * (n.val : ZMod r) + B * ((a * m + u * n.val + v : ℤ) : ZMod r) + C =
      (A + B * (u : ZMod r)) * n.val + (B * (a : ZMod r)) * (m : ZMod r) +
        (C + B * (v : ZMod r)) := by
    push_cast
    ring
  exact (hH.2 n _ (by rwa [he])).trans he

theorem SqCongr.cast_eq {r : ℕ} {x y : ℤ} (h : SqCongr r x y) :
    (x : ZMod r) = (y : ZMod r) := by
  apply sub_eq_zero.mp
  rw [← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((dvd_pow_self (r : ℤ) (by decide : 2 ≠ 0)).trans h)

end TranslationTiling.Sudoku
