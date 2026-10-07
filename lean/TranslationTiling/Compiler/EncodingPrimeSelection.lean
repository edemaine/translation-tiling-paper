/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.EncodingParameters
import TranslationTiling.Proofs.ComputableSearch
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose

set_option maxRecDepth 1000

namespace TranslationTiling

universe uι

noncomputable section

namespace Compiler
namespace EncodingPrimeSelection

private def nextPrime (bound : ℕ) : ℕ :=
  primeAbove (bound + 1)

private theorem nextPrime_prime (bound : ℕ) : Nat.Prime (nextPrime bound) :=
  (primeAbove_spec (bound + 1)).1

private theorem nextPrime_gt (bound : ℕ) : bound < nextPrime bound := by
  have h := (primeAbove_spec (bound + 1)).2
  exact h

def primeSequence (bound : ℕ) : ℕ → ℕ
  | 0 => nextPrime bound
  | n + 1 => nextPrime (primeSequence bound n)

theorem primeSequence_computable :
    Computable (fun z : ℕ × ℕ => primeSequence z.1 z.2) := by
  have hp : Computable (fun z : ℕ × ℕ => Nat.rec (motive := fun _ => ℕ) (nextPrime z.1)
      (fun _ r => nextPrime r) z.2) := by
    apply Computable.nat_rec (g := fun z : ℕ × ℕ => nextPrime z.1)
      (h := fun (_ : ℕ × ℕ) (z : ℕ × ℕ) => nextPrime z.2) Computable.snd
    · exact primeAbove_computable.comp
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)).to_comp
    · exact (primeAbove_computable.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)).to_comp).to₂
  apply hp.of_eq
  intro z
  induction z.2 with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, primeSequence] using congrArg nextPrime ih

theorem primeSequence_strictMono (bound : ℕ) :
    StrictMono (primeSequence bound) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact nextPrime_gt _

theorem primeSequence_prime (bound n : ℕ) :
    Nat.Prime (primeSequence bound n) := by
  cases n with
  | zero => exact nextPrime_prime _
  | succ n => exact nextPrime_prime _

theorem primeSequence_gt (bound n : ℕ) : bound < primeSequence bound n :=
  lt_of_lt_of_le (nextPrime_gt bound)
    ((primeSequence_strictMono bound).monotone (Nat.zero_le n))

theorem exists_prime_family (ι : Type uι) [Fintype ι] (bound : ℕ) :
    ∃ f : ι → ℕ, Function.Injective f ∧
      ∀ i, Nat.Prime (f i) ∧ bound < f i := by
  let e := Fintype.equivFin ι
  refine ⟨fun i => primeSequence bound (e i).val, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Fin.ext
    exact (primeSequence_strictMono bound).injective hij
  · intro i
    exact ⟨primeSequence_prime _ _, primeSequence_gt _ _⟩

theorem exists_positive_combination {a b r : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : 1 < b) (hr : a * b + a + b < r) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ r = A * a + B * b := by
  have hmem : r - a - b ∈ AddSubmonoid.closure ({a, b} : Set ℕ) := by
    by_contra hnot
    have hle := (frobeniusNumber_pair hab ha hb).2 hnot
    have hbound : a * b - a - b ≤ a * b :=
      (Nat.sub_le (a * b - a) b).trans (Nat.sub_le (a * b) a)
    omega
  obtain ⟨A, B, hAB⟩ := (AddSubmonoid.mem_closure_pair a b (r - a - b)).mp hmem
  simp only [smul_eq_mul] at hAB
  refine ⟨A + 1, B + 1, by omega, by omega, ?_⟩
  calc
    r = (r - a - b) + a + b := by omega
    _ = (A * a + B * b) + a + b := by rw [hAB]
    _ = (A + 1) * a + (B + 1) * b := by ring

private abbrev UsefulTag (T : LeanWang.TileSet) := Channel T ⊕ Channel T
private abbrev FreshUsefulTag (T : LeanWang.TileSet) := Column T ⊕ Channel T
private abbrev DigitTag (T : LeanWang.TileSet) := Σ i, Label T i

private def usefulTagEquiv (T : LeanWang.TileSet) :
    UsefulTag T ≃ Fin 2 ⊕ FreshUsefulTag T :=
  (Equiv.sumCongr (Equiv.sumComm (Column T) (Fin 2))
    (Equiv.refl (Channel T))).trans (Equiv.sumAssoc (Fin 2) (Column T) (Channel T))

private def usefulPrime {T : LeanWang.TileSet} (f : FreshUsefulTag T → ℕ) : UsefulTag T → ℕ :=
  Sum.elim (fun t : Fin 2 => t.val + 2) f ∘ usefulTagEquiv T

private theorem usefulPrime_injective {T : LeanWang.TileSet} {f : FreshUsefulTag T → ℕ}
    (hf : Function.Injective f) (hlarge : ∀ t, 3 < f t) :
    Function.Injective (usefulPrime f) := by
  have hseed : Function.Injective (fun t : Fin 2 => t.val + 2) := by
    intro t u htu
    apply Fin.ext
    change t.val + 2 = u.val + 2 at htu
    exact Nat.add_right_cancel htu
  have hsep : ∀ t : Fin 2, ∀ i, t.val + 2 ≠ f i := by
    intro t i heq
    have ht := t.isLt
    have hi := hlarge i
    omega
  exact (hseed.sumElim hf hsep).comp (usefulTagEquiv T).injective

private theorem usefulPrime_prime {T : LeanWang.TileSet} {f : FreshUsefulTag T → ℕ}
    (hf : ∀ i, Nat.Prime (f i)) (i : UsefulTag T) :
    Nat.Prime (usefulPrime f i) := by
  rcases i with (i | t) | i
  · exact hf (.inl i)
  · change Nat.Prime (t.val + 2)
    fin_cases t
    · exact Nat.prime_two
    · exact Nat.prime_three
  · exact hf (.inr i)

private def attachDigits {T : LeanWang.TileSet} (f : UsefulTag T → ℕ) (g : DigitTag T → ℕ) :
    PrimeTag T → ℕ :=
  Sum.elim f g ∘ (Equiv.sumAssoc (Channel T) (Channel T) (DigitTag T)).symm

private theorem attachDigits_injective {T : LeanWang.TileSet}
    {f : UsefulTag T → ℕ} {g : DigitTag T → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hsep : ∀ i j, f i ≠ g j) : Function.Injective (attachDigits f g) :=
  (hf.sumElim hg hsep).comp
    (Equiv.sumAssoc (Channel T) (Channel T) (DigitTag T)).symm.injective

theorem exists_parameters (T : LeanWang.TileSet) :
    Nonempty (EncodingParameters T) := by
  classical
  obtain ⟨f, hfinj, hf⟩ := exists_prime_family (FreshUsefulTag T) ((Sudoku.Width ^ 2) + Sudoku.p + Sudoku.q + 3)
  let useful : UsefulTag T → ℕ := usefulPrime f
  have huseful_prime : ∀ i, Nat.Prime (useful i) :=
    usefulPrime_prime (fun i => (hf i).1)
  have huseful_inj : Function.Injective useful := by
    apply usefulPrime_injective hfinj
    intro i
    have := (hf i).2
    omega
  have huseful_ne (v : ℕ) (hv : v = Sudoku.p ∨ v = Sudoku.q) :
      ∀ i, useful i ≠ v := by
    intro i
    have hvlarge : 200 < v := by rcases hv with rfl | rfl <;> decide
    have hvbound : v ≤ Sudoku.p + Sudoku.q := by
      rcases hv with rfl | rfl <;> omega
    rcases i with (i | t) | i
    · change f (.inl i) ≠ v
      have := (hf (.inl i)).2
      omega
    · change t.val + 2 ≠ v
      have := t.isLt
      omega
    · change f (.inr i) ≠ v
      have := (hf (.inr i)).2
      omega
  let threshold : Channel T → ℕ := fun i =>
    useful (.inl i) * useful (.inr i) + useful (.inl i) + useful (.inr i)
  let bound := Sudoku.p + Sudoku.q + Finset.univ.sup useful + Finset.univ.sup threshold
  obtain ⟨g, hginj, hg⟩ := exists_prime_family (DigitTag T) bound
  have hseparate : ∀ i j, useful i < g j := by
    intro i j
    have hi : useful i ≤ Finset.univ.sup useful := Finset.le_sup (Finset.mem_univ i)
    have hj := (hg j).2
    dsimp [bound] at hj
    omega
  have hthreshold : ∀ i j, threshold i < g ⟨i, j⟩ := by
    intro i j
    have hi : threshold i ≤ Finset.univ.sup threshold :=
      Finset.le_sup (Finset.mem_univ i)
    have hj := (hg ⟨i, j⟩).2
    dsimp [bound] at hj
    omega
  have hrepresentation : ∀ i (j : Label T i), ∃ A B : ℕ,
      0 < A ∧ 0 < B ∧ g ⟨i, j⟩ = A * useful (.inl i) + B * useful (.inr i) := by
    intro i j
    have hcop : Nat.Coprime (useful (.inl i)) (useful (.inr i)) := by
      apply (Nat.coprime_primes (huseful_prime _) (huseful_prime _)).2
      intro h
      have htags := huseful_inj h
      cases htags
    exact exists_positive_combination hcop
      (huseful_prime _).one_lt (huseful_prime _).one_lt (hthreshold i j)
  choose A B hA hB hrepresentation using hrepresentation
  refine ⟨{
    primeAt := attachDigits useful g
    prime_isPrime := ?_
    prime_injective := attachDigits_injective huseful_inj hginj
      (fun i j => (hseparate i j).ne)
    prime_ne_p := ?_
    prime_ne_q := ?_
    seed_a_eq := ?_
    seed_b_large := ?_
    blockA := A
    blockB := B
    blockA_pos := hA
    blockB_pos := hB
    digit_representation := ?_
    digitProduct := fun i => ∏ j : Label T i, g ⟨i, j⟩
    digitProduct_eq := fun _ => rfl
  }⟩
  · intro t
    rcases t with i | (i | j)
    · exact huseful_prime (.inl i)
    · exact huseful_prime (.inr i)
    · exact (hg j).1
  · intro t
    rcases t with i | (i | j)
    · exact huseful_ne Sudoku.p (Or.inl rfl) (.inl i)
    · exact huseful_ne Sudoku.p (Or.inl rfl) (.inr i)
    · change g j ≠ Sudoku.p
      have hj := (hg j).2
      dsimp [bound] at hj
      omega
  · intro t
    rcases t with i | (i | j)
    · exact huseful_ne Sudoku.q (Or.inr rfl) (.inl i)
    · exact huseful_ne Sudoku.q (Or.inr rfl) (.inr i)
    · change g j ≠ Sudoku.q
      have hj := (hg j).2
      dsimp [bound] at hj
      omega
  · intro t
    rfl
  · intro t
    change (Sudoku.Width ^ 2) < f (.inr (.inr t))
    have ht := (hf (.inr (.inr t))).2
    omega
  · intro i j
    exact hrepresentation i j

end EncodingPrimeSelection

theorem exists_encodingParameters (T : LeanWang.TileSet) :
    Nonempty (EncodingParameters T) :=
  EncodingPrimeSelection.exists_parameters T

noncomputable def encodingParameters (T : LeanWang.TileSet) : EncodingParameters T :=
  Classical.choice (exists_encodingParameters T)

end Compiler

end

end TranslationTiling
