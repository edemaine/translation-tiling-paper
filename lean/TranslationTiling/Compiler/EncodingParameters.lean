/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.Symbols
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option maxRecDepth 1000

namespace TranslationTiling

namespace Compiler

open scoped BigOperators

abbrev PrimeTag (T : LeanWang.TileSet) :=
  Channel T ⊕ (Channel T ⊕ (Σ i : Channel T, Label T i))

structure EncodingParameters (T : LeanWang.TileSet) where
  primeAt : PrimeTag T → ℕ
  prime_isPrime : ∀ t, Nat.Prime (primeAt t)
  prime_injective : Function.Injective primeAt
  prime_ne_p : ∀ t, primeAt t ≠ Sudoku.p
  prime_ne_q : ∀ t, primeAt t ≠ Sudoku.q
  seed_a_eq : ∀ t : Fin 2, primeAt (.inl (.inr t)) = t.val + 2
  seed_b_large : ∀ t : Fin 2, (Sudoku.Width ^ 2) < primeAt (.inr (.inl (.inr t)))
  blockA : ∀ i : Channel T, Label T i → ℕ
  blockB : ∀ i : Channel T, Label T i → ℕ
  blockA_pos : ∀ i j, 0 < blockA i j
  blockB_pos : ∀ i j, 0 < blockB i j
  digit_representation : ∀ i j,
    primeAt (.inr (.inr ⟨i, j⟩)) =
      blockA i j * primeAt (.inl i) + blockB i j * primeAt (.inr (.inl i))
  digitProduct : Channel T → ℕ
  digitProduct_eq : ∀ i, digitProduct i =
    ∏ j : Label T i, primeAt (.inr (.inr ⟨i, j⟩))

namespace EncodingParameters

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

def a (i : Channel T) : ℕ := E.primeAt (.inl i)
def b (i : Channel T) : ℕ := E.primeAt (.inr (.inl i))
def digitPrime (i : Channel T) (j : Label T i) : ℕ :=
  E.primeAt (.inr (.inr ⟨i, j⟩))

theorem a_prime (i : Channel T) : Nat.Prime (E.a i) := E.prime_isPrime _
theorem b_prime (i : Channel T) : Nat.Prime (E.b i) := E.prime_isPrime _
theorem digitPrime_prime (i : Channel T) (j : Label T i) :
    Nat.Prime (E.digitPrime i j) := E.prime_isPrime _

theorem a_pos (i : Channel T) : 0 < E.a i := (E.a_prime i).pos
theorem b_pos (i : Channel T) : 0 < E.b i := (E.b_prime i).pos
theorem digitPrime_pos (i : Channel T) (j : Label T i) :
    0 < E.digitPrime i j := (E.digitPrime_prime i j).pos

theorem a_two_le (i : Channel T) : 2 ≤ E.a i := (E.a_prime i).two_le
theorem b_two_le (i : Channel T) : 2 ≤ E.b i := (E.b_prime i).two_le

theorem seed_a (t : Fin 2) : E.a (.inr t) = t.val + 2 := E.seed_a_eq t

theorem digit_eq (i : Channel T) (j : Label T i) :
    E.digitPrime i j = E.blockA i j * E.a i + E.blockB i j * E.b i :=
  E.digit_representation i j

theorem prime_coprime {s t : PrimeTag T} (hst : s ≠ t) :
    Nat.Coprime (E.primeAt s) (E.primeAt t) :=
  (Nat.coprime_primes (E.prime_isPrime s) (E.prime_isPrime t)).2
    (fun h => hst (E.prime_injective h))

theorem prime_coprime_p (t : PrimeTag T) : Nat.Coprime (E.primeAt t) Sudoku.p :=
  (Nat.coprime_primes (E.prime_isPrime t) (by decide : Sudoku.p.Prime)).2 (E.prime_ne_p t)

theorem prime_coprime_q (t : PrimeTag T) : Nat.Coprime (E.primeAt t) Sudoku.q :=
  (Nat.coprime_primes (E.prime_isPrime t) (by decide : Sudoku.q.Prime)).2 (E.prime_ne_q t)

theorem prime_coprime_width (t : PrimeTag T) : Nat.Coprime (E.primeAt t) Sudoku.Width :=
  ((E.prime_coprime_p t).pow_right 2).mul_right ((E.prime_coprime_q t).pow_right 2)

theorem prime_coprime_modulus (t : PrimeTag T) : Nat.Coprime (E.primeAt t) residueModulus := by
  rw [residueModulus_eq]
  exact E.prime_coprime_width t

theorem a_coprime_b (i : Channel T) : Nat.Coprime (E.a i) (E.b i) := by
  apply E.prime_coprime
  simp

theorem digitPrime_pairwise (i : Channel T) :
    Pairwise (fun j j' : Label T i => Nat.Coprime (E.digitPrime i j) (E.digitPrime i j')) := by
  intro j j' hj
  apply E.prime_coprime
  intro he
  exact hj (by simpa using he)

section Finite



def r (i : Channel T) : ℕ := E.digitProduct i

theorem r_eq_prod (i : Channel T) : E.r i = ∏ j : Label T i, E.digitPrime i j :=
  E.digitProduct_eq i

theorem r_pos (i : Channel T) : 0 < E.r i := by
  rw [E.r_eq_prod]
  exact Finset.prod_pos (fun j _ => E.digitPrime_pos i j)

instance a_neZero (i : Channel T) : NeZero (E.a i) := ⟨(E.a_pos i).ne'⟩
instance b_neZero (i : Channel T) : NeZero (E.b i) := ⟨(E.b_pos i).ne'⟩
instance digitPrime_neZero (i : Channel T) (j : Label T i) :
    NeZero (E.digitPrime i j) := ⟨(E.digitPrime_pos i j).ne'⟩
instance r_neZero (i : Channel T) : NeZero (E.r i) := ⟨(E.r_pos i).ne'⟩

theorem r_coprime_a (i j : Channel T) : Nat.Coprime (E.r i) (E.a j) := by
  rw [E.r_eq_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_b (i j : Channel T) : Nat.Coprime (E.r i) (E.b j) := by
  rw [E.r_eq_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_p (i : Channel T) : Nat.Coprime (E.r i) Sudoku.p := by
  rw [E.r_eq_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  exact E.prime_coprime_p _

theorem r_coprime_width (i : Channel T) : Nat.Coprime (E.r i) Sudoku.Width := by
  rw [E.r_eq_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro j
  exact E.prime_coprime_width _

theorem r_coprime_modulus (i : Channel T) : Nat.Coprime (E.r i) residueModulus := by
  rw [residueModulus_eq]
  exact E.r_coprime_width i

theorem r_pairwise_coprime : Pairwise (fun i j : Channel T => Nat.Coprime (E.r i) (E.r j)) := by
  intro i j hij
  rw [E.r_eq_prod, E.r_eq_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply E.prime_coprime
  intro he
  have hs : (⟨i, k⟩ : Σ i : Channel T, Label T i) = ⟨j, l⟩ :=
    Sum.inr.inj (Sum.inr.inj he)
  exact hij (congrArg Sigma.fst hs)

end Finite
end EncodingParameters
end Compiler

end TranslationTiling
