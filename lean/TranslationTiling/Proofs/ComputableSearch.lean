import TranslationTiling.Definitions
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find

namespace TranslationTiling

noncomputable section

/-- The first witness of a total decidable search. -/
def leastWitness {α : Type*} (p : α → ℕ → Prop) (h : ∀ a, ∃ n, p a n) (a : α) : ℕ :=
  @Nat.find (p a) (Classical.decPred _) (h a)

theorem leastWitness_eq_find {α : Type*} (p : α → ℕ → Prop)
    (h : ∀ a, ∃ n, p a n) (a : α) [DecidablePred (p a)] :
    leastWitness p h a = Nat.find (h a) :=
  congrArg (fun D : DecidablePred (p a) => @Nat.find (p a) D (h a))
    (Subsingleton.elim _ _)

/-- An existence proof makes a computable semidecision search total; the proof
itself need not be computable. -/
theorem leastWitness_computable {α : Type*} [Primcodable α]
    (p : α → ℕ → Prop) (hp : ComputablePred fun z : α × ℕ => p z.1 z.2)
    (h : ∀ a, ∃ n, p a n) : Computable (leastWitness p h) := by
  obtain ⟨D, hd⟩ := hp
  letI : DecidableRel p := fun a n => D (a, n)
  have hd' : Computable₂ fun a n => decide (p a n) := hd.to₂
  have hr := Partrec.rfind hd'.partrec₂
  apply hr.of_eq
  intro a
  apply Part.ext
  intro n
  change n ∈ Nat.rfind (fun k => Part.some (decide (p a k))) ↔
    n ∈ Part.some (leastWitness p h a)
  rw [Part.mem_some_iff, leastWitness_eq_find]
  constructor
  · intro hn
    obtain ⟨htest, hmin⟩ := Nat.mem_rfind.mp hn
    have hpn : p a n := by simpa using htest
    have hsmall : ∀ m < n, ¬ p a m := by
      intro m hm
      simpa using hmin hm
    exact ((Nat.find_eq_iff (h a)).mpr ⟨hpn, hsmall⟩).symm
  · intro hn
    subst n
    apply Nat.mem_rfind.mpr
    refine ⟨?_, ?_⟩
    · simpa using Nat.find_spec (h a)
    · intro m hm
      simpa using Nat.find_min (h a) hm

theorem nat_prime_primrec : PrimrecPred Nat.Prime := by
  have hdiv : PrimrecRel fun m n : ℕ => m ∣ n :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst)
      (Primrec.const 0)).of_eq (by intro z; exact Nat.dvd_iff_mod_eq_zero.symm)
  have htest : PrimrecRel fun m n : ℕ => m ∣ n → m = 1 :=
    (hdiv.not.or (Primrec.eq.comp Primrec.fst (Primrec.const 1))).of_eq
      (by simp [imp_iff_not_or])
  exact ((Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and
    (htest.forall_lt.comp Primrec.id Primrec.id)).of_eq
      (fun n => Nat.prime_def_lt.symm)

def primeAbove (n : ℕ) : ℕ :=
  leastWitness (fun n q => q.Prime ∧ n ≤ q)
    (fun n => by obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes n; exact ⟨q, hp, hq⟩) n

theorem primeAbove_spec (n : ℕ) : (primeAbove n).Prime ∧ n ≤ primeAbove n := by
  unfold primeAbove leastWitness
  exact @Nat.find_spec (fun q => q.Prime ∧ n ≤ q) (Classical.decPred _) _

theorem primeAbove_computable : Computable primeAbove :=
  leastWitness_computable _
    (((nat_prime_primrec.comp Primrec.snd).and
      (Primrec.nat_le.comp Primrec.fst Primrec.snd)).computablePred) _

end
end TranslationTiling
