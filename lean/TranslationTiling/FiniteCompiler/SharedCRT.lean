import TranslationTiling.FiniteCompiler.SharedCoordinates
import Mathlib.Data.Nat.GCD.BigOperators

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I)

/-- A private first modulus of 1 uses no prime. -/
def firstFactors (a : ℕ) : List ℕ := if a = 1 then [] else [a]

@[simp] theorem firstFactors_prod (a : ℕ) : (firstFactors a).prod = a := by
  unfold firstFactors
  split <;> simp_all

def rowFactors (digits : I → List ℕ) (i : I) : List ℕ :=
  digits i ++ firstFactors (L.firstSize i) ++ [L.secondSize i]

private theorem primeProducts_coprime {ps qs : List ℕ}
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ q ∈ qs, q.Prime) (hdis : List.Disjoint ps qs) :
    Nat.Coprime ps.prod qs.prod := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hpm
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hqm
  exact (Nat.coprime_primes (hp p hpm) (hq q hqm)).mpr (fun he => hdis hpm (he ▸ hqm))

/-- The prime list for each row omits the shared coordinates. Pairwise
disjointness therefore gives a cyclic finite factor. -/
def finiteCRT_of_rowFactors (digits : I → List ℕ)
    (hprod : ∀ i, (digits i).prod = L.lowSize i)
    (hprime : ∀ i, ∀ p ∈ rowFactors L digits i, p.Prime)
    (hdup : ∀ i, (rowFactors L digits i).Nodup)
    (hdis : Pairwise (fun i j => List.Disjoint (rowFactors L digits i) (rowFactors L digits j)))
    (hfixed : ∀ i, List.Disjoint ([5,7,199,163] : List ℕ) (rowFactors L digits i)) :
    ZMod (order L) ≃+* Factor L := by
  let expanded i := digits i ++ rowFactors L digits i
  have hmem (i : I) (p : ℕ) : p ∈ expanded i ↔ p ∈ rowFactors L digits i := by
    unfold expanded
    simp only [List.mem_append]
    exact or_iff_right_of_imp (fun h => by simp [rowFactors,h])
  have hmod (i : I) : (expanded i).prod = rowModulus L i := by
    simp only [expanded,rowFactors,List.prod_append,firstFactors_prod,List.prod_cons,
      List.prod_nil,Nat.mul_one,hprod,rowModulus,pow_two]
    ac_rfl
  have h₁ (i : I) : Nat.Coprime ((L.lowSize i)^2) (L.firstSize i) := by
    have h := hdup i
    unfold rowFactors at h
    have hdis := (List.nodup_append'.mp (List.nodup_append'.mp h).1).2.2
    have hc : Nat.Coprime (digits i).prod (firstFactors (L.firstSize i)).prod :=
      primeProducts_coprime (fun p h => hprime i p (by simp [rowFactors,h]))
        (fun p h => hprime i p (by simp [rowFactors,h])) hdis
    rw [hprod,firstFactors_prod] at hc
    exact hc.pow_left 2
  have h₂ (i : I) : Nat.Coprime ((L.lowSize i)^2 * L.firstSize i) (L.secondSize i) := by
    let left := digits i ++ digits i ++ firstFactors (L.firstSize i)
    have hd (p : ℕ) (hp : p ∈ left) :
        p ∈ digits i ++ firstFactors (L.firstSize i) := by
      simpa only [left,List.mem_append,or_assoc,or_self] using hp
    have h := hdup i
    unfold rowFactors at h
    have hc : Nat.Coprime left.prod ([L.secondSize i] : List ℕ).prod :=
      primeProducts_coprime (fun p h => hprime i p (List.mem_append_left _ (hd p h)))
        (fun p h => hprime i p (List.mem_append_right _ h))
        (fun _ hp hq => (List.nodup_append'.mp h).2.2 (hd _ hp) hq)
    simpa only [left,List.prod_append,firstFactors_prod,List.prod_cons,List.prod_nil,
      Nat.mul_one,hprod,pow_two] using hc
  have hrows : Pairwise (fun i j => Nat.Coprime (rowModulus L i) (rowModulus L j)) := by
    intro i j hij
    rw [← hmod i, ← hmod j]
    exact primeProducts_coprime (fun p hp => hprime i p ((hmem i p).mp hp))
      (fun q hq => hprime j q ((hmem j q).mp hq))
      (fun _ hp hq => hdis hij ((hmem i _).mp hp) ((hmem j _).mp hq))
  have hfix : Nat.Coprime (1225*199*163) (∏ i, rowModulus L i) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro i
    rw [← hmod i,show 1225*199*163 = ([5,5,7,7,199,163] : List ℕ).prod by decide]
    apply primeProducts_coprime
    · decide
    · exact fun p hp => hprime i p ((hmem i p).mp hp)
    · intro p hp hq
      apply hfixed i _ ((hmem i p).mp hq)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
      tauto
  exact finiteCRT L h₁ h₂ hrows hfix

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
