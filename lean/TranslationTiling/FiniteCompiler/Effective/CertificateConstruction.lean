import TranslationTiling.FiniteCompiler.BudgetParameters
import TranslationTiling.FiniteCompiler.Effective.Parameters
import TranslationTiling.FiniteCompiler.Effective.Tables

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem certificate_of_parameters (T : System) (E : EncodingParameters T)
    (hu : ∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T))
    (hd : ∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T))
    (hsharp : 596750≤channelCount T ∧ T.alphabet=3 →
      (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
      (∀ i j, E.digitPrime i j≤channelCount T^3) ∧ ∀ i, (E.a i*E.b i)^3≤channelCount T^8)
    (hcompact : 1202≤channelCount T ∧ T.alphabet=3 → CompactPrimes E)
    (heconomical : 962≤channelCount T ∧ T.alphabet=3 → EconomicalPrimes E)
    (hbudget : T.alphabet=3 → BudgetPrimes E (primeBudget T)) :
    ∃ c : ParameterCertificate, ParameterValid (T.width,T.alphabet) c ∧
      (∀ i, c.1.getD (primeKey i) 0=E.primeAt i) ∧
      (∀ j : Σ i : Channel T, Label T i, c.2.1.getD (primeKey (.inr (.inr j))) 0=E.blockA j.1 j.2) ∧
      (∀ j : Σ i : Channel T, Label T i, c.2.2.getD (primeKey (.inr (.inr j))) 0=E.blockB j.1 j.2) := by
  classical
  obtain ⟨ps, hp⟩ := exists_finite_table (primeKey (T := T)) (primeKey_injective T) E.primeAt 0
  let key (j : Σ i : Channel T, Label T i) := primeKey (.inr (.inr j))
  have hkey : Function.Injective key := by
    intro i j h
    exact Sum.inr.inj (Sum.inr.inj (primeKey_injective T h))
  obtain ⟨as, ha⟩ := exists_finite_table key hkey (fun j => E.blockA j.1 j.2) 0
  obtain ⟨bs, hb⟩ := exists_finite_table key hkey (fun j => E.blockB j.1 j.2) 0
  refine ⟨(ps,as,bs), ?_, hp, ha, hb⟩
  apply Or.inr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    obtain ⟨i,rfl⟩ := (mem_primeKeys T k).mp hk
    dsimp only [Prod.fst]
    rw [hp]
    exact ⟨E.prime_isPrime i, E.prime_ne_p i, E.prime_ne_q i, E.prime_ne_five i⟩
  · intro k hk l hl
    obtain ⟨i,rfl⟩ := (mem_primeKeys T k).mp hk
    obtain ⟨j,rfl⟩ := (mem_primeKeys T l).mp hl
    dsimp only [Prod.fst]
    rw [hp, hp]
    by_cases hij : E.primeAt i = E.primeAt j
    · exact Or.inl (congrArg primeKey (E.prime_injective hij))
    · exact Or.inr hij
  · intro k hk
    obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
    change ps.getD (primeKey (.inl i)) 0 ≤ _ ∧ ps.getD (primeKey (.inr (.inl i))) 0 ≤ _
    rw [hp, hp]
    exact hu i
  · intro t ht
    have ht' : t < 2 := List.mem_range.mp ht
    let t' : Fin 2 := ⟨t,ht'⟩
    change ps.getD (primeKey (T := T) (.inl (.inr t'))) 0 = _ ∧
      _ < ps.getD (primeKey (T := T) (.inr (.inl (.inr t')))) 0
    rw [hp, hp]
    exact ⟨E.seed_a_eq t', E.seed_b_large t'⟩
  · intro k hk
    obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
    change 0 < as.getD (key ⟨i,j⟩) 0 ∧ 0 < bs.getD (key ⟨i,j⟩) 0 ∧
      ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 =
        as.getD (key ⟨i,j⟩) 0 * ps.getD (primeKey (.inl i)) 0 +
        bs.getD (key ⟨i,j⟩) 0 * ps.getD (primeKey (.inr (.inl i))) 0 ∧ _
    change _ ∧ _ ∧ _ ∧ ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 ≤ _
    rw [ha, hb, hp, hp, hp]
    exact ⟨E.blockA_pos i j, E.blockB_pos i j, E.digit_representation i j, hd i j⟩
  · constructor
    · by_cases hr : 596750 ≤ T.width+2 ∧ T.alphabet=3
      · right
        have hs := hsharp hr
        constructor
        · intro k hk
          obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
          change ps.getD (primeKey (.inl i)) 0 ≤ _ ∧ ps.getD (primeKey (.inr (.inl i))) 0 ≤ _
          rw [hp,hp]
          exact hs.1 i
        · constructor
          · intro k hk
            obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
            change ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 ≤ _
            rw [hp]
            exact hs.2.1 i j
          · intro k hk
            obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
            change (ps.getD (primeKey (.inl i)) 0*ps.getD (primeKey (.inr (.inl i))) 0)^3 ≤ _
            rw [hp,hp]
            exact hs.2.2 i
      · exact Or.inl hr
    · constructor
      · by_cases hr : 1202≤T.width+2 ∧ T.alphabet=3
        · right
          have hs := hcompact hr
          refine ⟨?_,?_,?_⟩
          · intro k hk
            obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
            change ps.getD (primeKey (.inl i)) 0≤_ ∧ ps.getD (primeKey (.inr (.inl i))) 0≤_
            rw [hp,hp]; exact hs.1 i
          · intro k hk
            obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
            change ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0≤_
            rw [hp]; exact hs.2.1 i j
          · intro k hk
            obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
            change ps.getD (primeKey (.inl i)) 0*ps.getD (primeKey (.inr (.inl i))) 0≤_
            rw [hp,hp]; exact hs.2.2 i
        · exact Or.inl hr
      · constructor
        · by_cases hr : 962≤T.width+2 ∧ T.alphabet=3
          · right
            have hs := heconomical hr
            refine ⟨?_,?_,?_,?_,?_,?_⟩
            · intro k hk
              obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
              change ps.getD (primeKey (.inl i)) 0≤_ ∧ ps.getD (primeKey (.inr (.inl i))) 0≤_
              rw [hp,hp]; exact hs.1 i
            · intro k hk
              obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
              change ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0≤_
              rw [hp]; exact hs.2.1 i j
            · intro k hk
              obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
              change ps.getD (primeKey (.inl i)) 0*ps.getD (primeKey (.inr (.inl i))) 0≤_
              rw [hp,hp]; exact hs.2.2.1 i
            · intro n hn
              let n' : Column T := ⟨n,List.mem_range.mp hn⟩
              change ps.getD (primeKey (.inl (.inl n'))) 0*ps.getD (primeKey (.inr (.inl (.inl n')))) 0≤_
              rw [hp,hp]; exact hs.2.2.2.1 n'
            · intro k hk
              obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
              change (ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0)^20≤_
              rw [hp]; exact hs.2.2.2.2.1 i j
            · intro n hn j hj
              let n' : Column T := ⟨n,List.mem_range.mp hn⟩
              let j' : Label T (.inl n') := ⟨j,List.mem_range.mp hj⟩
              change ps.getD (primeKey (.inr (.inr ⟨.inl n',j'⟩))) 0≤_
              rw [hp]
              exact hs.2.2.2.2.2 n' j'
          · exact Or.inl hr
        · by_cases hr : T.alphabet=3
          · right
            have hs := hbudget hr
            refine ⟨?_,?_,?_,?_,?_⟩
            · intro k hk
              obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
              change ps.getD (primeKey (.inl i)) 0≤_ ∧ ps.getD (primeKey (.inr (.inl i))) 0≤_
              rw [hp,hp]; exact hs.1 i
            · intro k hk
              obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
              change ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0≤_
              rw [hp]; exact hs.2.1 i j
            · intro k hk
              obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
              change ps.getD (primeKey (.inl i)) 0*ps.getD (primeKey (.inr (.inl i))) 0≤_
              rw [hp,hp]; exact hs.2.2.1 i
            · intro n hn
              let n' : Column T := ⟨n,List.mem_range.mp hn⟩
              change ps.getD (primeKey (.inl (.inl n'))) 0*ps.getD (primeKey (.inr (.inl (.inl n')))) 0≤_
              rw [hp,hp]; exact hs.2.2.2.1 n'
            · intro n hn j hj
              let n' : Column T := ⟨n,List.mem_range.mp hn⟩
              let j' : Label T (.inl n') := ⟨j,List.mem_range.mp hj⟩
              change ps.getD (primeKey (.inr (.inr ⟨.inl n',j'⟩))) 0≤_
              rw [hp]; exact hs.2.2.2.2 n' j'
          · exact Or.inl hr

end
end TranslationTiling.FiniteCompiler.Effective
