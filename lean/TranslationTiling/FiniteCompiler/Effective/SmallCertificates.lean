import TranslationTiling.FiniteCompiler.Effective.SmallParameters
import TranslationTiling.FiniteCompiler.Effective.CertificateConstruction

namespace TranslationTiling.FiniteCompiler.Effective.SmallProfiles
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exists_certificate (i : Fin 5) : ∃ c : ParameterCertificate,
    ParameterValid (width i,3) c ∧ ∀ j : PrimeTag (shape i),
      c.1.getD (primeKey j) 0=(profile i).entry (tagIndex j) := by
  let E := encoding (profile i) (profile_valid i) (show (shape i).alphabet=3 from rfl)
  have hprime := encoding_prime_bound (profile i) (profile_valid i) (show (shape i).alphabet=3 from rfl)
  have hpair := encoding_pair_bound (profile i) (profile_valid i) (show (shape i).alphabet=3 from rfl)
  have hw : (shape i).width+2≤114 := by change 48+16*i.val+2≤114; omega
  have hu : 65536≤usefulPrimeCap (channelCount (shape i)) := by
    have hs : 30625≤usefulStart := by
      norm_num [usefulStart,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    unfold usefulPrimeCap
    calc
      65536 ≤ (8*30625)^2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 (by omega)) 2
  have hd : 65536≤digitPrimeCap (shape i).alphabet (channelCount (shape i)) := by
    apply hu.trans
    unfold digitPrimeCap
    have hh : usefulPrimeCap (channelCount (shape i))≤
        8*(primeThreshold (usefulPrimeCap (channelCount (shape i)))+
          channelCount (shape i)*((shape i).alphabet+1)+1) := by
      unfold primeThreshold
      nlinarith
    exact hh.trans (Nat.le_self_pow (by decide) _)
  have hp : BudgetPrimes E (primeBudget (shape i)) := by
    have hC : primeBudget (shape i)=256 := by unfold primeBudget channelCount; omega
    rw [hC]
    exact ⟨fun j => ⟨(hprime _).trans (by decide),(hprime _).trans (by decide)⟩,
      fun j k => (hprime _).trans (by decide),fun j => (hpair j).trans (by decide),
      fun n => hpair _,fun n j => (hprime _).trans (by decide)⟩
  obtain ⟨c,hc,hlook,_,_⟩ := certificate_of_parameters (shape i) E
    (fun j => ⟨(hprime _).trans hu,(hprime _).trans hu⟩)
    (fun j k => (hprime _).trans hd)
    (fun h => by unfold channelCount at h; omega)
    (fun h => by unfold channelCount at h; omega)
    (fun h => by unfold channelCount at h; omega) (fun _ => hp)
  exact ⟨c,hc,hlook⟩

def certificate (i : Fin 5) : ParameterCertificate := (exists_certificate i).choose

theorem certificate_valid (i : Fin 5) : ParameterValid (width i,3) (certificate i) :=
  (exists_certificate i).choose_spec.1

theorem certificate_lookup (i : Fin 5) (j : PrimeTag (shape i)) :
    (certificate i).1.getD (primeKey j) 0=(profile i).entry (tagIndex j) :=
  (exists_certificate i).choose_spec.2 j

end
end TranslationTiling.FiniteCompiler.Effective.SmallProfiles
