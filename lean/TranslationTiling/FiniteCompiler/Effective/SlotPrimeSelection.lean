import TranslationTiling.FiniteCompiler.SlotPrimes
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective

def slotPrimePool (threshold count : ℕ) : List ℕ :=
  (List.range (guardedPrimeCap (threshold+count+16)+1)).filter
    fun p => decide (p.Prime ∧ threshold < p)

@[simp] theorem slotPrimePool_mem (threshold count p : ℕ) :
    p ∈ slotPrimePool threshold count ↔
      p.Prime ∧ threshold < p ∧ p ≤ guardedPrimeCap (threshold+count+16) := by
  simp only [slotPrimePool,List.mem_filter,List.mem_range,decide_eq_true_eq,Nat.lt_succ_iff]
  exact ⟨fun ⟨h, hp, ht⟩ => ⟨hp,ht,h⟩, fun ⟨hp,ht,h⟩ => ⟨h,hp,ht⟩⟩

theorem slotPrimePool_length (threshold count : ℕ) : count ≤ (slotPrimePool threshold count).length := by
  obtain ⟨p,hin,hp⟩ := exists_slot_primes_above threshold count
  let f (i : Fin count) : ↥(slotPrimePool threshold count).toFinset :=
    ⟨p i, List.mem_toFinset.mpr ((slotPrimePool_mem _ _ _).mpr (hp i))⟩
  have hf : Function.Injective f := fun _ _ h => hin (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin,Fintype.card_coe] at h
  exact h.trans (List.toFinset_card_le _)

def slotPrimeAt (threshold count index : ℕ) : ℕ :=
  (slotPrimePool threshold count).getD index 0

theorem slotPrimeAt_spec {threshold count index : ℕ} (hi : index < count) :
    (slotPrimeAt threshold count index).Prime ∧ threshold < slotPrimeAt threshold count index ∧
      slotPrimeAt threshold count index ≤ guardedPrimeCap (threshold+count+16) := by
  have h := hi.trans_le (slotPrimePool_length threshold count)
  apply (slotPrimePool_mem _ _ _).mp
  unfold slotPrimeAt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

theorem slotPrimeAt_injective (threshold count : ℕ) :
    Function.Injective (fun i : Fin count => slotPrimeAt threshold count i.val) := by
  intro i j h
  have hi := i.isLt.trans_le (slotPrimePool_length threshold count)
  have hj := j.isLt.trans_le (slotPrimePool_length threshold count)
  have hd : (slotPrimePool threshold count).Nodup :=
    List.Nodup.filter _ List.nodup_range
  simp only [slotPrimeAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] at h
  apply Fin.ext
  exact hd.getElem_inj_iff.mp h

theorem slotPrimePool_primrec : Primrec (fun z : ℕ × ℕ => slotPrimePool z.1 z.2) := by
  unfold slotPrimePool
  have hr : Primrec (fun z : ℕ × ℕ => List.range (guardedPrimeCap (z.1+z.2+16)+1)) := by
    fun_prop
  have hc : PrimrecPred (fun z : (ℕ × ℕ) × ℕ => z.1.1 < z.2) := by fun_prop
  exact filterList hr ((nat_prime_primrec.comp Primrec.snd).and hc)

theorem slotPrimeAt_primrec : Primrec (fun z : (ℕ × ℕ) × ℕ => slotPrimeAt z.1.1 z.1.2 z.2) := by
  unfold slotPrimeAt
  have hp := slotPrimePool_primrec.comp (Primrec.fst : Primrec (Prod.fst : (ℕ × ℕ) × ℕ → ℕ × ℕ))
  exact (Primrec.list_getD 0).comp hp Primrec.snd

end TranslationTiling.FiniteCompiler.Packed
