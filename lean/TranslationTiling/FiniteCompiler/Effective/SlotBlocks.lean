import TranslationTiling.FiniteCompiler.Effective.SlotLayout
import Mathlib.NumberTheory.FrobeniusNumber

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open scoped Classical
noncomputable section
variable {k m : ℕ} (s : SlotParameters k m)

instance low_neZero (i : WangSlot k m) : NeZero (s.low i) :=
  ⟨(s.prime_isPrime (.inl (i,none))).ne_zero⟩

def firstBlock (i : WangSlot k m) : ℕ := s.fallback (i.1,i.2.2,false)

def secondBlock (i : WangSlot k m) (state : Option (Fin 3)) : ℕ :=
  match state with
  | none => s.fallback (i.1,i.2.2,true)
  | some j => s.marker i j

instance firstBlock_neZero (i : WangSlot k m) : NeZero (s.firstBlock i) :=
  ⟨(s.prime_isPrime (.inr (i.1,i.2.2,false))).ne_zero⟩

instance secondBlock_neZero (i : WangSlot k m) (state : Option (Fin 3)) :
    NeZero (s.secondBlock i state) := by
  cases state with
  | none => exact ⟨(s.prime_isPrime (.inr (i.1,i.2.2,true))).ne_zero⟩
  | some j => exact ⟨(s.prime_isPrime (.inl (i,some j))).ne_zero⟩

theorem blockCounts_exist (i : WangSlot k m) (state : Option (Fin 3)) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ s.low i = u * s.firstBlock i + v * s.secondBlock i state := by
  let a := s.firstBlock i
  let b := s.secondBlock i state
  have ha : a.Prime := s.prime_isPrime (.inr (i.1,i.2.2,false))
  have hb : b.Prime := by
    cases state with
    | none => exact s.prime_isPrime (.inr (i.1,i.2.2,true))
    | some j => exact s.prime_isPrime (.inl (i,some j))
  have hab : a ≠ b := by
    intro h
    cases state with
    | none =>
      have he := Sum.inr.inj (s.prime_injective h)
      have hf := congrArg (fun x : SlotFallback m => x.2.2) he
      cases hf
    | some j =>
      cases s.prime_injective h
  rcases (s.block_budget i state : a*b < s.low i ∨
      (b < s.low i ∧ s.low i % a = b % a)) with hr | ⟨hlt,hmod⟩
  swap
  · let r := s.low i
    change b < r at hlt
    have h₁ := Nat.mod_add_div b a
    have h₂ := Nat.mod_add_div r a
    change r % a = b % a at hmod
    rw [hmod,mul_comm a (r/a)] at h₂
    rw [mul_comm a (b/a)] at h₁
    have hq : b/a < r/a := by
      by_contra! h
      have := Nat.mul_le_mul_right a h
      omega
    refine ⟨r/a-b/a,1,by omega,by decide,?_⟩
    change r = (r/a-b/a)*a+1*b
    rw [Nat.sub_mul,one_mul]
    have := Nat.mul_le_mul_right a hq.le
    omega
  change a*b < s.low i at hr
  have hadd := Nat.add_le_mul ha.one_lt hb.one_lt
  have hmem : s.low i-a-b ∈ AddSubmonoid.closure ({a,b} : Set ℕ) := by
    by_contra hnot
    have hF := (frobeniusNumber_pair ((Nat.coprime_primes ha hb).mpr hab)
      ha.one_lt hb.one_lt).2 hnot
    omega
  obtain ⟨u,v,huv⟩ := (AddSubmonoid.mem_closure_pair _ _ _).mp hmem
  simp only [smul_eq_mul] at huv
  refine ⟨u+1,v+1,by omega,by omega,?_⟩
  calc
    s.low i = (s.low i-a-b)+a+b := by omega
    _ = (u*a+v*b)+a+b := by rw [huv]
    _ = (u+1)*a+(v+1)*b := by ring

def leftCount (i : WangSlot k m) (state : Option (Fin 3)) :=
  (s.blockCounts_exist i state).choose

def rightCount (i : WangSlot k m) (state : Option (Fin 3)) :=
  (s.blockCounts_exist i state).choose_spec.choose

theorem leftCount_pos (i : WangSlot k m) (state : Option (Fin 3)) :
    0 < s.leftCount i state := (s.blockCounts_exist i state).choose_spec.choose_spec.1

theorem rightCount_pos (i : WangSlot k m) (state : Option (Fin 3)) :
    0 < s.rightCount i state := (s.blockCounts_exist i state).choose_spec.choose_spec.2.1

def blocks (i : WangSlot k m) (state : Option (Fin 3)) :
    LabeledBlocks (ZMod (s.low i)) (Fin (s.leftCount i state)) (Fin (s.rightCount i state))
      (s.firstBlock i) (s.secondBlock i state) :=
  LabeledBlocks.digit _ _ _ _ _ (s.blockCounts_exist i state).choose_spec.choose_spec.2.2

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
