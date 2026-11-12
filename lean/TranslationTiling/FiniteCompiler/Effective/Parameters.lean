import TranslationTiling.FiniteCompiler.Parameters
import TranslationTiling.Compiler.EffectiveChoices

/-! # Effective choice of bounded encoding parameters

Only finite arithmetic certificates are searched. The verifier checks prime
separation, positive block representations, and the same polynomial prime
caps used in the optimized size proof. It never tests tilability.
-/

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev ParameterCertificate := List ℕ × List ℕ × List ℕ

def channelKeys (w : ℕ) : List ℕ :=
  (List.range w).map (Nat.pair 0) ++ [Nat.pair 1 0, Nat.pair 1 1]

def digitKeys (w B : ℕ) : List (ℕ × ℕ) :=
  (List.range w).flatMap (fun i => (List.range B).map fun j => (Nat.pair 0 i, j)) ++
    [(Nat.pair 1 0, 0), (Nat.pair 1 1, 0)]

def primeKeys (w B : ℕ) : List ℕ :=
  (channelKeys w).map (Nat.pair 0) ++ (channelKeys w).map (Nat.pair 1) ++
    (digitKeys w B).map (fun j => Nat.pair 2 (Nat.pair j.1 j.2))

@[fun_prop] theorem pairNat {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => Nat.pair (f a) (g a)) :=
  (Primrec.encode.comp (hf.pair hg)).of_eq (fun _ => rfl)

@[fun_prop] theorem channelKeys_primrec : Primrec channelKeys := by
  unfold channelKeys
  fun_prop

@[fun_prop] theorem digitKeys_primrec : Primrec (fun d : ℕ × ℕ => digitKeys d.1 d.2) := by
  unfold digitKeys
  change Primrec _
  fun_prop

@[fun_prop] theorem primeKeys_primrec : Primrec (fun d : ℕ × ℕ => primeKeys d.1 d.2) := by
  unfold primeKeys
  change Primrec _
  fun_prop

/-- All conditions concern finite lists of natural numbers. -/
def ParameterValid (d : ℕ × ℕ) (c : ParameterCertificate) : Prop :=
  d.1 = 0 ∨
    ((∀ k ∈ primeKeys d.1 d.2,
        (c.1.getD k 0).Prime ∧ c.1.getD k 0 ≠ Sudoku.p ∧ c.1.getD k 0 ≠ Sudoku.q) ∧
    (∀ k ∈ primeKeys d.1 d.2, ∀ l ∈ primeKeys d.1 d.2,
        k = l ∨ c.1.getD k 0 ≠ c.1.getD l 0) ∧
    (∀ i ∈ channelKeys d.1,
        c.1.getD (Nat.pair 0 i) 0 ≤ usefulPrimeCap (d.1 + 2) ∧
        c.1.getD (Nat.pair 1 i) 0 ≤ usefulPrimeCap (d.1 + 2)) ∧
    (∀ t ∈ List.range 2,
        c.1.getD (Nat.pair 0 (Nat.pair 1 t)) 0 = t + 2 ∧
        Sudoku.Width ^ 2 < c.1.getD (Nat.pair 1 (Nat.pair 1 t)) 0) ∧
    (∀ j ∈ digitKeys d.1 d.2,
        let k := Nat.pair 2 (Nat.pair j.1 j.2)
        0 < c.2.1.getD k 0 ∧ 0 < c.2.2.getD k 0 ∧
        c.1.getD k 0 = c.2.1.getD k 0 * c.1.getD (Nat.pair 0 j.1) 0 +
          c.2.2.getD k 0 * c.1.getD (Nat.pair 1 j.1) 0 ∧
        c.1.getD k 0 ≤ digitPrimeCap d.2 (d.1 + 2)))

noncomputable instance (d : ℕ × ℕ) (c : ParameterCertificate) : Decidable (ParameterValid d c) := by
  unfold ParameterValid
  infer_instance

@[fun_prop] theorem parameterValid_primrec :
    PrimrecPred (fun z : (ℕ × ℕ) × ParameterCertificate => ParameterValid z.1 z.2) := by
  simp only [ParameterValid, usefulPrimeCap, digitPrimeCap, primeThreshold,
    pow_two]
  fun_prop

/-- Natural codes for channels and prime tags, with no arbitrary finite ordering. -/
def channelKey {T : System} : Channel T → ℕ
  | .inl i => Nat.pair 0 i.val
  | .inr t => Nat.pair 1 t.val

def labelKey {T : System} (i : Channel T) : Label T i → ℕ := by
  cases i with
  | inl _ => exact Fin.val
  | inr _ => exact fun _ => 0

def primeKey {T : System} : PrimeTag T → ℕ
  | .inl i => Nat.pair 0 (channelKey i)
  | .inr (.inl i) => Nat.pair 1 (channelKey i)
  | .inr (.inr j) => Nat.pair 2 (Nat.pair (channelKey j.1) (labelKey j.1 j.2))

theorem channelKey_injective (T : System) : Function.Injective (channelKey (T := T)) := by
  intro i j h
  cases i <;> cases j <;> simp only [channelKey, Nat.pair_eq_pair] at h
  · exact congrArg Sum.inl (Fin.ext h.2)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext h.2)

theorem labelKey_injective {T : System} (i : Channel T) : Function.Injective (labelKey i) := by
  cases i with
  | inl _ => exact Fin.val_injective
  | inr _ =>
    change Function.Injective (fun _ : Unit => (0 : ℕ))
    intro _ _ _; exact Subsingleton.elim _ _

theorem digitKey_injective (T : System) : Function.Injective
    (fun j : Σ i : Channel T, Label T i => Nat.pair (channelKey j.1) (labelKey j.1 j.2)) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  obtain ⟨hi,hj⟩ := Nat.pair_eq_pair.mp h
  have he := channelKey_injective T hi
  change i = i' at he
  subst i'
  dsimp only at hj
  exact Sigma.ext rfl (heq_of_eq (labelKey_injective i hj))

theorem primeKey_injective (T : System) : Function.Injective (primeKey (T := T)) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [primeKey, Nat.pair_eq_pair] at h
  · exact congrArg Sum.inl (channelKey_injective T h.2)
  · omega
  · omega
  · omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (channelKey_injective T h.2)
  · omega
  · omega
  · omega
  · exact congrArg (Sum.inr ∘ Sum.inr) (digitKey_injective T (Nat.pair_eq_pair.mpr h.2))

theorem mem_channelKeys (T : System) (k : ℕ) :
    k ∈ channelKeys T.width ↔ ∃ i : Channel T, channelKey i = k := by
  simp only [channelKeys, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  constructor
  · rintro (⟨i,hi,rfl⟩ | h | h)
    · exact ⟨.inl ⟨i,hi⟩,rfl⟩
    · exact ⟨.inr 0,h.symm⟩
    · exact ⟨.inr 1,h.symm⟩
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i.val,i.isLt,rfl⟩
    | inr t => fin_cases t <;> simp [channelKey]

theorem mem_digitKeys (T : System) (k : ℕ × ℕ) :
    k ∈ digitKeys T.width T.alphabet ↔
      ∃ j : Σ i : Channel T, Label T i, (channelKey j.1,labelKey j.1 j.2) = k := by
  simp only [digitKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  constructor
  · rintro (⟨i,hi,j,hj,rfl⟩ | h | h)
    · exact ⟨⟨.inl ⟨i,hi⟩,⟨j,hj⟩⟩,rfl⟩
    · exact ⟨⟨.inr 0,()⟩,h.symm⟩
    · exact ⟨⟨.inr 1,()⟩,h.symm⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i.val,i.isLt,j.val,j.isLt,rfl⟩
    | inr t => fin_cases t <;> simp [channelKey,labelKey]

theorem mem_primeKeys (T : System) (k : ℕ) :
    k ∈ primeKeys T.width T.alphabet ↔ ∃ i : PrimeTag T, primeKey i = k := by
  simp only [primeKeys, List.mem_append, List.mem_map, mem_channelKeys, mem_digitKeys, or_assoc]
  constructor
  · rintro (⟨c,⟨i,rfl⟩,rfl⟩ | ⟨c,⟨i,rfl⟩,rfl⟩ | ⟨c,⟨j,rfl⟩,rfl⟩)
    · exact ⟨.inl i,rfl⟩
    · exact ⟨.inr (.inl i),rfl⟩
    · exact ⟨.inr (.inr j),rfl⟩
  · rintro ⟨i,rfl⟩
    rcases i with i | (i | j)
    · exact Or.inl ⟨_,⟨i,rfl⟩,rfl⟩
    · exact Or.inr (Or.inl ⟨_,⟨i,rfl⟩,rfl⟩)
    · exact Or.inr (Or.inr ⟨_,⟨j,rfl⟩,rfl⟩)

end TranslationTiling.FiniteCompiler.Effective
