/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.CyclicCoordinates
import TranslationTiling.Compiler.ShiftMultiplicity
import TranslationTiling.CompactIndex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option maxRecDepth 1000

namespace TranslationTiling

universe uJ

namespace Compiler


noncomputable section

def separatedResidueLift {J : Type uJ} (M : ℕ) [NeZero M]
    (v : J → ZMod M) (code : J → ℕ) (j : J) : ℤ :=
  ((v j).val : ℤ) + (M : ℤ) * (code j : ℤ)

@[simp] theorem separatedResidueLift_cast {J : Type uJ}
    (M : ℕ) [NeZero M] (v : J → ZMod M) (code : J → ℕ) (j : J) :
    (separatedResidueLift M v code j : ZMod M) = v j := by
  simp [separatedResidueLift]

theorem separatedResidueLift_injective {J : Type uJ}
    (M : ℕ) [NeZero M] (v : J → ZMod M) (code : J → ℕ)
    (hc : Function.Injective code) :
    Function.Injective (separatedResidueLift M v code) := by
  intro i j hij
  change ((v i).val : ℤ) + (M : ℤ) * (code i : ℤ) =
    ((v j).val : ℤ) + (M : ℤ) * (code j : ℤ) at hij
  have he : (v i).val + M * code i = (v j).val + M * code j := by
    exact_mod_cast hij
  apply hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hlt)
    have hi := ZMod.val_lt (v i)
    nlinarith
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hgt)
    have hj := ZMod.val_lt (v j)
    nlinarith

theorem separatedResidueLift_code_eq {J : Type uJ}
    (M : ℕ) [NeZero M] (v : J → ZMod M) (code : J → ℕ) {i j : J}
    (h : separatedResidueLift M v code i=separatedResidueLift M v code j) : code i=code j := by
  have he : (v i).val+M*code i=(v j).val+M*code j := by
    unfold separatedResidueLift at h
    exact_mod_cast h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hlt)
    have hi := ZMod.val_lt (v i)
    nlinarith
  · have hm := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hgt)
    have hj := ZMod.val_lt (v j)
    nlinarith

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

abbrev ActivationIndex (i : Channel T) :=
  K E i × ShiftIndex (E.a i) (E.b i)

abbrev SeedActivationIndex (t : Fin 2) := ActivationIndex E (.inr t) × Residues T

/-- Mixed-radix batch index, with two slots for the shift multiplicity. -/
def activationIndexCode (i : Channel T) (j : ActivationIndex E i) : ℕ :=
  CompactIndex.pack 2
    (CompactIndex.pack (E.b i) j.2.1.1.val j.2.1.2.val) j.2.2.val

theorem activation_multiplicity_lt (i : Channel T) (j : ActivationIndex E i) : j.2.2.val<2 := by
  have hm : shiftMultiplicity (E.a i) (E.b i) j.2.1≤2 := by
    unfold shiftMultiplicity
    split_ifs <;> omega
  exact lt_of_lt_of_le j.2.2.isLt hm

theorem activationIndexCode_injective (i : Channel T) :
    ∀ {j k : ActivationIndex E i}, j.1=k.1 → activationIndexCode E i j=activationIndexCode E i k → j=k := by
  rintro ⟨k,⟨⟨α,ξ⟩,d⟩⟩ ⟨l,⟨⟨β,η⟩,e⟩⟩ hkl h
  obtain ⟨hrest,hd⟩ := CompactIndex.pack_injective (by decide)
    (activation_multiplicity_lt E i (k,⟨(α,ξ),d⟩))
    (activation_multiplicity_lt E i (l,⟨(β,η),e⟩)) h
  obtain ⟨hα,hξ⟩ := CompactIndex.pack_injective (E.b_pos i) (ZMod.val_lt ξ) (ZMod.val_lt η) hrest
  have hαβ : α=β := ZMod.val_injective (E.a i) hα
  have hξη : ξ=η := ZMod.val_injective (E.b i) hξ
  change k=l at hkl
  subst l β η
  have hde : d=e := Fin.ext hd
  subst e
  rfl

theorem activationIndexCode_sharp_lt (i : Channel T) (j : ActivationIndex E i) :
    activationIndexCode E i j<2*(E.a i*E.b i) := by
  have h1 := CompactIndex.pack_lt (ZMod.val_lt j.2.1.1) (ZMod.val_lt j.2.1.2)
  have h2 := CompactIndex.pack_lt h1 (activation_multiplicity_lt E i j)
  simpa only [activationIndexCode,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h2

theorem activationIndexCode_lt (i : Channel T) (j : ActivationIndex E i) :
    activationIndexCode E i j<2*(E.r i*E.a i*E.b i) := by
  have hc := activationIndexCode_sharp_lt E i j
  have hm := Nat.mul_le_mul_right (2*(E.a i*E.b i)) (Nat.succ_le_of_lt (E.r_pos i))
  nlinarith only [hc,hm]

def seedActivationIndexCode (t : Fin 2) (j : SeedActivationIndex E t) : ℕ :=
  CompactIndex.pack residueModulus
    (CompactIndex.pack residueModulus (activationIndexCode E (.inr t) j.1) j.2.1.val) j.2.2.val

theorem seedActivationIndexCode_injective (t : Fin 2) :
    ∀ {j k : SeedActivationIndex E t}, j.1.1=k.1.1 → seedActivationIndexCode E t j=seedActivationIndexCode E t k → j=k := by
  intro j k hlow h
  obtain ⟨hrest,hy⟩ := CompactIndex.pack_injective (NeZero.pos residueModulus)
    (ZMod.val_lt j.2.2) (ZMod.val_lt k.2.2) h
  obtain ⟨ha,hx⟩ := CompactIndex.pack_injective (NeZero.pos residueModulus)
    (ZMod.val_lt j.2.1) (ZMod.val_lt k.2.1) hrest
  exact Prod.ext (activationIndexCode_injective E (.inr t) hlow ha)
    (Prod.ext (ZMod.val_injective _ hx) (ZMod.val_injective _ hy))

theorem seedActivationIndexCode_sharp_lt (t : Fin 2) (j : SeedActivationIndex E t) :
    seedActivationIndexCode E t j<2*(E.a (.inr t)*E.b (.inr t))*residueModulus^2 := by
  have h1 := CompactIndex.pack_lt (activationIndexCode_sharp_lt E (.inr t) j.1) (ZMod.val_lt j.2.1)
  have h2 := CompactIndex.pack_lt h1 (ZMod.val_lt j.2.2)
  simpa only [seedActivationIndexCode,pow_two,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h2

theorem seedActivationIndexCode_lt (t : Fin 2) (j : SeedActivationIndex E t) :
    seedActivationIndexCode E t j<2*(E.r (.inr t)*E.a (.inr t)*E.b (.inr t))*residueModulus^2 := by
  have h1 := CompactIndex.pack_lt (activationIndexCode_lt E (.inr t) j.1) (ZMod.val_lt j.2.1)
  have h2 := CompactIndex.pack_lt h1 (ZMod.val_lt j.2.2)
  simpa only [seedActivationIndexCode,pow_two,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h2

def otherSeed (t : Fin 2) : Fin 2 := ⟨1 - t.val, by omega⟩

@[simp] theorem otherSeed_ne_self (t : Fin 2) : otherSeed t ≠ t := by
  fin_cases t <;> decide

@[simp] theorem otherSeed_otherSeed (t : Fin 2) : otherSeed (otherSeed t) = t := by
  fin_cases t <;> decide

def activationModulus (i : Channel T) : ℕ := (E.r i * E.a i) * E.b i

instance activationModulus_neZero (i : Channel T) : NeZero (activationModulus E i) := by
  unfold activationModulus
  infer_instance

private theorem activationCoprime (i : Channel T) :
    Nat.Coprime (E.r i * E.a i) (E.b i) := by
  rw [Nat.coprime_mul_iff_left]
  exact ⟨E.r_coprime_b i i, E.a_coprime_b i⟩

def activationCRT (i : Channel T) :
    ZMod (activationModulus E i) ≃+* ((K E i × ZMod (E.a i)) × ZMod (E.b i)) :=
  (ZMod.chineseRemainder (activationCoprime E i)).trans
    (RingEquiv.prodCongr (ZMod.chineseRemainder (E.r_coprime_a i i))
      (RingEquiv.refl _))

def activationResidue (i : Channel T) (j : ActivationIndex E i) :
    ZMod (activationModulus E i) :=
  (activationCRT E i).symm
    ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.2)

def ordinaryFirst (n : Column T) : ActivationIndex E (.inl n) → ℤ :=
  separatedResidueLift (activationModulus E (.inl n)) (activationResidue E (.inl n)) (activationIndexCode E (.inl n))

def ordinaryOffset (n : Column T) (j : ActivationIndex E (.inl n)) : Plane :=
  (ordinaryFirst E n j, -(n.val : ℤ) * ordinaryFirst E n j)

theorem ordinaryFirst_residues (n : Column T) (j : ActivationIndex E (.inl n)) :
    (((ordinaryFirst E n j : K E (.inl n)),
       (ordinaryFirst E n j : ZMod (E.a (.inl n)))),
       (ordinaryFirst E n j : ZMod (E.b (.inl n)))) =
      ((j.1, rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2),
        rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2) := by
  have h := congrArg (activationCRT E (.inl n))
    (separatedResidueLift_cast (activationModulus E (.inl n))
      (activationResidue E (.inl n)) (activationIndexCode E (.inl n)) j)
  rw [activationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1) h
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [ordinaryFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem ordinaryOffset_low (n : Column T) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : K E (.inl n)) = j.1 :=
  congrArg (fun z => z.1.1) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoA (n : Column T) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.a (.inl n))) =
      rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg (fun z => z.1.2) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoB (n : Column T) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.b (.inl n))) =
      rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg Prod.snd (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_lineValue (n : Column T) (j : ActivationIndex E (.inl n)) :
    lineValue n (ordinaryOffset E n j) = 0 := by
  simp [lineValue, ordinaryOffset]

theorem ordinaryOffset_injective (n : Column T) : Function.Injective (ordinaryOffset E n) := by
  intro i j hij
  have hl : i.1=j.1 := by
    simpa only [ordinaryOffset_low] using congrArg (fun p : Plane => (p.1 : K E (.inl n))) hij
  exact activationIndexCode_injective E (.inl n) hl
    (separatedResidueLift_code_eq _ _ _ (congrArg Prod.fst hij))

def seedModulus (t : Fin 2) : ℕ :=
  (activationModulus E (.inr t) * residueModulus) * E.a (.inr (otherSeed t))

instance seedModulus_neZero (t : Fin 2) : NeZero (seedModulus E t) := by
  unfold seedModulus
  infer_instance

private theorem activationCoprime_p (i : Channel T) :
    Nat.Coprime (activationModulus E i) (residueModulus) := by
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  exact ⟨⟨E.r_coprime_modulus i, E.prime_coprime_modulus (.inl i)⟩,
    E.prime_coprime_modulus (.inr (.inl i))⟩

private theorem seedCoprime_other (t : Fin 2) :
    Nat.Coprime (activationModulus E (.inr t) * residueModulus)
      (E.a (.inr (otherSeed t))) := by
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  refine ⟨⟨⟨E.r_coprime_a _ _, ?_⟩, ?_⟩, ?_⟩
  · apply E.prime_coprime
    simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq]
    exact (otherSeed_ne_self t).symm
  · apply E.prime_coprime
    simp
  · exact
      (E.prime_coprime_modulus (.inl (.inr (otherSeed t)))).symm

def seedCRT (t : Fin 2) :
    ZMod (seedModulus E t) ≃+*
      ((((K E (.inr t) × ZMod (E.a (.inr t))) × ZMod (E.b (.inr t))) ×
        ZMod (residueModulus)) × ZMod (E.a (.inr (otherSeed t)))) :=
  (ZMod.chineseRemainder (seedCoprime_other E t)).trans
    (RingEquiv.prodCongr
      ((ZMod.chineseRemainder (activationCoprime_p E (.inr t))).trans
        (RingEquiv.prodCongr (activationCRT E (.inr t)) (RingEquiv.refl _)))
      (RingEquiv.refl _))

def seedActivationResidue (t : Fin 2) (j : SeedActivationIndex E t) :
    ZMod (seedModulus E t) :=
  (seedCRT E t).symm
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0)

def seedFirst (t : Fin 2) : SeedActivationIndex E t → ℤ :=
  separatedResidueLift (seedModulus E t) (seedActivationResidue E t) (seedActivationIndexCode E t)

def seedOffset (t : Fin 2) (j : SeedActivationIndex E t) : Plane :=
  (seedFirst E t j, (j.2.2.val : ℤ))

theorem seedFirst_residues (t : Fin 2) (j : SeedActivationIndex E t) :
    (((((seedFirst E t j : K E (.inr t)),
      (seedFirst E t j : ZMod (E.a (.inr t)))),
      (seedFirst E t j : ZMod (E.b (.inr t)))),
      (seedFirst E t j : ZMod (residueModulus))),
      (seedFirst E t j : ZMod (E.a (.inr (otherSeed t))))) =
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0) := by
  have h := congrArg (seedCRT E t)
    (separatedResidueLift_cast (seedModulus E t) (seedActivationResidue E t) (seedActivationIndexCode E t) j)
  rw [seedActivationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_) ?_
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1.1.1) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem seedOffset_low (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : K E (.inr t)) = j.1.1 :=
  congrArg (fun z => z.1.1.1.1) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoA (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr t))) =
      rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoB (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.b (.inr t))) =
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_other (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr (otherSeed t)))) = 0 :=
  congrArg Prod.snd (seedFirst_residues E t j)

@[simp] theorem seedOffset_residue (t : Fin 2) (j : SeedActivationIndex E t) :
    (((seedOffset E t j).1 : ZMod (residueModulus)),
      ((seedOffset E t j).2 : ZMod (residueModulus))) = j.2 := by
  apply Prod.ext
  · exact congrArg (fun z => z.1.2) (seedFirst_residues E t j)
  · simp [seedOffset]

theorem seedOffset_injective (t : Fin 2) : Function.Injective (seedOffset E t) := by
  intro i j hij
  have hl : i.1.1=j.1.1 := by
    simpa only [seedOffset_low] using congrArg (fun p : Plane => (p.1 : K E (.inr t))) hij
  exact seedActivationIndexCode_injective E t hl
    (separatedResidueLift_code_eq _ _ _ (congrArg Prod.fst hij))

end

end Compiler

end TranslationTiling
