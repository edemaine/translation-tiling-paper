/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.SharedSeedSizeTransport
import TranslationTiling.Compiler.ChannelDigitBlocks
import TranslationTiling.Compiler.ActivationOffsets

namespace TranslationTiling

noncomputable section

namespace Compiler


open SharedSeed

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

theorem seedOneSize
    {T : LeanWang.TileSet} (E : EncodingParameters T)
    : E.a (.inr (0 : Fin 2)) = 2 := by
  simpa using E.seed_a (0 : Fin 2)

theorem seedTwoSize
    {T : LeanWang.TileSet} (E : EncodingParameters T)
    : E.a (.inr (1 : Fin 2)) = 3 := by
  simpa using E.seed_a (1 : Fin 2)

def seedUseful (t : Fin 2) : Residues T → K E (.inr t) → P E (.inr t) :=
  Fin.cases
    (fun s u => usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
      (residueEquiv T s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun s u => usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv T s)) t

def seedHigh (t : Fin 2) : ℤ → Residues T → K E (.inr t) → K E (.inr t) :=
  Fin.cases
    (fun x s u => highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
      (residueEquiv T s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun x s u => highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv T s)) t

@[simp] theorem seedUseful_zero (s : Residues T) (u : K E (.inr (0 : Fin 2))) :
    seedUseful E 0 s u =
      usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
        (residueEquiv T s) := rfl

@[simp] theorem seedUseful_one (s : Residues T) (u : K E (.inr (1 : Fin 2))) :
    seedUseful E 1 s u =
      usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv T s) := rfl

@[simp] theorem seedHigh_zero (x : ℤ) (s : Residues T) (u : K E (.inr (0 : Fin 2))) :
    seedHigh E 0 x s u =
      highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
        (residueEquiv T s) := rfl

@[simp] theorem seedHigh_one (x : ℤ) (s : Residues T) (u : K E (.inr (1 : Fin 2))) :
    seedHigh E 1 x s u =
      highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv T s) := rfl

def seedC (t : Fin 2) (x : Plane) (k : Input E) : P E (.inr t) :=
  seedUseful E t (residue T x) (k (.inr t))

def seedBeta (t : Fin 2) (x : Plane) (k : Input E) : K E (.inr t) :=
  seedHigh E t x.1 (residue T x) (k (.inr t))

theorem seedC_eq_of_residue_low (t : Fin 2) {x y : Plane} {k l : Input E}
    (hx : residue T x = residue T y) (hk : k (.inr t) = l (.inr t)) :
    seedC E t x k = seedC E t y l := by
  simp only [seedC, hx, hk]

def seedSourceInput (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) : Input E :=
  Function.update k (.inr t) (k (.inr t) - j.1.1)

@[simp] theorem seedSourceInput_same (t : Fin 2) (k : Input E)
    (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) = k (.inr t) - j.1.1 := by
  simp [seedSourceInput]

theorem seedSourceInput_low (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) =
      k (.inr t) - ((seedOffset E t j).1 : K E (.inr t)) := by
  rw [seedSourceInput_same, seedOffset_low]

theorem seed_source_residue (t : Fin 2) (x : Plane) (j : SeedActivationIndex E t) :
    residue T (x - seedOffset E t j) = residue T x - j.2 := by
  have hs : residue T (seedOffset E t j) = j.2 := seedOffset_residue E t j
  have hfirst : ((seedOffset E t j).1 : ZMod (residueModulus)) = j.2.1 := congrArg Prod.fst hs
  have hsecond : ((seedOffset E t j).2 : ZMod (residueModulus)) = j.2.2 := congrArg Prod.snd hs
  apply Prod.ext
  · change ((x.1 - (seedOffset E t j).1 : ℤ) : ZMod (residueModulus)) =
      (x.1 : ZMod (residueModulus)) - j.2.1
    rw [Int.cast_sub, hfirst]
  · change ((x.2 - (seedOffset E t j).2 : ℤ) : ZMod (residueModulus)) =
      (x.2 : ZMod (residueModulus)) - j.2.2
    rw [Int.cast_sub, hsecond]

def seedActualForward (t : Fin 2) (x : Plane) (k : Input E)
    (j : SeedActivationIndex E t) : (P E (.inr t) × K E (.inr t)) × ZMod (D T) :=
  let x' := x - seedOffset E t j
  let k' := seedSourceInput E t k j
  ((seedC E t x' k' + shift (E.a (.inr t)) (E.b (.inr t)) j.1.2,
    seedBeta E t x' k'), commonZ T x' k')

theorem seedActualForward_zero_eq (x : Plane) (k : Input E) :
    seedActualForward E 0 x k =
      oneForwardOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 0)) (E.b_two_le (.inr 0)))
        (residueEquiv T) (outputEquiv T)
        (fun j => (seedOffset E 0 j).1) x.1 (residue T x) (k (.inr 0)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_zero, seedHigh_zero, commonZ,
    oneForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_one_eq (x : Plane) (k : Input E) :
    seedActualForward E 1 x k =
      twoForwardOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 1)) (E.b_two_le (.inr 1)))
        (residueEquiv T) (outputEquiv T)
        (fun j => (seedOffset E 1 j).1) x.1 (residue T x) (k (.inr 1)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_one, seedHigh_one, commonZ,
    twoForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_bijective (t : Fin 2) (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E t x k) := by
  fin_cases t
  · change Function.Bijective (seedActualForward E (0 : Fin 2) x k)
    rw [seedActualForward_zero_eq]
    apply oneForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 0 j
    · intro j
      exact seedOffset_rhoB E 0 j
    · intro j
      have h := seedOffset_other E (0 : Fin 2) j
      have ha : E.a (.inr (otherSeed (0 : Fin 2))) = 3 := by
        change E.a (.inr (1 : Fin 2)) = 3
        exact seedTwoSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (0 : Fin 2) j).1 : ZMod modulus) = 0) ha) h
  · change Function.Bijective (seedActualForward E (1 : Fin 2) x k)
    rw [seedActualForward_one_eq]
    apply twoForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 1 j
    · intro j
      exact seedOffset_rhoB E 1 j
    · intro j
      have h := seedOffset_other E (1 : Fin 2) j
      have ha : E.a (.inr (otherSeed (1 : Fin 2))) = 2 := by
        change E.a (.inr (0 : Fin 2)) = 2
        exact seedOneSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (1 : Fin 2) j).1 : ZMod modulus) = 0) ha) h

theorem both_seed_tests (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E 0 x k) ∧
      Function.Bijective (seedActualForward E 1 x k) :=
  ⟨seedActualForward_bijective E 0 x k, seedActualForward_bijective E 1 x k⟩

def seedActiveRegion (T : LeanWang.TileSet) (t : Fin 2) : Set (Residues T) :=
  if t = 0 then firstRegion T else secondRegion T

theorem seedUseful_active_iff (t : Fin 2) (s : Residues T) :
    (∃ u v : K E (.inr t), u - v ∈ digitSubgroup E (.inr t) () ∧
      seedUseful E t s u ≠ seedUseful E t s v) ↔ s ∈ seedActiveRegion T t := by
  classical
  fin_cases t
  · change (∃ u v : K E (.inr (0 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (0 : Fin 2)) () ∧
        seedUseful E 0 s u ≠ seedUseful E 0 s v) ↔
          s ∈ seedActiveRegion T (0 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (0 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveOne (residueEquiv T s) ↔ s ∈ firstRegion T := by
      rw [← residueEquiv_first_iff T s]
      cases hs : residueEquiv T s <;> simp [ActiveOne]
    have h := usefulOneOfEq_activity_iff (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 0) ()) hC
      (residueEquiv T s)
    rw [seedActiveRegion, if_pos (rfl : (0 : Fin 2) = 0)]
    simpa only [seedUseful_zero] using h.trans hlabel
  · change (∃ u v : K E (.inr (1 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (1 : Fin 2)) () ∧
        seedUseful E 1 s u ≠ seedUseful E 1 s v) ↔
          s ∈ seedActiveRegion T (1 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (1 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveTwo (residueEquiv T s) ↔ s ∈ secondRegion T := by
      rw [← residueEquiv_second_iff T s]
      cases hs : residueEquiv T s with
      | inl y => simp [ActiveTwo]
      | inr u => cases u <;> simp [ActiveTwo]
    have h := usefulTwoOfEq_activity_iff (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 1) ()) hC
      (residueEquiv T s)
    simpa only [seedUseful_one, seedActiveRegion, if_neg (by decide : (1 : Fin 2) ≠ 0)]
      using h.trans hlabel

end Compiler

end

end TranslationTiling
