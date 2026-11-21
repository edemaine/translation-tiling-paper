import TranslationTiling.FiniteCompiler.Effective.GeometryPrimitives

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
open scoped Classical

noncomputable section

local instance compactActivationFrame : SeedFrame := compactSeedFrame

set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

attribute [local irreducible] activationBatchCodes decodeNumericalPoint

def compactFirst (z : ActivationNumbers) : ℤ :=
  let a := z.1.1
  let b := z.1.2.1
  let r := z.1.2.2
  let x := z.2.2.1
  let y := z.2.2.2.1
  let j := z.2.2.2.2
  let ra := Compiler.numericalRank x y j
  let rb := Compiler.numericalRank y x j
  let m := r*a*b
  (residueSearch m [(r,z.2.1), (a,differenceResidue a (2*ra) x),
    (b,differenceResidue b (2*rb) y)] : ℤ) +
    (m : ℤ) * (if ra = x then 0 else 1)

@[fun_prop] theorem compactFirst_primrec : Primrec compactFirst := by
  unfold compactFirst
  have hm : Primrec (fun z : ActivationNumbers => z.1.2.2*z.1.1*z.1.2.1) := by fun_prop
  have hr : Primrec (fun z : ActivationNumbers => residueSearch (z.1.2.2*z.1.1*z.1.2.1)
      [(z.1.2.2,z.2.1),
        (z.1.1,differenceResidue z.1.1 (2*Compiler.numericalRank z.2.2.1 z.2.2.2.1 z.2.2.2.2) z.2.2.1),
        (z.1.2.1,differenceResidue z.1.2.1 (2*Compiler.numericalRank z.2.2.2.1 z.2.2.1 z.2.2.2.2) z.2.2.2.1)]) :=
    residueSearch_primrec.comp (hm.pair (by fun_prop))
  apply intPlus (intCast hr)
  apply intTimes (intCast hm)
  fun_prop

theorem compactFirst_eq {T : System} [AlphabetFamily T] (E : EncodingParameters T)
    (n : Column T) (j : ActivationIndex E (.inl n)) :
    compactFirst (nativeActivationNumbers E (.inl n) j) = ordinaryFirst E n j := by
  let i : Channel T := .inl n
  have ha : differenceResidue (E.a i)
      (2*Compiler.numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val) j.2.1.1.val =
        (compactRhoA j.2).val := by
    rw [differenceResidue_eq,ZMod.natCast_zmod_val]
    simp [compactRhoA,rankA,show FiniteCompiler.numericalRank = Compiler.numericalRank from rfl]
  have hb : differenceResidue (E.b i)
      (2*Compiler.numericalRank j.2.1.2.val j.2.1.1.val j.2.2.val) j.2.1.2.val =
        (compactRhoB j.2).val := by
    rw [differenceResidue_eq,ZMod.natCast_zmod_val]
    simp [compactRhoB,rankB,show FiniteCompiler.numericalRank = Compiler.numericalRank from rfl]
  have hs := residueSearch_of_equiv (activationCRT E i).toEquiv
    ((j.1,compactRhoA j.2),compactRhoB j.2)
    [(E.r i,j.1.val),(E.a i,(compactRhoA j.2).val),(E.b i,(compactRhoB j.2).val)]
    (activationCongruences_iff E i j.1 _ _)
  unfold compactFirst nativeActivationNumbers ordinaryFirst separatedResidueLift
  dsimp only [i,activationModulus] at ha hb hs
  have hc : SeedFrame.compact = true := rfl
  simp only [ordinaryResidue,ordinaryShiftData,ordinaryLiftCode,hc,
    ↓reduceIte, BlockShiftData.compact]
  rw [ha,hb,hs]
  by_cases h : Compiler.numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val = j.2.1.1.val <;>
    simp [show FiniteCompiler.numericalRank = Compiler.numericalRank from rfl,
      extraShift, h, activationModulus] <;> rfl

def compactBatch (env : ActivationEnvironment) (s : ℕ) (j : ActivationCode) :
    List NumericalPoint :=
  let first := compactFirst ((env.2.2.1,env.2.2.2.1,env.2.1),j)
  activationBatchCodes (env.1,env.2,(first,-(s:ℤ)*first),(j.2.1,j.2.2.1),true)

@[fun_prop] theorem compactBatch_primrec :
    Primrec (fun z : ActivationEnvironment × ℕ × ActivationCode => compactBatch z.1 z.2.1 z.2.2) := by
  have hf := compactFirst_primrec.comp (show Primrec (fun z : ActivationEnvironment × ℕ × ActivationCode =>
    ((z.1.2.2.1,z.1.2.2.2.1,z.1.2.1),z.2.2)) by fun_prop)
  unfold compactBatch
  exact activationBatchCodes_primrec.comp
    (pairValue (by fun_prop) (pairValue (by fun_prop) (pairValue
      (hf.pair (intTimes (intNegative (intCast (by fun_prop))) hf)) (by fun_prop))))

def compactCodes (env : ActivationEnvironment) (s : ℕ) : List NumericalPoint :=
  (activationIndices env.2.2.1 env.2.2.2.1 env.2.1).flatMap (compactBatch env s)

@[fun_prop] theorem compactCodes_primrec :
    Primrec (fun z : ActivationEnvironment × ℕ => compactCodes z.1 z.2) := by
  have hp : Primrec (fun z : ActivationEnvironment × ℕ =>
      (z.1.2.2.1, z.1.2.2.2.1, z.1.2.1)) := by fun_prop
  have hg : Primrec (fun z : (ActivationEnvironment × ℕ) × ActivationCode =>
      (z.1.1, z.1.2, z.2)) := by fun_prop
  exact flatMapList
    (f := fun z : ActivationEnvironment × ℕ => activationIndices z.1.2.2.1 z.1.2.2.2.1 z.1.2.1)
    (g := fun z j => compactBatch z.1 z.2 j) (activationIndices_primrec.comp hp)
    (compactBatch_primrec.comp hg)

private theorem compactBatch_correct {T : System} [AlphabetFamily T]
    (E : EncodingParameters T) (n : Column T) (s : ℕ)
    (hs : T.slope n = (s : ℤ)) (j : ActivationIndex E (.inl n)) :
    (compactBatch (nativeActivationEnvironment E (.inl n)) s (rawActivationIndex E (.inl n) j)).toFinset.image
      (decodeNumericalPoint E) =
      activationBatch E (.inl n) (ordinaryOffset E n j)
        (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true := by
  unfold compactBatch
  change (activationBatchCodes (_, _,
    (compactFirst (nativeActivationNumbers E (.inl n) j),
      -(s : ℤ)*compactFirst (nativeActivationNumbers E (.inl n) j)), _, _)).toFinset.image _ = _
  rw [compactFirst_eq]
  simpa only [ordinaryOffset,hs,nativeActivationBatchData,nativeActivationEnvironment,
    rawActivationIndex,shift] using
    (activationBatchCodes_correct E (.inl n) (ordinaryOffset E n j)
      (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true)

theorem compactCodes_correct {T : System} [AlphabetFamily T] (E : EncodingParameters T) (n : Column T)
    (k : ℕ) (hs : T.slope n = (k : ℤ)) :
    (compactCodes (nativeActivationEnvironment E (.inl n)) k).toFinset.image
      (decodeNumericalPoint E) = ordinaryActivationTile E n := by
  ext g
  simp only [compactCodes, nativeActivationEnvironment, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap, activationIndices_native, ordinaryActivationTile,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨code, ⟨j, rfl⟩, hf⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← compactBatch_correct E n k hs j]
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, he⟩
  · rintro ⟨j, hg⟩
    rw [← compactBatch_correct E n k hs j] at hg
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hg
    exact ⟨f, ⟨_, ⟨j, rfl⟩, List.mem_toFinset.mp hf⟩, he⟩

end
end TranslationTiling.FiniteCompiler.Effective
