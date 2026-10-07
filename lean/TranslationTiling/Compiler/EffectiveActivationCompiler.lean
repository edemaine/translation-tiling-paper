import TranslationTiling.Compiler.EffectiveActivationIndices
import TranslationTiling.Compiler.EffectiveActivationBatch
import TranslationTiling.Compiler.EffectiveGraphCompiler

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

abbrev ActivationEnvironment := (ℕ × List ℕ) × (ℕ × ℕ × ℕ × ℕ)

def ordinaryBatchCodes (env : ActivationEnvironment) (column : ℕ)
    (j : ActivationCode) : List NumericalPoint :=
  let first := numericalActivationFirst ((env.2.2.1, env.2.2.2.1, env.2.1), j)
  activationBatchCodes (env.1, env.2, (first, -(column : ℤ) * first), (j.2.1, j.2.2.1), true)

theorem ordinaryBatchCodes_primrec : Primrec (fun z : ActivationEnvironment × ℕ × ActivationCode =>
    ordinaryBatchCodes z.1 z.2.1 z.2.2) := by
  have hp : Primrec (fun z : ActivationEnvironment × ℕ × ActivationCode =>
      ((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2)) := by fun_prop
  have hf := numericalActivationFirst_primrec.comp hp
  have hd : Primrec (fun z : ActivationEnvironment × ℕ × ActivationCode =>
      (z.1.1, z.1.2, (numericalActivationFirst
        ((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2),
         -(z.2.1 : ℤ) * numericalActivationFirst
           ((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2)),
        (z.2.2.2.1, z.2.2.2.2.1), true)) :=
    pairValue (by fun_prop) (pairValue (by fun_prop)
      (pairValue (hf.pair (intTimes (intNegative (intCast (by fun_prop))) hf)) (by fun_prop)))
  have h := activationBatchCodes_primrec.comp hd
  exact h

def ordinaryCodes (env : ActivationEnvironment) (column : ℕ) : List NumericalPoint :=
  (activationIndices env.2.2.1 env.2.2.2.1 env.2.1).flatMap (ordinaryBatchCodes env column)

theorem ordinaryCodes_primrec : Primrec (fun z : ActivationEnvironment × ℕ =>
    ordinaryCodes z.1 z.2) := by
  have hp : Primrec (fun z : ActivationEnvironment × ℕ =>
      (z.1.2.2.1, z.1.2.2.2.1, z.1.2.1)) := by fun_prop
  have hi := activationIndices_primrec.comp hp
  have hgdata : Primrec (fun z : (ActivationEnvironment × ℕ) × ActivationCode =>
      (z.1.1, z.1.2, z.2)) := by fun_prop
  have hg := ordinaryBatchCodes_primrec.comp hgdata
  have h := flatMapList
    (f := fun z : ActivationEnvironment × ℕ =>
      activationIndices z.1.2.2.1 z.1.2.2.2.1 z.1.2.1)
    (g := fun z j => ordinaryBatchCodes z.1 z.2 j) hi hg
  exact h

def seedBatchCodes (env : ActivationEnvironment) (other W : ℕ)
    (j : SeedCode) : List NumericalPoint :=
  let first := numericalSeedFirst
    (((env.2.2.1, env.2.2.2.1, env.2.1), j.1), (W, other, j.2.1, j.2.2))
  activationBatchCodes (env.1, env.2, (first, (j.2.2 : ℤ)),
    (j.1.2.1, j.1.2.2.1), false)

theorem seedBatchCodes_primrec : Primrec (fun z :
    ActivationEnvironment × (ℕ × ℕ) × SeedCode => seedBatchCodes z.1 z.2.1.1 z.2.1.2 z.2.2) := by
  have hp : Primrec (fun z : ActivationEnvironment × (ℕ × ℕ) × SeedCode =>
      (((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2.1),
        (z.2.1.2, z.2.1.1, z.2.2.2.1, z.2.2.2.2))) := by fun_prop
  have hf := numericalSeedFirst_primrec.comp hp
  have hd : Primrec (fun z : ActivationEnvironment × (ℕ × ℕ) × SeedCode =>
      (z.1.1, z.1.2, (numericalSeedFirst
        (((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2.1),
          (z.2.1.2, z.2.1.1, z.2.2.2.1, z.2.2.2.2)), (z.2.2.2.2 : ℤ)),
        (z.2.2.1.2.1, z.2.2.1.2.2.1), false)) := pairValue (Primrec.fst.comp Primrec.fst)
    (pairValue (Primrec.snd.comp Primrec.fst)
      (pairValue (hf.pair (intCast (by fun_prop))) (by fun_prop)))
  have h := activationBatchCodes_primrec.comp hd
  exact h

def seedCodes (env : ActivationEnvironment) (other W : ℕ) : List NumericalPoint :=
  (seedIndices env.2.2.1 env.2.2.2.1 env.2.1 W).flatMap (seedBatchCodes env other W)

theorem seedCodes_primrec : Primrec (fun z : ActivationEnvironment × (ℕ × ℕ) =>
    seedCodes z.1 z.2.1 z.2.2) := by
  have hp : Primrec (fun z : ActivationEnvironment × (ℕ × ℕ) =>
      ((z.1.2.2.1, z.1.2.2.2.1, z.1.2.1), z.2.2)) := by fun_prop
  have hi := seedIndices_primrec.comp hp
  have hgdata : Primrec (fun z : (ActivationEnvironment × (ℕ × ℕ)) × SeedCode =>
      (z.1.1, z.1.2, z.2)) := by fun_prop
  have hg := seedBatchCodes_primrec.comp hgdata
  have h := flatMapList
    (f := fun z : ActivationEnvironment × (ℕ × ℕ) =>
      seedIndices z.1.2.2.1 z.1.2.2.2.1 z.1.2.1 z.2.2)
    (g := fun z j => seedBatchCodes z.1 z.2.1 z.2.2 j) hi hg
  exact h

open scoped Classical

noncomputable def nativeActivationEnvironment {T : LeanWang.TileSet}
    (E : EncodingParameters T) (i : Channel T) : ActivationEnvironment :=
  ((E.cyclicOrder, ((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r),
    (E.r i, E.a i, E.b i, D T))

theorem ordinaryBatchCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T)
    (n : Column T) (j : ActivationIndex E (.inl n)) :
    (ordinaryBatchCodes (nativeActivationEnvironment E (.inl n)) n.val
      (rawActivationIndex E (.inl n) j)).toFinset.image (decodeNumericalPoint E) =
      activationBatch E (.inl n) (ordinaryOffset E n j)
        (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true := by
  unfold ordinaryBatchCodes
  change (activationBatchCodes (_, _,
    (numericalActivationFirst (nativeActivationNumbers E (.inl n) j),
      -(n.val : ℤ) * numericalActivationFirst (nativeActivationNumbers E (.inl n) j)), _, _)).toFinset.image _ = _
  rw [numericalActivationFirst_eq]
  exact activationBatchCodes_correct E (.inl n) _ _ _

theorem seedBatchCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) :
    (seedBatchCodes (nativeActivationEnvironment E (.inr t))
      (E.a (.inr (otherSeed t))) residueModulus (rawSeedIndex E t j)).toFinset.image
        (decodeNumericalPoint E) = activationBatch E (.inr t) (seedOffset E t j)
          (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false := by
  unfold seedBatchCodes
  change (activationBatchCodes (_, _,
    (numericalSeedFirst (nativeSeedNumbers E t j), (j.2.2.val : ℤ)), _, _)).toFinset.image _ = _
  rw [numericalSeedFirst_eq]
  exact activationBatchCodes_correct E (.inr t) _ _ _

theorem ordinaryCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T) (n : Column T) :
    (ordinaryCodes (nativeActivationEnvironment E (.inl n)) n.val).toFinset.image
      (decodeNumericalPoint E) = ordinaryActivationTile E n := by
  ext g
  simp only [ordinaryCodes, nativeActivationEnvironment, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap, activationIndices_native, ordinaryActivationTile,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨code, ⟨j, rfl⟩, hf⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← ordinaryBatchCodes_correct E n j]
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, he⟩
  · rintro ⟨j, hg⟩
    rw [← ordinaryBatchCodes_correct E n j] at hg
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hg
    exact ⟨f, ⟨_, ⟨j, rfl⟩, List.mem_toFinset.mp hf⟩, he⟩

theorem seedCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T) (t : Fin 2) :
    (seedCodes (nativeActivationEnvironment E (.inr t)) (E.a (.inr (otherSeed t)))
      residueModulus).toFinset.image (decodeNumericalPoint E) = seedActivationTile E t := by
  ext g
  simp only [seedCodes, nativeActivationEnvironment, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap, seedIndices_native, seedActivationTile,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨code, ⟨j, rfl⟩, hf⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← seedBatchCodes_correct E t j]
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, he⟩
  · rintro ⟨j, hg⟩
    rw [← seedBatchCodes_correct E t j] at hg
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hg
    exact ⟨f, ⟨_, ⟨j, rfl⟩, List.mem_toFinset.mp hf⟩, he⟩

end TranslationTiling.Compiler.Effective
