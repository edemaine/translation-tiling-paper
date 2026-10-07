import TranslationTiling.Compiler.EffectiveGraphTiles
import TranslationTiling.Compiler.ActivationTiles

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

abbrev ActivationBatchData := (ℕ × List ℕ) × (ℕ × ℕ × ℕ × ℕ) ×
  Plane × (ℕ × ℕ) × Bool

def ActivationBatchTest (z : ActivationBatchData) (n : ℕ) : Prop :=
  n % z.2.1.1 ^ 2 = (z.2.2.1.1 % (z.2.1.1 ^ 2 : ℕ)).toNat ∧
  n % z.2.1.2.1 = z.2.2.2.1.1 % z.2.1.2.1 ∧
  n % z.2.1.2.2.1 = z.2.2.2.1.2 % z.2.1.2.2.1 ∧
  KernelTest z.1.2 n ∧ (z.2.2.2.2 = true ∨ n % z.2.1.2.2.2 = 0)

instance (z : ActivationBatchData) (n : ℕ) : Decidable (ActivationBatchTest z n) := by
  unfold ActivationBatchTest
  infer_instance

theorem activationBatchTest_primrec : PrimrecPred (fun z : ActivationBatchData × ℕ =>
    ActivationBatchTest z.1 z.2) := by
  have hp : Primrec (fun z : ActivationBatchData × ℕ => (z.1.1.2, z.2)) := by fun_prop
  have hk := kernelTest_primrec.comp hp
  unfold ActivationBatchTest
  simp only [pow_two]
  fun_prop

def activationBatchCodes (z : ActivationBatchData) : List NumericalPoint :=
  ((List.range z.1.1).filter fun n => decide (ActivationBatchTest z n)).map
    fun n => (z.2.2.1, n)

theorem activationBatchCodes_primrec : Primrec activationBatchCodes := by
  unfold activationBatchCodes
  apply mapList
  · exact filterList (by fun_prop) activationBatchTest_primrec
  · fun_prop

open scoped Classical

noncomputable def nativeActivationBatchData {T : LeanWang.TileSet}
    (E : EncodingParameters T) (i : Channel T) (h : Plane) (e : P E i)
    (freeZ : Bool) : ActivationBatchData :=
  ((E.cyclicOrder, ((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r),
    (E.r i, E.a i, E.b i, D T), h, (e.1.val, e.2.val), freeZ)

theorem activationBatchTest_iff {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (h : Plane) (e : P E i) (freeZ : Bool) (n : ℕ) :
    ActivationBatchTest (nativeActivationBatchData E i h e freeZ) n ↔
      decodeNumericalPoint E (h, n) ∈ activationBatch E i h e freeZ := by
  have hother : KernelTest
      (((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r) n ↔
      ∀ j, j ≠ i → low E j (n : ZMod (E.r j ^ 2)) = 0 := by
    simp only [KernelTest, List.mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and, CyclicShear.low_natCast]
    constructor
    · intro hn j hj
      apply ZMod.val_injective (E.r j)
      simpa only [ZMod.val_natCast, ZMod.val_zero] using hn _ ⟨j, hj, rfl⟩
    · intro hn r ⟨j, hj, he⟩
      subst r
      simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val (hn j hj)
  rw [mem_activationBatch]
  change ActivationBatchTest (nativeActivationBatchData E i h e freeZ) n ↔
    h = h ∧ (n : ZMod (E.r i ^ 2)) = (h.1 : ZMod (E.r i ^ 2)) ∧
    (((n : ZMod (E.a i)), (n : ZMod (E.b i))) = e) ∧
    (∀ j, j ≠ i → low E j (n : ZMod (E.r j ^ 2)) = 0) ∧
    (freeZ = true ∨ (n : ZMod (D T)) = 0)
  simp only [true_and, ← hother, ← (ZMod.val_injective (E.r i ^ 2)).eq_iff,
    ← (ZMod.val_injective (D T)).eq_iff, ZMod.val_natCast, ZMod.val_intCast,
    ZMod.val_zero, Prod.ext_iff, ← (ZMod.val_injective (E.a i)).eq_iff,
    ← (ZMod.val_injective (E.b i)).eq_iff, ZMod.val_natCast]
  unfold ActivationBatchTest nativeActivationBatchData
  dsimp only
  have hval : (h.1 : ZMod (E.r i ^ 2)).val = (h.1 % (E.r i ^ 2 : ℕ)).toNat := by
    have hv := congrArg Int.toNat (ZMod.val_intCast (n := E.r i ^ 2) h.1)
    simpa only [Int.toNat_natCast] using hv
  rw [hval]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt e.1), Nat.mod_eq_of_lt (ZMod.val_lt e.2)]
  tauto

theorem activationBatchCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (h : Plane) (e : P E i) (freeZ : Bool) :
    (activationBatchCodes (nativeActivationBatchData E i h e freeZ)).toFinset.image
      (decodeNumericalPoint E) = activationBatch E i h e freeZ := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    exact (activationBatchTest_iff E i h e freeZ n).mp
      (of_decide_eq_true (List.mem_filter.mp hn).2)
  · intro hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = h := ((mem_activationBatch E i h e freeZ g).mp hg).1
    have he : decodeNumericalPoint E (h, n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨(h, n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    exact decide_eq_true ((activationBatchTest_iff E i h e freeZ n).mpr (he.symm ▸ hg))

end TranslationTiling.Compiler.Effective
