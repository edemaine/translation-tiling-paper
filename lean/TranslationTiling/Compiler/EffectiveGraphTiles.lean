import TranslationTiling.Compiler.EffectiveFiniteFactor
import TranslationTiling.Compiler.EffectiveArithmetic
import TranslationTiling.Compiler.EffectiveResidues
import TranslationTiling.Compiler.GraphTests

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

abbrev NumericalPoint := (ℤ × ℤ) × ℕ

/-- Low-coordinate kernel test on a numerical cyclic representative. -/
def KernelTest (rs : List ℕ) (n : ℕ) : Prop := ∀ r ∈ rs, n % r = 0

instance (rs : List ℕ) (n : ℕ) : Decidable (KernelTest rs n) := by
  unfold KernelTest
  infer_instance

theorem kernelTest_primrec : PrimrecPred (fun z : List ℕ × ℕ => KernelTest z.1 z.2) := by
  unfold KernelTest
  fun_prop

def kernelCodes (N : ℕ) (rs : List ℕ) : List NumericalPoint :=
  ((List.range N).filter fun n => decide (KernelTest rs n)).map fun n => ((0, 0), n)

theorem kernelCodes_primrec : Primrec (fun z : ℕ × List ℕ => kernelCodes z.1 z.2) := by
  unfold kernelCodes
  apply mapList
  · apply filterList (by fun_prop)
    exact kernelTest_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  · fun_prop

def UsefulZero (a b n : ℕ) : Prop := n % a = 0 ∧ n % b = 0

instance (a b n : ℕ) : Decidable (UsefulZero a b n) := by
  unfold UsefulZero
  infer_instance

@[fun_prop] theorem usefulZeroRule {α : Type*} [Primcodable α] {a b n : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hn : Primrec n) :
    PrimrecPred (fun z => UsefulZero (a z) (b z) (n z)) := by
  unfold UsefulZero
  fun_prop

/-- An invariance tile consists of the nonzero useful fibres over zero and
zero useful fibres over the prescribed base displacement. -/
def invarianceCodes (N : ℕ) (rs : List ℕ) (a b : ℕ)
    (h : ℤ × ℤ) (cs : CongruenceList) : List NumericalPoint :=
  (((List.range N).filter fun n => decide (KernelTest rs n ∧ ¬ UsefulZero a b n)).map
    fun n => ((0, 0), n)) ++
  (((List.range N).filter fun n => decide (Congruences cs n ∧ UsefulZero a b n)).map
    fun n => (h, n))

theorem invarianceCodes_primrec : Primrec (fun z :
    (ℕ × List ℕ) × (ℕ × ℕ) × (ℤ × ℤ) × CongruenceList =>
      invarianceCodes z.1.1 z.1.2 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) := by
  have hprojectK : Primrec (fun z :
      ((ℕ × List ℕ) × (ℕ × ℕ) × (ℤ × ℤ) × CongruenceList) × ℕ =>
        (z.1.1.2, z.2)) := by fun_prop
  have hprojectC : Primrec (fun z :
      ((ℕ × List ℕ) × (ℕ × ℕ) × (ℤ × ℤ) × CongruenceList) × ℕ =>
        (z.1.2.2.2, z.2)) := by fun_prop
  have hk := kernelTest_primrec.comp hprojectK
  have hc := congruences_primrec.comp hprojectC
  unfold invarianceCodes
  fun_prop

noncomputable def decodeNumericalPoint {T : LeanWang.TileSet} (E : EncodingParameters T)
    (f : NumericalPoint) : Ambient E := (f.1, numericalFactor E f.2)

theorem kernelTest_iff {T : LeanWang.TileSet} (E : EncodingParameters T) (n : ℕ) :
    KernelTest ((Finset.univ : Finset (Channel T)).toList.map E.r) n ↔
      q0 E (decodeNumericalPoint E ((0, 0), n)) = 0 := by
  simp only [KernelTest, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h
    change (((0, 0) : Plane), fun i => low E i ((n : ZMod (E.r i ^ 2)))) =
      ((0, 0), (0 : Input E))
    refine Prod.ext (by rfl) ?_
    funext i
    change low E i ((n : ZMod (E.r i ^ 2))) = 0
    rw [CyclicShear.low_natCast]
    apply ZMod.val_injective (E.r i)
    simpa only [ZMod.val_natCast, ZMod.val_zero] using h _ ⟨i, rfl⟩
  · intro h r ⟨i, he⟩
    subst r
    have hi := congrFun (congrArg Prod.snd h) i
    change low E i ((n : ZMod (E.r i ^ 2))) = 0 at hi
    rw [CyclicShear.low_natCast] at hi
    simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val hi

theorem lowCongruences_iff {T : LeanWang.TileSet} (E : EncodingParameters T)
    (k : Input E) (n : ℕ) :
    Congruences ((Finset.univ : Finset (Channel T)).toList.map
      (fun i => (E.r i, (k i).val))) n ↔ ∀ i, (n : K E i) = k i := by
  simp only [Congruences, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h i
    apply ZMod.val_injective (E.r i)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using
      h _ ⟨i, rfl⟩
  · intro h c ⟨i, he⟩
    subst c
    have hi := congrArg ZMod.val (h i)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using hi

theorem usefulZero_iff {T : LeanWang.TileSet} (E : EncodingParameters T) (i : Channel T)
    (h : Plane) (n : ℕ) : UsefulZero (E.a i) (E.b i) n ↔
      usefulCoord E i (decodeNumericalPoint E (h, n)) = 0 := by
  change (n % E.a i = 0 ∧ n % E.b i = 0) ↔
    (((n : ZMod (E.a i)), (n : ZMod (E.b i))) = (0, 0))
  simp only [Prod.mk.injEq, ← (ZMod.val_injective (E.a i)).eq_iff,
    ← (ZMod.val_injective (E.b i)).eq_iff, ZMod.val_natCast, ZMod.val_zero]


theorem kernelCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T) :
    (kernelCodes E.cyclicOrder ((Finset.univ : Finset (Channel T)).toList.map E.r)).toFinset.image
      (decodeNumericalPoint E) = kernelTile E := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    exact (mem_kernelTile E _).mpr ((kernelTest_iff E n).mp
      (of_decide_eq_true (List.mem_filter.mp hn).2))
  · intro hg
    have hq := (mem_kernelTile E g).mp hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = (0, 0) := congrArg Prod.fst hq
    have he : decodeNumericalPoint E ((0, 0), n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨((0, 0), n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    apply decide_eq_true ((kernelTest_iff E n).mpr (he.symm ▸ hq))

end TranslationTiling.Compiler.Effective
