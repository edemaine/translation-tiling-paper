/- The collision proof specializes `CycleTests.lean`, adapted from
openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. The sparse family and count are added here. -/
import TranslationTiling.Compiler.CycleTests

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! # Cycle tests supported at a single useful-output value

The collision witnessing simultaneous activity already uses only these maps.
Enumerating arbitrary functions is unnecessary. The smaller family has at most
`∏ j, card (N (cycle (j-1))) * card (U j)` tests.
-/

namespace TranslationTiling.Compiler

open scoped Classical BigOperators
noncomputable section

section Combinatorics

variable {ι : Type*} [Fintype ι]
variable {M N : ι → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable {t : ℕ} [NeZero t]

abbrev SparseCycleIndex (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j))) :=
  ∀ j, N (cycle (j - 1)) × U j

def sparseCycleMaps (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (z : SparseCycleIndex (N := N) cycle U) : ∀ j, N (cycle (j - 1)) → U j :=
  fun j v => if v = (z j).1 then (z j).2 else 0

theorem sparseCycleMap_collision_of_all_active (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j))) (g : ∀ i, M i → N i)
    (hactive : ∀ j, DigitActive (g (cycle j)) (U j)) :
    ∃ (k : ∀ i, M i) (z : SparseCycleIndex (N := N) cycle U)
      (ε : ∀ i, N i), ε ≠ 0 ∧
      cycleMap cycle U (sparseCycleMaps cycle U z) g k 0 =
        cycleMap cycle U (sparseCycleMaps cycle U z) g k ε := by
  choose w w' hmem hne using hactive
  let ε₀ : ∀ j, N (cycle j) := fun j => g (cycle j) (w j) - g (cycle j) (w' j)
  have hε₀ (j : ZMod t) : ε₀ j ≠ 0 := sub_ne_zero.mpr (hne j)
  let ε : ∀ i, N i := cycleExtend cycle ε₀
  let k : ∀ i, M i := cycleExtend cycle w
  let z : SparseCycleIndex (N := N) cycle U :=
    fun j => (ε₀ (j - 1), ⟨w j - w' j, hmem j⟩)
  let d := sparseCycleMaps cycle U z
  have hd₀ (j : ZMod t) : d j 0 = 0 := by
    simp [d, sparseCycleMaps, z, Ne.symm (hε₀ (j - 1))]
  have hdε (j : ZMod t) : d j (ε (cycle (j - 1))) = ⟨w j - w' j, hmem j⟩ := by
    simp [d, sparseCycleMaps, z, ε]
  refine ⟨k, z, ε, ?_, ?_⟩
  · intro hz
    have h := congrFun hz (cycle 0)
    apply hε₀ 0
    simpa only [ε, cycleExtend_apply, Pi.zero_apply] using h
  · change cycleMap cycle U d g k 0 = cycleMap cycle U d g k ε
    funext i
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j, rfl⟩ := hi
      calc
        cycleMap cycle U d g k 0 (cycle j) = g (cycle j) (w j) := by
          simp only [cycleMap_apply_cycle, Pi.zero_apply, hd₀, ZeroMemClass.coe_zero,
            sub_zero, zero_add, k, cycleExtend_apply]
        _ = ε₀ j + g (cycle j) (w' j) := (sub_add_cancel _ _).symm
        _ = cycleMap cycle U d g k ε (cycle j) := by
          rw [cycleMap_apply_cycle, hdε]
          simp only [k, ε, cycleExtend_apply, sub_sub_cancel]
    · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      simp only [cycleMap, Pi.zero_apply, ε, cycleExtend_eq_zero cycle ε₀ hoff,
        cycleShift_eq_zero cycle U d 0 hoff,
        cycleShift_eq_zero cycle U d (cycleExtend cycle ε₀) hoff]

theorem forall_sparseCycleMap_bijective_iff [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (g : ∀ i, M i → N i) :
    (∀ (z : SparseCycleIndex (N := N) cycle U) (k : ∀ i, M i),
      Function.Bijective (cycleMap cycle U (sparseCycleMaps cycle U z) g k)) ↔
      ∃ j, ¬ DigitActive (g (cycle j)) (U j) := by
  constructor
  · intro hall
    by_contra hnone
    have hactive : ∀ j, DigitActive (g (cycle j)) (U j) := by
      simpa only [not_exists, not_not] using hnone
    obtain ⟨k, z, ε, hε, hcollision⟩ :=
      sparseCycleMap_collision_of_all_active cycle U g hactive
    exact hε ((hall z k).1 hcollision).symm
  · rintro ⟨j, hj⟩ z k
    exact cycleMap_bijective_of_inactive cycle U (sparseCycleMaps cycle U z) g k j hj

omit [Fintype ι] [∀ i, AddCommGroup (N i)] in
theorem sparseCycleIndex_card [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j))) [∀ j, Fintype (U j)] :
    Fintype.card (SparseCycleIndex (N := N) cycle U) =
      ∏ j, Fintype.card (N (cycle (j - 1))) * Fintype.card (U j) := by
  simp only [SparseCycleIndex, Fintype.card_pi, Fintype.card_prod]

omit [Fintype ι] [∀ i, AddCommGroup (N i)] in
theorem sparseCycleIndex_card_le [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j))) [∀ j, Fintype (U j)]
    {p q : ℕ} (hN : ∀ i, Fintype.card (N i) ≤ p)
    (hU : ∀ j, Fintype.card (U j) ≤ q) :
    Fintype.card (SparseCycleIndex (N := N) cycle U) ≤ (p * q) ^ t := by
  rw [sparseCycleIndex_card]
  calc
    _ ≤ ∏ _j : ZMod t, p * q :=
      Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hN _) (hU j))
    _ = _ := by simp

end Combinatorics

section Tiles

variable {T : LeanWang.TileSet} (E : EncodingParameters T) {t : ℕ} [NeZero t]

def sparseCycleTiles (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    Finset (Finset (Ambient E)) :=
  Finset.univ.image fun z => cycleTile E cycle labels
    (sparseCycleMaps (M := K E) (N := P E) cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) z)

theorem sparseCycleTiles_subset_cycleTiles (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) :
    sparseCycleTiles E cycle labels ⊆ cycleTiles E cycle labels := by
  intro F hF
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hF
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem nonempty_of_mem_sparseCycleTiles (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) {F : Finset (Ambient E)}
    (hF : F ∈ sparseCycleTiles E cycle labels) : F.Nonempty :=
  nonempty_of_mem_cycleTiles E cycle labels
    (sparseCycleTiles_subset_cycleTiles E cycle labels hF)

theorem sparse_cycle_exclusion_iff (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ sparseCycleTiles E cycle labels, Tiles F (graph o)) ↔
      ∀ x, ∃ j, ¬ Active E o (cycle j) x (labels j) := by
  have hmem : (∀ F ∈ sparseCycleTiles E cycle labels, Tiles F (graph o)) ↔
      ∀ z, Tiles (cycleTile E cycle labels
        (sparseCycleMaps (M := K E) (N := P E) cycle
          (fun j => digitSubgroup E (cycle j) (labels j)) z)) (graph o) := by
    simp only [sparseCycleTiles, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h z
      exact h _ ⟨z, rfl⟩
    · rintro h F ⟨z, rfl⟩
      exact h z
  rw [hmem]
  simp_rw [cycleTile_iff E cycle labels _ o (usefulAt E o) (usefulAt_factor E hdep)]
  constructor
  · intro h x
    exact (forall_sparseCycleMap_bijective_iff (M := K E) (N := P E) cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) (fun i => usefulAt E o i x)).mp
        (fun z k => h z x k)
  · intro h z x k
    exact (forall_sparseCycleMap_bijective_iff (M := K E) (N := P E) cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) (fun i => usefulAt E o i x)).mpr
        (h x) z k

theorem sparseCycleTiles_card_le (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) :
    (sparseCycleTiles E cycle labels).card ≤
      ∏ j, Fintype.card (P E (cycle (j - 1))) *
        Fintype.card (digitSubgroup E (cycle j) (labels j)) := by
  unfold sparseCycleTiles
  apply (Finset.card_image_le.trans (le_of_eq Finset.card_univ)).trans
  exact le_of_eq (sparseCycleIndex_card cycle _)

end Tiles

end
end TranslationTiling.Compiler
