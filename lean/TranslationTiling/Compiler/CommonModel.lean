/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.OrdinaryActivation
import TranslationTiling.Compiler.CommonSeedOutputs
import TranslationTiling.Compiler.ConstraintCycles

namespace TranslationTiling

noncomputable section

namespace Compiler.CommonModel

variable {T : LeanWang.TileSet} (E : EncodingParameters T) (W : WordArray T)

def outputs : GraphOutputs E where
  c b i := match i with
    | .inl n => ordinaryUseful E W n b.1 (b.2 (.inl n))
    | .inr t => seedC E t b.1 b.2
  beta b i := match i with
    | .inl n => ordinaryHigh E W n b.1 (b.2 (.inl n))
    | .inr t => seedBeta E t b.1 b.2
  z b := SharedSeed.commonZ T b.1 b.2

def commonGraph : Set (Ambient E) := graph (outputs E W)

@[simp] theorem outputs_c_ordinary (n : Column T) (x : Plane) (k : Input E) :
    (outputs E W).c (x,k) (.inl n) = ordinaryUseful E W n x (k (.inl n)) := rfl

@[simp] theorem outputs_c_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E W).c (x,k) (.inr t) = seedC E t x k := rfl

@[simp] theorem outputs_beta_ordinary (n : Column T) (x : Plane) (k : Input E) :
    (outputs E W).beta (x,k) (.inl n) = ordinaryHigh E W n x (k (.inl n)) := rfl

@[simp] theorem outputs_beta_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E W).beta (x,k) (.inr t) = seedBeta E t x k := rfl

@[simp] theorem outputs_z (x : Plane) (k : Input E) :
    (outputs E W).z (x,k) = SharedSeed.commonZ T x k := rfl

@[simp] theorem usefulAt_ordinary (n : Column T) (x : Plane) (w : K E (.inl n)) :
    usefulAt E (outputs E W) (.inl n) x w = ordinaryUseful E W n x w := by
  simp [usefulAt]

@[simp] theorem usefulAt_seed (t : Fin 2) (x : Plane) (w : K E (.inr t)) :
    usefulAt E (outputs E W) (.inr t) x w =
      seedUseful E t (SharedSeed.residue T x) w := by
  simp [usefulAt, seedC]

theorem outputs_hasDependence : HasDependence E (outputs E W) := by
  constructor
  · intro n x k
    simp only [outputs_c_ordinary, ordinaryFactor, usefulAt_ordinary]
    apply ordinaryUseful_eq_of_lineValue_eq E W n
    simp
  · intro t x k
    simp only [outputs_c_seed, seedFactor, usefulAt_seed, seedC]
    have hr : SharedSeed.residue T (seedRepresentative T (seedResidue T x)) =
        SharedSeed.residue T x :=
      seedResidue_representative (T := T) (seedResidue T x)
    rw [hr]

theorem active_ordinary_iff (n : Column T) (x : Plane) (j : Symbol T) :
    Active E (outputs E W) (.inl n) x j ↔ j = ordinarySymbol W n x := by
  simpa only [Active, DigitActive, usefulAt_ordinary] using
    ordinaryUseful_active_iff E W n x j

theorem active_seed_iff (t : Fin 2) (x : Plane) :
    Active E (outputs E W) (.inr t) x () ↔
      SharedSeed.residue T x ∈ seedActiveRegion T t := by
  simpa only [Active, DigitActive, usefulAt_seed] using
    seedUseful_active_iff E t (SharedSeed.residue T x)

theorem active_word_allowed (hrule : Sudoku.LineRule W) (x : Plane) (w : Word T)
    (hw : ∀ n, Active E (outputs E W) (.inl n) x (w n)) : Allowed T w := by
  have he : w = ordinaryWord W x :=
    funext fun n => (active_ordinary_iff E W n x (w n)).mp (hw n)
  rw [he]
  exact ordinaryWord_allowed W hrule x

theorem active_seed_forces_symbol
    (hseedW : ∀ t n x, SharedSeed.residue T x ∈ seedActiveRegion T t →
      SeedSet t (W n (lineValue n x)))
    (t : Fin 2) (n : Column T) (x : Plane)
    (j : Symbol T) (ht : Active E (outputs E W) (.inr t) x ())
    (hj : Active E (outputs E W) (.inl n) x j) : SeedSet t j := by
  rw [(active_ordinary_iff E W n x j).mp hj]
  exact hseedW t n x ((active_seed_iff E W t x).mp ht)

theorem commonGraph_tiles_kernel : Tiles (kernelTile E) (commonGraph E W) :=
  kernelTile_graph E (outputs E W)

end Compiler.CommonModel

end

end TranslationTiling
