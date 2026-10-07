/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.CyclicTypes
import TranslationTiling.Compiler.CyclicShear

set_option maxRecDepth 1000

namespace TranslationTiling

namespace Compiler


noncomputable section

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

abbrev low (i : Channel T) : ZMod ((E.r i) ^ 2) →+ K E i :=
  CyclicShear.low (E.r i)

abbrev highMul (i : Channel T) : K E i →+ ZMod ((E.r i) ^ 2) :=
  CyclicShear.highMul (E.r i)

abbrev shear (i : Channel T) (x : ℤ) (k b : K E i) : ZMod ((E.r i) ^ 2) :=
  CyclicShear.shear (E.r i) x k b

abbrev shearEquiv (i : Channel T) (x : ℤ) (k : K E i) :
    K E i ≃ {v : ZMod ((E.r i) ^ 2) // low E i v = k} :=
  CyclicShear.shearEquiv (E.r i) x k

@[simp] theorem low_shear (i : Channel T) (x : ℤ) (k b : K E i) :
    low E i (shear E i x k b) = k := CyclicShear.low_shear _ _ _ _

theorem highMul_injective (i : Channel T) : Function.Injective (highMul E i) :=
  CyclicShear.highMul_injective _

@[simp] theorem low_highMul (i : Channel T) (b : K E i) : low E i (highMul E i b) = 0 :=
  CyclicShear.low_highMul _ _

theorem shear_injective (i : Channel T) (x : ℤ) (k : K E i) :
    Function.Injective (shear E i x k) := CyclicShear.shear_injective _ _ _

theorem shear_add (i : Channel T) (x h : ℤ) (k b : K E i) :
    shear E i (x + h) (k + (h : K E i)) b =
      shear E i x k b + (h : ZMod ((E.r i) ^ 2)) :=
  CyclicShear.shear_add _ _ _ _ _

theorem shear_source_add (i : Channel T) (x h : ℤ) (k l b : K E i)
    (hl : (h : K E i) = l) :
    shear E i (x - h) (k - l) b + (h : ZMod ((E.r i) ^ 2)) = shear E i x k b :=
  CyclicShear.shear_source_add _ _ _ _ _ _ hl

def q0 : Ambient E →+ Base E where
  toFun g := (g.1, fun i => low E i (g.2.2 i).1)
  map_zero' := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      exact map_zero (low E i)
  map_add' g h := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      exact map_add (low E i) (g.2.2 i).1 (h.2.2 i).1

@[simp] theorem q0_apply (g : Ambient E) :
    q0 E g = (g.1, fun i => low E i (g.2.2 i).1) := rfl

variable {E}

def point (o : GraphOutputs E) (b : Base E) : Ambient E :=
  (b.1, o.z b, fun i => (shear E i b.1.1 (b.2 i) (o.beta b i), o.c b i))

@[simp] theorem point_horizontal (o : GraphOutputs E) (b : Base E) : (point o b).1 = b.1 := rfl
@[simp] theorem point_z (o : GraphOutputs E) (b : Base E) : (point o b).2.1 = o.z b := rfl
@[simp] theorem point_c (o : GraphOutputs E) (b : Base E) (i : Channel T) :
    ((point o b).2.2 i).2 = o.c b i := rfl
@[simp] theorem point_v (o : GraphOutputs E) (b : Base E) (i : Channel T) :
    ((point o b).2.2 i).1 = shear E i b.1.1 (b.2 i) (o.beta b i) := rfl

@[simp] theorem q0_point (o : GraphOutputs E) (b : Base E) : q0 E (point o b) = b := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    exact low_shear E i b.1.1 (b.2 i) (o.beta b i)

theorem point_injective (o : GraphOutputs E) : Function.Injective (point o) := by
  intro b d h
  have hq := congrArg (q0 E) h
  simpa only [q0_point] using hq

def graph (o : GraphOutputs E) : Set (Ambient E) := Set.range (point o)

@[simp] theorem point_mem_graph (o : GraphOutputs E) (b : Base E) : point o b ∈ graph o :=
  ⟨b, rfl⟩

theorem eq_point_of_mem_graph (o : GraphOutputs E) {g : Ambient E} (hg : g ∈ graph o) :
    g = point o (q0 E g) := by
  obtain ⟨b, rfl⟩ := hg
  rw [q0_point]

def zeroOutputs (E : EncodingParameters T) : GraphOutputs E :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩

theorem q0_surjective (E : EncodingParameters T) : Function.Surjective (q0 E) := by
  intro b
  exact ⟨point (zeroOutputs E) b, q0_point _ _⟩

private theorem section_low (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b)
    (b : Base E) (i : Channel T) : low E i ((s b).2.2 i).1 = b.2 i :=
  congrArg (fun t : Base E => t.2 i) (hs b)

def outputsOfSection (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b) : GraphOutputs E where
  c b i := ((s b).2.2 i).2
  beta b i := (shearEquiv E i b.1.1 (b.2 i)).symm
    ⟨((s b).2.2 i).1, section_low s hs b i⟩
  z b := (s b).2.1

@[simp] theorem point_outputsOfSection (s : Base E → Ambient E)
    (hs : ∀ b, q0 E (s b) = b) (b : Base E) :
    point (outputsOfSection s hs) b = s b := by
  refine Prod.ext ?_ ?_
  · exact (congrArg (fun t : Base E => t.1) (hs b)).symm
  · refine Prod.ext ?_ ?_
    · rfl
    · funext i
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val ((shearEquiv E i b.1.1 (b.2 i)).apply_symm_apply
          ⟨((s b).2.2 i).1, section_low s hs b i⟩)
      · rfl

theorem graph_outputsOfSection (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b) :
    graph (outputsOfSection s hs) = Set.range s := by
  exact congrArg (fun f : Base E → Ambient E => Set.range f)
    (funext (point_outputsOfSection s hs))

end

end Compiler

end TranslationTiling
