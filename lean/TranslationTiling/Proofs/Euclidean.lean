import TranslationTiling.EuclideanDefinitions
import TranslationTiling.Proofs.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-! The paper's sampling/rounding lemma, with arbitrary real translations.
The overlap and floor arguments adapt openai/math's AETilingCountable and
LatticeThickening (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Apache 2.0; see third_party/openai-math.LICENSE). -/

namespace TranslationTiling

noncomputable section
open Set MeasureTheory

abbrev Space (d : ℕ) := Fin d → ℝ

def castLattice {d : ℕ} : Lattice d →+ Space d where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

@[simp] theorem castLattice_apply {d : ℕ} (z : Lattice d) (i : Fin d) :
    castLattice z i = (z i : ℝ) := rfl

def RealCover {d : ℕ} (F : Tile d) (A : Set (Space d)) : Prop :=
  ∀ᵐ x ∂volume, ∃! a : A, x - a.val ∈ CubeUnion F

private theorem cast_injective {d : ℕ} : Function.Injective (@castLattice d) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

private theorem cubeUnion_iff {d : ℕ} (F : Tile d) (x : Space d) :
    x ∈ CubeUnion F ↔ ∃ f ∈ F, x - castLattice f ∈ Set.Icc 0 1 := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun i => sub_nonneg.mpr (h i).1,
      fun i => (sub_le_iff_le_add.mpr (by simpa [add_comm] using (h i).2))⟩
  · rintro ⟨f, hf, hlo, hhi⟩
    refine ⟨f, hf, fun i => ⟨sub_nonneg.mp (hlo i), ?_⟩⟩
    simpa [add_comm] using sub_le_iff_le_add.mp (hhi i)

private theorem ae_noninteger_coordinates (d : ℕ) :
    ∀ᵐ x : Space d ∂volume, ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro z
  exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (z : ℝ)

private def floorLattice {d : ℕ} (x : Space d) : Lattice d := fun i => ⌊x i⌋

private theorem floor_eq_of_voxel {d : ℕ} {x : Space d}
    (hx : ∀ i, ∀ z : ℤ, x i ≠ (z : ℝ)) {z : Lattice d}
    (hz : x - castLattice z ∈ Set.Icc 0 1) : floorLattice x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  have hl := hz.1 i
  have hu := hz.2 i
  have hne : x i ≠ (z i : ℝ) + 1 := by simpa using hx i (z i + 1)
  constructor
  · exact sub_nonneg.mp hl
  · change x i - (z i : ℝ) ≤ 1 at hu
    have := lt_of_le_of_ne (sub_le_iff_le_add.mp hu) (by simpa [add_comm] using hne)
    simpa [add_comm] using this

/-- Thickening an integer exact tiling gives an almost-everywhere real tiling. -/
theorem realTiles_of_tiles {d : ℕ} {F : Tile d} (h : Tiles F) : RealTiles F := by
  obtain ⟨A, hA⟩ := h
  refine ⟨castLattice '' A, (ae_noninteger_coordinates d).mono ?_⟩
  intro x hx
  obtain ⟨⟨a, f⟩, haf⟩ := hA.2 (floorLattice x)
  refine ⟨⟨castLattice a.val, Set.mem_image_of_mem _ a.property⟩, ?_, ?_⟩
  · apply (cubeUnion_iff F _).mpr
    refine ⟨f.val, f.property, ?_, ?_⟩
    · intro i
      have hi := congrFun haf i
      change 0 ≤ x i - (a.val i : ℝ) - (f.val i : ℝ)
      change a.val i + f.val i = ⌊x i⌋ at hi
      have hr : (a.val i : ℝ) + (f.val i : ℝ) = (⌊x i⌋ : ℝ) := by exact_mod_cast hi
      have := Int.floor_le (x i)
      linarith
    · intro i
      have hi := congrFun haf i
      change x i - (a.val i : ℝ) - (f.val i : ℝ) ≤ 1
      change a.val i + f.val i = ⌊x i⌋ at hi
      have hr : (a.val i : ℝ) + (f.val i : ℝ) = (⌊x i⌋ : ℝ) := by exact_mod_cast hi
      have := Int.lt_floor_add_one (x i)
      linarith
  · intro b hb
    obtain ⟨a', ha', hea⟩ := b.property
    obtain ⟨f', hf', hvoxel⟩ := (cubeUnion_iff F _).mp hb
    have hz : x - castLattice (a' + f') ∈ Set.Icc 0 1 := by
      have he : x - castLattice (a' + f') = x - b.val - castLattice f' := by
        rw [map_add, hea]
        abel
      rwa [he]
    have hc := floor_eq_of_voxel hx hz
    have hp : ((⟨a', ha'⟩ : A), (⟨f', hf'⟩ : {f | f ∈ F})) = (a, f) := by
      apply hA.1
      exact hc.symm.trans haf.symm
    apply Subtype.ext
    rw [← hea]
    exact congrArg castLattice (congrArg (fun p : A × {f | f ∈ F} => p.1.val) hp)

private def voxel {d : ℕ} (a : Space d) := Set.Icc a (a + 1)

private theorem voxel_inter_pos {d : ℕ} (a b : Space d)
    (h : ∀ i, |b i - a i| < 1) : 0 < volume (voxel a ∩ voxel b) := by
  have he : voxel a ∩ voxel b =
      Set.Icc (fun i => max (a i) (b i)) (fun i => min (a i + 1) (b i + 1)) := by
    ext x
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨fun i => max_le (ha.1 i) (hb.1 i), fun i => le_min (ha.2 i) (hb.2 i)⟩
    · rintro ⟨hl, hu⟩
      exact ⟨⟨fun i => (le_max_left _ _).trans (hl i),
        fun i => (hu i).trans (min_le_left _ _)⟩,
        ⟨fun i => (le_max_right _ _).trans (hl i),
        fun i => (hu i).trans (min_le_right _ _)⟩⟩
  rw [he, Real.volume_Icc_pi]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply sub_pos.mpr
  apply max_lt
  · apply lt_min
    · linarith
    · have hi := (abs_lt.mp (h i)).1; linarith
  · apply lt_min
    · have hi := (abs_lt.mp (h i)).2; linarith
    · linarith

private theorem RealCover.aedisjoint {d : ℕ} {F : Tile d} {A : Set (Space d)}
    (h : RealCover F A) {a b : A} (hne : a ≠ b) :
    AEDisjoint volume {x | x - a.val ∈ CubeUnion F} {x | x - b.val ∈ CubeUnion F} := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨c, _, hu⟩
  exact hne ((hu a hx).trans (hu b hx').symm)

/-- A real translation set is countable, certified by an injective integer floor map. -/
theorem realCover_floor_injective {d : ℕ} {F : Tile d} {A : Set (Space d)}
    (h : RealCover F A) (hF : F ≠ []) : Function.Injective (fun a : A => floorLattice a.val) := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil F hF
  intro a b he
  by_contra hne
  have hc : ∀ i, |b.val i - a.val i| < 1 := by
    intro i
    have hi := congrFun he i
    have ha := Int.floor_le (a.val i)
    have ha' := Int.lt_floor_add_one (a.val i)
    have hb := Int.floor_le (b.val i)
    have hb' := Int.lt_floor_add_one (b.val i)
    change ⌊a.val i⌋ = ⌊b.val i⌋ at hi
    rw [hi] at ha ha'
    apply abs_lt.mpr
    constructor <;> linarith
  have hpos := voxel_inter_pos (a.val + castLattice f) (b.val + castLattice f) (by
    intro i; simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hc i)
  have hsub (c : A) : voxel (c.val + castLattice f) ⊆ {x | x - c.val ∈ CubeUnion F} := by
    intro x hx
    refine ⟨f, hf, fun i => ?_⟩
    have hl := hx.1 i
    have hu := hx.2 i
    change c.val i + (f i : ℝ) ≤ x i at hl
    change x i ≤ c.val i + (f i : ℝ) + 1 at hu
    exact ⟨by change (f i : ℝ) ≤ x i - c.val i; linarith,
      by change x i - c.val i ≤ (f i : ℝ) + 1; linarith⟩
  exact (ne_of_gt hpos) ((h.aedisjoint hne).mono (hsub a) (hsub b)).eq


private def rounded {d : ℕ} (θ a : Space d) : Lattice d := fun i => ⌈a i - θ i⌉

/-- Sampling one cube away from its boundary gives the rounded integer cube. -/
private theorem sampled_voxel_iff {d : ℕ} (θ a : Space d) (n f : Lattice d)
    (hθ : ∀ i, ∀ z : ℤ, θ i ≠ a i + z) :
    θ + castLattice n - a - castLattice f ∈ Set.Icc 0 1 ↔ n = rounded θ a + f := by
  constructor
  · intro h
    funext i
    have hl := h.1 i
    have hu := h.2 i
    change 0 ≤ θ i + (n i : ℝ) - a i - (f i : ℝ) at hl
    change θ i + (n i : ℝ) - a i - (f i : ℝ) ≤ 1 at hu
    have hne := hθ i (f i - n i + 1)
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one] at hne
    have he : ⌈a i - θ i⌉ = n i - f i := Int.ceil_eq_iff.mpr ⟨by
      simp only [Int.cast_sub]
      by_contra hn
      apply hne
      linarith, by simp only [Int.cast_sub]; linarith⟩
    change n i = ⌈a i - θ i⌉ + f i
    omega
  · intro h
    constructor
    · intro i
      have hi := congrFun h i
      have hc := Int.le_ceil (a i - θ i)
      change 0 ≤ θ i + (n i : ℝ) - a i - (f i : ℝ)
      change n i = ⌈a i - θ i⌉ + f i at hi
      rw [hi, Int.cast_add]
      linarith
    · intro i
      have hi := congrFun h i
      have hc := Int.ceil_lt_add_one (a i - θ i)
      change θ i + (n i : ℝ) - a i - (f i : ℝ) ≤ 1
      change n i = ⌈a i - θ i⌉ + f i at hi
      rw [hi, Int.cast_add]
      linarith

private theorem sampled_tile_iff {d : ℕ} (F : Tile d) (θ a : Space d) (n : Lattice d)
    (hθ : ∀ i, ∀ z : ℤ, θ i ≠ a i + z) :
    θ + castLattice n - a ∈ CubeUnion F ↔ ∃ f ∈ F, n = rounded θ a + f := by
  simp only [cubeUnion_iff, sampled_voxel_iff θ a n _ hθ]

/-- A single translated integer grid avoids all exceptional points and all cube boundaries. -/
private theorem good_grid {d : ℕ} {F : Tile d} {A : Set (Space d)}
    (h : RealCover F A) (hF : F ≠ []) :
    ∃ θ : Space d,
      (∀ n : Lattice d, ∃! a : A, θ + castLattice n - a.val ∈ CubeUnion F) ∧
      (∀ a : A, ∀ i, ∀ z : ℤ, θ i ≠ a.val i + z) := by
  letI : Countable A := (realCover_floor_injective h hF).countable
  have hgood : ∀ᵐ θ : Space d ∂volume,
      ∀ n : Lattice d, ∃! a : A, θ + castLattice n - a.val ∈ CubeUnion F := by
    apply ae_all_iff.mpr
    intro n
    exact (eventually_add_right_iff volume (castLattice n)).mpr h
  have hboundary : ∀ᵐ θ : Space d ∂volume,
      ∀ a : A, ∀ i, ∀ z : ℤ, θ i ≠ a.val i + z := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro z
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (a.val i + z)
  exact (hgood.and hboundary).exists

/-- The converse uses sampling, and assumes no integrality of the original translations. -/
theorem tiles_of_realTiles {d : ℕ} {F : Tile d} (h : RealTiles F) : Tiles F := by
  obtain ⟨A, hA⟩ := h
  have hF : F ≠ [] := by
    obtain ⟨x, a, ha, _⟩ := hA.exists
    obtain ⟨f, hf, _⟩ := ha
    intro he
    simpa [he] using hf
  obtain ⟨θ, hgrid, hθ⟩ := good_grid hA hF
  let B : Set (Lattice d) := Set.range (fun a : A => rounded θ a.val)
  refine ⟨B, (exactTiling_iff B _).mpr ?_⟩
  intro n
  obtain ⟨a, ha, hu⟩ := hgrid n
  obtain ⟨f, hf, he⟩ := (sampled_tile_iff F θ a.val n (hθ a)).mp ha
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · exact ⟨a, by rw [he]; simp⟩
  · intro g hg
    obtain ⟨b, hb⟩ := hg
    have hn : n = rounded θ b.val + g.val := by
      change rounded θ b.val = n - g.val at hb
      rw [hb]
      simp
    have hb' := (sampled_tile_iff F θ b.val n (hθ b)).mpr ⟨g.val, g.property, hn⟩
    have hba : b = a := hu b hb'
    apply Subtype.ext
    have hsum : rounded θ a.val + g.val = rounded θ a.val + f := by
      simpa [hba] using hn.symm.trans he
    exact add_left_cancel hsum

/-- The paper's rounding lemma, in every dimension (including the degenerate dimension zero). -/
theorem realTiles_iff_tiles {d : ℕ} (F : Tile d) : RealTiles F ↔ Tiles F :=
  ⟨tiles_of_realTiles, realTiles_of_tiles⟩

end
end TranslationTiling
