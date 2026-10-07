/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Proofs.StackingContributions

namespace TranslationTiling.Stacking

universe uH uK uι
variable {H : Type uH} {K : Type uK} {ι : Type uι}
variable [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]

theorem tiles_stack_lift
    {H : Type uH} {K : Type uK} {ι : Type uι}
    [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]
    {F : ι → Finset H} {E : ι → Finset K} {A : Set H}
    (hpart : IsColorPartition E) (hA : ∀ ν, Covers (F ν) A) :
    Covers (stack F E) (A ×ˢ ({0} : Set K)) := by
  classical
  apply covers_iff_unique_tile.mpr
  intro x
  obtain ⟨ν, hν, _⟩ := hpart x.2
  obtain ⟨f, hf, huniq⟩ := covers_iff_unique_tile.mp (hA ν) x.1
  refine ⟨⟨((f : H), x.2), mem_stack.mpr ⟨ν, f.property, hν⟩⟩, ?_, ?_⟩
  · change x.1 - (f : H) ∈ A ∧ x.2 - x.2 ∈ ({0} : Set K)
    exact ⟨hf, by simp⟩
  · intro y hy
    change x.1 - y.1.1 ∈ A ∧ x.2 - y.1.2 ∈ ({0} : Set K) at hy
    obtain ⟨μ, hyF, hyE⟩ := mem_stack.mp y.property
    have hy2 : y.1.2 = x.2 := (sub_eq_zero.mp (Set.mem_singleton_iff.mp hy.2)).symm
    have hμν : μ = ν := hpart.eq_of_mem (hy2 ▸ hyE) hν
    cases hμν
    have hy1 : (⟨y.1.1, hyF⟩ : ↥(F ν)) = f := huniq ⟨y.1.1, hyF⟩ hy.1
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hy1) hy2

theorem exists_tiles_stack_iff {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) :
    (∃ A : Set H, ∀ ν, Covers (F ν) A) ↔
      ∃ B : Set (H × K), Covers (stack F E) B := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A ×ˢ ({0} : Set K), tiles_stack_lift hpart hA⟩
  · rintro ⟨B, hB⟩
    exact ⟨Prod.fst '' B, tiles_of_tiles_stack hpart hfull hE hB⟩

end TranslationTiling.Stacking
