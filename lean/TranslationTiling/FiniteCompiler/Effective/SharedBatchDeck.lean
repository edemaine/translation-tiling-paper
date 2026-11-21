import TranslationTiling.FiniteCompiler.Effective.SharedKernel
import TranslationTiling.FiniteCompiler.SharedActivationBatch

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler.Effective
open scoped Classical

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] (L : Layout I)

def batchDeck (i : I) (rs : List ℕ) {a b : ℕ}
    (indices : List J) (offset : J → Plane) (shift : J → ZMod a × ZMod b) : List NumericalPoint :=
  indices.flatMap fun j => activationBatchCodes
    ((order L,rs),(L.lowSize i,a,b,1225),offset j,((shift j).1.val,(shift j).2.val),true)

/-- The ordinary activation test is a bijection on the observed pair and
one sheared high coordinate, even when the pair uses a shared factor. -/
theorem tiles_batchDeck_iff [NeZero (order L)] (crt : ZMod (order L) ≃+* Factor L)
    {a b : ℕ} [NeZero a] [NeZero b] (ψ : Factor L →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode L n) = ((n : ZMod a),(n : ZMod b)))
    (i : I) (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ j, j ≠ i ∧ L.lowSize j = r)
    (indices : List J) (hi : ∀ j, j ∈ indices)
    (offset : J → Plane) (hoffset : Function.Injective offset)
    (shift : J → ZMod a × ZMod b) (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ c : ZMod a × ZMod b, ∀ d : Low L i,
      ∃ v : Ambient L, baseProjection L v = x ∧ ψ v.2 = c ∧ highCoordinate L i v = d) :
    let src := fun x j => activationSource L i (offset j) ((offset j).1 : Low L i) x
    Tiles ((batchDeck L i rs indices offset shift).toFinset.image (decodePoint L))
        (Set.range (point L o)) ↔
      ∀ x, Function.Bijective (fun j => (ψ (point L o (src x j)).2 + shift j, o.high (src x j) i)) := by
  let src := fun x j => activationSource L i (offset j) ((offset j).1 : Low L i) x
  let tgt := fun v : Ambient L => (ψ v.2,highCoordinate L i v)
  have hs (x : Base L) : Function.Injective (src x) := by
    intro j j' he
    apply hoffset
    exact sub_right_inj.mp (congrArg (fun y : Base L => y.1) he)
  have ht (x : Base L) (y : (ZMod a × ZMod b) × Low L i) :
      ∃ v : Ambient L, baseProjection L v = x ∧ tgt v = y := by
    obtain ⟨v,hx,hc,hd⟩ := htarget x y.1 y.2
    exact ⟨v,hx,Prod.ext hc hd⟩
  apply tiles_indexed_activation_iff _ _ (point_injective L o) (baseProjection L) tgt src hs _ ht
  intro v x
  have hbatch (j : J) :
      (v - point L o x) ∈
        (activationBatchCodes ((order L,rs),(L.lowSize i,a,b,1225),offset j,
            ((shift j).1.val,(shift j).2.val),true)).toFinset.image (decodePoint L) ↔
      ActivationBatch L i ψ (offset j) (shift j) (v-point L o x) := by
    rw [mem_decoded_activation_batch L crt ψ hψ i rs hr]
    simp only [ActivationBatch,true_or,and_true]
  have hmem :
      (v-point L o x) ∈ (batchDeck L i rs indices offset shift).toFinset.image (decodePoint L) ↔
      ∃ j, ActivationBatch L i ψ (offset j) (shift j) (v-point L o x) := by
    simp only [batchDeck, Finset.mem_image, List.mem_toFinset, List.mem_flatMap, hi, true_and]
    constructor
    · rintro ⟨f,⟨j,hf⟩,he⟩
      exact ⟨j,(hbatch j).mp (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,he⟩)⟩
    · rintro ⟨j,hj⟩
      obtain ⟨f,hf,he⟩ := Finset.mem_image.mp ((hbatch j).mpr hj)
      exact ⟨f,⟨j,List.mem_toFinset.mp hf⟩,he⟩
  rw [hmem]
  apply exists_congr
  intro j
  rw [sub_point_activationBatch L i ψ]
  change src (baseProjection L v) j = x ∧ _ ↔ _
  constructor
  · rintro ⟨rfl,hc,hd⟩
    exact ⟨rfl,Prod.ext hc hd⟩
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,congrArg Prod.fst h,congrArg Prod.snd h⟩

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
