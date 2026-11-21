import TranslationTiling.FiniteCompiler.Effective.SharedLayout
import TranslationTiling.Compiler.EffectiveLattice

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective
open scoped Classical

noncomputable section

private theorem member_dvd_product {p : ℕ} {l : List ℕ} (hp : p ∈ l) : p ∣ l.prod := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp hp with rfl|h
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih h) a

/-- The kernel contains the full vertical lattice of the shared deck. -/
theorem sharedKernel_column (k : ℕ) (t : ℤ) :
    let R := (guardedModuli (sharedRows k)).prod
    let N := sharedOrder (sharedRows k)
    (((0 : Plane),((R : ℤ)*t : ℤ)) : Plane × ZMod N) ∈
      cyclicTileSet N (kernelCodes N (guardedModuli (sharedRows k))) := by
  let R := (guardedModuli (sharedRows k)).prod
  let N := sharedOrder (sharedRows k)
  let z : ZMod N := ((R : ℤ)*t : ℤ)
  have hRN : R ∣ N := ⟨sharedMass (sharedRows k),(shared_input_mul_mass (sharedRows k)).symm⟩
  letI : NeZero N := ⟨(sharedOrder_pos k).ne'⟩
  change ((0:Plane),z) ∈ cyclicTileSet N (kernelCodes N (guardedModuli (sharedRows k)))
  apply Finset.mem_image.mpr
  refine ⟨((0,0),z.val),List.mem_toFinset.mpr ?_,Prod.ext rfl (ZMod.natCast_zmod_val z)⟩
  unfold kernelCodes
  apply List.mem_map.mpr
  refine ⟨z.val,List.mem_filter.mpr ⟨List.mem_range.mpr (ZMod.val_lt z),decide_eq_true ?_⟩,rfl⟩
  intro r hr
  have hrR : r ∣ R := member_dvd_product hr
  let f := ZMod.castHom (hrR.trans hRN) (ZMod r)
  have hn : (z.val : ZMod r) = f z := by
    rw [← map_natCast f,ZMod.natCast_zmod_val]
  have hf : f z = 0 := by
    change f (((R : ℤ)*t : ℤ) : ZMod N) = 0
    rw [map_intCast,Int.cast_mul,Int.cast_natCast,(ZMod.natCast_eq_zero_iff _ _).mpr hrR,zero_mul]
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp (hn.trans hf))

end
end TranslationTiling.FiniteCompiler.Packed
