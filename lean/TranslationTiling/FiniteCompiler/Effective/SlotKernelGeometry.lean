import TranslationTiling.FiniteCompiler.Effective.SlotFinite
import TranslationTiling.FiniteCompiler.Effective.SlotEncoding
import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.Effective.GuardedAssembly
import TranslationTiling.FiniteCompiler.SlotLift

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift
open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 5000
variable {k m : ℕ} (s : SlotParameters k m)
local instance : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

def period := ∏ i : SlotRow k m, s.layout.lowSize i

theorem period_pos : 0 < s.period :=
  Finset.prod_pos fun i _ => s.layout.lowSize_pos i

theorem period_dvd : s.period ∣ order s.layout := by
  unfold period order
  apply dvd_mul_of_dvd_right
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  unfold rowModulus
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _) _

instance lowSize_neZero (i : SlotRow k m) : NeZero (s.layout.lowSize i) :=
  ⟨(s.layout.lowSize_pos i).ne'⟩

theorem period_eq_card : s.period = Fintype.card (∀ i, SharedCoordinates.Low s.layout i) := by
  simp only [period,Fintype.card_pi,SharedCoordinates.Low,ZMod.card]

theorem tile_mass (F : Finset (SharedCoordinates.Ambient s.layout))
    (o : SharedCoordinates.Outputs s.layout)
    (h : Tiles F (Set.range (SharedCoordinates.point s.layout o))) :
    F.card * s.period = order s.layout := by
  have hi : Function.Injective (SharedCoordinates.point s.layout o) := by
    intro x y he
    exact ((baseProjection_point s.layout o x).symm.trans
      (congrArg (baseProjection s.layout) he)).trans (baseProjection_point s.layout o y)
  rw [s.period_eq_card,← ZMod.card (order s.layout),Fintype.card_congr s.crt.toEquiv]
  exact card_mul_low_eq_of_tiles_graph F (fun p => (SharedCoordinates.point s.layout o p).2) hi h

theorem encode_mass (F : Finset (SharedCoordinates.Ambient s.layout))
    (o : SharedCoordinates.Outputs s.layout)
    (h : Tiles F (Set.range (SharedCoordinates.point s.layout o))) :
    (cyclicTileSet (order s.layout) (s.encodeTile F)).card * s.period = order s.layout := by
  have he := (cyclicTileSet_image s.layout s.crt (s.encodeTile F)).trans
    (@encodeTile_decode k m s _ _ (fun a b => Classical.propDecidable (a = b)) F)
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (cyclicAmbientEquiv s.layout s.crt).injective] at hcard
  exact (congrArg (· * s.period) hcard).trans (s.tile_mass F o h)

set_option linter.constructorNameAsVariable false in
theorem kernel_column (j : ℤ) :
    (((0 : Plane),((s.period : ℤ)*j : ℤ)) : Plane × ZMod (order s.layout)) ∈
      cyclicTileSet (order s.layout) (s.encodeTile (productKernel s.layout)) := by
  have he := (cyclicTileSet_image s.layout s.crt (s.encodeTile (productKernel s.layout))).trans
    (@encodeTile_decode k m s _ _ (fun a b => Classical.propDecidable (a = b)) _)
  have h : ((0 : Plane),s.crt (((s.period : ℤ)*j : ℤ) : ZMod (order s.layout))) ∈
      productKernel s.layout := by
    rw [mem_productKernel]
    refine Prod.ext rfl (funext fun i => ?_)
    have hd : s.layout.lowSize i ∣ s.period :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hc : ((s.period : ℕ) : ZMod (s.layout.lowSize i)) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [map_intCast]
    change CyclicShear.low (s.layout.lowSize i)
      (((s.period : ℤ)*j : ℤ) : ZMod ((s.layout.lowSize i)^2)) = 0
    rw [CyclicShear.low_intCast,Int.cast_mul,Int.cast_natCast,hc,zero_mul]
  rw [← he] at h
  obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp h
  have heq : q = (((0 : Plane),((s.period : ℤ)*j : ℤ)) : Plane × ZMod (order s.layout)) :=
    (cyclicAmbientEquiv s.layout s.crt).injective hEq
  exact heq ▸ hq

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
