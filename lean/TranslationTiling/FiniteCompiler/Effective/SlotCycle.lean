import TranslationTiling.FiniteCompiler.Effective.SlotCRT
import TranslationTiling.FiniteCompiler.FixedCycleTests

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped Classical
noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I) [Fintype (Factor L)]
variable {N : I → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Fintype (N i)]
  [∀ i, DecidableEq (N i)]
variable {t : ℕ} [NeZero t]
variable (cyc : ZMod t ↪ I) (U : ∀ j, AddSubgroup (Low L (cyc j))) (step : ∀ j, U j)

abbrev gateOffset (e : ∀ i, N i) : ∀ i, Low L i :=
  cycleShift cyc U (cycleGeneratorMaps cyc U step) e

/-- A vertical cycle test using one chosen output projection per row. -/
def productCycle (obs : Factor L →+ (∀ i, N i)) : Finset (Ambient L) :=
  (Finset.univ.map ⟨fun a : Factor L => ((0 : Plane),a),fun _ _ h => congrArg Prod.snd h⟩).filter
    (fun v => baseProjection L v = (0,gateOffset L cyc U step (obs v.2)))

theorem mem_productCycle (obs : Factor L →+ (∀ i, N i)) (v : Ambient L) :
    v ∈ productCycle L cyc U step obs ↔ baseProjection L v = (0,gateOffset L cyc U step (obs v.2)) := by
  simp only [productCycle,Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨v.2,Prod.ext (congrArg Prod.fst h).symm rfl⟩,h⟩

theorem productCycle_vertical (obs : Factor L →+ (∀ i, N i)) {v : Ambient L}
    (hv : v ∈ productCycle L cyc U step obs) : v.1 = 0 := by
  exact congrArg Prod.fst ((mem_productCycle L cyc U step obs v).mp hv)

theorem productCycle_iff (hspan : ∀ j u, u ∈ U j → ∃ n : ℕ, n • (step j : Low L (cyc j)) = u)
    (obs : Factor L →+ (∀ i, N i))
    (htarget : Function.Surjective (fun v : Ambient L => (baseProjection L v,obs v.2)))
    (o : Outputs L) (g : Plane → ∀ i, Low L i → N i)
    (hlocal : ∀ x k i, obs (point L o (x,k)).2 i = g x i (k i)) :
    Tiles (productCycle L cyc U step obs) (Set.range (point L o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (g x (cyc j)) (U j) := by
  let ψ := obs.comp (AddMonoidHom.snd Plane (Factor L))
  rw [tiles_offset_iff_permutation (baseProjection L) ψ (point L o) (baseProjection_point L o)
    htarget (fun e => ((0 : Plane),gateOffset L cyc U step e)) _ (mem_productCycle L cyc U step obs)]
  have hmap (x : Plane) (v : ∀ i, Low L i) :
      (fun e => e + ψ (point L o ((x,v)-(0,gateOffset L cyc U step e)))) =
        cycleMap cyc U (cycleGeneratorMaps cyc U step) (g x) v := by
    funext e i
    change e i + obs (point L o (x-0,v-gateOffset L cyc U step e)).2 i = _
    rw [sub_zero,hlocal]
    rfl
  constructor
  · intro h x
    apply (cycleMap_generator_bijective_iff cyc U step hspan (g x)).mp
    intro v
    rw [← hmap]
    exact h (x,v)
  · rintro h ⟨x,v⟩
    rw [hmap]
    exact (cycleMap_generator_bijective_iff cyc U step hspan (g x)).mpr (h x) v

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
