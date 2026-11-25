import TranslationTiling.FiniteCompiler.Effective.SlotCRT
import TranslationTiling.FiniteCompiler.SharedDependence

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I)
variable [Fintype (Factor L)]

/-- The kernel graph test in product coordinates. -/
def productKernel : Finset (Ambient L) :=
  (Finset.univ.map ⟨fun a : Factor L => ((0 : Plane),a),
    fun _ _ h => congrArg Prod.snd h⟩).filter (fun v => baseProjection L v = 0)

theorem mem_productKernel (v : Ambient L) :
    v ∈ productKernel L ↔ baseProjection L v = 0 := by
  simp only [productKernel,Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨v.2,Prod.ext (congrArg Prod.fst h).symm rfl⟩,h⟩

theorem productKernel_iff (A : Set (Ambient L)) :
    Tiles (productKernel L) A ↔ ∃ o : Outputs L, Set.range (point L o) = A := by
  rw [tiles_kernel_iff_unique_fibre _ (baseProjection_surjective L) _ (mem_productKernel L)]
  constructor
  · intro hf
    let a (x : Base L) : A := (hf x).choose
    have ha (x : Base L) : baseProjection L (a x) = x := (hf x).choose_spec.1
    refine ⟨outputsOfSection L (fun x => a x) ha,?_⟩
    ext v
    simp only [Set.mem_range,point_outputsOfSection]
    constructor
    · rintro ⟨x,rfl⟩
      exact (a x).property
    · intro hv
      exact ⟨baseProjection L v,congrArg Subtype.val ((hf _).choose_spec.2 ⟨v,hv⟩ rfl).symm⟩
  · rintro ⟨o,rfl⟩ x
    refine ⟨⟨point L o x,⟨x,rfl⟩⟩,baseProjection_point L o x,?_⟩
    rintro ⟨v,⟨y,rfl⟩⟩ h
    change baseProjection L (point L o y) = x at h
    rw [baseProjection_point] at h
    subst y
    rfl

variable {Y : Type*} [AddCommGroup Y]

/-- The useful-coordinate invariance test for an arbitrary base shift. -/
def productInvariance (ψ : Factor L →+ Y) (σ : Base L) : Finset (Ambient L) :=
  (productKernel L).filter (fun v => ψ v.2 ≠ 0) ∪
  ((Finset.univ.map ⟨fun a : Factor L => (σ.1,a),
    fun _ _ h => congrArg Prod.snd h⟩).filter
      (fun v => baseProjection L v = σ ∧ ψ v.2 = 0))

theorem productInvariance_iff (ψ : Factor L →+ Y) (σ : Base L) (o : Outputs L) :
    Tiles (productInvariance L ψ σ) (Set.range (point L o)) ↔
      ∀ x, ψ (point L o (x-σ)).2 = ψ (point L o x).2 := by
  apply tiles_invariance_iff (baseProjection L) (ψ.comp (AddMonoidHom.snd _ _)) _ (baseProjection_point L o)
  intro v
  simp only [productInvariance,Finset.mem_union,Finset.mem_filter,mem_productKernel,
    AddMonoidHom.comp_apply,Finset.mem_map,Finset.mem_univ,true_and]
  apply or_congr_right
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨v.2,Prod.ext (congrArg Prod.fst h.1).symm rfl⟩,h⟩

end

section Dependence

variable {I Y : Type*} [Fintype I] [DecidableEq I] (L : Layout I)

/-- Independence from the lows outside a set follows by testing their
generators individually. -/
theorem factor_selected_lows (f : Base L → Y) (S : Set I)
    (h : ∀ j ∉ S, ∀ v, f (v - lowStep L j) = f v)
    (x : Plane) (u v : ∀ i, Low L i) (hkeep : ∀ j ∈ S, u j = v j) :
    f (x,u) = f (x,v) := by
  have hset (A : Finset I) : f (x,A.piecewise u v) = f (x,v) := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert j A hj ih =>
      rw [Finset.piecewise_insert]
      by_cases hS : j ∈ S
      · have huv : A.piecewise u v j = u j := by
          by_cases hmem : j ∈ A <;> simp [Finset.piecewise,hmem,hkeep j hS]
        rw [← huv,Function.update_eq_self]
        exact ih
      · let w := A.piecewise u v
        obtain ⟨a,ha⟩ := ZMod.intCast_surjective (w j - u j)
        have he : (x,Function.update w j (u j)) = (x,w) - a • lowStep L j := by
          refine Prod.ext (by simp [lowStep]) (funext fun t => ?_)
          by_cases ht : t = j
          · subst t
            simp [lowStep,zsmul_eq_mul,ha]
          · simp [lowStep,ht]
        have hp : Function.Periodic f (lowStep L j) := fun b => by
          simpa using (h j hS (b+lowStep L j)).symm
        change f (x,Function.update w j (u j)) = _
        rw [he,hp.sub_zsmul_eq a]
        exact ih
  simpa using hset Finset.univ

end Dependence
end TranslationTiling.FiniteCompiler.SharedCoordinates
