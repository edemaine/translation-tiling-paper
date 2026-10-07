import TranslationTiling.Proofs.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic

namespace TranslationTiling

/-- A finite set of target equations is satisfiable by a Boolean assignment. -/
def LocallyTileable {d : ℕ} (F : Tile d) (X : List (Lattice d)) : Prop :=
  ∃ b : Lattice d → Bool, ∀ x ∈ X,
    ∃ f ∈ F, b (x - f) = true ∧ ∀ g ∈ F, b (x - g) = true → g = f

private def Cylinder {d : ℕ} (F : Tile d) (x : Lattice d) :
    Set (Lattice d → Bool) :=
  {b | ∃ f ∈ F, b (x - f) = true ∧ ∀ g ∈ F, b (x - g) = true → g = f}

private theorem cylinder_closed {d : ℕ} (F : Tile d) (x : Lattice d) :
    IsClosed (Cylinder F x) := by
  classical
  have hf (f : Lattice d) : IsClosed {b : Lattice d → Bool | b (x - f) = true} :=
    by exact (isClosed_discrete ({v : Bool | v = true})).preimage (continuous_apply (A := fun _ => Bool) (x - f))
  have hg (f g : Lattice d) :
      IsClosed {b : Lattice d → Bool | b (x - g) = true → g = f} := by
    by_cases he : g = f
    · simp [he]
    · have hh : {b : Lattice d → Bool | b (x - g) = true → g = f} =
          {b | b (x - g) = false} := by
        ext b
        cases b (x - g) <;> simp [he]
      rw [hh]
      exact (isClosed_discrete ({v : Bool | v = false})).preimage (continuous_apply (A := fun _ => Bool) (x - g))
  have he : Cylinder F x = ⋃ f ∈ (F.toFinset : Finset (Lattice d)),
      {b | b (x - f) = true} ∩ ⋂ g ∈ (F.toFinset : Finset (Lattice d)),
        {b | b (x - g) = true → g = f} := by
    ext b
    simp [Cylinder, and_left_comm]
  rw [he]
  exact isClosed_biUnion_finset fun f _ =>
    (hf f).inter (isClosed_iInter fun g => isClosed_iInter fun _ => hg f g)

/-- Compactness for the exact-cover equations, with arbitrary finite target lists. -/
theorem tiles_iff_locallyTileable {d : ℕ} (F : Tile d) :
    Tiles F ↔ ∀ X, LocallyTileable F X := by
  classical
  constructor
  · rintro ⟨A, hA⟩ X
    refine ⟨fun a => decide (a ∈ A), ?_⟩
    intro x _
    obtain ⟨f, hf, hu⟩ := (exactTiling_iff A _).mp hA x
    refine ⟨f.val, f.property, by simpa using hf, ?_⟩
    intro g hg hbg
    exact congrArg Subtype.val (hu ⟨g, hg⟩ (by simpa using hbg))
  · intro h
    have hfinite (s : Finset (Lattice d)) :
        (⋂ x ∈ s, Cylinder F x).Nonempty := by
      obtain ⟨b, hb⟩ := h s.toList
      exact ⟨b, by simpa [Cylinder] using hb⟩
    obtain ⟨b, hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Lattice d → Bool))).inter_iInter_nonempty
      (Cylinder F) (fun x => cylinder_closed F x) (by simpa using hfinite)
    refine ⟨{a | b a = true}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    have hx : b ∈ Cylinder F x := Set.mem_iInter.mp hb.2 x
    obtain ⟨f, hf, hbf, hu⟩ := hx
    exact ⟨⟨f, hf⟩, hbf, fun g hg => Subtype.ext (hu g.val g.property hg)⟩

end TranslationTiling
