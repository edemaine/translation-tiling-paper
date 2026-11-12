import TranslationTiling.Proofs.FacePaths
import Mathlib.Data.Set.Card

/-! The single-entrance argument is independent of the particular key geometry.
No orientation or periodicity assumption is made on the covering family. -/

namespace TranslationTiling.Rotations

variable {d : ℕ}

abbrev Connected (S : Set (Lattice d)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, FacePath (· ∈ S) x y

/-- A nonempty connected component after deleting a vertex. -/
structure CutComponent (S : Set (Lattice d)) (v : Lattice d)
    (K : Set (Lattice d)) : Prop where
  nonempty : K.Nonempty
  subset : K ⊆ S
  avoids : v ∉ K
  connected : Connected K
  closed : ∀ x ∈ K, ∀ y ∈ S, y ≠ v → FaceAdjacent x y → y ∈ K

/-- Exact coverage retains the identity of each placed copy. -/
def ExactCover {ι : Type*} (P : ι → Set (Lattice d)) : Prop :=
  ∀ x, ∃! i, x ∈ P i

theorem ExactCover.same {ι : Type*} {P : ι → Set (Lattice d)}
    (h : ExactCover P) {i j : ι} {x : Lattice d}
    (hi : x ∈ P i) (hj : x ∈ P j) : i = j := by
  obtain ⟨k, _, hk⟩ := h x
  exact (hk i hi).trans (hk j hj).symm

/-- A path that avoids the unique entrance cannot leave the chamber. -/
theorem path_trapped {K S : Set (Lattice d)} {g x y : Lattice d}
    (hx : x ∈ K) (hg : g ∉ S)
    (boundary : ∀ a ∈ K, ∀ b ∈ S, FaceAdjacent a b → b ∈ K ∨ b = g)
    (path : FacePath (· ∈ S) x y) : y ∈ K := by
  induction path with
  | refl => exact hx
  | @tail y z _ hyz ih =>
    rcases boundary y ih z hyz.2.1 hyz.2.2 with hz | hz
    · exact hz
    · exact (hg (hz ▸ hyz.2.1)).elim

/-- Every connected component meeting a one-entrance chamber must use its gate.
The `escape` hypothesis will follow from the cardinalities of the gadget and
the chamber. -/
theorem uses_gate {K S : Set (Lattice d)} {g x : Lattice d}
    (hx : x ∈ K) (hxS : x ∈ S) (conn : Connected S)
    (escape : ∃ y ∈ S, y ∉ K)
    (boundary : ∀ a ∈ K, ∀ b ∈ S, FaceAdjacent a b → b ∈ K ∨ b = g) :
    g ∈ S := by
  by_contra hg
  obtain ⟨y, hy, hyK⟩ := escape
  exact hyK (path_trapped hx hg boundary (conn x hxS y hy))

/-- A chamber in one placed copy is filled by one other copy. The result also
identifies it as a whole cut component of that other copy. -/
theorem chamber_component {ι : Type*} {P : ι → Set (Lattice d)}
    (cover : ExactCover P) (conn : ∀ i, Connected (P i))
    (host : ι) (K : Set (Lattice d)) (g : Lattice d)
    (hK : K.Nonempty) (hconn : Connected K) (hgK : g ∉ K)
    (host_avoids : ∀ x ∈ K, x ∉ P host) (gate_free : g ∉ P host)
    (boundary : ∀ x ∈ K, ∀ y, FaceAdjacent x y → y ∈ K ∨ y = g ∨ y ∈ P host)
    (escape : ∀ i, ∃ y ∈ P i, y ∉ K) :
    ∃ i, g ∈ P i ∧ i ≠ host ∧ CutComponent (P i) g K := by
  obtain ⟨i, hi, _⟩ := cover g
  have ine : i ≠ host := by intro he; exact gate_free (he ▸ hi)
  have inside (x : Lattice d) (hx : x ∈ K) : x ∈ P i := by
    obtain ⟨j, hj, _⟩ := cover x
    have jne : j ≠ host := by intro he; exact host_avoids x hx (he ▸ hj)
    have hjg : g ∈ P j := uses_gate hx hj (conn j) (escape j) (by
      intro a ha b hb hab
      rcases boundary a ha b hab with hbK | hbG | hbH
      · exact Or.inl hbK
      · exact Or.inr hbG
      · exact (jne (cover.same hb hbH)).elim)
    exact cover.same hjg hi ▸ hj
  refine ⟨i, hi, ine, hK, inside, hgK, hconn, ?_⟩
  intro x hx y hy hyG hxy
  rcases boundary x hx y hxy with hyK | hyGate | hyHost
  · exact hyK
  · exact (hyG hyGate).elim
  · exact (ine (cover.same hy hyHost)).elim

/-- Cardinality supplies the escape hypothesis without a search for an exit. -/
theorem escape_of_card {K S : Set (Lattice d)} (hK : K.Finite)
    (hcard : K.ncard < S.ncard) : ∃ y ∈ S, y ∉ K := by
  by_contra! h
  exact (not_le_of_gt hcard) (Set.ncard_le_ncard h hK)

end TranslationTiling.Rotations
