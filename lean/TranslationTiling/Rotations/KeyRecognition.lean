import TranslationTiling.Rotations.Chambers

namespace TranslationTiling.Rotations

variable {d : ℕ}

theorem CutComponent.absorbs {S K A : Set (Lattice d)} {v x : Lattice d}
    (c : CutComponent S v K) (conn : Connected A) (sub : A ⊆ S)
    (avoids : v ∉ A) (hxA : x ∈ A) (hxK : x ∈ K) : A ⊆ K := by
  intro y hy
  exact path_trapped hxK avoids (by
    intro a ha b hb hab
    exact Or.inl (c.closed a ha b (sub hb) (by intro he; exact avoids (he ▸ hb)) hab))
    (conn x hxA y hy)

/-- Local, finite conditions sufficient for recognizing a key by the cardinality
of a component exposed when one voxel is deleted. -/
structure KeyedBody (ι : Type*) (S B : Set (Lattice d)) (keys : ι → Set (Lattice d))
    (gate attach : ι → Lattice d) (k : ℕ) : Prop where
  body_finite : B.Finite
  body_large : k + 1 < B.ncard
  body_subset : B ⊆ S
  punctured : ∀ v, Connected (B \ {v})
  parts : ∀ x ∈ S, x ∈ B ∨ ∃ i, x ∈ keys i
  key_subset : ∀ i, keys i ⊆ S
  key_finite : ∀ i, (keys i).Finite
  key_size : ∀ i, (keys i).ncard = k + 1
  key_connected : ∀ i, Connected (keys i)
  gate_mem : ∀ i, gate i ∈ keys i
  disjoint_body : ∀ i, Disjoint (keys i) B
  boundary : ∀ i, ∀ x ∈ keys i, ∀ y ∈ S, FaceAdjacent x y → y ∈ keys i ∨ y ∈ B
  attachment : ∀ i, attach i ∈ B ∧ FaceAdjacent (gate i) (attach i)

/-- A component of the designated size must be a whole key minus its gate.
This implication does not assume that the key has no internal cut vertices. -/
theorem KeyedBody.recognize {ι : Type*} {S B : Set (Lattice d)}
    {keys : ι → Set (Lattice d)} {gate attach : ι → Lattice d} {k : ℕ}
    (b : KeyedBody ι S B keys gate attach k)
    {v : Lattice d} {K : Set (Lattice d)} (c : CutComponent S v K)
    (hK : K.Finite) (hcard : K.ncard = k) :
    ∃ i, v = gate i ∧ K = keys i \ {gate i} := by
  have noBody (x : Lattice d) (hx : x ∈ K) : x ∉ B := by
    intro hxB
    have hxv : x ≠ v := by intro he; exact c.avoids (he ▸ hx)
    have sub : B \ {v} ⊆ K := c.absorbs (b.punctured v)
      (fun _ hy => b.body_subset hy.1) (by simp) ⟨hxB, hxv⟩ hx
    have hle := Set.ncard_le_ncard sub hK
    have hp := Set.pred_ncard_le_ncard_sdiff_singleton B v
    have hb := b.body_large
    omega
  obtain ⟨x, hx⟩ := c.nonempty
  obtain hxB | ⟨i, hi⟩ := b.parts x (c.subset hx)
  · exact (noBody x hx hxB).elim
  have subsetKey : K ⊆ keys i := by
    intro y hy
    have path := c.connected x hx y hy
    induction path with
    | refl => exact hi
    | @tail y z _ hyz ih =>
      rcases b.boundary i y (ih hyz.1) z (c.subset hyz.2.1) hyz.2.2 with hz | hz
      · exact hz
      · exact (noBody z hyz.2.1 hz).elim
  have hvKey : v ∈ keys i := by
    by_contra hv
    have sub := c.absorbs (b.key_connected i) (b.key_subset i) hv hi hx
    have hle := Set.ncard_le_ncard sub hK
    have hk := b.key_size i
    omega
  have hvBody : v ∉ B := fun hv => Set.disjoint_left.mp (b.disjoint_body i) hvKey hv
  have gate_eq : v = gate i := by
    by_contra hne
    have hgate : gate i ∉ K := by
      intro hg
      have att := b.attachment i
      have hvatt : attach i ≠ v := by intro he; exact hvBody (he ▸ att.1)
      exact noBody _ (c.closed _ hg _ (b.body_subset att.1) hvatt att.2) att.1
    have sub : K ⊆ (keys i \ {v}) \ {gate i} := by
      intro y hy
      exact ⟨⟨subsetKey hy, by intro he; exact c.avoids (he ▸ hy)⟩,
        by intro he; exact hgate (he ▸ hy)⟩
    have hle := Set.ncard_le_ncard sub ((b.key_finite i).sdiff.sdiff)
    have gateLeft : gate i ∈ keys i \ {v} := ⟨b.gate_mem i, Ne.symm hne⟩
    have hc₁ := Set.ncard_sdiff_singleton_add_one hvKey (b.key_finite i)
    have hc₂ := Set.ncard_sdiff_singleton_add_one gateLeft (b.key_finite i).sdiff
    have hk := b.key_size i
    omega
  refine ⟨i, gate_eq, ?_⟩
  apply Set.eq_of_subset_of_ncard_le
  · intro y hy
    exact ⟨subsetKey hy, by intro he; exact c.avoids ((he.trans gate_eq.symm) ▸ hy)⟩
  · have h := Set.ncard_sdiff_singleton_add_one (b.gate_mem i) (b.key_finite i)
    have hk := b.key_size i
    omega
  · exact (b.key_finite i).sdiff

end TranslationTiling.Rotations
