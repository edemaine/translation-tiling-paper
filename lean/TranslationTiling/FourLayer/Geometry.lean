import TranslationTiling.FourLayer.MicroContacts

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

def At (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (i : Fin m) (v : Lattice 3) : Prop :=
  (∃ r, MicroFiber m p q i r ∧ v=gridMap (scales m) (X i)+r) ∨
    (i=0 ∧ ∃ k, v=Kim.bumpAt k)

def core (X : Fin m → Lattice 3) (i : Fin m) : Lattice 3 :=
  gridMap (scales m) (X i)+center (hub m i)

theorem at_mem (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) {i : Fin m} {v : Lattice 3}
    (hv : At m X p q i v) : v∈Shape m X p q := by
  rcases hv with ⟨r,hr,rfl⟩ | ⟨rfl,k,rfl⟩
  · refine ⟨⟨r,hr.1⟩,?_⟩
    change modified m X p q r=gridMap (scales m) (X i)+r
    simp [modified,hr.2.2,relocate,hr.2.1]
  · exact ⟨⟨dent (scales m) k,dent_mem_rect m k⟩,modified_dent m X p q k⟩

theorem shape_at (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) {v : Lattice 3}
    (hv : v∈Shape m X p q) : ∃ i, At m X p q i v := by
  obtain ⟨r,rfl⟩ := hv
  change ∃ i, At m X p q i (modified m X p q r.val)
  unfold modified
  split_ifs with h0 h1 h2
  · exact ⟨0,Or.inr ⟨rfl,0,rfl⟩⟩
  · exact ⟨0,Or.inr ⟨rfl,1,rfl⟩⟩
  · exact ⟨0,Or.inr ⟨rfl,2,rfl⟩⟩
  · refine ⟨color m p q (block r.val),Or.inl ⟨r.val,?_,rfl⟩⟩
    refine ⟨r.property,rfl,?_⟩
    intro j
    fin_cases j <;> assumption

theorem core_at (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (i : Fin m) :
    At m X p q i (core m X i) :=
  Or.inl ⟨_,center_mem m p q i _ (hub_mem m p q i),rfl⟩

theorem micro_path_in_shape (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m)) (i : Fin m)
    {r t : Lattice 3} (hr : MicroFiber m p q i r) (ht : MicroFiber m p q i t) :
    FacePath (Shape m X p q) (gridMap (scales m) (X i)+r) (gridMap (scales m) (X i)+t) := by
  apply Relation.ReflTransGen.lift (fun r => gridMap (scales m) (X i)+r) _ _ _ (micro_connected m p q i hr ht)
  intro a b hab
  exact ⟨at_mem m X p q (Or.inl ⟨a,hab.1,rfl⟩),at_mem m X p q (Or.inl ⟨b,hab.2.1,rfl⟩),
    Kim.adjacent_add_left _ hab.2.2⟩

theorem first_micro (p q : Equiv.Perm (Fin m)) (c : Lattice 3) (hc : c∈Kim.cube 3) :
    MicroFiber m p q 0 c := by
  have hr : Rect (scales m) c := by
    intro i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    have hw := widths_pos m i
    dsimp [scales]
    push_cast
    omega
  have hb : block c=0 := by
    ext i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    change c i/3=0
    omega
  exact ⟨hr,by simp [hb,color],small_not_dent m c hc⟩

theorem at_path_core (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    {i : Fin m} {v : Lattice 3} (hv : At m X p q i v) :
    FacePath (Shape m X p q) v (core m X i) := by
  rcases hv with ⟨r,hr,rfl⟩ | ⟨rfl,k,rfl⟩
  · exact micro_path_in_shape m X p q i hr (center_mem m p q i _ (hub_mem m p q i))
  · let c := Kim.bumpAt k+Pi.single k 1
    have hc : c∈Kim.cube 3 := by
      apply (Kim.mem_cube_iff 3 _).mpr
      intro j
      by_cases hj : j=k
      · subst j; simp [c,Kim.bumpAt]
      · have hh : j.val≠k.val := fun h => hj (Fin.ext h)
        simp [c,Kim.bumpAt,hh,hj]
    have hm := first_micro m p q c hc
    have hcS : c∈Shape m X p q := by
      have hh := at_mem m X p q (Or.inl ⟨c,hm,rfl⟩ : At m X p q 0 (gridMap (scales m) (X 0)+c))
      simpa [hX] using hh
    have hbS : Kim.bumpAt k∈Shape m X p q := at_mem m X p q (Or.inr ⟨rfl,k,rfl⟩ : At m X p q 0 _)
    have hstep : FacePath (Shape m X p q) (Kim.bumpAt k) c := FacePath.step hbS hcS ⟨k,Or.inl rfl⟩
    have hp := micro_path_in_shape m X p q 0 hm (center_mem m p q 0 _ (hub_mem m p q 0))
    simpa [hX,core] using hstep.trans (by simpa [hX] using hp)

theorem within_at (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    {i : Fin m} {v w : Lattice 3} (hv : At m X p q i v) (hw : At m X p q i w) :
    FacePath (Shape m X p q) v w :=
  (at_path_core m X hX p q hv).trans (FacePath.reverse (at_path_core m X hX p q hw))

theorem slot_edge (X : Fin m → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin m))
    (hp : ∀ i j, X j=X i+Pi.single 0 1 → p j=i)
    (hq : ∀ i j, X j=X i+Pi.single 1 1 → q j=i)
    {i j : Fin m} (k : Fin 3) (he : X j=X i+Pi.single k 1) :
    FacePath (Shape m X p q) (core m X i) (core m X j) := by
  have hij : i≠j := by
    intro hh
    subst j
    have h := congrFun he k
    simp at h
  have ports : ∃ r t, MicroFiber m p q i r ∧ MicroFiber m p q j t ∧
      r+Pi.single k 1=gridMap (scales m) (Pi.single k 1)+t := by
    fin_cases k
    · simpa [hp i j he] using x_micro_contact m p q j
    · simpa [hq i j he] using y_micro_contact m p q j
    · exact z_micro_contact m p q i j hij
  obtain ⟨r,t,hr,ht,hport⟩ := ports
  have hri : At m X p q i (gridMap (scales m) (X i)+r) := Or.inl ⟨r,hr,rfl⟩
  have htj : At m X p q j (gridMap (scales m) (X j)+t) := Or.inl ⟨t,ht,rfl⟩
  have hed : gridMap (scales m) (X j)=gridMap (scales m) (X i)+gridMap (scales m) (Pi.single k 1) := by rw [he,map_add]
  have hadj : FaceAdjacent (gridMap (scales m) (X i)+r) (gridMap (scales m) (X j)+t) := by
    refine ⟨k,Or.inl ?_⟩
    rw [hed]
    calc
      _ = gridMap (scales m) (X i)+(gridMap (scales m) (Pi.single k 1)+t) := by abel
      _ = _ := by rw [← hport]; abel
  exact ((within_at m X hX p q (core_at m X p q i) hri).trans
    (FacePath.step (at_mem m X p q hri) (at_mem m X p q htj) hadj)).trans
      (within_at m X hX p q htj (core_at m X p q j))

theorem shape_connected (X : Fin m → Lattice 3) (hX : X 0=0) (hinj : Function.Injective X)
    (p q : Equiv.Perm (Fin m))
    (hp : ∀ i j, X j=X i+Pi.single 0 1 → p j=i)
    (hq : ∀ i j, X j=X i+Pi.single 1 1 → q j=i)
    (hslots : ∀ i j, FacePath (Set.range X) (X i) (X j)) :
    ∀ v∈Shape m X p q, ∀ w∈Shape m X p q, FacePath (Shape m X p q) v w := by
  have route {a b : Lattice 3} (h : FacePath (Set.range X) a b) :
      ∀ i j, X i=a → X j=b → FacePath (Shape m X p q) (core m X i) (core m X j) := by
    induction h with
    | refl =>
      intro i j hi hj
      have he : i=j := hinj (hi.trans hj.symm)
      subst j
      exact Relation.ReflTransGen.refl
    | @tail c d h hcd ih =>
      intro i j hi hj
      obtain ⟨k,hk⟩ := hcd.1
      have prev := ih i k hi hk
      obtain ⟨a,ha | ha⟩ := hcd.2.2
      · have he : X j=X k+Pi.single a 1 := by rw [hk,hj]; exact ha
        exact prev.trans (slot_edge m X hX p q hp hq a he)
      · have he : X k=X j+Pi.single a 1 := by rw [hk,hj]; exact ha
        exact prev.trans (FacePath.reverse (slot_edge m X hX p q hp hq a he))
  intro v hv w hw
  obtain ⟨i,hi⟩ := shape_at m X p q hv
  obtain ⟨j,hj⟩ := shape_at m X p q hw
  exact ((at_path_core m X hX p q hi).trans (route (hslots i j) i j rfl rfl)).trans
    (FacePath.reverse (at_path_core m X hX p q hj))

theorem shape_contacts (X : Fin m → Lattice 3) (p q : Equiv.Perm (Fin m))
    {u v : Lattice 3} {i j : Fin m} (hij : i≠j) (he : u+X i=v+X j) :
    ∃ a∈Shape m X p q, ∃ b∈Shape m X p q,
      FaceAdjacent (gridMap (scales m) u+a) (gridMap (scales m) v+b) := by
  obtain ⟨r,t,hr,ht,hadj⟩ := internal_micro_contact m p q i j
  refine ⟨gridMap (scales m) (X i)+r,at_mem m X p q (Or.inl ⟨r,hr,rfl⟩),
    gridMap (scales m) (X j)+t,at_mem m X p q (Or.inl ⟨t,ht,rfl⟩),2,Or.inl ?_⟩
  have hh := congrArg (gridMap (scales m)) he
  rw [map_add,map_add] at hh
  rw [hadj]
  calc
    _ = (gridMap (scales m) v+gridMap (scales m) (X j))+r+Pi.single 2 1 := by abel
    _ = _ := by rw [← hh]; abel

end
end TranslationTiling.FourLayer
