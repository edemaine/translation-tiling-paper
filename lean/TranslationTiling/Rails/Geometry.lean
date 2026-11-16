import TranslationTiling.Rails.MicroContacts

namespace TranslationTiling.Rails
open FourLayer (gridMap Rect dent)
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (a B : ℕ) [NeZero a] [NeZero B]

def Used (i : ℕ) : Prop := i<a ∨ ∃ k, 0<k ∧ k<B ∧ i=a+k

def root (B i : ℕ) : Lattice 3 :=
  if i<a then point i i 2 else point (4*a+7*(i-a)+6) (2*a) 0

theorem root_mem (p q : Equiv.Perm (Fin a)) (i : ℕ) (hi : Used a B i) :
    Fiber a B p q i (root a B i) := by
  have ha := NeZero.pos a
  have hb := NeZero.pos B
  rcases hi with hi | ⟨k,hk,hkb,rfl⟩
  · simp only [root,if_pos hi]
    change Fiber a B p q (⟨i,hi⟩ : Fin a).val (point i i 2)
    apply small_point a B p q ⟨i,hi⟩
    · simp [box_point,lengthX,lengthY]; omega
    · omega
    · left; omega
    · simpa [small] using congrArg Fin.val (FourLayer.band_val a ⟨i,hi⟩)
  · have hna : ¬a+k<a := by omega
    simp only [root,if_neg hna,Nat.add_sub_cancel_left]
    apply (positive_point_iff a B p q k hk hkb _ _ _).mpr
    refine ⟨by simp [box_point,lengthX,lengthY]; omega,?_,?_,?_⟩ <;> omega

def At (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (i : ℕ) (v : Lattice 3) : Prop :=
  (∃ r, MicroFiber a B p q i r ∧ v=gridMap (scales a B) (X i)+r) ∨
    (i=0 ∧ ∃ k, v=Kim.bumpAt k)

def core (X : ℕ → Lattice 3) (i : ℕ) : Lattice 3 :=
  gridMap (scales a B) (X i)+center (root a B i)

theorem at_mem (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) {i : ℕ} {v : Lattice 3}
    (hv : At a B X p q i v) : v∈Shape a B X p q := by
  rcases hv with ⟨r,hr,rfl⟩ | ⟨rfl,k,rfl⟩
  · refine ⟨⟨r,hr.1⟩,?_⟩
    change modified a B X p q r=gridMap (scales a B) (X i)+r
    simp [modified,hr.2.2,relocate,hr.2.1]
  · exact ⟨⟨dent (scales a B) k,dent_mem_rect a B k⟩,modified_dent a B X p q k⟩

theorem shape_at (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) {v : Lattice 3}
    (hv : v∈Shape a B X p q) : ∃ i, At a B X p q i v := by
  obtain ⟨r,rfl⟩ := hv
  change ∃ i, At a B X p q i (modified a B X p q r.val)
  unfold modified
  split_ifs with h0 h1 h2
  · exact ⟨0,Or.inr ⟨rfl,0,rfl⟩⟩
  · exact ⟨0,Or.inr ⟨rfl,1,rfl⟩⟩
  · exact ⟨0,Or.inr ⟨rfl,2,rfl⟩⟩
  · refine ⟨color a B p q (block r.val),Or.inl ⟨r.val,?_,rfl⟩⟩
    refine ⟨r.property,rfl,?_⟩
    intro j
    fin_cases j <;> assumption

theorem core_at (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (i : ℕ) (hi : Used a B i) :
    At a B X p q i (core a B X i) :=
  Or.inl ⟨_,center_mem a B p q i _ (root_mem a B p q i hi),rfl⟩

theorem micro_path_in_shape (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) (i : ℕ)
    {r t : Lattice 3} (hr : MicroFiber a B p q i r) (ht : MicroFiber a B p q i t) :
    FacePath (Shape a B X p q) (gridMap (scales a B) (X i)+r) (gridMap (scales a B) (X i)+t) := by
  apply Relation.ReflTransGen.lift (fun r => gridMap (scales a B) (X i)+r) _ _ _ (micro_connected a B p q i hr ht)
  intro u v hab
  exact ⟨at_mem a B X p q (Or.inl ⟨u,hab.1,rfl⟩),at_mem a B X p q (Or.inl ⟨v,hab.2.1,rfl⟩),
    Kim.adjacent_add_left _ hab.2.2⟩

theorem first_micro (p q : Equiv.Perm (Fin a)) (c : Lattice 3) (hc : c∈Kim.cube 3) :
    MicroFiber a B p q 0 c := by
  have hr : Rect (scales a B) c := by
    intro i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    have hw := widths_pos a B i
    dsimp [scales]
    push_cast
    omega
  have hb : block c=0 := by
    ext i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    change c i/3=0
    omega
  exact ⟨hr,by simp [hb,color],small_not_dent a B c hc⟩

theorem at_path_core (X : ℕ → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin a))
    {i : ℕ} {v : Lattice 3} (hi : Used a B i) (hv : At a B X p q i v) :
    FacePath (Shape a B X p q) v (core a B X i) := by
  rcases hv with ⟨r,hr,rfl⟩ | ⟨rfl,k,rfl⟩
  · exact micro_path_in_shape a B X p q i hr (center_mem a B p q i _ (root_mem a B p q i hi))
  · let c := Kim.bumpAt k+Pi.single k 1
    have hc : c∈Kim.cube 3 := by
      apply (Kim.mem_cube_iff 3 _).mpr
      intro j
      by_cases hj : j=k
      · subst j; simp [c,Kim.bumpAt]
      · have hh : j.val≠k.val := fun h => hj (Fin.ext h)
        simp [c,Kim.bumpAt,hh,hj]
    have hm := first_micro a B p q c hc
    have hcS : c∈Shape a B X p q := by
      have hh := at_mem a B X p q (Or.inl ⟨c,hm,rfl⟩ : At a B X p q 0 (gridMap (scales a B) (X 0)+c))
      simpa [hX] using hh
    have hbS : Kim.bumpAt k∈Shape a B X p q := at_mem a B X p q (Or.inr ⟨rfl,k,rfl⟩ : At a B X p q 0 _)
    have hstep : FacePath (Shape a B X p q) (Kim.bumpAt k) c := FacePath.step hbS hcS ⟨k,Or.inl rfl⟩
    have hp := micro_path_in_shape a B X p q 0 hm (center_mem a B p q 0 _ (root_mem a B p q 0 (Or.inl (NeZero.pos a))))
    simpa [hX,core] using hstep.trans (by simpa [hX] using hp)

theorem within_at (X : ℕ → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin a))
    {i : ℕ} {v w : Lattice 3} (hi : Used a B i) (hv : At a B X p q i v) (hw : At a B X p q i w) :
    FacePath (Shape a B X p q) v w :=
  (at_path_core a B X hX p q hi hv).trans (FacePath.reverse (at_path_core a B X hX p q hi hw))

theorem used_at (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a)) {i : ℕ} {v : Lattice 3}
    (hv : At a B X p q i v) : Used a B i := by
  rcases hv with ⟨r,hr,_⟩ | ⟨rfl,_⟩
  · have hh := color_cases a B p q (block r)
    rw [hr.2.1] at hh
    exact hh
  · exact Or.inl (NeZero.pos a)

theorem slot_edge (X : ℕ → Lattice 3) (hX : X 0=0) (p q : Equiv.Perm (Fin a))
    (hports : ∀ i j, Used a B i → Used a B j → ∀ k : Fin 3, X j=X i+Pi.single k 1 →
      ∃ r t, MicroFiber a B p q i r ∧ MicroFiber a B p q j t ∧
        r+Pi.single k 1=gridMap (scales a B) (Pi.single k 1)+t)
    {i j : ℕ} (hi : Used a B i) (hj : Used a B j) (k : Fin 3) (he : X j=X i+Pi.single k 1) :
    FacePath (Shape a B X p q) (core a B X i) (core a B X j) := by
  obtain ⟨r,t,hr,ht,hport⟩ := hports i j hi hj k he
  have hri : At a B X p q i (gridMap (scales a B) (X i)+r) := Or.inl ⟨r,hr,rfl⟩
  have htj : At a B X p q j (gridMap (scales a B) (X j)+t) := Or.inl ⟨t,ht,rfl⟩
  have hed : gridMap (scales a B) (X j)=gridMap (scales a B) (X i)+gridMap (scales a B) (Pi.single k 1) := by rw [he,map_add]
  have hadj : FaceAdjacent (gridMap (scales a B) (X i)+r) (gridMap (scales a B) (X j)+t) := by
    refine ⟨k,Or.inl ?_⟩
    rw [hed]
    calc
      _ = gridMap (scales a B) (X i)+(gridMap (scales a B) (Pi.single k 1)+t) := by abel
      _ = _ := by rw [← hport]; abel
  exact ((within_at a B X hX p q hi (core_at a B X p q i hi) hri).trans
    (FacePath.step (at_mem a B X p q hri) (at_mem a B X p q htj) hadj)).trans
      (within_at a B X hX p q hj htj (core_at a B X p q j hj))

theorem shape_connected (X : ℕ → Lattice 3) (hX : X 0=0)
    (hinj : ∀ i j, Used a B i → Used a B j → X i=X j → i=j)
    (p q : Equiv.Perm (Fin a))
    (hports : ∀ i j, Used a B i → Used a B j → ∀ k : Fin 3, X j=X i+Pi.single k 1 →
      ∃ r t, MicroFiber a B p q i r ∧ MicroFiber a B p q j t ∧
        r+Pi.single k 1=gridMap (scales a B) (Pi.single k 1)+t)
    (hslots : ∀ i j, Used a B i → Used a B j →
      FacePath (fun v => ∃ k, Used a B k ∧ X k=v) (X i) (X j)) :
    ∀ v∈Shape a B X p q, ∀ w∈Shape a B X p q, FacePath (Shape a B X p q) v w := by
  have route {u v : Lattice 3} (h : FacePath (fun v => ∃ k, Used a B k ∧ X k=v) u v) :
      ∀ i j, Used a B i → Used a B j → X i=u → X j=v →
        FacePath (Shape a B X p q) (core a B X i) (core a B X j) := by
    induction h with
    | refl =>
      intro i j hi hj hu hv
      have he : i=j := hinj i j hi hj (hu.trans hv.symm)
      subst j
      exact Relation.ReflTransGen.refl
    | @tail c d h hcd ih =>
      intro i j hi hj hu hv
      obtain ⟨k,hk,hkc⟩ := hcd.1
      have prev := ih i k hi hk hu hkc
      obtain ⟨l,hl | hl⟩ := hcd.2.2
      · have he : X j=X k+Pi.single l 1 := by rw [hkc,hv]; exact hl
        exact prev.trans (slot_edge a B X hX p q hports hk hj l he)
      · have he : X k=X j+Pi.single l 1 := by rw [hkc,hv]; exact hl
        exact prev.trans (FacePath.reverse (slot_edge a B X hX p q hports hj hk l he))
  intro v hv w hw
  obtain ⟨i,hi⟩ := shape_at a B X p q hv
  obtain ⟨j,hj⟩ := shape_at a B X p q hw
  have hiu := used_at a B X p q hi
  have hju := used_at a B X p q hj
  exact ((at_path_core a B X hX p q hiu hi).trans
    (route (hslots i j hiu hju) i j hiu hju rfl rfl)).trans
    (FacePath.reverse (at_path_core a B X hX p q hju hj))

theorem shape_contacts (X : ℕ → Lattice 3) (p q : Equiv.Perm (Fin a))
    {u v : Lattice 3} (i : Fin B) (j : Fin a)
    (he : u+X (railLabel a i.val)=v+X j.val) :
    ∃ r∈Shape a B X p q, ∃ t∈Shape a B X p q,
      FaceAdjacent (gridMap (scales a B) u+r) (gridMap (scales a B) v+t) := by
  obtain ⟨r,t,hr,ht,hadj⟩ := internal_micro_contact a B p q i j
  refine ⟨gridMap (scales a B) (X (railLabel a i.val))+r,at_mem a B X p q (Or.inl ⟨r,hr,rfl⟩),
    gridMap (scales a B) (X j.val)+t,at_mem a B X p q (Or.inl ⟨t,ht,rfl⟩),2,Or.inl ?_⟩
  have hh := congrArg (gridMap (scales a B)) he
  rw [map_add,map_add] at hh
  rw [hadj]
  calc
    _ = (gridMap (scales a B) v+gridMap (scales a B) (X j.val))+r+Pi.single 2 1 := by abel
    _ = _ := by rw [← hh]; abel

end
end TranslationTiling.Rails
