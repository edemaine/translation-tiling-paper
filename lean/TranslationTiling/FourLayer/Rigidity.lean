import TranslationTiling.Proofs.KimDentForcing
import TranslationTiling.Proofs.KimRigidity

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def gridMap (s : Fin 3 → ℕ) : Lattice 3 →+ Lattice 3 where
  toFun v := fun i => (s i:ℤ)*v i
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp [mul_add]

def gridCoset (s : Fin 3 → ℕ) (a : Lattice 3) : Set (Lattice 3) :=
  {x | ∃ z, x=a+gridMap s z}

def dent (s : Fin 3 → ℕ) (i : Fin 3) : Lattice 3 :=
  gridMap s (Pi.single i 1)+Kim.bumpAt i

/-- Finite local geometry sufficient for arbitrary-complement rigidity. -/
structure LocalData (s : Fin 3 → ℕ) (S : Set (Lattice 3)) where
  raw : Set (Lattice 3)
  raw_or_bump : ∀ v ∈ S, v∈raw ∨ ∃ i : Fin 3, v=Kim.bumpAt i
  first_block : ∀ c ∈ Kim.cube 3, c∈S
  dent_absent : ∀ i, dent s i∉S
  rim : ∀ i j : Fin 3, j≠i → ∀ e : ℤ, e=1 ∨ e=-1 → dent s i+Pi.single j e∈S
  blocks : ∀ v∈raw, ∃ q c : Lattice 3, c∈Kim.cube 3 ∧ v=3 • q+c ∧
    ∀ d∈Kim.cube 3, 3 • q+d∈raw
  missing_close : ∀ u∈raw, ∀ v∈raw, u∉S → v∉S →
    (∀ i, -2≤v i-u i ∧ v i-u i≤2) → u=v

variable {s : Fin 3 → ℕ} {S : Set (Lattice 3)}

theorem raw_cannot_cover_dent (D : LocalData s S) {A : Set (Lattice 3)}
    (hA : ExactTiling A S) {a b v : Lattice 3} (ha : a∈A) (hb : b∈A)
    (hne : b≠a) (i : Fin 3) (hv : v∈D.raw) (he : b+v=a+dent s i) : False := by
  obtain ⟨j,k,hji,hki,hjk⟩ : ∃ j k : Fin 3, j≠i ∧ k≠i ∧ j≠k := by
    fin_cases i
    · exact ⟨1,2,by decide,by decide,by decide⟩
    · exact ⟨0,2,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  obtain ⟨q,c,hc,hvc,hblock⟩ := D.blocks v hv
  let e : Fin 3 → ℤ := fun r => if c r≤1 then 1 else -1
  have hes (r) : e r=1 ∨ e r=-1 := by dsimp [e]; split_ifs <;> simp
  have hstep (r : Fin 3) : c+Pi.single r (e r)∈Kim.cube 3 := by
    apply Kim.coordinate_step_cube hc
    have := (Kim.mem_cube_iff 3 _).mp hc r
    dsimp [e]; split_ifs <;> omega
  have hraw (r) : v+Pi.single r (e r)∈D.raw := by
    have hh := hblock _ (hstep r)
    rw [hvc]
    convert hh using 1
    abel
  have missing (r) (hri : r≠i) : v+Pi.single r (e r)∉S := by
    intro hh
    apply hne
    apply Kim.exactTiling_centers_eq hA hb ha hh (D.rim i r hri _ (hes r))
    calc
      _ = (b+v)+Pi.single r (e r) := by abel
      _ = _ := by rw [he]; abel
  have hclose : ∀ r : Fin 3, -2≤(v+Pi.single k (e k) : Lattice 3) r-(v+Pi.single j (e j) : Lattice 3) r ∧
      (v+Pi.single k (e k) : Lattice 3) r-(v+Pi.single j (e j) : Lattice 3) r≤2 := by
    intro r
    have hej := hes j
    have hek := hes k
    simp only [Pi.add_apply,Pi.single_apply]
    split_ifs <;> omega
  have heq := D.missing_close _ (hraw j) _ (hraw k) (missing j hji) (missing k hki) hclose
  have hh := congrFun heq j
  simp only [Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne hjk] at hh
  have hej := hes j
  omega

theorem forward_step (D : LocalData s S) {A : Set (Lattice 3)} (hA : ExactTiling A S)
    {a : Lattice 3} (ha : a∈A) (i : Fin 3) : a+gridMap s (Pi.single i 1)∈A := by
  obtain ⟨⟨b,v⟩,he⟩ := hA.2 (a+dent s i)
  have hne : b.val≠a := by
    intro hb
    have hv : v.val=dent s i := by
      change b.val+v.val=a+dent s i at he
      rw [hb] at he
      exact add_left_cancel he
    exact D.dent_absent i (hv ▸ v.property)
  rcases D.raw_or_bump v.val v.property with hv | ⟨j,hv⟩
  · exact (raw_cannot_cover_dent D hA ha b.property hne i hv he).elim
  · have hji : j=i := by
      by_contra hji
      let c := Kim.bumpAt j+Pi.single j 1
      have hc : c∈Kim.cube 3 := by
        apply (Kim.mem_cube_iff 3 _).mpr
        intro r
        by_cases hr : r=j
        · subst r; simp [c,Kim.bumpAt] <;> omega
        · have hh : r.val≠j.val := fun h => hr (Fin.ext h)
          simp [c,Kim.bumpAt,hh,hr] <;> omega
      apply hne
      apply Kim.exactTiling_centers_eq hA b.property ha (D.first_block c hc) (D.rim i j hji 1 (Or.inl rfl))
      change b.val+v.val=a+dent s i at he
      rw [hv] at he
      dsimp [c]
      calc
        _ = (b.val+Kim.bumpAt j)+Pi.single j 1 := by abel
        _ = _ := by rw [he,add_assoc]
    have hb : b.val=a+gridMap s (Pi.single i 1) := by
      change b.val+v.val=a+dent s i at he
      rw [hv,hji] at he
      unfold dent at he
      apply add_right_cancel (b:=Kim.bumpAt i)
      convert he using 1 <;> abel
    exact hb ▸ b.property

theorem gridMap_injective (hs : ∀ i, 0<s i) : Function.Injective (gridMap s) := by
  intro v w h
  ext i
  have hh := congrFun h i
  exact mul_left_cancel₀ (by exact_mod_cast (hs i).ne' : (s i:ℤ)≠0) hh

theorem exactTiling_coset (t : Lattice 3) (hfund : ExactTiling (Set.range (gridMap s)) S) :
    ExactTiling (gridCoset s t) S := by
  rw [exactTiling_iff] at hfund ⊢
  intro x
  obtain ⟨f,hf,hu⟩ := hfund (x-t)
  refine ⟨f,?_,?_⟩
  · obtain ⟨z,hz⟩ := hf
    refine ⟨z,?_⟩
    change gridMap s z=x-t-f.val at hz
    change x-f.val=t+gridMap s z
    rw [hz]
    abel
  · intro g hg
    apply hu
    obtain ⟨z,hz⟩ := hg
    refine ⟨z,?_⟩
    change gridMap s z=x-t-g.val
    change x-g.val=t+gridMap s z at hz
    rw [show x-t-g.val=(x-g.val)-t by abel,hz]
    abel

theorem coset_of_forward (hs : ∀ i, 0<s i) (D : LocalData s S)
    (hfund : ExactTiling (Set.range (gridMap s)) S)
    (hbound : ∃ upper : ℤ, ∀ v∈S, ∀ i, v i≤upper)
    (A : Set (Lattice 3)) (hA : ExactTiling A S) : ∃ t, A=gridCoset s t := by
  obtain ⟨upper,hupper⟩ := hbound
  have positive {a : Lattice 3} (ha : a∈A) (v : Fin 3 → ℕ) : a+gridMap s (fun i => (v i:ℤ))∈A := by
    have iterate (i : Fin 3) (n : ℕ) {a : Lattice 3} (ha : a∈A) :
        a+gridMap s (fun j => if j=i then (n:ℤ) else 0)∈A := by
      induction n with
      | zero =>
        simp only [Nat.cast_zero,ite_self]
        change a+gridMap s 0∈A
        simpa using ha
      | succ n ih =>
        have hh := forward_step D hA ih i
        convert hh using 1
        ext j
        by_cases hj : j=i <;> simp [gridMap,Pi.single_apply,hj] <;> ring
    have h0 := iterate 0 (v 0) ha
    have h1 := iterate 1 (v 1) h0
    have h2 := iterate 2 (v 2) h1
    convert h2 using 1
    ext i
    fin_cases i <;> simp [gridMap]
  obtain ⟨⟨t,f0⟩,_⟩ := hA.2 0
  have htfund := exactTiling_coset t.val hfund
  have subset : A⊆gridCoset s t.val := by
    intro a ha
    let n : Fin 3 → ℕ := fun i => (max (t.val i+upper-(a i+f0.val i)) 0).toNat
    let a' := a+gridMap s (fun i => (n i:ℤ))
    have ha' : a'∈A := positive ha n
    have above (i) : t.val i+upper≤a' i+f0.val i := by
      have hn : 0≤(n i:ℤ) ∧ t.val i+upper-(a i+f0.val i)≤(n i:ℤ) := by dsimp [n]; omega
      have hpos : (1:ℤ)≤s i := by exact_mod_cast hs i
      change _≤a i+(s i:ℤ)*(n i:ℤ)+f0.val i
      nlinarith
    obtain ⟨⟨b,f⟩,he⟩ := htfund.2 (a'+f0.val)
    have hbA : b.val∈A := by
      obtain ⟨z,hz⟩ := b.property
      have hn (i) : 0≤z i := by
        have hf := hupper f.val f.property i
        have hei := congrFun he i
        have hzi := congrFun hz i
        have hh := above i
        have hpos : (0:ℤ)<s i := by exact_mod_cast hs i
        change b.val i+f.val i=a' i+f0.val i at hei
        change b.val i=t.val i+(s i:ℤ)*z i at hzi
        nlinarith
      have hnat : (fun i => ((z i).toNat:ℤ))=z := by ext i; exact Int.toNat_of_nonneg (hn i)
      rw [hz,← hnat]
      exact positive t.property _
    have heq := Kim.exactTiling_centers_eq hA hbA ha' f.property f0.property he
    obtain ⟨z,hz⟩ := heq ▸ b.property
    refine ⟨fun i => z i-(n i:ℤ),?_⟩
    ext i
    have hh := congrFun hz i
    change a i+(s i:ℤ)*(n i:ℤ)=t.val i+(s i:ℤ)*z i at hh
    change a i=t.val i+(s i:ℤ)*(z i-(n i:ℤ))
    nlinarith
  refine ⟨t.val,Set.Subset.antisymm subset ?_⟩
  intro b hb
  obtain ⟨⟨a,f⟩,he⟩ := hA.2 (b+f0.val)
  have hh := Kim.exactTiling_centers_eq htfund (subset a.property) hb f.property f0.property he
  exact hh ▸ a.property

end
end TranslationTiling.FourLayer
