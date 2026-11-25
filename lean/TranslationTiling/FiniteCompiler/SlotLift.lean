import TranslationTiling.FiniteCompiler.GraphTests

namespace TranslationTiling.FiniteCompiler

open scoped Classical

noncomputable section

/-- A test on the arithmetic frame extends across the new slots by filling
all their high outputs and keeping their low inputs fixed. Each low slice
then satisfies precisely the original arithmetic test. -/
theorem tiles_product_low_kernel_iff
    {G H K B : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K] [Fintype H]
    (π : H →+ K) (hπ : Function.Surjective π) (F : Finset G)
    (old : K → B → G) (hold : ∀ k, Function.Injective (old k))
    (extra : K × B → H) (hExtra : ∀ p, π (extra p) = p.1) :
    Tiles (F.product (Finset.univ.filter fun h => π h = 0))
        (Set.range fun p : K × B => (old p.1 p.2,extra p)) ↔
      ∀ k, Tiles F (Set.range (old k)) := by
  let emb (p : K × B) : G × H := (old p.1 p.2,extra p)
  have hemb : Function.Injective emb := by
    rintro ⟨k,b⟩ ⟨l,c⟩ h
    have hkl := congrArg (fun x : G × H => π x.2) h
    change π (extra (k,b)) = π (extra (l,c)) at hkl
    simp only [hExtra] at hkl
    subst l
    exact Prod.ext rfl (hold k (congrArg Prod.fst h))
  have hmem (y : G × H) (p : K × B) :
      y-emb p ∈ F.product (Finset.univ.filter fun h => π h = 0) ↔
        y.1-old p.1 p.2 ∈ F ∧ π y.2 = p.1 := by
    simp [emb,Finset.mem_product,map_sub,hExtra,sub_eq_zero]
  rw [tiles_range_iff_unique_base emb hemb]
  simp_rw [tiles_range_iff_unique_base _ (hold _), hmem]
  constructor
  · intro h k y
    obtain ⟨t,ht⟩ := hπ k
    obtain ⟨⟨l,b⟩,⟨hb,hkl⟩,hu⟩ := h (y,t)
    change π t = l at hkl
    rw [ht] at hkl
    subst l
    refine ⟨b,hb,fun b' hb' => ?_⟩
    exact congrArg Prod.snd (hu (k,b') ⟨hb',ht⟩)
  · intro h y
    obtain ⟨b,hb,hu⟩ := h (π y.2) y.1
    refine ⟨(π y.2,b),⟨hb,rfl⟩,?_⟩
    rintro ⟨k,a⟩ ⟨ha,hk⟩
    change π y.2 = k at hk
    subst k
    exact Prod.ext rfl (hu a ha)

/-- All tests admitting a graph over the same low inputs have the
same mass. Count their coverage over one planar point. -/
theorem card_mul_low_eq_of_tiles_graph {H K : Type*} [AddCommGroup H] [Fintype H] [Fintype K]
    (F : Finset (Plane × H)) (o : Plane × K → H)
    (hinj : Function.Injective (fun p : Plane × K => (p.1,o p)))
    (hf : Tiles F (Set.range fun p : Plane × K => (p.1,o p))) :
    F.card * Fintype.card K = Fintype.card H := by
  let s (p : Plane × K) : Plane × H := (p.1,o p)
  let source (p : {f // f ∈ F} × K) : Plane × K := (-p.1.val.1,p.2)
  let y (p : {f // f ∈ F} × K) : H := o (source p) + p.1.val.2
  have eq (p : {f // f ∈ F} × K) : ((0 : Plane),y p) - s (source p) = p.1.val := by
    exact Prod.ext (by simp [s,source]) (by simp [s,y,add_comm])
  have hz := (tiles_range_iff_unique_base s hinj F).mp hf
  have hb : Function.Bijective y := by
    constructor
    · intro p q h
      obtain ⟨b,_,hu⟩ := hz ((0 : Plane),y p)
      have hP : ((0 : Plane),y p) - s (source p) ∈ F := eq p ▸ p.1.property
      have hQ : ((0 : Plane),y p) - s (source q) ∈ F := h ▸ (eq q ▸ q.1.property)
      have hs := (hu _ hP).trans (hu _ hQ).symm
      have hm : p.1.val = q.1.val := by rw [← eq p,← eq q,hs,h]
      have hk := congrArg (fun x : Plane × K => x.2) hs
      exact Prod.ext (Subtype.ext hm) hk
    · intro z
      obtain ⟨b,hb,_⟩ := hz ((0 : Plane),z)
      let p : {f // f ∈ F} × K := (⟨((0 : Plane),z) - s b,hb⟩,b.2)
      have hs : source p = b := by exact Prod.ext (by simp [source,p,s]) rfl
      refine ⟨p,?_⟩
      change o (source p) + (z - o b) = z
      rw [hs,add_comm,sub_add_cancel]
  have hcard := Fintype.card_congr (Equiv.ofBijective y hb)
  simpa only [Fintype.card_prod,Fintype.card_coe] using hcard


end

end TranslationTiling.FiniteCompiler
