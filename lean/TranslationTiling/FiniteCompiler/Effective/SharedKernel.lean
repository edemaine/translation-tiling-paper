import TranslationTiling.FiniteCompiler.SharedCoordinates
import TranslationTiling.FiniteCompiler.Effective.SharedNumericalDeck
import TranslationTiling.Compiler.Consolidation
import TranslationTiling.Compiler.EffectiveLattice

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler Compiler.Effective
open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I)

def decodePoint (f : NumericalPoint) : Ambient L := (f.1,decode L f.2)

theorem decode_bounded_surjective [NeZero (order L)] (e : ZMod (order L) ≃+* Factor L)
    (f : Factor L) : ∃ n < order L, decode L n = f := by
  let z := e.symm f
  refine ⟨z.val,ZMod.val_lt z,?_⟩
  have hn : e (z.val : ZMod (order L)) = decode L z.val := by
    rw [map_natCast]
    rfl
  rw [← hn,ZMod.natCast_zmod_val]
  exact e.apply_symm_apply f

theorem decoded_range_filter_iff [NeZero (order L)]
    (e : ZMod (order L) ≃+* Factor L) (h : Plane) (p : ℕ → Bool)
    (P : Factor L → Prop) (hp : ∀ n, p n = true ↔ P (decode L n)) (v : Ambient L) :
    v ∈ (((List.range (order L)).filter p).map (fun n => (h,n))).toFinset.image (decodePoint L) ↔
      v.1 = h ∧ P v.2 := by
  classical
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨f,⟨n,⟨_,hn⟩,rfl⟩,rfl⟩
    exact ⟨rfl,(hp n).mp hn⟩
  · rintro ⟨hv,hP⟩
    obtain ⟨n,hn,rfl'⟩ := decode_bounded_surjective L e v.2
    exact ⟨(h,n),⟨n,⟨hn,(hp n).mpr (rfl'.symm ▸ hP)⟩,rfl⟩,
      Prod.ext hv.symm rfl'⟩

omit [Fintype I] in
theorem kernel_moduli_test (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ i, L.lowSize i = r)
    (n : ℕ) :
    KernelTest rs n ↔ ∀ i, CyclicShear.low (L.lowSize i) ((decode L n).2 i).1.1 = 0 := by
  constructor
  · intro hn i
    change CyclicShear.low (L.lowSize i) (n : Square L i) = 0
    rw [CyclicShear.low_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_iff_mod_eq_zero.mpr (hn _ ((hr _).mpr ⟨i,rfl⟩)))
  · intro hn r h
    obtain ⟨i,rfl⟩ := (hr _).mp h
    have he := hn i
    change CyclicShear.low (L.lowSize i) (n : Square L i) = 0 at he
    rw [CyclicShear.low_natCast] at he
    exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp he)

theorem mem_decoded_kernel [NeZero (order L)] (e : ZMod (order L) ≃+* Factor L)
    (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ i, L.lowSize i = r) (v : Ambient L) :
    v ∈ (kernelCodes (order L) rs).toFinset.image (decodePoint L) ↔ baseProjection L v = 0 := by
  classical
  unfold kernelCodes
  rw [decoded_range_filter_iff L e _ _
    (fun f => ∀ i, CyclicShear.low (L.lowSize i) (f.2 i).1.1 = 0)
    (fun n => by rw [decide_eq_true_eq]; exact kernel_moduli_test L rs hr n)]
  constructor
  · rintro ⟨hv,hl⟩
    exact Prod.ext hv (funext hl)
  · intro hv
    exact ⟨congrArg Prod.fst hv,fun i => congrFun (congrArg Prod.snd hv) i⟩

theorem tiles_decoded_kernel_iff_graph [NeZero (order L)] (e : ZMod (order L) ≃+* Factor L)
    (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ i, L.lowSize i = r) (A : Set (Ambient L)) :
    Tiles ((kernelCodes (order L) rs).toFinset.image (decodePoint L)) A ↔
    ∃ o : Outputs L, Set.range (point L o) = A := by
  classical
  rw [tiles_kernel_iff_unique_fibre (baseProjection L) (baseProjection_surjective L) _
    (mem_decoded_kernel L e rs hr) A]
  constructor
  · intro hf
    let a : Base L → A := fun b => Classical.choose (hf b)
    let s : Base L → Ambient L := fun b => a b
    have hs (b : Base L) : baseProjection L (s b) = b := (Classical.choose_spec (hf b)).1
    refine ⟨outputsOfSection L s hs,?_⟩
    rw [show point L (outputsOfSection L s hs) = s from
      funext (point_outputsOfSection L s hs)]
    ext y
    constructor
    · rintro ⟨b,rfl⟩
      exact (a b).property
    · intro hy
      refine ⟨baseProjection L y,?_⟩
      have h : (⟨y,hy⟩ : A) = a (baseProjection L y) :=
        (Classical.choose_spec (hf (baseProjection L y))).2 _ rfl
      exact (congrArg Subtype.val h).symm
  · rintro ⟨o,rfl⟩ x
    refine ⟨⟨point L o x,⟨x,rfl⟩⟩,baseProjection_point L o x,?_⟩
    rintro ⟨v,⟨x',rfl⟩⟩ hx
    have h : x' = x := (baseProjection_point L o x').symm.trans hx
    subst x'
    rfl

omit [Fintype I] in
private theorem low_congruences_test (cs : CongruenceList) (k : ∀ i, Low L i)
    (hcs : ∀ c, c ∈ cs ↔ ∃ i, (L.lowSize i,(k i).val) = c) (n : ℕ) :
    Congruences cs n ↔ ∀ i, CyclicShear.low (L.lowSize i) ((decode L n).2 i).1.1 = k i := by
  constructor
  · intro h i
    change CyclicShear.low (L.lowSize i) (n : Square L i) = k i
    rw [CyclicShear.low_natCast]
    apply ZMod.val_injective (L.lowSize i)
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using h _ ((hcs _).mpr ⟨i,rfl⟩)
  · intro h c hc
    obtain ⟨i,rfl⟩ := (hcs _).mp hc
    have he := h i
    change CyclicShear.low (L.lowSize i) (n : Square L i) = k i at he
    rw [CyclicShear.low_natCast] at he
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using congrArg ZMod.val he

/-- The numerical invariance tile sees only its selected output, which may be
a private pair, one private coordinate, or a shared coordinate. -/
theorem mem_decoded_invariance [NeZero (order L)]
    (e : ZMod (order L) ≃+* Factor L) {a b : ℕ}
    (ψ : Factor L →+ ZMod a × ZMod b) (hψ : ∀ n : ℕ, ψ (decode L n) = ((n : ZMod a),(n : ZMod b)))
    (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ i, L.lowSize i = r)
    (cs : CongruenceList) (h : Plane) (k : ∀ i, Low L i)
    (hcs : ∀ c, c ∈ cs ↔ ∃ i, (L.lowSize i,(k i).val) = c) (v : Ambient L) :
    v ∈ (invarianceCodes (order L) rs a b h cs).toFinset.image (decodePoint L) ↔
    (baseProjection L v = 0 ∧ ψ v.2 ≠ 0) ∨ (baseProjection L v = (h,k) ∧ ψ v.2 = 0) := by
  have hzero (n : ℕ) : UsefulZero a b n ↔ ψ (decode L n) = 0 := by
    rw [hψ]
    change (n % a = 0 ∧ n % b = 0) ↔
      (((n : ZMod a),(n : ZMod b)) = (0,0))
    rw [Prod.mk.injEq, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
    simp only [Nat.dvd_iff_mod_eq_zero]
  have hleft (n : ℕ) :
      decide (KernelTest rs n ∧ ¬ UsefulZero a b n) = true ↔
        (∀ i, CyclicShear.low (L.lowSize i) ((decode L n).2 i).1.1 = 0) ∧
          ψ (decode L n) ≠ 0 := by
    rw [decide_eq_true_eq,kernel_moduli_test L rs hr,hzero]
  have hright (n : ℕ) :
      decide (Congruences cs n ∧ UsefulZero a b n) = true ↔
        (∀ i, CyclicShear.low (L.lowSize i) ((decode L n).2 i).1.1 = k i) ∧
          ψ (decode L n) = 0 := by
    rw [decide_eq_true_eq,low_congruences_test L cs k hcs,hzero]
  unfold invarianceCodes
  rw [List.toFinset_append,Finset.image_union,Finset.mem_union,
    decoded_range_filter_iff L e _ _
      (fun f => (∀ i, CyclicShear.low (L.lowSize i) (f.2 i).1.1 = 0) ∧ ψ f ≠ 0) hleft,
    decoded_range_filter_iff L e _ _
      (fun f => (∀ i, CyclicShear.low (L.lowSize i) (f.2 i).1.1 = k i) ∧ ψ f = 0) hright]
  constructor
  · rintro (⟨hv,hk,hψ⟩|⟨hv,hk,hψ⟩)
    · exact Or.inl ⟨Prod.ext hv (funext hk),hψ⟩
    · exact Or.inr ⟨Prod.ext hv (funext hk),hψ⟩
  · rintro (⟨hv,hψ⟩|⟨hv,hψ⟩)
    · exact Or.inl ⟨congrArg Prod.fst hv,fun i => congrFun (congrArg Prod.snd hv) i,hψ⟩
    · exact Or.inr ⟨congrArg Prod.fst hv,fun i => congrFun (congrArg Prod.snd hv) i,hψ⟩

/-- Activation batches observe the selected useful pair and high coordinate.
All other high and useful coordinates are free, except for the seed output
when the batch asks for its zero fibre. -/
theorem mem_decoded_activation_batch [NeZero (order L)]
    (crt : ZMod (order L) ≃+* Factor L) {a b : ℕ} [NeZero a] [NeZero b]
    (ψ : Factor L →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode L n) = ((n : ZMod a),(n : ZMod b)))
    (i : I) (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ j, j ≠ i ∧ L.lowSize j = r)
    (h : Plane) (v : ZMod a × ZMod b) (freeZ : Bool) (f : Ambient L) :
    f ∈ (activationBatchCodes ((order L,rs),(L.lowSize i,a,b,1225),h,(v.1.val,v.2.val),freeZ)).toFinset.image
      (decodePoint L) ↔
    f.1 = h ∧ (f.2.2 i).1.1 = (h.1 : Square L i) ∧ ψ f.2 = v ∧
      (∀ j, j ≠ i → CyclicShear.low (L.lowSize j) (f.2.2 j).1.1 = 0) ∧
      (freeZ = true ∨ f.2.1.1.1 = 0) := by
  unfold activationBatchCodes
  dsimp only
  apply decoded_range_filter_iff L crt h _
    (fun y => (y.2 i).1.1 = (h.1 : Square L i) ∧ ψ y = v ∧
      (∀ j, j ≠ i → CyclicShear.low (L.lowSize j) (y.2 j).1.1 = 0) ∧
      (freeZ = true ∨ y.1.1.1 = 0))
  intro n
  have hother : KernelTest rs n ↔ ∀ j, j ≠ i → (n : Low L j) = 0 := by
    constructor
    · intro hn j hj
      exact (ZMod.natCast_eq_zero_iff _ _).mpr
        (Nat.dvd_iff_mod_eq_zero.mpr (hn _ ((hr _).mpr ⟨j,hj,rfl⟩)))
    · intro hn r hur
      obtain ⟨j,hji,rfl⟩ := (hr _).mp hur
      exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp (hn j hji))
  simp only [decide_eq_true_eq,hψ]
  change ActivationBatchTest _ n ↔
    (n : Square L i) = (h.1 : Square L i) ∧
      (((n : ZMod a),(n : ZMod b)) = v) ∧
      (∀ j, j ≠ i → CyclicShear.low (L.lowSize j) (n : Square L j) = 0) ∧
      (freeZ = true ∨ (n : ZMod 1225) = 0)
  simp only [CyclicShear.low_natCast, ← hother, Prod.ext_iff,
    ← (ZMod.val_injective ((L.lowSize i)^2)).eq_iff, ← (ZMod.val_injective a).eq_iff,
    ← (ZMod.val_injective b).eq_iff, ← (ZMod.val_injective 1225).eq_iff,
    ZMod.val_natCast, ZMod.val_zero]
  have hval : (h.1 : Square L i).val = (h.1 % ((L.lowSize i)^2 : ℕ)).toNat := by
    simpa only [Int.toNat_natCast] using
      congrArg Int.toNat (ZMod.val_intCast (n := (L.lowSize i)^2) h.1)
  unfold ActivationBatchTest
  dsimp only
  rw [hval,Nat.mod_eq_of_lt (ZMod.val_lt v.1),Nat.mod_eq_of_lt (ZMod.val_lt v.2)]
  tauto

def cyclicAmbientEquiv (crt : ZMod (order L) ≃+* Factor L) :
    (Plane × ZMod (order L)) ≃+ Ambient L :=
  (AddEquiv.refl Plane).prodCongr crt.toAddEquiv

theorem cyclicTileSet_image (crt : ZMod (order L) ≃+* Factor L) (F : CyclicTile) :
    (cyclicTileSet (order L) F).image (cyclicAmbientEquiv L crt) =
      F.toFinset.image (decodePoint L) := by
  rw [cyclicTileSet, Finset.image_image]
  apply Finset.image_congr
  intro f _
  change (f.1,crt (f.2 : ZMod (order L))) = decodePoint L f
  rw [map_natCast]
  rfl

/-- Transport the cyclic tiling equations to the product coordinates used
for the graph, activation and cycle proofs. -/
theorem cyclic_deck_iff (crt : ZMod (order L) ≃+* Factor L) (Fs : List CyclicTile) :
    (∃ B : Set (Plane × ZMod (order L)),
      ∀ i : Fin Fs.length, Tiles (cyclicTileSet (order L) (Fs.getD i.val [])) B) ↔
    ∃ A : Set (Ambient L), ∀ F ∈ Fs, Tiles (F.toFinset.image (decodePoint L)) A := by
  let e := cyclicAmbientEquiv L crt
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨e '' B, ?_⟩
    intro F hF
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hF
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi, he] at h
    have h := Compiler.covers_image e _ B h
    rwa [cyclicTileSet_image L crt F] at h
  · rintro ⟨A,hA⟩
    refine ⟨e.symm '' A, ?_⟩
    intro i
    let F := Fs.getD i.val []
    have hF : F ∈ Fs := by
      dsimp [F]
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact List.getElem_mem i.isLt
    have h := hA F hF
    rw [← cyclicTileSet_image L crt F] at h
    have ht := Compiler.covers_image e.symm _ A h
    simpa only [e,Finset.image_image,Function.comp_def,AddEquiv.symm_apply_apply,
      Finset.image_id'] using ht

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
