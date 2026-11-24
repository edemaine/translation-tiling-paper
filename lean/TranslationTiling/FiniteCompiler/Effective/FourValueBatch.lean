import TranslationTiling.FiniteCompiler.Effective.SharedKernel
import TranslationTiling.FiniteCompiler.SharedActivationBatch

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler Compiler.Effective
open scoped Classical

noncomputable section

variable {I J Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y] (L : Layout I)

/-- A collection of batches can specify the observed output by several
congruences. Each batch has one horizontal offset and one sheared high residue. -/
def congruenceBatchCodes (N r : ℕ) (h : Plane) (cs : CongruenceList) : CyclicTile :=
  ((List.range N).filter fun n =>
    decide (Congruences ((r^2,(h.1 % (r^2 : ℕ)).toNat) :: cs) n)).map fun n => (h,n)

def congruenceBatchDeck (N r : ℕ) (records : List (Plane × CongruenceList)) : CyclicTile :=
  records.flatMap fun v => congruenceBatchCodes N r v.1 v.2

theorem congruenceBatchCodes_primrec :
    Primrec (fun v : (ℕ × ℕ) × Plane × CongruenceList =>
      congruenceBatchCodes v.1.1 v.1.2 v.2.1 v.2.2) := by
  unfold congruenceBatchCodes
  apply mapList
  · apply filterList (by fun_prop)
    exact congruences_primrec.comp (show Primrec
      (fun z : ((ℕ × ℕ) × Plane × CongruenceList) × ℕ =>
        ((z.1.1.2 ^ 2,(z.1.2.1.1 % (z.1.1.2 ^ 2 : ℕ)).toNat) :: z.1.2.2,z.2)) by
          simp only [pow_two]
          fun_prop)
  · fun_prop

theorem congruenceBatchDeck_primrec :
    Primrec (fun v : (ℕ × ℕ) × List (Plane × CongruenceList) =>
      congruenceBatchDeck v.1.1 v.1.2 v.2) := by
  unfold congruenceBatchDeck
  exact flatMapList Primrec.snd (congruenceBatchCodes_primrec.comp
    (show Primrec (fun z : ((ℕ × ℕ) × List (Plane × CongruenceList)) ×
      (Plane × CongruenceList) => (z.1.1,z.2)) by fun_prop))

/-- Numerical congruence batches implement the indexed activation test. -/
theorem tiles_congruenceBatchDeck_iff [NeZero (order L)]
    (crt : ZMod (order L) ≃+* Factor L) (i : I) (ψ : Factor L →+ Y)
    (indices : List J) (hall : ∀ j, j ∈ indices) (h : J → Plane)
    (e : J → Y) (hh : Function.Injective (fun j => (h j,e j))) (cs : J → CongruenceList)
    (hcs : ∀ j n, Congruences (cs j) n ↔
      ψ (decode L n) = e j ∧ ∀ j' ≠ i, (n : Low L j') = 0)
    (o : Outputs L) (htarget : ∀ x : Base L, ∀ y : Y × Low L i, ∃ v : Ambient L,
      baseProjection L v = x ∧ (ψ v.2,highCoordinate L i v) = y) :
    let src := fun x j => activationSource L i (h j) ((h j).1 : Low L i) x
    Tiles ((congruenceBatchDeck (order L) (L.lowSize i)
      (indices.map fun j => (h j,cs j))).toFinset.image (decodePoint L))
      (Set.range (point L o)) ↔
    ∀ x, Function.Bijective (fun j =>
      (ψ (point L o (src x j)).2 + e j, o.high (src x j) i)) := by
  let src := fun x j => activationSource L i (h j) ((h j).1 : Low L i) x
  let tgt := fun v : Ambient L => (ψ v.2,highCoordinate L i v)
  let test (x : Base L) (j : J) : Y × Low L i :=
    (ψ (point L o (src x j)).2 + e j, o.high (src x j) i)
  have hsrc (x : Base L) {a b : J} (hs : src x a = src x b)
      (ht : test x a = test x b) : a = b := by
    apply hh
    refine Prod.ext (sub_right_inj.mp (congrArg (fun y : Base L => y.1) hs)) ?_
    have he := congrArg Prod.fst ht
    change ψ (point L o (src x a)).2 + e a = ψ (point L o (src x b)).2 + e b at he
    rw [hs] at he
    exact add_left_cancel he
  have hm (v : Ambient L) (x : Base L) : (v-point L o x) ∈
      ((congruenceBatchDeck (order L) (L.lowSize i)
        (indices.map fun j => (h j,cs j))).toFinset.image (decodePoint L)) ↔
      ∃ j, src (baseProjection L v) j = x ∧ test (baseProjection L v) j = tgt v := by
    have batch (j : J) (f : Ambient L) :
        f ∈ (congruenceBatchCodes (order L) (L.lowSize i) (h j) (cs j)).toFinset.image
          (decodePoint L) ↔ ActivationBatch L i ψ (h j) (e j) f := by
      unfold congruenceBatchCodes ActivationBatch
      apply decoded_range_filter_iff L crt _ _
        (fun v => (v.2 i).1.1 = ((h j).1 : Square L i) ∧ ψ v = e j ∧
          ∀ j' ≠ i, CyclicShear.low (L.lowSize j') (v.2 j').1.1 = 0) _ f
      intro n
      rw [decide_eq_true_eq]
      have hval : ((h j).1 : Square L i).val = ((h j).1 % ((L.lowSize i)^2 : ℕ)).toNat := by
        simpa only [Int.toNat_natCast] using congrArg Int.toNat (ZMod.val_intCast
          (n := (L.lowSize i)^2) (h j).1)
      have hlow (j' : I) : CyclicShear.low (L.lowSize j') ((decode L n).2 j').1.1 =
          (n : Low L j') := CyclicShear.low_natCast _ _
      have hsplit : Congruences (((L.lowSize i)^2,((h j).1 % ((L.lowSize i)^2 : ℕ)).toNat) ::
          cs j) n ↔ n % (L.lowSize i)^2 =
            ((h j).1 % ((L.lowSize i)^2 : ℕ)).toNat % (L.lowSize i)^2 ∧
          Congruences (cs j) n := by
        simp only [Congruences,List.forall_mem_cons]
      rw [hsplit,hcs]
      simp only [hlow]
      change n % (L.lowSize i)^2 = _ ∧ _ ↔
        (n : Square L i) = ((h j).1 : Square L i) ∧ _
      rw [← hval,Nat.mod_eq_of_lt (ZMod.val_lt ((h j).1 : Square L i)),
        ← (ZMod.val_injective ((L.lowSize i)^2)).eq_iff,ZMod.val_natCast]
    have hmem : (v-point L o x) ∈ ((congruenceBatchDeck (order L) (L.lowSize i)
        (indices.map fun j => (h j,cs j))).toFinset.image (decodePoint L)) ↔
        ∃ j, ActivationBatch L i ψ (h j) (e j) (v-point L o x) := by
      simp only [congruenceBatchDeck,List.flatMap_map,
        Finset.mem_image,List.mem_toFinset,List.mem_flatMap,hall,true_and]
      constructor
      · rintro ⟨f,⟨j,hf⟩,he⟩
        exact ⟨j,(batch j _).mp (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,he⟩)⟩
      · rintro ⟨j,hj⟩
        obtain ⟨f,hf,he⟩ := Finset.mem_image.mp ((batch j _).mpr hj)
        exact ⟨f,⟨j,List.mem_toFinset.mp hf⟩,he⟩
    rw [hmem]
    apply exists_congr
    intro j
    rw [sub_point_activationBatch L i ψ]
    change src (baseProjection L v) j = x ∧ _ ↔ _
    constructor
    · rintro ⟨rfl,hc,hd⟩
      exact ⟨rfl,Prod.ext hc hd⟩
    · rintro ⟨rfl,hw⟩
      exact ⟨rfl,congrArg Prod.fst hw,congrArg Prod.snd hw⟩

  rw [tiles_range_iff_unique_base _ (point_injective L o)]
  simp_rw [hm]
  constructor
  · intro h x
    apply (Function.bijective_iff_existsUnique _).mpr
    intro y
    obtain ⟨v,hv,hy⟩ := htarget x y
    obtain ⟨w,hw,hu⟩ := h v
    change tgt v = y at hy
    rw [hv,hy] at hw hu
    obtain ⟨j,hj,ht⟩ := hw
    refine ⟨j,ht,fun j' ht' => hsrc x ?_ (ht'.trans ht.symm)⟩
    exact (hu (src x j') ⟨j',rfl,ht'⟩).trans hj.symm
  · intro h v
    obtain ⟨j,hj,hu⟩ := (h (baseProjection L v)).existsUnique (tgt v)
    exact ⟨src (baseProjection L v) j,⟨j,rfl,hj⟩,by
      rintro w ⟨j',rfl,hj'⟩
      rw [hu j' hj']⟩

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
