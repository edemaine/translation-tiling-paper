import TranslationTiling.FiniteCompiler.Effective.SparsePrimitives
import TranslationTiling.FiniteCompiler.Effective.NumericalParameters
import TranslationTiling.FiniteCompiler.SparseCycleTests

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Transfer a numerical row specification to the checked offset gadget. -/
theorem cycleCodes_correct {T : System} (E : EncodingParameters T)
    (D : Useful E → Low E) (rows : List CycleRow)
    (hspec : ∀ n, CycleTest rows n ↔ q0 E (decodeNumericalPoint E ((0, 0), n)) =
      (0, D (usefulProjection E (decodeNumericalPoint E ((0, 0), n))))) :
    (cycleCodes E.cyclicOrder rows).toFinset.image (decodeNumericalPoint E) = offsetTile E D := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    apply (mem_offsetTile E D _).mpr
    exact (hspec n).mp (of_decide_eq_true (List.mem_filter.mp hn).2)
  · intro hg
    have hq := (mem_offsetTile E D g).mp hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = (0, 0) := congrArg Prod.fst hq
    have he : decodeNumericalPoint E ((0, 0), n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨((0, 0), n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    apply decide_eq_true
    apply (hspec n).mpr
    simpa only [he] using hq


variable {T : System} (E : EncodingParameters T) {t : ℕ} [NeZero t]

abbrev Slots (T : System) := Fin (T.width + 2)

structure SparseConfigMatches (cs : Slots T → CycleConfiguration)
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) where
  other : ZMod t → List ℕ
  on : ∀ j, cs (channelEquiv T (cycle j)) =
    (E.r (cycle j),other j,E.a (cycle (j-1)),E.b (cycle (j-1)),true)
  test : ∀ j n, KernelTest (other j) n ↔ (n : K E (cycle j)) ∈ digitSubgroup E (cycle j) (labels j)
  off : ∀ i, (∀ j, cycle j ≠ i) →
    (cs (channelEquiv T i)).1 = E.r i ∧ (cs (channelEquiv T i)).2.2.2.2 = false

variable {E} {cs : Slots T → CycleConfiguration} {cycle : ZMod t ↪ Channel T}
  {labels : ∀ j, Label T (cycle j)}

/-- Valid choices provide bounded coordinates and a subgroup displacement. -/
theorem sparseChoice_on (hs : SparseConfigMatches E cs cycle labels)
    (zs : Slots T → SparseChoice) (hz : ∀ s, zs s ∈ sparseAlphabet (cs s)) (j : ZMod t) :
    (zs (channelEquiv T (cycle j))).1 < E.a (cycle (j-1)) ∧
    (zs (channelEquiv T (cycle j))).2.1 < E.b (cycle (j-1)) ∧
    (zs (channelEquiv T (cycle j))).2.2 < E.r (cycle j) ∧
    ((zs (channelEquiv T (cycle j))).2.2 : K E (cycle j)) ∈
      digitSubgroup E (cycle j) (labels j) := by
  have h := hz (channelEquiv T (cycle j))
  rw [hs.on j] at h
  simp only [sparseAlphabet,ite_true,List.mem_flatMap,List.mem_map,
    List.mem_range,subgroupCodes,List.mem_filter,decide_eq_true_eq] at h
  obtain ⟨a,ha,b,hb,d,⟨hd,ht⟩,he⟩ := h
  rw [← he]
  exact ⟨ha,hb,hd,(hs.test j d).mp ht⟩

noncomputable def decodeSparse (hs : SparseConfigMatches E cs cycle labels)
    (zs : Slots T → SparseChoice) (hz : ∀ s, zs s ∈ sparseAlphabet (cs s)) :
    SparseCycleIndex (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j)) :=
  fun j => (((zs (channelEquiv T (cycle j))).1,(zs (channelEquiv T (cycle j))).2.1),
    ⟨(zs (channelEquiv T (cycle j))).2.2,(sparseChoice_on hs zs hz j).2.2.2⟩)

theorem sparseRows_correct (hs : SparseConfigMatches E cs cycle labels)
    (zs : Slots T → SparseChoice) (hz : ∀ s, zs s ∈ sparseAlphabet (cs s)) (n : ℕ) :
    CycleTest (List.ofFn fun s => sparseRow (cs s) (zs s)) n ↔
    q0 E (decodeNumericalPoint E ((0,0),n)) =
      (0,cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j))
        (sparseCycleMaps (M := K E) (N := P E) cycle _ (decodeSparse hs zs hz))
        (usefulProjection E (decodeNumericalPoint E ((0,0),n)))) := by
  let z := decodeSparse hs zs hz
  let d := sparseCycleMaps (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j)) z
  have hrow (i : Channel T) : CycleRowTest (sparseRow (cs (channelEquiv T i))
      (zs (channelEquiv T i))) n ↔
      (n : K E i) = cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0,0),n))) i := by
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j,rfl⟩ := hi
      rw [hs.on j]
      simp only [sparseRow,ite_true,cycleShift_apply]
      change (n % E.r (cycle j) =
        (pointTable (E.a (cycle (j-1))) (E.b (cycle (j-1))) (zs (channelEquiv T (cycle j)))).getD
          (rectangularIndex (E.b (cycle (j-1))) (n % E.a (cycle (j-1))) (n % E.b (cycle (j-1)))) 0 % E.r (cycle j)) ↔ _
      have he := pointTable_apply (zs (channelEquiv T (cycle j)))
        ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1)))))
      simp only [ZMod.val_natCast] at he
      rw [he]
      change (n % E.r (cycle j) = (if n % E.a (cycle (j-1)) = (zs (channelEquiv T (cycle j))).1 ∧
          n % E.b (cycle (j-1)) = (zs (channelEquiv T (cycle j))).2.1 then
          (zs (channelEquiv T (cycle j))).2.2 else 0) % E.r (cycle j)) ↔
        (n : K E (cycle j)) = d j ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1)))))
      have hbounds := sparseChoice_on hs zs hz j
      have hpoint : ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1))))) = (z j).1 ↔
          n % E.a (cycle (j-1)) = (zs (channelEquiv T (cycle j))).1 ∧
          n % E.b (cycle (j-1)) = (zs (channelEquiv T (cycle j))).2.1 := by
        rw [Prod.ext_iff,← (ZMod.val_injective (E.a (cycle (j-1)))).eq_iff,
          ← (ZMod.val_injective (E.b (cycle (j-1)))).eq_iff]
        simp only [z,decodeSparse,ZMod.val_natCast,Nat.mod_eq_of_lt hbounds.1,
          Nat.mod_eq_of_lt hbounds.2.1]
      rw [← (ZMod.val_injective (E.r (cycle j))).eq_iff]
      simp only [d,sparseCycleMaps,← hpoint]
      split_ifs <;> simp_all [z,decodeSparse,ZMod.val_natCast]
    · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      obtain ⟨hr,hf⟩ := hs.off i hoff
      simp only [sparseRow,hf,Bool.false_eq_true,ite_false,hr,cycleRowTest_zero,
        cycleShift_eq_zero (M := K E) (N := P E) cycle _ d _ hoff]
      rw [← (ZMod.val_injective (E.r i)).eq_iff]
      simp only [ZMod.val_natCast,ZMod.val_zero]
  have hrows : CycleTest (List.ofFn fun s => sparseRow (cs s) (zs s)) n ↔
      ∀ i : Channel T, (n : K E i) = cycleShift cycle
        (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0,0),n))) i := by
    simp only [CycleTest,List.forall_mem_ofFn_iff]
    constructor
    · intro h i; exact (hrow i).mp (h (channelEquiv T i))
    · intro h s
      simpa only [Equiv.apply_symm_apply] using (hrow ((channelEquiv T).symm s)).mpr (h _)
  rw [hrows]
  constructor
  · intro h
    refine Prod.ext (by rfl) ?_
    funext i
    change low E i (n : ZMod (E.r i ^ 2)) = _
    rw [CyclicShear.low_natCast]
    exact h i
  · intro h i
    have hi := congrFun (congrArg Prod.snd h) i
    change low E i (n : ZMod (E.r i ^ 2)) = _ at hi
    rw [CyclicShear.low_natCast] at hi
    exact hi

noncomputable def encodeSparse
    (z : SparseCycleIndex (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j)))
    (s : Slots T) : SparseChoice :=
  if h : ∃ j, cycle j = (channelEquiv T).symm s then
    let j := Classical.choose h
    ((z j).1.1.val,(z j).1.2.val,(z j).2.val.val)
  else (0,0,0)

theorem encodeSparse_on
    (z : SparseCycleIndex (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j)))
    (j : ZMod t) : encodeSparse z (channelEquiv T (cycle j)) =
      ((z j).1.1.val,(z j).1.2.val,(z j).2.val.val) := by
  have h : ∃ k, cycle k = (channelEquiv T).symm (channelEquiv T (cycle j)) :=
    ⟨j,((channelEquiv T).symm_apply_apply _).symm⟩
  have hc : Classical.choose h = j := cycle.injective
    ((Classical.choose_spec h).trans ((channelEquiv T).symm_apply_apply _))
  rw [encodeSparse,dif_pos h]
  exact congrArg (fun k => ((z k).1.1.val,(z k).1.2.val,(z k).2.val.val)) hc

theorem encodeSparse_valid (hs : SparseConfigMatches E cs cycle labels)
    (z : SparseCycleIndex (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j))) :
    ∀ s, encodeSparse z s ∈ sparseAlphabet (cs s) := by
  intro s
  by_cases hi : ∃ j, cycle j = (channelEquiv T).symm s
  · obtain ⟨j,hj⟩ := hi
    have he : s = channelEquiv T (cycle j) :=
      ((channelEquiv T).apply_symm_apply s).symm.trans (congrArg (channelEquiv T) hj.symm)
    subst s
    rw [encodeSparse_on,hs.on j]
    simp only [sparseAlphabet,ite_true,List.mem_flatMap,List.mem_range,List.mem_map]
    refine ⟨_,ZMod.val_lt _,_,ZMod.val_lt _,_,?_,rfl⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (ZMod.val_lt _),decide_eq_true ?_⟩
    apply (hs.test j _).mpr
    simpa only [ZMod.natCast_zmod_val] using (z j).2.property
  · have hoff : ∀ j, cycle j ≠ (channelEquiv T).symm s := by simpa only [not_exists] using hi
    have hb : (cs s).2.2.2.2 = false := by
      simpa only [Equiv.apply_symm_apply] using (hs.off ((channelEquiv T).symm s) hoff).2
    simp only [encodeSparse,dif_neg hi,sparseAlphabet,hb,Bool.false_eq_true,ite_false,List.mem_singleton]

theorem decode_encodeSparse (hs : SparseConfigMatches E cs cycle labels)
    (z : SparseCycleIndex (M := K E) (N := P E) cycle (fun j => digitSubgroup E (cycle j) (labels j))) :
    decodeSparse hs (encodeSparse z) (encodeSparse_valid hs z) = z := by
  funext j
  apply Prod.ext
  · change (((encodeSparse z (channelEquiv T (cycle j))).1 : ZMod (E.a (cycle (j-1)))),
      ((encodeSparse z (channelEquiv T (cycle j))).2.1 : ZMod (E.b (cycle (j-1))))) = (z j).1
    rw [encodeSparse_on]
    simp only [ZMod.natCast_zmod_val]
  · apply Subtype.ext
    change ((encodeSparse z (channelEquiv T (cycle j))).2.2 : K E (cycle j)) = (z j).2.val
    rw [encodeSparse_on]
    exact ZMod.natCast_zmod_val _

theorem sparseRows_ofFn {m : ℕ} (cs : Fin m → CycleConfiguration) (xs : List SparseChoice) :
    sparseRows (List.ofFn cs) xs =
      List.ofFn (fun s => sparseRow (cs s) (vectorOfList xs s)) := by
  apply List.ext_getElem
  · simp only [sparseRows,List.length_map,List.length_range,List.length_ofFn]
  · intro k hk hk'
    have hkm : k < m := by simpa only [sparseRows,List.length_map,List.length_range,List.length_ofFn] using hk
    simp only [sparseRows,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,dif_pos hkm,Option.getD_some,List.getElem_ofFn,vectorOfList]
    rfl

theorem sparseGadgets_ofFn {m : ℕ} (N : ℕ) (cs : Fin m → CycleConfiguration) :
    sparseGadgets N (List.ofFn cs) =
      (vectors (fun s => sparseAlphabet (cs s))).map fun zs =>
        cycleCodes N (List.ofFn fun s => sparseRow (cs s) (zs s)) := by
  unfold sparseGadgets vectors
  rw [List.map_ofFn,List.map_map]
  apply List.map_congr_left
  intro xs _
  rw [sparseRows_ofFn]
  rfl

theorem sparseGadgets_correct (hs : SparseConfigMatches E cs cycle labels) :
    ((sparseGadgets E.cyclicOrder (List.ofFn cs)).map fun xs =>
      xs.toFinset.image (decodeNumericalPoint E)).toFinset = sparseCycleTiles E cycle labels := by
  have hg (zs : Slots T → SparseChoice) (hz : ∀ s, zs s ∈ sparseAlphabet (cs s)) :
      (cycleCodes E.cyclicOrder (List.ofFn fun s => sparseRow (cs s) (zs s))).toFinset.image
        (decodeNumericalPoint E) =
      cycleTile E cycle labels (sparseCycleMaps (M := K E) (N := P E) cycle _ (decodeSparse hs zs hz)) :=
    cycleCodes_correct E _ _ (sparseRows_correct hs zs hz)
  rw [sparseGadgets_ofFn]
  ext F
  simp only [List.mem_toFinset,List.mem_map,sparseCycleTiles,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨zs,hzs,rfl⟩,rfl⟩
    exact ⟨decodeSparse hs zs ((mem_vectors _ _).mp hzs),(hg zs ((mem_vectors _ _).mp hzs)).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_,⟨encodeSparse z,(mem_vectors _ _).mpr (encodeSparse_valid hs z),rfl⟩,?_⟩
    rw [hg _ (encodeSparse_valid hs z),decode_encodeSparse]

end
end TranslationTiling.FiniteCompiler.Effective
