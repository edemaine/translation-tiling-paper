import TranslationTiling.FiniteCompiler.Effective.GuardedNumericalDeck
import TranslationTiling.FiniteCompiler.PartialStrip

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective
open scoped Classical BigOperators

noncomputable section

local instance guardedNumericalCorrectFrame : SeedFrame := compactSeedFrame

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

abbrev channelNumber (i : Channel T) : ℕ := (channelEquiv T i).val

def guardedLabelNumber (i : Channel T) : Label T i → ℕ :=
  match i with
  | .inl _ => Fin.val
  | .inr _ => fun _ => 0

structure GuardedRowsMatch (rs : GuardedRows) : Prop where
  length : rs.length = T.width+2
  a : ∀ i, rowA rs (channelNumber i) = E.a i
  b : ∀ i, rowB rs (channelNumber i) = E.b i
  r : ∀ i, rowR rs (channelNumber i) = E.r i
  digit : ∀ (i : Channel T) (v : Label T i),
    (rowDigits rs (channelNumber i)).getD (guardedLabelNumber i v) 0 = E.digitPrime i v

variable {E} {rs : GuardedRows} (hm : GuardedRowsMatch E rs)

include hm in
theorem rowsIndex (n : ℕ) :
    n ∈ List.range rs.length ↔ ∃ i : Channel T, channelNumber i = n := by
  rw [List.mem_range,hm.length]
  constructor
  · intro h
    exact ⟨(channelEquiv T).symm ⟨n,h⟩,by simp [channelNumber]⟩
  · rintro ⟨i,rfl⟩
    exact (channelEquiv T i).isLt

include hm in
theorem rowsMap_mem {α : Type*} {f : ℕ → α} {g : Channel T → α}
    (he : ∀ i, f (channelNumber i) = g i) {a : α} :
    a ∈ (List.range rs.length).map f ↔
      a ∈ (Finset.univ : Finset (Channel T)).toList.map g := by
  simp only [List.mem_map,rowsIndex hm,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(he i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨channelNumber i,⟨i,rfl⟩,he i⟩

include hm in
theorem rowsOrder_eq : guardedOrder rs = E.cyclicOrder := by
  have he : (List.range rs.length).map (fun j => (rowR rs j)^2 * rowA rs j * rowB rs j) =
      List.ofFn (fun (i : Fin (T.width+2)) =>
        (rowR rs i.val)^2 * rowA rs i.val * rowB rs i.val) := by
    apply List.ext_getElem
    · simp [hm.length]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  unfold guardedOrder
  rw [he,Fin.prod_ofFn]
  have hf : (∏ i : Fin (T.width+2), (rowR rs i.val)^2 * rowA rs i.val * rowB rs i.val) =
        ∏ i : Channel T, E.blockModulus i := by
    rw [← (channelEquiv T).prod_comp]
    simp only [hm.r,hm.a,hm.b,EncodingParameters.blockModulus]
  rw [hf]
  norm_num [EncodingParameters.cyclicOrder,residueModulus_value,compactSeedFrame]

include hm in
theorem rowsInput_eq : (guardedModuli rs).prod = inputOrder E := by
  have he : guardedModuli rs = List.ofFn (fun (i : Fin (T.width+2)) => rowR rs i.val) := by
    unfold guardedModuli
    apply List.ext_getElem
    · simp [hm.length]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [he,Fin.prod_ofFn,← (channelEquiv T).prod_comp]
  simp only [inputOrder,hm.r,channelNumber]

include hm in
theorem numericalKernel_correct :
    (kernelCodes (guardedOrder rs) (guardedModuli rs)).toFinset.image (decodeNumericalPoint E) =
      kernelTile E := by
  have hmod (n : ℕ) : KernelTest (guardedModuli rs) n ↔
      KernelTest ((Finset.univ : Finset (Channel T)).toList.map E.r) n := by
    simp only [KernelTest,guardedModuli,rowsMap_mem hm hm.r]
  simpa only [kernelCodes,rowsOrder_eq hm,hmod] using kernelCodes_correct E

include hm in
theorem numericalInvariance_correct (i : Channel T) (h : Plane) (o : Option ℕ) :
    (guardedInvariance rs (channelNumber i) h o).toFinset.image (decodeNumericalPoint E) =
      invarianceTile E i (h, fun j => if o = some (channelNumber j) then 1 else 0) := by
  have hmod (n : ℕ) : KernelTest (guardedModuli rs) n ↔
      KernelTest ((Finset.univ : Finset (Channel T)).toList.map E.r) n := by
    simp only [KernelTest,guardedModuli,rowsMap_mem hm hm.r]
  let q (j : Channel T) : K E j := if o = some (channelNumber j) then 1 else 0
  have hmap (j : Channel T) :
      (rowR rs (channelNumber j), if o = some (channelNumber j) then 1 % rowR rs (channelNumber j) else 0) =
        (E.r j,(q j).val) := by
    rw [hm.r]
    dsimp [q]
    split <;> simp [ZMod.val_one_eq_one_mod]
  have hcongr (n : ℕ) : Congruences
      ((List.range rs.length).map fun j => (rowR rs j, if o = some j then 1 % rowR rs j else 0)) n ↔
      Congruences ((Finset.univ : Finset (Channel T)).toList.map (fun j => (E.r j,(q j).val))) n := by
    unfold Congruences
    simp only [rowsMap_mem hm
      (f := fun j => (rowR rs j, if o = some j then 1 % rowR rs j else 0))
      (g := fun j => (E.r j,(q j).val)) hmap]
  simpa only [guardedInvariance,invarianceCodes,rowsOrder_eq hm,hm.a,hm.b,hmod,hcongr] using
    invarianceCodes_correct E i (h,q)

include hm in
theorem numericalEnvironment_test (i : Channel T) (n : ℕ) :
    KernelTest (guardedOther rs (channelNumber i)) n ↔
      KernelTest (((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r) n := by
  unfold KernelTest guardedOther
  simp only [List.mem_map,List.mem_filter,decide_eq_true_eq,Finset.mem_toList,
    Finset.mem_filter,Finset.mem_univ,true_and,rowsIndex hm]
  constructor
  · rintro h r ⟨j, hj,rfl⟩
    have he : channelNumber j ≠ channelNumber i :=
      fun hh => hj ((channelEquiv T).injective (Fin.ext hh))
    rw [← hm.r]
    exact h _ ⟨_,⟨⟨j,rfl⟩,he⟩,rfl⟩
  · rintro h r ⟨_,⟨⟨j,rfl⟩,hj⟩,rfl⟩
    rw [hm.r]
    exact h _ ⟨j,fun hh => hj (congrArg channelNumber hh),rfl⟩

include hm in
theorem numericalOrdinary_correct (i : Column T) (s : ℕ) (hs : T.slope i = s) :
    (compactCodes (guardedEnv rs (channelNumber (.inl i))) s).toFinset.image
      (decodeNumericalPoint E) = ordinaryActivationTile E i := by
  have hD : D T = 1225 := by norm_num [D,residueModulus_value,compactSeedFrame]
  have hcode : compactCodes (guardedEnv rs (channelNumber (.inl i))) s =
      compactCodes (nativeActivationEnvironment E (.inl i)) s := by
    unfold compactCodes compactBatch activationBatchCodes ActivationBatchTest guardedEnv
      nativeActivationEnvironment
    simp only [rowsOrder_eq hm,hm.a,hm.b,hm.r,hD]
    simp_rw [numericalEnvironment_test hm]
  rw [hcode]
  exact compactCodes_correct E i s hs

include hm in
theorem numericalSeed_correct (t : Fin 2) :
    (seedCodes (guardedEnv rs (channelNumber (T:=T) (.inr t)))
      (rowA rs (channelNumber (T:=T) (.inr (otherSeed t)))) 35).toFinset.image
      (decodeNumericalPoint E) = seedActivationTile E t := by
  have he : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
  have hD : D T = 1225 := by norm_num [D,he]
  have hcode : seedCodes (guardedEnv rs (channelNumber (T:=T) (.inr t)))
      (rowA rs (channelNumber (T:=T) (.inr (otherSeed t)))) 35 =
      seedCodes (nativeActivationEnvironment E (.inr t))
        (E.a (.inr (otherSeed t))) residueModulus := by
    unfold seedCodes seedBatchCodes activationBatchCodes ActivationBatchTest guardedEnv
      nativeActivationEnvironment
    simp only [rowsOrder_eq hm,hm.a,hm.b,hm.r,hD,he]
    simp_rw [numericalEnvironment_test hm]
  rw [hcode]
  exact seedCodes_correct E t

def vectorForCycle {t : ℕ} [NeZero t] (cy : ZMod t ↪ Channel T)
    (lab : ∀ j, Label T (cy j)) : GuardedAssignments := List.ofFn fun j =>
      (channelNumber (cy (ZMod.finEquiv t j)),
        guardedLabelNumber _ (lab (ZMod.finEquiv t j)))

include hm in
theorem numericalCycle_correct {t : ℕ} [NeZero t] (cy : ZMod t ↪ Channel T)
    (lab : ∀ j, Label T (cy j)) :
    ((guardedCycle rs (vectorForCycle cy lab)).map
      (fun xs => xs.toFinset.image (decodeNumericalPoint E))).toFinset =
      fixedCycleTiles E cy lab := by
  let xs := vectorForCycle cy lab
  have hlen : xs.length = t := by simp [xs,vectorForCycle]
  have hnonempty : xs.length ≠ 0 := by rw [hlen]; exact NeZero.ne t
  have hkeys : xs.map Prod.fst = List.ofFn (fun j : Fin t => channelNumber (cy (ZMod.finEquiv t j))) := by
    simp [xs,vectorForCycle,List.map_ofFn,Function.comp_def]
  have hget (j : Fin t) : xs.getD j.val (0,0) =
      (channelNumber (cy (ZMod.finEquiv t j)), guardedLabelNumber _ (lab (ZMod.finEquiv t j))) := by
    simp [xs,vectorForCycle,List.getD_eq_getElem?_getD,j.isLt]
  have hkey (j : ZMod t) : (xs.map Prod.fst).idxOf (channelNumber (cy j)) = j.val := by
    let f (i : Fin t) := channelNumber (cy (ZMod.finEquiv t i))
    have hf : Function.Injective f := by
      intro a b h
      exact (ZMod.finEquiv t).injective (cy.injective ((channelEquiv T).injective (Fin.ext h)))
    let a := (ZMod.finEquiv t).symm j
    have ha : t > a.val := a.isLt
    have hval : a.val = j.val := by cases t with | zero => exact (NeZero.ne 0 rfl).elim | succ t => rfl
    rw [hkeys]
    have hm : channelNumber (cy j) ∈ List.ofFn f :=
      List.mem_ofFn.mpr ⟨a,by simp [f,a]⟩
    have hi := List.idxOf_lt_length_of_mem hm
    rw [List.length_ofFn] at hi
    have hu := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
    rw [List.getElem_ofFn] at hu
    have hv : f ⟨(List.ofFn f).idxOf (channelNumber (cy j)),hi⟩ = f a := by
      simpa [f,a] using hu
    exact (congrArg Fin.val (hf hv)).trans hval
  have hoffIndex (i : Channel T) (hi : ∀ j, cy j ≠ i) :
      xs.length ≤ (xs.map Prod.fst).idxOf (channelNumber i) := by
    by_contra! h
    have hx : channelNumber i ∈ xs.map Prod.fst := by
      apply List.idxOf_lt_length_iff.mp
      simpa using h
    rw [hkeys] at hx
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx
    exact hi (ZMod.finEquiv t j) ((channelEquiv T).injective (Fin.ext hj))
  have hprev (j : ZMod t) : previousColumn xs j.val = channelNumber (cy (j-1)) := by
    have ht : 0 < t := NeZero.pos _
    have he : ((j.val+t-1 : ℕ) : ZMod t) = j-1 := by
      rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,
        Nat.cast_one,add_zero]
    have hmod : (j.val+t-1)%t = (j-1).val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val he
    unfold previousColumn
    rw [hlen,hmod]
    have hv : (((ZMod.finEquiv t).symm (j-1) : Fin t) : ℕ) = (j-1).val := by cases t with | zero => exact (NeZero.ne 0 rfl).elim | succ t => rfl
    rw [← hv,hget]
    simp
  let raw := guardedCycleRows rs xs
  let cs (i : Slots T) := (raw.getD i.val ((0,[],0,0,false),0)).1
  let qs := raw.map Prod.snd
  have htab (i : Slots T) : raw.getD i.val ((0,[],0,0,false),0) =
      let j := (xs.map Prod.fst).idxOf i.val
      ((rowR rs i.val, [], rowA rs (previousColumn xs j), rowB rs (previousColumn xs j),
        decide (j < xs.length)), (rowDigits rs i.val).getD (xs.getD j (0,0)).2 0) := by
    have hi : i.val < rs.length := hm.length.symm ▸ i.isLt
    simp [raw,guardedCycleRows,List.getD_eq_getElem?_getD,hi]
  have hone (j : ZMod t) : cs (channelEquiv T (cy j)) =
      (E.r (cy j),[],E.a (cy (j-1)),E.b (cy (j-1)),true) := by
    unfold cs
    rw [htab]
    simp only [hkey,hprev,hm.r,hm.a,hm.b,hlen,ZMod.val_lt,decide_true]
  have hzero (i : Channel T) (hn : ∀ j, cy j ≠ i) :
      (cs (channelEquiv T i)).1 = E.r i ∧ (cs (channelEquiv T i)).2.2.2.2 = false := by
    unfold cs
    rw [htab]
    simp [hm.r,not_lt_of_ge (hoffIndex i hn)]
  have hq (j : ZMod t) :
      qs.getD (channelNumber (cy j)) 0 = E.digitPrime (cy j) (lab j) := by
    have hi : channelNumber (cy j) < raw.length := by
      unfold raw guardedCycleRows
      simp only [List.length_map,List.length_range,hm.length]
      exact (channelEquiv T (cy j)).isLt
    have hi' : channelNumber (cy j) < qs.length := by simpa only [qs,List.length_map] using hi
    rw [List.getD_eq_getElem _ _ hi']
    simp only [qs,List.getElem_map]
    rw [← List.getD_eq_getElem _ ((0,[],0,0,false),0) hi,htab (channelEquiv T (cy j))]
    simp only [hkey]
    have hv : (((ZMod.finEquiv t).symm j : Fin t) : ℕ) = j.val := by cases t with | zero => exact (NeZero.ne 0 rfl).elim | succ t => rfl
    rw [← hv,hget]
    exact (congrArg (fun z : ZMod t =>
      (rowDigits rs (channelNumber (cy j))).getD (guardedLabelNumber (cy z) (lab z)) 0)
        ((ZMod.finEquiv t).apply_symm_apply j)).trans (hm.digit (cy j) (lab j))
  have hrs : raw.map Prod.fst = List.ofFn cs := by
    apply List.ext_getElem
    · simp [raw,guardedCycleRows,hm.length]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn,cs]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
  simp only [guardedCycle,show (vectorForCycle cy lab) = xs from rfl,hnonempty,
    rowsOrder_eq hm]
  change ((fixedGadgets E.cyclicOrder (raw.map Prod.fst) qs).map _).toFinset = _
  rw [hrs]
  exact fixedGadgets_correct_of_rows (fun _ => []) hone hzero qs hq

def guardedDecodedFamily (E : EncodingParameters T) (Fs : List CyclicTile) :
    Finset (Finset (Ambient E)) :=
  (Fs.map (fun xs => xs.toFinset.image (decodeNumericalPoint E))).toFinset

@[simp] theorem mem_guardedDecodedFamily (Fs : List CyclicTile) (F : Finset (Ambient E)) :
    F ∈ guardedDecodedFamily E Fs ↔ ∃ xs ∈ Fs, xs.toFinset.image (decodeNumericalPoint E) = F := by
  simp only [guardedDecodedFamily,List.mem_toFinset,List.mem_map]

@[simp] theorem guardedDecodedFamily_append (Fs Gs : List CyclicTile) :
    guardedDecodedFamily E (Fs++Gs) = guardedDecodedFamily E Fs ∪ guardedDecodedFamily E Gs := by
  simp only [guardedDecodedFamily,List.map_append,List.toFinset_append]

@[simp] theorem guardedDecodedFamily_cons (F : CyclicTile) (Fs : List CyclicTile) :
    guardedDecodedFamily E (F::Fs) =
      insert (F.toFinset.image (decodeNumericalPoint E)) (guardedDecodedFamily E Fs) := by
  simp only [guardedDecodedFamily,List.map_cons,List.toFinset_cons]

theorem channelNumber_injective : Function.Injective (channelNumber (T := T)) :=
  fun _ _ h => (channelEquiv T).injective (Fin.ext h)

theorem channelNumber_inl (i : Column T) : channelNumber (.inl i) = i.val := rfl
theorem channelNumber_inr (t : Fin 2) : channelNumber (.inr t : Channel T) = T.width+t.val := rfl

include hm in
theorem numericalDependence_correct (slopes : List ℕ)
    (hs : ∀ i : Column T, T.slope i = slopes.getD i.val 0) :
    guardedDecodedFamily E (guardedRawDependence rs slopes) = dependenceTiles E := by
  let low : List CyclicTile := (List.range rs.length).flatMap (fun i =>
    ((List.range rs.length).filter (fun j => decide (j ≠ i))).map
      (fun j => guardedInvariance rs i 0 (some j)))
  let lines : List CyclicTile := ((List.range (rs.length-2)).map fun i =>
    guardedInvariance rs i (1,-(slopes.getD i 0 : ℤ)) none)
  let seeds : List CyclicTile := (List.range 2).flatMap fun j =>
    [guardedInvariance rs (rs.length-2+j) (35,0) none,
     guardedInvariance rs (rs.length-2+j) (0,35) none]
  have hwidth : rs.length-2 = T.width := by rw [hm.length]; omega
  have hm' : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
  have hl (i j : Channel T) (he : j ≠ i) :
      (guardedInvariance rs (channelNumber i) 0 (some (channelNumber j))).toFinset.image
        (decodeNumericalPoint E) = dependenceTile E (.inl ⟨i,⟨j,he⟩⟩) := by
    rw [numericalInvariance_correct hm]
    unfold dependenceTile dependenceShift lowGenerator
    congr 2
    funext u
    by_cases h : j=u
    · subst u
      simp
    · have hn : channelNumber j ≠ channelNumber u := fun he => h (channelNumber_injective he)
      simp [h,Ne.symm h,hn]
  have hline (i : Column T) :
      (guardedInvariance rs i.val (1,-(slopes.getD i.val 0 : ℤ)) none).toFinset.image
        (decodeNumericalPoint E) = dependenceTile E (.inr (.inl i)) := by
    rw [← channelNumber_inl i]
    rw [numericalInvariance_correct hm,channelNumber_inl,← hs]
    rfl
  have hseed (i : Fin 2) (b : Bool) :
      (guardedInvariance rs (rs.length-2+i.val)
        (if b then (0,35) else (35,0)) none).toFinset.image (decodeNumericalPoint E) =
        dependenceTile E (.inr (.inr (i,b))) := by
    rw [hwidth,← channelNumber_inr i,numericalInvariance_correct hm]
    cases b <;> simp [dependenceTile,dependenceChannel,dependenceShift,seedStep,hm'] <;> rfl
  have hlow : guardedDecodedFamily E low =
      Finset.univ.image (fun d : Σ i : Channel T, {j : Channel T // j ≠ i} =>
        dependenceTile E (Sum.inl d)) := by
    ext F
    simp only [mem_guardedDecodedFamily,low,List.mem_flatMap,List.mem_map,List.mem_filter,
      decide_eq_true_eq,rowsIndex hm,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨xs,⟨_,⟨i,rfl⟩,_,⟨⟨j,rfl⟩,hne⟩,rfl⟩,rfl⟩
      have he : j ≠ i := fun h => hne (congrArg channelNumber h)
      exact ⟨⟨i,⟨j,he⟩⟩,(hl i j he).symm⟩
    · rintro ⟨⟨i,⟨j,hji⟩⟩,rfl⟩
      exact ⟨_,⟨_,⟨i,rfl⟩,_,⟨⟨j,rfl⟩,fun he => hji (channelNumber_injective he)⟩,rfl⟩,
          hl i j hji⟩
  have hlines : guardedDecodedFamily E lines =
      Finset.univ.image (fun n : Column T => dependenceTile E (.inr (.inl n))) := by
    ext F
    simp only [mem_guardedDecodedFamily,lines,List.mem_map,List.mem_range,
      hwidth,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨xs,⟨i,hi,rfl⟩,rfl⟩
      exact ⟨⟨i,hi⟩,(hline ⟨i,hi⟩).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i.val,i.isLt,rfl⟩,hline i⟩
  have hseeds : guardedDecodedFamily E seeds =
      Finset.univ.image (fun d : Fin 2 × Bool => dependenceTile E (.inr (.inr d))) := by
    ext F
    simp only [mem_guardedDecodedFamily,seeds,List.mem_flatMap,List.mem_range,
      List.mem_cons,List.not_mem_nil,or_false,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨xs,⟨t,ht,rfl|rfl⟩,rfl⟩
      · exact ⟨(⟨t,ht⟩,false),(hseed ⟨t,ht⟩ false).symm⟩
      · exact ⟨(⟨t,ht⟩,true),(hseed ⟨t,ht⟩ true).symm⟩
    · rintro ⟨⟨t,b⟩,rfl⟩
      cases b
      · exact ⟨_,⟨t.val,t.isLt,Or.inl rfl⟩,hseed t false⟩
      · exact ⟨_,⟨t.val,t.isLt,Or.inr rfl⟩,hseed t true⟩
  change guardedDecodedFamily E ((low++lines)++seeds) = _
  rw [guardedDecodedFamily_append,guardedDecodedFamily_append,hlow,hlines,hseeds]
  ext F
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,dependenceTiles]
  constructor
  · rintro ((⟨a,rfl⟩|⟨b,rfl⟩)|⟨c,rfl⟩)
    · exact ⟨.inl a,rfl⟩
    · exact ⟨.inr (.inl b),rfl⟩
    · exact ⟨.inr (.inr c),rfl⟩
  · rintro ⟨a|b|c,rfl⟩
    · exact Or.inl (Or.inl ⟨a,rfl⟩)
    · exact Or.inl (Or.inr ⟨b,rfl⟩)
    · exact Or.inr ⟨c,rfl⟩

include hm in
theorem numericalActivation_correct (slopes : List ℕ)
    (hs : ∀ i : Column T, T.slope i = slopes.getD i.val 0) :
    guardedDecodedFamily E (guardedRawActivation rs slopes) =
      (Finset.univ.image (ordinaryActivationTile E)) ∪
        (Finset.univ.image (seedActivationTile E)) := by
  unfold guardedRawActivation
  rw [guardedDecodedFamily_append]
  have hwidth : rs.length-2 = T.width := by rw [hm.length]; omega
  rw [hwidth]
  congr 1
  · ext F
    simp only [mem_guardedDecodedFamily,List.mem_map,List.mem_range,
      Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨F,⟨i,hi,rfl⟩,rfl⟩
      exact ⟨⟨i,hi⟩,(numericalOrdinary_correct hm ⟨i,hi⟩ _ (hs _)).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i.val,i.isLt,rfl⟩,numericalOrdinary_correct hm i _ (hs _)⟩
  · ext F
    simp only [mem_guardedDecodedFamily,List.mem_map,List.mem_range,
      Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨F,⟨i,hi,rfl⟩,rfl⟩
      exact ⟨⟨i,hi⟩,(numericalSeed_correct hm ⟨i,hi⟩).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i.val,i.isLt,rfl⟩,numericalSeed_correct hm i⟩

include hm in
theorem numericalDeck_correct (slopes : List ℕ) (tests : List GuardedAssignments)
    (ps : List (PartialTest T)) (hs : ∀ i : Column T, T.slope i = slopes.getD i.val 0)
    (htests : guardedDecodedFamily E (tests.flatMap (guardedCycle rs)) =
      seedConstraintTiles E ∪ (ps.flatMap fun p => (partialTiles E p).toList).toFinset) :
    guardedDecodedFamily E (guardedRawDeck rs slopes tests) = partialDeck E ps := by
  unfold guardedRawDeck partialDeck structuralTiles
  rw [guardedDecodedFamily_cons, guardedDecodedFamily_append, guardedDecodedFamily_append,
    numericalKernel_correct hm,numericalDependence_correct hm slopes hs,
    numericalActivation_correct hm slopes hs,htests]
  ext F
  simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
  tauto

theorem guardedCycle_length (rs : GuardedRows) (s : GuardedAssignments) :
    (guardedCycle rs s).length ≤ 1 := by
  unfold guardedCycle fixedGadgets
  split <;> simp

theorem listSumMap_le {α : Type*} {as : List α} {f g : α → ℕ}
    (h : ∀ a ∈ as, f a ≤ g a) : (as.map f).sum ≤ (as.map g).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem guardedRawDeck_length (rs : GuardedRows) (slopes : List ℕ) (ts : List GuardedAssignments) :
    (guardedRawDeck rs slopes ts).length ≤ rs.length^2 + 2*(rs.length-2)+ts.length+7 := by
  have hinv (i : ℕ) : ((List.range rs.length).filter fun j => decide (j ≠ i)).length ≤ rs.length := by
    simpa only [List.length_range] using List.length_filter_le
      (l := List.range rs.length) (p := fun j => decide (j ≠ i))
  have ha : ((List.range rs.length).flatMap fun i =>
      ((List.range rs.length).filter (fun j => decide (j ≠ i))).map
        (fun j => guardedInvariance rs i 0 (some j))).length ≤ rs.length^2 := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.range rs.length).map fun _ => rs.length).sum := by
        apply listSumMap_le
        intro i hi
        simpa only [Function.comp_apply,List.length_map] using hinv i
      _ = _ := by simp [pow_two]
  have hb : (ts.flatMap (guardedCycle rs)).length ≤ ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
      have ht := guardedCycle_length rs t
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  unfold guardedRawDeck guardedRawDependence guardedRawActivation
  simp only [List.length_cons,List.length_append,List.length_map,List.length_range]
  have hc : ((List.range 2).flatMap fun j =>
      [guardedInvariance rs (rs.length-2+j) (35,0) none,
        guardedInvariance rs (rs.length-2+j) (0,35) none]).length = 4 := rfl
  omega

end
end TranslationTiling.FiniteCompiler.Effective
