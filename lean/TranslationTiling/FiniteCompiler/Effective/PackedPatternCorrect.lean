import TranslationTiling.FiniteCompiler.Effective.PackedPatternData
import TranslationTiling.FiniteCompiler.Effective.GuardedNumericalCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall GuardedCompiler Effective Compiler.Effective
open scoped Classical

noncomputable section

local instance packedPatternCorrectFrame : SeedFrame := compactSeedFrame
local instance packedPatternCorrectPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance packedPatternCorrectPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩
attribute [local instance] ColumnRefinement.family

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

variable {T : LeanWang.TileSet} {D : ℕ} (C : Code T D)
local instance packedPatternCorrectAlphabet : AlphabetFamily (system C) := GuardedCompiler.alphabet C

def testMask (p : PartialTest (system C)) : RawMask :=
  List.ofFn fun i => if h : i ∈ p.columns then some (p.label ⟨i,h⟩).val else none

theorem testMask_get (p : PartialTest (system C)) (i : Column (system C)) :
    (testMask C p).getD i.val none =
      if h : i ∈ p.columns then some (p.label ⟨i,h⟩).val else none := by
  rw [testMask,List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
    List.getElem_ofFn]

private theorem mask_of_pattern (P : PVec) (Q : QVec) (V : CVec D) :
    testMask C (pattern C P Q V) = List.ofFn (rawSelection P Q V) := by
  apply List.ofFn_inj.mpr
  funext i
  unfold pattern PartialTest.select
  by_cases h : (selection C P Q V i).isSome
  · rw [dif_pos (by simpa using h)]
    exact ((selection_some C P Q V i ((selection C P Q V i).get h)).mp
      (Option.some_get h).symm).symm
  · rw [dif_neg (by simpa using h)]
    have he : selection C P Q V i = none := by
      cases hg : selection C P Q V i <;> simp_all
    cases hg : rawSelection P Q V i with
    | none => rfl
    | some j =>
      have hj : j < arity D i := by
        unfold rawSelection at hg
        split at hg <;> simp_all [arity] <;> grind [Fin.isLt]
      have hh := (selection_some C P Q V i ⟨j,hj⟩).mpr hg
      simp_all

private theorem mask_of_query (a b : Fin D) (z : QueryPhase) :
    testMask C (queryPattern C (z.1,z.2.1,z.2.2,a,b)) =
      ((List.ofFn (rawSelection (d:=1) (queryLabels 5 z.1 z.2.1)
        (queryLabels 7 z.1 z.2.2) (fun _ => none))).take 18) ++ [some a.val,some b.val] := by
  rw [queryPattern,mask_of_pattern]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hel : i < 20 := by simpa using hi
    let idx : Fin 20 := ⟨i,hel⟩
    simp only [List.getElem_ofFn,Prod.fst,Prod.snd]
    by_cases h : i < 18
    · have h' : i < (List.take 18 (List.ofFn (rawSelection (d:=1) (queryLabels 5 z.1 z.2.1)
          (queryLabels 7 z.1 z.2.2) (fun _ => none)))).length := by simpa using h
      simp only [List.getElem_append_left h', List.getElem_take, List.getElem_ofFn]
      change _ = rawSelection _ _ _ idx
      unfold rawSelection
      have hrole : ¬ ∃ j : Fin 2, roleEquiv.symm idx = .inr (.inr j) := by
        rintro ⟨j,hj'⟩
        have hv := congrArg (fun r => (roleEquiv r).val) hj'
        simp only [Equiv.apply_symm_apply,idx] at hv
        change i = 9+(9+j.val) at hv
        omega
      cases hv : roleEquiv.symm idx with
      | inl i => rfl
      | inr r =>
        cases r with
        | inl j => rfl
        | inr j => exact (hrole ⟨j,hv⟩).elim
    · have hh : i = 18 ∨ i = 19 := by omega
      rcases hh with rfl | rfl <;> rfl

private theorem code_decode_getD (hn : 0 < T.length) (hcap : T.length ≤ D) (j : Fin D) :
    ((code T D hn hcap).decode j).val = T.getD j.val (T.getD 0 ⟨0,0,0,0⟩) := by
  unfold code
  dsimp only
  rw [List.getD_eq_getElem _ _ hn]
  by_cases h : j.val < T.length
  · rw [dif_pos h,List.getD_eq_getElem _ _ h]
  · rw [dif_neg h,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega),Option.getD_none]

theorem rawMask_membership (hn : 0 < T.length) (hcap : T.length ≤ D) (m : RawMask) :
    m ∈ rawGuardedMasks T D ↔
      ∃ p ∈ patterns (code T D hn hcap), testMask (code T D hn hcap) p = m := by
  let c := code T D hn hcap
  have hbad (z : QueryPhase) (a b : Fin D) :
      rawBadQuery z.1.val (T.getD a.val (T.getD 0 ⟨0,0,0,0⟩))
        (T.getD b.val (T.getD 0 ⟨0,0,0,0⟩)) ↔ badQuery c (z.1,z.2.1,z.2.2,a,b) := by
    rw [← code_decode_getD hn hcap a,← code_decode_getD hn hcap b]
    rcases z with ⟨j,u,v⟩
    fin_cases j <;> simp [rawBadQuery,badQuery,Sudoku.PairBoard.QueryMatch,c,
      Fin.ext_iff,Subtype.ext_iff]
  change _ ↔ ∃ p ∈ patterns c, testMask c p = m
  simp only [rawGuardedMasks,arithmeticMasks,guardTemplates,patterns,List.mem_append,List.mem_map,
    List.mem_flatMap,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
    List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ((⟨j,hj,rfl⟩|⟨j,hj,rfl⟩)|⟨_,⟨z,rfl⟩,a,ha,b,⟨hb,h⟩,rfl⟩)
    · exact ⟨_,Or.inl (Or.inl ⟨j,hj,rfl⟩),mask_of_pattern c _ _ _⟩
    · exact ⟨_,Or.inl (Or.inr ⟨j,hj,rfl⟩),mask_of_pattern c _ _ _⟩
    · exact ⟨_,Or.inr ⟨(z.1,z.2.1,z.2.2,⟨a,ha⟩,⟨b,hb⟩),(hbad z ⟨a,ha⟩ ⟨b,hb⟩).mp h,rfl⟩,
        mask_of_query c ⟨a,ha⟩ ⟨b,hb⟩ z⟩
  · rintro ⟨p, (⟨j,hj,rfl⟩|⟨j,hj,rfl⟩)|⟨⟨j,u,v,a,b⟩,h,rfl⟩,rfl⟩
    · exact Or.inl (Or.inl ⟨j,hj,(mask_of_pattern c (digits 5 j) (fun _ => none) (fun _ => none)).symm⟩)
    · exact Or.inl (Or.inr ⟨j,hj,(mask_of_pattern c (fun _ => none) (digits 7 j) (fun _ => none)).symm⟩)
    · let z : QueryPhase := (j,u,v)
      exact Or.inr ⟨_,⟨z,rfl⟩,a.val,a.isLt,b.val,⟨b.isLt,(hbad z a b).mpr h⟩,
        (mask_of_query c a b z).symm⟩

theorem rawGuardedMasks_length (T : LeanWang.TileSet) (D : ℕ) :
    (rawGuardedMasks T D).length ≤ 2313+72*D^2 := by
  have hA : arithmeticMasks.length = 2313 := by
    simp only [arithmeticMasks,List.length_append,List.length_map]
    decide +kernel
  have hG : guardTemplates.length = 72 := by
    simp only [guardTemplates,List.length_map,Finset.length_toList,Finset.card_univ,
      QueryPhase,Fintype.card_prod,Fintype.card_fin]
    rw [Fintype.card_congr pEquiv,Fintype.card_congr qEquiv]
    norm_num
  unfold rawGuardedMasks
  simp only [List.length_append,hA]
  have hinner (j : ℕ) (s : RawMask) :
      ((List.range D).map fun a =>
        (((List.range D).filter (fun b => decide (rawBadQuery j
            (T.getD a (T.getD 0 ⟨0,0,0,0⟩)) (T.getD b (T.getD 0 ⟨0,0,0,0⟩))))).map
          fun b => s++[some a,some b]).length).sum ≤ D^2 := by
    calc
      _ ≤ ((List.range D).map (fun _ => D)).sum := by
        apply listSumMap_le
        intro a ha
        simp only [List.length_map]
        exact (List.length_filter_le _ _).trans_eq List.length_range
      _ = _ := by simp [pow_two]
  have houter :
      (guardTemplates.map (fun (j,s) =>
        ((List.range D).flatMap fun a =>
          ((List.range D).filter (fun b => decide (rawBadQuery j
            (T.getD a (T.getD 0 ⟨0,0,0,0⟩)) (T.getD b (T.getD 0 ⟨0,0,0,0⟩))))).map
            fun b => s++[some a,some b]).length)).sum ≤ 72*D^2 := by
    calc
      _ ≤ (guardTemplates.map (fun _ => D^2)).sum := by
        apply listSumMap_le
        rintro ⟨j,s⟩ hj
        simpa only [List.length_flatMap] using hinner j s
      _ = _ := by
        change (guardTemplates.map (Function.const _ (D^2))).sum = _
        rw [List.map_const,List.sum_replicate,hG]
        rfl
  rw [List.length_flatMap]
  exact Nat.add_le_add_left houter 2313

variable {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
  (c : Code T (radixLayoutProfile r k).radices.prod)

local notation "p" => radixLayoutProfile r k

def tailRefinement : ColumnRefinement (system c) :=
  refinementWith p (packedRadix_layout p hk hr rfl) c (explicitRadixCode hk hr c)

theorem tailRefinement_width : (tailRefinement hk hr c).width = 18+2*k :=
  radixLayout_width r k

private theorem rawOrigin_eq (j : Column (tailRefinement hk hr c).system) :
    rawOrigin k j.val = ((tailRefinement hk hr c).origin j).val := by
  let j' : Fin (p).width := ⟨j.val,j.isLt⟩
  change rawOrigin k j'.val = ((p).origin j').val
  rw [origin_val]
  simp [rawOrigin,radixLayoutProfile]

private theorem expandMask_get (b : PartialTest (system c))
    (j : Column (tailRefinement hk hr c).system) :
    let S := tailRefinement hk hr c
    (testMask c b).getD (rawOrigin k j.val) none =
      if h : j ∈ (S.expand b).columns then some (b.label
        ⟨S.origin j,(Finset.mem_filter.mp h).2⟩).val else none := by
  dsimp only
  rw [rawOrigin_eq hk hr c j, testMask_get]
  by_cases h : (tailRefinement hk hr c).origin j ∈ b.columns
  · have hj : j ∈ ((tailRefinement hk hr c).expand b).columns := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    rw [dif_pos h,dif_pos hj]
  · have hj : j ∉ ((tailRefinement hk hr c).expand b).columns :=
      fun hj => h (Finset.mem_filter.mp hj).2
    rw [dif_neg h,dif_neg hj]

private theorem expandMask_label (b : PartialTest (system c))
    (j : ((tailRefinement hk hr c).expand b).columns) :
    let q := (tailRefinement hk hr c).expand b
    (q.label j).val =
      radixDigit r k j.val.val (((testMask c b).getD (rawOrigin k j.val.val) none).getD 0) := by
  dsimp only
  rw [expandMask_get hk hr c b j, dif_pos j.property,Option.getD_some]
  rfl

theorem numericalExpandedPattern_indices (b : PartialTest (system c)) :
    let q := (tailRefinement hk hr c).expand b
    expandMask r k (testMask c b) = if q.columns.Nonempty then
      List.ofFn (fun j : Fin q.columns.card => ((testEquiv q j).val.val,(q.label (testEquiv q j)).val))
    else [] := by
  let S := tailRefinement hk hr c
  let q := S.expand b
  let f (j : ℕ) := radixDigit r k j (((testMask c b).getD (rawOrigin k j) none).getD 0)
  let js := (List.range (18+2*k)).filter (fun i => ((testMask c b).getD (rawOrigin k i) none).isSome)
  have hj (j : ℕ) : j ∈ js ↔ ∃ i : q.columns, i.val.val = j := by
    unfold js
    rw [List.mem_filter]
    constructor
    · intro h
      let i : Column S.system := ⟨j,by
        change j < (tailRefinement hk hr c).width
        rw [tailRefinement_width hk hr c]
        exact List.mem_range.mp h.1⟩
      refine ⟨⟨i,?_⟩,rfl⟩
      have he := h.2
      change ((testMask c b).getD (rawOrigin k i.val) none).isSome = true at he
      rw [expandMask_get hk hr c b i] at he
      split at he
      · assumption
      · contradiction
    · rintro ⟨i,rfl⟩
      refine ⟨List.mem_range.mpr (by have := i.val.isLt; simpa [S,tailRefinement_width] using this),?_⟩
      rw [expandMask_get hk hr c b i,dif_pos i.property]
      rfl
  change expandMask r k (testMask c b) = if q.columns.Nonempty then
    List.ofFn (fun j : Fin q.columns.card => ((testEquiv q j).val.val,(q.label (testEquiv q j)).val))
    else []
  by_cases hn : q.columns.Nonempty
  · rw [if_pos hn]
    let xs := List.ofFn (fun j : Fin q.columns.card =>
      ((testEquiv q j).val.val,(q.label (testEquiv q j)).val))
    have hxsk : xs.map Prod.fst = List.ofFn (fun j => (testEquiv q j).val.val) := by
      simp only [xs,List.map_ofFn]
      rfl
    have hs₁ : js.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    have hs₂ : (xs.map Prod.fst).Pairwise (· < ·) := by
      rw [hxsk,List.pairwise_ofFn]
      intro a b hab
      exact (q.columns.orderIsoOfFin rfl).strictMono hab
    have hkeys : js = xs.map Prod.fst := by
      apply List.Subset.antisymm_of_pairwise hs₁ hs₂
      · intro i hi
        obtain ⟨j,hj'⟩ := (hj i).mp hi
        rw [hxsk]
        exact List.mem_ofFn.mpr ⟨(testEquiv q).symm j,by simpa only [Equiv.apply_symm_apply] using hj'⟩
      · intro i hi
        rw [hxsk] at hi
        obtain ⟨j,hj'⟩ := List.mem_ofFn.mp hi
        exact (hj i).mpr ⟨testEquiv q j,hj'⟩
    change js.map (fun i => (i,f i)) = xs
    rw [hkeys,hxsk]
    unfold xs
    rw [List.map_ofFn]
    congr 1
    funext j
    exact Prod.ext rfl (expandMask_label hk hr c b (testEquiv q j)).symm
  · rw [if_neg hn]
    have he : js = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j h
      obtain ⟨i,_⟩ := (hj j).mp h
      exact hn ⟨i.val,i.property⟩
    change js.map (fun i => (i,f i)) = []
    simp [he]

theorem numericalExpandedPattern (E : EncodingParameters (tailRefinement hk hr c).system)
    (rs : GuardedRows) (hm : GuardedRowsMatch E rs)
    (b : PartialTest (system c)) :
    guardedDecodedFamily E (guardedCycle rs (expandMask r k (testMask c b))) =
      partialTiles E ((tailRefinement hk hr c).expand b) := by
  let q := (tailRefinement hk hr c).expand b
  rw [numericalExpandedPattern_indices hk hr c b]
  change _ = partialTiles E q
  by_cases hn : q.columns.Nonempty
  · letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr hn).ne'⟩
    rw [if_pos hn,partialTiles,dif_pos hn]
    let cy := projectedCycle (testEmbedding q)
    let labs := partialLabels (testEmbedding q) (fun j => q.label (testEquiv q j))
    have he : vectorForCycle cy labs = List.ofFn (fun j : Fin q.columns.card =>
        ((testEquiv q j).val.val,(q.label (testEquiv q j)).val)) := by
      apply List.ofFn_inj.mpr
      funext j
      let out (v : Fin q.columns.card) :=
        ((testEquiv q v).val.val,(q.label (testEquiv q v)).val)
      change out ((ZMod.finEquiv q.columns.card).symm ((ZMod.finEquiv q.columns.card) j)) = out j
      exact congrArg out ((ZMod.finEquiv q.columns.card).symm_apply_apply j)
    rw [← he]
    exact numericalCycle_correct hm cy labs
  · rw [if_neg hn,partialTiles,dif_neg hn]
    simp [guardedCycle,guardedDecodedFamily]

def seedTemplateSet (t : Fin 2) (i v : ℕ) : Prop :=
  if i < 9 then ∃ u : Units5, seedDigit 5 t u.val ∧ (pEquiv u).val=v
  else if i < 18 then ∃ u : Units7, seedDigit 7 t u.val ∧ (qEquiv u).val=v
  else True

private theorem originalSeed_matches {D : ℕ} (c : Code T D)
    (t : Fin 2) (i : Column (system c)) (v : Letter (system c) i) :
    LetterSeedSet (system c) t i v ↔ seedTemplateSet t i.val v.val := by
  obtain ⟨r,rfl⟩ := roleEquiv.surjective i
  unfold LetterSeedSet packedPatternCorrectAlphabet GuardedCompiler.alphabet AlphabetFamily.seed
  dsimp only []
  simp only [Equiv.symm_apply_apply]
  rcases r with a|a|a
  · change _ ↔ seedTemplateSet t a.val v.val
    simp only [seedTemplateSet,if_pos a.isLt]
  · change _ ↔ seedTemplateSet t (9+a.val) v.val
    simp only [seedTemplateSet,if_neg (by omega : ¬ 9+a.val < 9),if_pos (by omega : 9+a.val < 18)]
  · change True ↔ seedTemplateSet t (9+(9+a.val)) v.val
    simp only [seedTemplateSet,if_neg (by omega : ¬ 9+(9+a.val)<9),
      if_neg (by omega : ¬ 9+(9+a.val)<18)]

theorem tailSeedTest_matches (t : Fin 2) (i : Column (tailRefinement hk hr c).system)
    (v : Letter (tailRefinement hk hr c).system i) :
    LetterSeedSet (tailRefinement hk hr c).system t i v ↔ seedTemplateSet t i.val v.val := by
  let i' : Fin (p).width := ⟨i.val,i.isLt⟩
  let j := (p).origin i'
  let digits := oneDigit p (packedRadix_layout p hk hr rfl) i' v
  let u := (explicitRadixCode hk hr c j).symm digits
  have hj := origin_val p i'
  change (if j.val < 18 then LetterSeedSet (system c) t j u else True) ↔ _
  by_cases hi : i'.val < 18
  · have hj' : j.val = i.val := by simpa only [if_pos hi] using hj
    rw [if_pos (show j.val < 18 from hj'.trans_lt hi),originalSeed_matches c]
    have hv : u.val = v.val := by
      let a : (p).Fibre j := ⟨i',rfl⟩
      have he : ((explicitRadixCode hk hr c j) u a).val = (digits a).val :=
        congrArg Fin.val (congrFun ((explicitRadixCode hk hr c j).apply_symm_apply digits) a)
      rw [explicitRadixCode_val hk hr c j u a] at he
      change radixDigit r k i'.val u.val = _ at he
      have hd : digits a = v := by
        unfold digits oneDigit
        split
        · rfl
        · rename_i he
          exact (he rfl).elim
      rw [hd] at he
      simpa only [radixDigit,if_pos hi] using he
    exact iff_of_eq (congrArg₂ (seedTemplateSet t) hj' hv)
  · have hj' : ¬ j.val < 18 := by rw [hj,if_neg hi]; split <;> omega
    rw [if_neg hj']
    have hi0 : ¬ i.val < 18 := hi
    simp only [seedTemplateSet,if_neg (show ¬ i.val < 9 by omega),if_neg hi0]

include hk in
theorem seedTest_template (t : Fin 2) {i v : ℕ}
    (hi : i < 18+2*k) (hv : v < (radixLayoutProfile r k).arity i) :
    (t.val,i,v) ∈ seedTestTemplates ↔ ¬ seedTemplateSet t i v := by
  have hv' := hv
  rw [radixLayout_arity hk (by simpa using hi)] at hv'
  simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
    Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq]
  by_cases h : i < 9
  · simp only [seedTemplateSet,if_pos h] at ⊢
    have hv4 : v < 4 := by simpa only [if_pos h] using hv'
    constructor
    · rintro ⟨⟨t',b⟩,h'|h'⟩
      · rcases h' with ⟨u,hu,ht,hb,hv⟩
        have he : t'=t := Fin.ext ht
        subst t'
        rintro ⟨u',hu',hv'⟩
        refine hu ?_
        have he : u'=u := pEquiv.injective (Fin.ext (hv'.trans hv.symm))
        rwa [←he]
      · rcases h' with ⟨u,hu,ht,hb,hv⟩
        omega
    · intro hp
      let u := pEquiv.symm ⟨v,hv4⟩
      have hu : (pEquiv u).val=v := by simp [u]
      exact ⟨(t,⟨i,h⟩),Or.inl ⟨u,fun h' => hp ⟨u,h',hu⟩,rfl,rfl,hu⟩⟩
  · by_cases h' : i < 18
    · simp only [seedTemplateSet,if_neg h,if_pos h'] at ⊢
      have hv6 : v < 6 := by simpa only [if_neg h,if_pos h'] using hv'
      constructor
      · rintro ⟨⟨t',b⟩,ha|hb⟩
        · rcases ha with ⟨u,hu,ht,hi,hv⟩
          omega
        · rcases hb with ⟨u,hu,ht,hi,hv⟩
          have he : t'=t := Fin.ext ht
          subst t'
          rintro ⟨u',hu',hv'⟩
          refine hu ?_
          have he : u'=u := qEquiv.injective (Fin.ext (hv'.trans hv.symm))
          rwa [←he]
      · intro hp
        let u := qEquiv.symm ⟨v,hv6⟩
        have hu : (qEquiv u).val=v := by simp [u]
        exact ⟨(t,⟨i-9,by omega⟩),Or.inr ⟨u,fun h' => hp ⟨u,h',hu⟩,rfl,by change 9+(i-9)=i; omega,hu⟩⟩
    · simp only [seedTemplateSet,if_neg h,if_neg h',not_true_eq_false,iff_false]
      rintro ⟨⟨t',b⟩,ha|hb⟩
      · rcases ha with ⟨u,hu,ht,hi,hv⟩
        omega
      · rcases hb with ⟨u,hu,ht,hi,hv⟩
        omega

private theorem seedVector_eq (t : Fin 2) (i : Column (tailRefinement hk hr c).system) (v : Letter _ i) :
    vectorForCycle (seedCycle t i) (seedCycleLabels t i v) =
      [(18+2*k+t.val,0),(i.val,v.val)] := by
  unfold vectorForCycle
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  change [((tailRefinement hk hr c).width+t.val,0),(i.val,v.val)] = _
  rw [tailRefinement_width]

theorem numericalSeedTests_correct (E : EncodingParameters (tailRefinement hk hr c).system)
    (rs : GuardedRows) (hm : GuardedRowsMatch E rs) :
    guardedDecodedFamily E ((tailSeedTests k).flatMap (guardedCycle rs)) =
      seedConstraintTiles E := by
  ext F
  simp only [seedConstraintTiles, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_guardedDecodedFamily, List.mem_flatMap, tailSeedTests, List.mem_map]
  constructor
  · rintro ⟨xs,⟨_,⟨⟨t,i,v⟩,h,rfl⟩,hxs⟩,rfl⟩
    have ht : t < 2 := by
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at h
      rcases h with ⟨⟨u,b⟩,_,⟨a,_,h,_⟩ | ⟨a,_,h,_⟩⟩ <;> omega
    have hi : i < 18+2*k := by
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at h
      rcases h with ⟨⟨u,b⟩,_,⟨a,_,_,h,_⟩ | ⟨a,_,_,h,_⟩⟩ <;> omega
    have hv : v < (radixLayoutProfile r k).arity i := by
      rw [radixLayout_arity hk (by simpa using hi)]
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at h
      rcases h with ⟨⟨u,b⟩,_,⟨a,_,_,rfl,rfl⟩ | ⟨a,_,_,rfl,rfl⟩⟩
      · rw [if_pos b.isLt]; exact (pEquiv a).isLt
      · rw [if_neg (by omega),if_pos (by omega)]; exact (qEquiv a).isLt
    let t' : Fin 2 := ⟨t,ht⟩
    let i' : Column (tailRefinement hk hr c).system := ⟨i,by change i < (tailRefinement hk hr c).width; rwa [tailRefinement_width]⟩
    let v' : Letter (tailRefinement hk hr c).system i' := ⟨v,hv⟩
    refine ⟨⟨t',i',v'⟩, ?_, ?_⟩
    · rw [tailSeedTest_matches hk hr c]
      exact (seedTest_template hk t' hi hv).mp h
    · rw [← numericalCycle_correct hm, seedVector_eq hk hr c]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs,hxs,rfl⟩)
  · rintro ⟨⟨t,i,v⟩,h,hF⟩
    have hi : i.val < 18+2*k := by simpa only [tailRefinement_width] using i.isLt
    have hv : v.val < (radixLayoutProfile r k).arity i.val := v.isLt
    have htemp := (seedTest_template hk t hi hv).mpr (fun hp => h ((tailSeedTest_matches hk hr c _ _ _).mpr hp))
    rw [← numericalCycle_correct hm, seedVector_eq hk hr c] at hF
    obtain ⟨xs,hxs,hFx⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact ⟨xs,⟨_,⟨_,htemp,rfl⟩,hxs⟩,hFx⟩

theorem numericalExpandedTests_correct (hn : 0 < T.length) (hcap : T.length ≤ (radixLayoutProfile r k).radices.prod)
    (E : EncodingParameters (tailRefinement hk hr (code T ((radixLayoutProfile r k).radices.prod) hn hcap)).system)
    (rs : GuardedRows) (hm : GuardedRowsMatch E rs) :
    guardedDecodedFamily E (((rawGuardedMasks T ((radixLayoutProfile r k).radices.prod)).map (expandMask r k)).flatMap (guardedCycle rs)) =
      (List.flatMap (fun test => (partialTiles E test).toList)
        (GuardedCompiler.refinedPatterns (code T ((radixLayoutProfile r k).radices.prod) hn hcap)
          (tailRefinement hk hr (code T ((radixLayoutProfile r k).radices.prod) hn hcap)))).toFinset := by
  let c := code T ((radixLayoutProfile r k).radices.prod) hn hcap
  ext F
  simp only [mem_guardedDecodedFamily,List.mem_flatMap,List.mem_map,List.mem_toFinset,
    Finset.mem_toList,GuardedCompiler.refinedPatterns]
  constructor
  · rintro ⟨xs,⟨_,⟨m,hm',rfl⟩,hxs⟩,rfl⟩
    obtain ⟨test,hp,rfl⟩ := (rawMask_membership hn hcap m).mp hm'
    refine ⟨_,⟨test,hp,rfl⟩,?_⟩
    rw [← numericalExpandedPattern hk hr c E rs hm test]
    exact (mem_guardedDecodedFamily _ _).mpr ⟨xs,hxs,rfl⟩
  · rintro ⟨_,⟨test,hp,rfl⟩,hF⟩
    rw [← numericalExpandedPattern hk hr c E rs hm test] at hF
    obtain ⟨xs,hxs,rfl⟩ := (mem_guardedDecodedFamily _ _).mp hF
    exact ⟨xs,⟨_,⟨_,(rawMask_membership hn hcap _).mpr ⟨test,hp,rfl⟩,rfl⟩,hxs⟩,rfl⟩


end
end TranslationTiling.FiniteCompiler.Packed
