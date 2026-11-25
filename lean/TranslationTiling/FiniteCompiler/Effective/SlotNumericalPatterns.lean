import TranslationTiling.FiniteCompiler.Effective.SlotNumericalGuards
import TranslationTiling.FiniteCompiler.Effective.SlotGuardMasks

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Compiler Compiler.Effective SlotWords
set_option autoImplicit false
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical
noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

local instance numericalPatternsFrame : SeedFrame := compactSeedFrame

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance numericalPatternsAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

private theorem expandedArith_get (p : PartialTest (system c)) (i : Fin 18) :
    (testMask c p).getD i.val none =
      if h : arithmeticColumn i ∈ p.columns then
        some (arithmeticLetterEquiv c i (p.label ⟨arithmeticColumn i,h⟩)).val
      else none := by
  rw [show i.val = (arithmeticColumn i).val from rfl,testMask_get]
  split <;> rfl

private theorem expandedWang_get (p : PartialTest (system c)) (g : Bool)
    (d : Fin k) (i : Fin m) (j : Fin 3) :
    wangWordLabel k m w (testMask c p) g d i = some j.val ↔
      ∃ (hg : wangColumn g ∈ p.columns), SlotWords.Uses (patternDigit c p ⟨g,hg⟩ d) i j := by
  unfold wangWordLabel
  rw [show (if g then 18 else 19) = (wangColumn g).val by cases g <;> rfl, testMask_get]
  by_cases hg : wangColumn g ∈ p.columns
  · rw [dite_eq_left hg]
    simp only [Option.bind_some]
    have hsupport :
        (∃ h : wangColumn g ∈ p.columns, SlotWords.Uses (patternDigit c p ⟨g,h⟩ d) i j) ↔
          SlotWords.Uses (patternDigit c p ⟨g,hg⟩ d) i j :=
      ⟨fun ⟨_,h⟩ => h,fun h => ⟨hg,h⟩⟩
    rw [hsupport]
    let n := (p.label ⟨wangColumn g,hg⟩).val
    let a : Fin ((m.choose w * 3^w)^k) := ⟨n,by
      have h := (p.label ⟨wangColumn g,hg⟩).isLt
      cases g <;> exact h⟩
    change (if numericalWordDigit m w (n / slotRadix m w ^ d.val % slotRadix m w) i.val = 0 then
      none else some (numericalWordDigit m w (n / slotRadix m w ^ d.val % slotRadix m w) i.val - 1)) = some j.val
       ↔ SlotWords.Uses (patternDigit c p ⟨g,hg⟩ d) i j
    change (if numericalWordDigit m w (a.val / (m.choose w * 3^w)^d.val % (m.choose w * 3^w)) i.val = 0 then
      none else some (numericalWordDigit m w (a.val / (m.choose w * 3^w)^d.val % (m.choose w * 3^w)) i.val - 1)) =
        some j.val ↔ SlotWords.Uses (SlotWords.rankedWordTuple k m w a d) i j
    rw [SlotWords.rankedWordTuple_coordinate,← SlotWords.numericalWordDigit_uses]
    let v := numericalWordDigit m w (a.val / (m.choose w * 3^w)^d.val % (m.choose w * 3^w)) i.val
    change (if v = 0 then none else some (v-1)) = some j.val ↔ v = j.val+1
    split
    · rename_i h
      simp [h]
    · rename_i h
      rw [Option.some.injEq]
      omega
  · rw [dite_eq_right hg]
    simp [hg]
private theorem pattern_numbering_at (p : PartialTest (system c)) (g : Bool) (d : Fin k)
    (i : Fin m) (v : ℕ) :
    wangWordLabel k m w (testMask c p) g d i = some v ↔
      ∃ (hg : wangColumn g ∈ p.columns) (hi : i ∈ (patternDigit c p ⟨g,hg⟩ d).1.val),
        ((patternDigit c p ⟨g,hg⟩ d).2 ⟨i,hi⟩).val = v := by
  constructor
  · intro h
    have hv : v < 3 := by
      unfold wangWordLabel at h
      cases he : (testMask c p).getD (if g then 18 else 19) none with
      | none => rw [he] at h; cases h
      | some a =>
        rw [he] at h
        simp only [Option.bind_some] at h
        have hnum := SlotWords.numericalWordDigit_lt m w
          (a / slotRadix m w ^ d.val % slotRadix m w) i.val
        split at h
        · cases h
        · simp only [Option.some.injEq] at h
          omega
    let j : Fin 3 := ⟨v,hv⟩
    obtain ⟨hg,hi,he⟩ := (expandedWang_get c p g d i j).mp h
    exact ⟨hg,hi,congrArg Fin.val he⟩
  · rintro ⟨hg,hi,rfl⟩
    exact (expandedWang_get c p g d i _).mpr ⟨hg,hi,rfl⟩

private theorem assignment_membership (p : PartialTest (system c)) (z : ℕ × ℕ) :
    z ∈ expandSlotMask k m w (testMask c p) ↔
      ∃ i : Support c p,
        (slotRowNumber (patternRow c p i), rowLabelNumber (patternRow c p i) (patternLabel c p i)) = z := by
  rcases z with ⟨r,v⟩
  simp only [expandSlotMask,indexedLabels,List.mem_append,List.mem_flatMap,List.mem_filterMap,List.mem_range]
  constructor
  · rintro (⟨i,hi,he⟩ | ⟨g,_,d,hd,i,hi,he⟩)
    · let j : Fin 18 := ⟨i,hi⟩
      change (Option.map (i,·) ((testMask c p).getD j.val none)) = _ at he
      rw [expandedArith_get c p j] at he
      split at he
      · rename_i hj
        exact ⟨.inl ⟨j,hj⟩,Option.some.inj he⟩
      · cases he
    · let e : Fin k := ⟨d,hd⟩
      let j : Fin m := ⟨i,hi⟩
      have hv : wangWordLabel k m w (testMask c p) g e j = some v := by
        cases hh : wangWordLabel k m w (testMask c p) g e j with
        | none =>
          change (wangWordLabel k m w (testMask c p) g e j).map _ = _ at he
          rw [hh] at he
          cases he
        | some a =>
          change (wangWordLabel k m w (testMask c p) g e j).map _ = _ at he
          rw [hh] at he
          exact congrArg some (congrArg Prod.snd (Option.some.inj he))
      obtain ⟨hg,hj,hv'⟩ := (pattern_numbering_at c p g e j v).mp hv
      change (wangWordLabel k m w (testMask c p) g e j).map _ = _ at he
      rw [hv] at he
      have hrow : 20+wangCode k m g d i = r :=
        congrArg Prod.fst (Option.some.inj (show some (20+wangCode k m g d i,v) = some (r,v) from he))
      exact ⟨.inr ⟨⟨g,hg⟩,e,⟨j,hj⟩⟩,Prod.ext hrow hv'⟩
  · rintro ⟨i,h⟩
    have hr := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    dsimp only at hr hv
    subst r
    subst v
    rcases i with i | ⟨g,d,i⟩
    · refine Or.inl ⟨i.val.val,i.val.isLt,?_⟩
      rw [expandedArith_get c p i.val,dite_eq_left i.property]
      rfl
    · refine Or.inr ⟨g.val,by cases g.val <;> simp,d.val,d.isLt,i.val.val,i.val.isLt,?_⟩
      have he := (pattern_numbering_at c p g.val d i.val
        ((patternDigit c p g d).2 i).val).mpr ⟨g.property,i.property,rfl⟩
      rw [he]
      rfl
private theorem slotKey_inj {k m : ℕ} {g g' : Bool} {d d' : Fin k} {i i' : Fin m}
    (h : wangCode k m g d i = wangCode k m g' d' i') : g = g' ∧ d = d' ∧ i = i' := by
  have he : (wangRow (g,d,i) : SlotRow k m) = wangRow (g',d',i') := by
    apply (slotRowEquiv k m).injective
    apply Fin.ext
    simp only [slotRowEquiv_val,slotRowNumber,wangRow]
    exact congrArg (20+·) h
  exact Prod.mk.inj (Sum.inl.inj (Sum.inr.inj he)) |>.imp_right Prod.mk.inj

private theorem onlyCodes {m : ℕ} (f : ℕ → ℕ) (p : ℕ → Option ℕ) :
    (((List.range m).filterMap fun i => (p i).map (f i,·)).map Prod.fst) =
      ((List.range m).filter fun i => (p i).isSome).map f := by
  simp only [List.map_filterMap,Function.comp_def,Option.map_map]
  induction List.range m with
  | nil => rfl
  | cons i is ih =>
    cases h : p i <;> simp [h,ih]

theorem expandSlotMask_nodup (k m w : ℕ) (p : RawMask) :
    ((expandSlotMask k m w p).map Prod.fst).Nodup := by
  simp only [expandSlotMask,indexedLabels,List.map_append,List.map_flatMap,onlyCodes]
  have hx (g : Bool) (d : ℕ) (x : ℕ) :
      x ∈ (((List.range m).filter fun i => (wangWordLabel k m w p g d i).isSome).map
        fun i => 20+wangCode k m g d i) → ∃ i : Fin m, x = 20+wangCode k m g d i := by
    rintro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact ⟨⟨i,List.mem_range.mp (List.mem_filter.mp hi).1⟩,rfl⟩
  apply List.Nodup.append
  · simpa using (List.nodup_range : (List.range 18).Nodup).filter (fun i => (p.getD i none).isSome)
  · apply List.nodup_flatMap.mpr
    constructor
    · intro g _
      apply List.nodup_flatMap.mpr
      constructor
      · intro d hd
        have hd' := List.mem_range.mp hd
        apply List.Nodup.map_on
        · intro i hi j hj he
          let a : Fin m := ⟨i,List.mem_range.mp (List.mem_filter.mp hi).1⟩
          let b : Fin m := ⟨j,List.mem_range.mp (List.mem_filter.mp hj).1⟩
          have hh : wangCode k m g (⟨d,hd'⟩ : Fin k) a = wangCode k m g (⟨d,hd'⟩ : Fin k) b :=
            Nat.add_left_cancel he
          exact congrArg Fin.val (slotKey_inj hh).2.2
        · exact List.nodup_range.filter _
      · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range : (List.range k).Nodup)
        intro a b ha hb hab
        rw [Function.onFun,List.disjoint_left]
        intro x hx₁ hx₂
        obtain ⟨i,hi⟩ := hx g a x hx₁
        obtain ⟨j,hj⟩ := hx g b x hx₂
        let d : Fin k := ⟨a,List.mem_range.mp ha⟩
        let e : Fin k := ⟨b,List.mem_range.mp hb⟩
        have he : wangCode k m g d i = wangCode k m g e j := Nat.add_left_cancel (hi.symm.trans hj)
        exact hab (congrArg Fin.val (slotKey_inj he).2.1)
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) .nil)
      intro g hg
      have he : g = true := by simpa using hg
      subst g
      rw [Function.onFun,List.disjoint_left]
      intro x hx₁ hx₂
      obtain ⟨d,hd,hx₁⟩ := List.mem_flatMap.mp hx₁
      obtain ⟨e,he,hx₂⟩ := List.mem_flatMap.mp hx₂
      obtain ⟨i,hi⟩ := hx false d x hx₁
      obtain ⟨j,hj⟩ := hx true e x hx₂
      have hf : wangCode k m false (⟨d,List.mem_range.mp hd⟩ : Fin k) i =
          wangCode k m true (⟨e,List.mem_range.mp he⟩ : Fin k) j :=
        Nat.add_left_cancel (hi.symm.trans hj)
      cases (slotKey_inj hf).1
  · rw [List.disjoint_left]
    intro x ha hb
    obtain ⟨g,_,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨d,_,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i,hi⟩ := hx g d x hb
    have ha' : x < 18 := by
      obtain ⟨i,him,hix⟩ := List.mem_map.mp ha
      have hlt : i < 18 := List.mem_range.mp (List.mem_filter.mp him).1
      exact (show i = x from hix) ▸ hlt
    omega
theorem numericalGuardFor_nonempty {N : ℕ} (p : PartialTest (system c)) (G : CyclicTile)
    (hG : G ∈ numericalSlotCycle N k m (expandSlotMask k m w (testMask c p))) :
    p.columns.Nonempty := by
  let xs := expandSlotMask k m w (testMask c p)
  have hx : xs ≠ [] := by
    intro he
    change G ∈ numericalSlotCycle N k m xs at hG
    simp [he,numericalSlotCycle] at hG
  obtain ⟨x,hx'⟩ : ∃ x, x ∈ xs := by
    cases he : xs with
    | nil => exact (hx he).elim
    | cons x xs => exact ⟨x,List.mem_cons_self ..⟩
  obtain ⟨i,_⟩ := (assignment_membership c p x).mp hx'
  rcases i with i | ⟨g,d,i⟩
  · exact ⟨_,i.property⟩
  · exact ⟨_,g.property⟩

variable (s : SlotParameters k m)
local instance numericalPatternsDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

theorem numericalPatternFor_spec {W : Type} [Nonempty W]
    (hs : s.prime = rankedSlotPrime k m) (xs : GuardedAssignments)
    (rows : W ↪ SlotRow k m) (label : ∀ i, RowLabel (rows i))
    (hn : (xs.map Prod.fst).Nodup)
    (hm : ∀ p, p ∈ xs ↔ ∃ i, (slotRowNumber (rows i),rowLabelNumber (rows i) (label i)) = p) :
    ∃ G : CyclicTile, numericalSlotCycle (order s.layout) k m xs = [G] ∧
      let F := G.toFinset.image (decodePoint s.layout)
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ o, s.cycleDependencies o → (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
        ∀ x, ∃ w, ¬ s.labelActive o x (rows w) (label w)) := by
  obtain ⟨ht,e,hx⟩ := exists_numberedCycle xs rows label hn hm
  let cycle := e.toEmbedding.trans rows
  let a := assignLabels rows label
  let G := cycleCodes (order s.layout) (numericalSlotCycleRows k m xs)
  have hnum : G.toFinset.image (decodePoint s.layout) = s.rowCycleMask cycle a := by
    calc
      _ = (cycleCodes (order s.layout) (numericalSlotCycleRows k m
          (numberedCycleAssignments cycle a))).toFinset.image (decodePoint s.layout) :=
        congrArg (fun u => (cycleCodes (order s.layout) (numericalSlotCycleRows k m u)).toFinset.image
          (decodePoint s.layout)) hx
      _ = _ := s.numericalSlotCycle_correct cycle a hs
  refine ⟨G,by simp [numericalSlotCycle,ht.ne,G],?_⟩
  rw [hnum]
  refine ⟨fun x => @rowCycleMask_vertical k m s (s.finiteFactor) xs.length ht cycle a x,
    @rowCycleMask_satisfiable k m s (s.finiteFactor) xs.length ht cycle a,?_⟩
  exact s.pattern_cycle_spec e rows label

theorem numericalGuardFor_spec (hs : s.prime = rankedSlotPrime k m)
    (p : PartialTest (system c)) (hp : p ∈ patterns c) :
    ∃ G : CyclicTile,
      numericalSlotCycle (order s.layout) k m (expandSlotMask k m w (testMask c p)) = [G] ∧
      let F := G.toFinset.image (decodePoint s.layout)
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ o, s.cycleDependencies o →
        (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
          ∀ x, ¬ ∀ i (hi : columnIndex i ∈ p.columns),
            s.letterActive c o x i (p.label ⟨columnIndex i,hi⟩)) := by
  have := support_nonempty c p hp
  let rows : Support c p ↪ SlotRow k m := ⟨patternRow c p,patternRow_inj c p⟩
  obtain ⟨G,hG,hv,hmass,he⟩ := s.numericalPatternFor_spec hs _ rows (patternLabel c p)
    (expandSlotMask_nodup k m w _) (assignment_membership c p)
  refine ⟨G,hG,hv,hmass,fun o ho => ?_⟩
  rw [he o ho]
  simp only [← s.patternActive_iff c p o,not_forall]
  rfl
def numericalSeedAssignments (t : Fin 2) (i : Fin 18)
    (a : Letter (system c) (arithmeticColumn i)) : GuardedAssignments :=
  [(18+t.val,0),(i.val,a.val)]

theorem numericalSeedFor_spec (hs : s.prime = rankedSlotPrime k m)
    (t : Fin 2) (i : Fin 18) (a : Letter (system c) (arithmeticColumn i)) :
    ∃ G : CyclicTile, numericalSlotCycle (order s.layout) k m (numericalSeedAssignments c t i a) = [G] ∧
      let F := G.toFinset.image (decodePoint s.layout)
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ o, s.cycleDependencies o →
        (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
          ∀ x, ¬ (s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t) ∧
            s.letterActive c o x (.inl i) a)) := by
  let rows : Bool ↪ SlotRow k m := ⟨seedRow t i,seedRow_inj t i⟩
  have hi : i.val < 18 := i.isLt
  have hn : ((numericalSeedAssignments c t i a).map Prod.fst).Nodup := by
    simp [numericalSeedAssignments,show 18+t.val ≠ i.val by omega]
  have he (b : Bool) :
      (slotRowNumber (rows b),rowLabelNumber (rows b) (seedTestLabel c t i a b)) =
        if b then (18+t.val,0) else (i.val,a.val) := by
    cases b
    · rfl
    · change ((fourValueSeedRow 0 t).val,0) = (18+t.val,0)
      rw [fourValueSeedRow_val]
  have hm (p : ℕ × ℕ) : p ∈ numericalSeedAssignments c t i a ↔
      ∃ b, (slotRowNumber (rows b),rowLabelNumber (rows b) (seedTestLabel c t i a b)) = p := by
    simp only [numericalSeedAssignments,List.mem_cons,List.not_mem_nil,or_false,he]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨true,rfl⟩
      · exact ⟨false,rfl⟩
    · rintro ⟨b,h⟩
      cases b
      · exact Or.inr h.symm
      · exact Or.inl h.symm
  obtain ⟨G,hG,hv,hmass,he⟩ := s.numericalPatternFor_spec hs _ rows (seedTestLabel c t i a) hn hm
  refine ⟨G,hG,hv,hmass,fun o ho => ?_⟩
  rw [he o ho]
  constructor
  · intro h x hx
    obtain ⟨b,hb⟩ := h x
    cases b
    · exact hb hx.2
    · exact hb hx.1
  · intro h x
    by_cases hseed : s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t)
    · exact ⟨false,fun ha => h x ⟨hseed,ha⟩⟩
    · exact ⟨true,hseed⟩

private theorem arithmeticSeedTemplate (t : Fin 2) (i : Fin 18)
    (a : Letter (system c) (arithmeticColumn i)) :
    (t.val,i.val,a.val) ∈ seedTestTemplates ↔ ¬ LetterSeedSet (system c) t (arithmeticColumn i) a := by
  have hx : (radixLayoutProfile 3 1).arity i.val =
      (rowDigits (fourValueRows 0) (arithmeticRow i)).length :=
    (by decide +kernel : ∀ i : Fin 18, (radixLayoutProfile 3 1).arity i.val =
      (rowDigits (fourValueRows 0) (arithmeticRow i)).length) i
  rw [seedTest_template (k := 1) (r := 3) (by decide) t (by have := i.isLt; omega)
      (by rw [hx,arithmetic_arity]; exact a.isLt),originalSeed_matches c]
  rfl

private theorem seedTemplateValid {t i v : ℕ} (h : (t,i,v) ∈ seedTestTemplates) :
    t < 2 ∧ ∃ i' : Fin 18, i'.val = i ∧
      v < arity ((slotRadix m w)^k) (arithmeticColumn i') := by
  simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
    Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq] at h
  obtain ⟨⟨j,b⟩,h⟩ := h
  rcases h with ⟨u,_,rfl,rfl,rfl⟩ | ⟨u,_,rfl,rfl,rfl⟩
  · refine ⟨j.isLt,⟨b.val,by have := b.isLt; omega⟩,rfl,?_⟩
    change (pEquiv u).val < arity _ (atP b)
    simpa only [arity_p] using (pEquiv u).isLt
  · refine ⟨j.isLt,⟨9+b.val,by have := b.isLt; omega⟩,rfl,?_⟩
    change (qEquiv u).val < arity _ (atQ b)
    simpa only [arity_q] using (qEquiv u).isLt

theorem numericalSeeds_lists (xs : GuardedAssignments) :
    xs ∈ tailSeedTests 0 ↔
      ∃ (t : Fin 2) (i : Fin 18) (a : Letter (system c) (arithmeticColumn i)),
        ¬ LetterSeedSet (system c) t (arithmeticColumn i) a ∧
        numericalSeedAssignments c t i a = xs := by
  simp only [tailSeedTests,List.mem_map]
  constructor
  · rintro ⟨⟨t,i,v⟩,h,rfl⟩
    obtain ⟨ht,j,rfl,hv⟩ := seedTemplateValid (m := m) (w := w) (k := k) h
    exact ⟨⟨t,ht⟩,j,⟨v,hv⟩,(arithmeticSeedTemplate c ⟨t,ht⟩ j ⟨v,hv⟩).mp h,rfl⟩
  · rintro ⟨t,i,a,h,rfl⟩
    exact ⟨(t.val,i.val,a.val),(arithmeticSeedTemplate c t i a).mpr h,rfl⟩

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
