import TranslationTiling.FiniteCompiler.PartialTests
import TranslationTiling.FiniteCompiler.GuardedSeeds
import TranslationTiling.SudokuArithmetic.PartialWordSoundness
import TranslationTiling.SudokuArithmetic.QueryGuards

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open PairSmall
open Sudoku.PairBoard (Guard QueryMatch GuardedRule querySlope)
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000

local instance : SeedFrame := compactSeedFrame
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance : AlphabetFamily (system code) := alphabet code

abbrev Units5 := (ZMod 5)ˣ
abbrev Units7 := (ZMod 7)ˣ
abbrev PVec := Fin 9 → Option Units5
abbrev QVec := Fin 9 → Option Units7
abbrev CVec (d : ℕ) := Fin 2 → Option (Fin d)

def rawSelection (P : PVec) (Q : QVec) (C : CVec d) (n : Fin 20) : Option ℕ :=
  match roleEquiv.symm n with
  | .inl i => (P i).map fun v => (pEquiv v).val
  | .inr (.inl i) => (Q i).map fun v => (qEquiv v).val
  | .inr (.inr i) => (C i).map Fin.val

def selection (P : PVec) (Q : QVec) (C : CVec d) (n : Column (system code)) :
    Option (Letter (system code) n) :=
  (rawSelection P Q C n).bind fun k =>
    if hk : k<arity d n then some ⟨k,hk⟩ else none

theorem selection_some (P : PVec) (Q : QVec) (C : CVec d) (n : Column (system code))
    (v : Letter (system code) n) :
    selection code P Q C n=some v ↔ rawSelection P Q C n=some v.val := by
  unfold selection
  cases rawSelection P Q C n with
  | none => simp
  | some k =>
    by_cases hk : k<arity d n
    · simp only [Option.bind_some,dif_pos hk,Option.some.injEq]
      exact ⟨congrArg Fin.val,fun h => Fin.ext h⟩
    · simp only [Option.bind_some,dif_neg hk,reduceCtorEq,false_iff,Option.some.injEq]
      rintro rfl
      exact hk v.isLt

def pattern (P : PVec) (Q : QVec) (C : CVec d) : PartialTest (system code) :=
  PartialTest.select (selection code P Q C)

def wordP (w : Word (system code)) (i : Fin 9) : Units5 :=
  readP code (fun n _ => w n) i 0

def wordQ (w : Word (system code)) (i : Fin 9) : Units7 :=
  readQ code (fun n _ => w n) i 0

def wordC (w : Word (system code)) (i : Fin 2) : Fin d :=
  ⟨(w (atC i)).val,by
    have h : (w (atC i)).val<arity d (atC i) := (w (atC i)).isLt
    simpa only [arity_c] using h⟩

def Satisfies {α β : Type} (f : α → β) (p : α → Option β) : Prop :=
  ∀ i v, p i=some v → f i=v

private theorem rawP (P : PVec) (Q : QVec) (C : CVec d) (i : Fin 9) :
    rawSelection P Q C (atP i)=(P i).map (fun v => (pEquiv v).val) := by
  simp [rawSelection,atP]

private theorem rawQ (P : PVec) (Q : QVec) (C : CVec d) (i : Fin 9) :
    rawSelection P Q C (atQ i)=(Q i).map (fun v => (qEquiv v).val) := by
  simp [rawSelection,atQ]

private theorem rawC (P : PVec) (Q : QVec) (C : CVec d) (i : Fin 2) :
    rawSelection P Q C (atC i)=(C i).map Fin.val := by
  simp [rawSelection,atC]

private theorem letterP_lt (i : Fin 9) (u : Units5) : (pEquiv u).val < arity d (atP i) := by
  rw [arity_p]
  exact (pEquiv u).isLt

private theorem letterQ_lt (i : Fin 9) (u : Units7) : (qEquiv u).val < arity d (atQ i) := by
  rw [arity_q]
  exact (qEquiv u).isLt

private theorem letterC_lt (i : Fin 2) (u : Fin d) : u.val < arity d (atC i) := by
  rw [arity_c]
  exact u.isLt

theorem matches_pattern (P : PVec) (Q : QVec) (C : CVec d) (w : Word (system code)) :
    (pattern code P Q C).Matches w ↔
      Satisfies (wordP code w) P ∧ Satisfies (wordQ code w) Q ∧ Satisfies (wordC code w) C := by
  rw [pattern,PartialTest.matches_select]
  simp_rw [selection_some]
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i v hv
      have he := h (atP i) ⟨(pEquiv v).val,letterP_lt i v⟩ (by rw [rawP,hv]; rfl)
      apply pEquiv.injective
      apply Fin.ext
      simpa [wordP,readP] using congrArg Fin.val he
    · intro i v hv
      have he := h (atQ i) ⟨(qEquiv v).val,letterQ_lt i v⟩ (by rw [rawQ,hv]; rfl)
      apply qEquiv.injective
      apply Fin.ext
      simpa [wordQ,readQ] using congrArg Fin.val he
    · intro i v hv
      have he := h (atC i) ⟨v.val,letterC_lt i v⟩ (by rw [rawC,hv]; rfl)
      apply Fin.ext
      change (w (atC i)).val=v.val
      exact congrArg Fin.val he
  · rintro ⟨hp,hq,hc⟩ n v hv
    obtain ⟨i,rfl⟩ := roleEquiv.surjective n
    rcases i with i|i|i
    · change rawSelection P Q C (atP i)=some v.val at hv
      obtain ⟨u,hu,huv⟩ := Option.map_eq_some_iff.mp ((rawP P Q C i).symm.trans hv)
      apply Fin.ext
      have he := congrArg (fun a => (pEquiv a).val) (hp i u hu)
      simpa [wordP,readP,atP,huv] using he
    · change rawSelection P Q C (atQ i)=some v.val at hv
      obtain ⟨u,hu,huv⟩ := Option.map_eq_some_iff.mp ((rawQ P Q C i).symm.trans hv)
      apply Fin.ext
      have he := congrArg (fun a => (qEquiv a).val) (hq i u hu)
      simpa [wordQ,readQ,atQ,huv] using he
    · change rawSelection P Q C (atC i)=some v.val at hv
      obtain ⟨u,hu,huv⟩ := Option.map_eq_some_iff.mp ((rawC P Q C i).symm.trans hv)
      apply Fin.ext
      exact (congrArg Fin.val (hc i u hu)).trans huv

theorem pattern_nonempty (P : PVec) (Q : QVec) (C : CVec d)
    (h : (∃ i, (P i).isSome) ∨ (∃ i, (Q i).isSome) ∨ (∃ i, (C i).isSome)) :
    (pattern code P Q C).columns.Nonempty := by
  change (Finset.univ.filter (fun i => (selection code P Q C i).isSome)).Nonempty
  rcases h with ⟨i,hi⟩|⟨i,hi⟩|⟨i,hi⟩
  · obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp hi
    have h := (selection_some code P Q C (atP i) ⟨(pEquiv u).val,letterP_lt i u⟩).mpr (by rw [rawP,hu]; rfl)
    exact ⟨atP i,by simp [h]⟩
  · obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp hi
    have h := (selection_some code P Q C (atQ i) ⟨(qEquiv u).val,letterQ_lt i u⟩).mpr (by rw [rawQ,hu]; rfl)
    exact ⟨atQ i,by simp [h]⟩
  · obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp hi
    have h := (selection_some code P Q C (atC i) ⟨u.val,letterC_lt i u⟩).mpr (by rw [rawC,hu]; rfl)
    exact ⟨atC i,by simp [h]⟩

theorem pattern_has_arithmetic (P : PVec) (Q : QVec) (C : CVec d)
    (h : (∃ i, (P i).isSome) ∨ (∃ i, (Q i).isSome)) :
    ∃ i : Column (system code), i.val < 18 ∧ i ∈ (pattern code P Q C).columns := by
  change ∃ i : Fin 20, i.val < 18 ∧
    i ∈ Finset.univ.filter (fun i => (selection code P Q C i).isSome)
  rcases h with ⟨i,hi⟩ | ⟨i,hi⟩
  · obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp hi
    have h := (selection_some code P Q C (atP i) ⟨(pEquiv u).val,letterP_lt i u⟩).mpr
      (by rw [rawP,hu]; rfl)
    exact ⟨atP i,by change i.val < 18; omega,by simp [h]⟩
  · obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp hi
    have h := (selection_some code P Q C (atQ i) ⟨(qEquiv u).val,letterQ_lt i u⟩).mpr
      (by rw [rawQ,hu]; rfl)
    exact ⟨atQ i,by change 9+i.val < 18; omega,by simp [h]⟩

def toUnit (r : ℕ) [Fact r.Prime] (v : ZMod r) : Option (ZMod r)ˣ :=
  if h : v≠0 then some (Units.mk0 v h) else none

theorem toUnit_some (r : ℕ) [Fact r.Prime] (v : ZMod r) (u : (ZMod r)ˣ) :
    toUnit r v=some u ↔ v=u.val := by
  by_cases h : v≠0
  · simp only [toUnit,dif_pos h,Option.some.injEq]
    exact ⟨congrArg Units.val,fun h => Units.ext h⟩
  · have he : v=0 := not_not.mp h
    simp [toUnit,he,zero_ne_one,Ne.symm (Units.ne_zero u)]

def digits (r : ℕ) [Fact r.Prime] (m : ℕ) (i : Fin 9) : Option (ZMod r)ˣ :=
  toUnit r ((m/r^i.val%r : ℕ):ZMod r)

private theorem cast_digit_val (r m i : ℕ) [Fact r.Prime] :
    (((m/r^i%r : ℕ):ZMod r)).val=m/r^i%r :=
  ZMod.val_natCast_of_lt (Nat.mod_lt _ (Fact.out (p:=r.Prime)).pos)

theorem digits_matches (r : ℕ) [Fact r.Prime] (m : ℕ) (V : Fin 9 → (ZMod r)ˣ) :
    Satisfies V (digits r m) ↔ Sudoku.PartialWord.Matches (Sudoku.PartialWord.values r V)
      (Sudoku.PartialWord.decode r m) := by
  constructor
  · intro h iv hiv
    obtain ⟨hi,hne,he⟩ := Sudoku.PartialWord.mem_coordinates_iff.mp hiv
    let i : Fin 9 := ⟨iv.1,hi⟩
    let a : ZMod r := (m/r^iv.1%r:ℕ)
    have ha : a.val=m/r^iv.1%r := cast_digit_val r m _
    have han : a≠0 := fun h0 => hne (ha.symm.trans (h0 ▸ ZMod.val_zero))
    have hu := h i (Units.mk0 a han) ((toUnit_some r a _).mpr rfl)
    change Sudoku.PartialWord.values r V iv.1=iv.2
    rw [Sudoku.PartialWord.values,dif_pos hi,he]
    exact (congrArg (fun u : (ZMod r)ˣ => u.val.val) hu).trans ha
  · intro h i v hv
    have hcast := (toUnit_some r _ _).mp hv
    have ha : v.val.val=m/r^i.val%r := (congrArg ZMod.val hcast).symm.trans (cast_digit_val r m _)
    have han : m/r^i.val%r≠0 := by
      intro h0
      apply Units.ne_zero v
      exact ZMod.val_injective r (ha.trans (h0.trans ZMod.val_zero.symm))
    have he := h (i.val,m/r^i.val%r) (Sudoku.PartialWord.mem_coordinates_iff.mpr ⟨i.isLt,han,rfl⟩)
    apply Units.ext
    apply ZMod.val_injective r
    exact (show (V i).val.val=m/r^i.val%r from by simpa [Sudoku.PartialWord.values,i.isLt] using he).trans ha.symm

def queryValue (r : ℕ) (j : Fin 3) (c : (ZMod r)ˣ) (i : Fin 9) : Option (ZMod r) :=
  if ∃ b : Fin 3, Sudoku.NineArithmetic.baseSample r b=i then
    some (c.val*((querySlope j:ZMod r)*Sudoku.NineArithmetic.position r i+1))
  else if i=Sudoku.NineArithmetic.atColumn r (2+r) ∧ 2*querySlope j+1=(r:ℤ) then
    some (c.val*((querySlope j:ZMod r)+1))
  else none

def queryLabels (r : ℕ) [Fact r.Prime] (j : Fin 3) (c : (ZMod r)ˣ) (i : Fin 9) : Option (ZMod r)ˣ :=
  (queryValue r j c i).bind (toUnit r)

theorem queryLabels_some (r : ℕ) [Fact r.Prime] (j : Fin 3)
    (c : (ZMod r)ˣ) (i : Fin 9) (v : (ZMod r)ˣ) :
    queryLabels r j c i=some v ↔ queryValue r j c i=some v.val := by
  unfold queryLabels
  cases queryValue r j c i <;> simp [toUnit_some]

private theorem query_base_unit {r : ℕ} (hr : r=5 ∨ r=7) :
    ∀ k : Fin 3, ∀ i : Fin 3,
    (querySlope k:ZMod r)*Sudoku.NineArithmetic.position r (Sudoku.NineArithmetic.baseSample r i)+1≠0 := by
  rcases hr with rfl|rfl <;> decide +kernel

private theorem query_root_unit {r : ℕ} (hr : r=5 ∨ r=7) :
    ∀ k : Fin 3, 2*querySlope k+1=(r:ℤ) → (querySlope k:ZMod r)+1≠0 := by
  rcases hr with rfl|rfl <;> decide +kernel

theorem guard_labels (r : ℕ) [Fact r.Prime] (hr : r=5 ∨ r=7) (j : Fin 3)
    (c : (ZMod r)ˣ) (V : Fin 9 → (ZMod r)ˣ) :
    Satisfies V (queryLabels r j c) ↔ Guard r j c V := by
  have hx : ∀ b : Fin 3, Sudoku.NineArithmetic.baseSample r b≠Sudoku.NineArithmetic.atColumn r (2+r) := by
    rcases hr with rfl|rfl <;> decide +kernel
  constructor
  · intro h
    constructor
    · intro i
      let k := Sudoku.NineArithmetic.baseSample r i
      let a := c.val*((querySlope j:ZMod r)*Sudoku.NineArithmetic.position r k+1)
      have ha : a≠0 := mul_ne_zero (Units.ne_zero _) (query_base_unit hr j i)
      have he : queryLabels r j c k=some (Units.mk0 a ha) := by
        apply (queryLabels_some r j c _ _).mpr
        simp [queryValue,show ∃ b, Sudoku.NineArithmetic.baseSample r b=k from ⟨i,rfl⟩,a]
      exact congrArg Units.val (h k _ he)
    · intro hj
      let k := Sudoku.NineArithmetic.atColumn r (2+r)
      let a := c.val*((querySlope j:ZMod r)+1)
      have ha : a≠0 := mul_ne_zero (Units.ne_zero _) (query_root_unit hr j hj)
      have he : queryLabels r j c k=some (Units.mk0 a ha) := by
        apply (queryLabels_some r j c _ _).mpr
        simp [queryValue,k,a,hj,hx]
      exact congrArg Units.val (h k _ he)
  · intro h i v hv
    have he := (queryLabels_some r j c i v).mp hv
    unfold queryValue at he
    apply Units.ext
    split at he
    · rename_i hi
      obtain ⟨k,rfl⟩ := hi
      exact (h.1 k).trans (Option.some.inj he)
    · split at he
      · rename_i hi
        obtain ⟨rfl,hj⟩ := hi
        exact (h.2 hj).trans (Option.some.inj he)
      · contradiction

def testP (m : ℕ) := pattern code (digits 5 m) (fun _ => none) (fun _ => none)
def testQ (m : ℕ) := pattern code (fun _ => none) (digits 7 m) (fun _ => none)

theorem testP_matches (m : ℕ) (w : Word (system code)) :
    (testP code m).Matches w ↔ Sudoku.PartialWord.Matches
      (Sudoku.PartialWord.values 5 (wordP code w)) (Sudoku.PartialWord.decode 5 m) := by
  rw [testP,matches_pattern,digits_matches]
  simp [Satisfies]

theorem testQ_matches (m : ℕ) (w : Word (system code)) :
    (testQ code m).Matches w ↔ Sudoku.PartialWord.Matches
      (Sudoku.PartialWord.values 7 (wordQ code w)) (Sudoku.PartialWord.decode 7 m) := by
  rw [testQ,matches_pattern,digits_matches]
  simp [Satisfies]

theorem digits_nonempty (r : ℕ) [Fact r.Prime] (m : ℕ)
    (h : Sudoku.PartialWord.decode r m≠[]) :
    ∃ i, (digits r m i).isSome := by
  obtain ⟨iv,hiv⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hi,hn,_⟩ := Sudoku.PartialWord.mem_coordinates_iff.mp hiv
  have hp : 0<r := Fact.out (p:=r.Prime) |>.pos
  let a : ZMod r := (m/r^iv.1%r:ℕ)
  have ha : a.val=m/r^iv.1%r := cast_digit_val r m _
  have han : a≠0 := fun h0 => hn (ha.symm.trans (h0 ▸ ZMod.val_zero))
  refine ⟨⟨iv.1,hi⟩,?_⟩
  change (toUnit r a).isSome
  simp [toUnit,han]

abbrev QueryIndex (d : ℕ) := Fin 3 × Units5 × Units7 × Fin d × Fin d

def badQuery (i : QueryIndex d) : Prop :=
  ¬ QueryMatch i.1 (code.decode i.2.2.2.1) (code.decode i.2.2.2.2)

def queryPattern (i : QueryIndex d) : PartialTest (system code) :=
  pattern code (queryLabels 5 i.1 i.2.1) (queryLabels 7 i.1 i.2.2.1)
    (fun k => some (![i.2.2.2.1,i.2.2.2.2] k))

theorem query_matches (i : QueryIndex d) (w : Word (system code)) :
    (queryPattern code i).Matches w ↔
    Guard 5 i.1 i.2.1 (wordP code w) ∧ Guard 7 i.1 i.2.2.1 (wordQ code w) ∧
      wordC code w 0=i.2.2.2.1 ∧ wordC code w 1=i.2.2.2.2 := by
  rw [queryPattern,matches_pattern,guard_labels 5 (by decide),guard_labels 7 (by decide)]
  simp [Satisfies,Fin.forall_fin_two]

theorem query_nonempty (i : QueryIndex d) : (queryPattern code i).columns.Nonempty :=
  pattern_nonempty code _ _ _ (Or.inr (Or.inr ⟨0,rfl⟩))

theorem query_has_arithmetic (i : QueryIndex d) :
    ∃ n : Column (system code), n.val < 18 ∧ n ∈ (queryPattern code i).columns := by
  apply pattern_has_arithmetic
  left
  let n := Sudoku.NineArithmetic.baseSample 5 0
  let a := i.2.1.val *
    ((querySlope i.1 : ZMod 5) * Sudoku.NineArithmetic.position 5 n + 1)
  have ha : a ≠ 0 := mul_ne_zero (Units.ne_zero _) (query_base_unit (Or.inl rfl) i.1 0)
  have h : queryLabels 5 i.1 i.2.1 n = some (Units.mk0 a ha) := by
    apply (queryLabels_some 5 i.1 i.2.1 _ _).mpr
    simp [queryValue,show ∃ b, Sudoku.NineArithmetic.baseSample 5 b = n from ⟨0,rfl⟩,a]
  exact ⟨n,by simp [h]⟩

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
