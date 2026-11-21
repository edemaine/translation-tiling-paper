import TranslationTiling.FiniteCompiler.Effective.SharedModelDependence
import TranslationTiling.FiniteCompiler.Effective.SharedPatterns
import TranslationTiling.FiniteCompiler.Effective.SharedStrip
import TranslationTiling.FiniteCompiler.Effective.SharedMass

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance sharedDeckCorrectFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

def sharedHolds (k : ℕ) (o : SharedOutput k) (F : CyclicTile) : Prop :=
  FiniteCompiler.Tiles (F.toFinset.image (decodePoint (sharedLayout k)))
    (Set.range (SharedCoordinates.point (sharedLayout k) o))

def sharedKernel (k : ℕ) :=
  kernelCodes (sharedOrder (sharedRows k)) (guardedModuli (sharedRows k))

theorem sharedKernel_iff (k : ℕ) (A : Set (SharedCoordinates.Ambient (sharedLayout k))) :
    FiniteCompiler.Tiles ((sharedKernel k).toFinset.image (decodePoint (sharedLayout k))) A ↔
      ∃ o : SharedOutput k, Set.range (SharedCoordinates.point (sharedLayout k) o) = A := by
  unfold sharedKernel
  rw [← sharedLayout_order k]
  exact tiles_decoded_kernel_iff_graph (sharedLayout k) (sharedLayoutCRT k) _
    (sharedModuli_membership k) A

theorem sharedKernel_holds (k : ℕ) (o : SharedOutput k) :
    sharedHolds k o (sharedKernel k) :=
  (sharedKernel_iff k _).mpr ⟨o,rfl⟩

theorem sharedActivation_members (k : ℕ) (F : CyclicTile) :
    F ∈ sharedActivationCodes (sharedRows k) (tailSlopes k) ↔
      (∃ (i : SharedRow k), i.val < (sharedRows k).length-2 ∧
        compactCodes (sharedEnvironment (sharedRows k) i) ((tailSlopes k).getD i 0) = F) ∨
      (∃ t : Fin 2, seedRaw k t = F) := by
  simp only [sharedActivationCodes,List.mem_append,List.mem_map,List.mem_range]
  apply or_congr
  · constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi.trans_le (Nat.sub_le _ _)⟩,hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨i.val,hi,rfl⟩
  · constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,by rw [seedRaw,sharedSeedRow_other]; rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t.val,t.isLt,by rw [seedRaw,sharedSeedRow_other]; rfl⟩

theorem sharedBaseline_holds (k : ℕ) (pick : SharedPicker k) (F : CyclicTile)
    (hF : F ∈ sharedKernel k ::
      (sharedDependence (sharedRows k) (tailSlopes k) ++ sharedActivationCodes (sharedRows k) (tailSlopes k))) :
    sharedHolds k (sharedModel pick) F := by
  simp only [List.mem_cons,List.mem_append,sharedActivation_members] at hF
  rcases hF with rfl | hdep | ⟨i,hi,rfl⟩ | ⟨t,rfl⟩
  · exact sharedKernel_holds k _
  · exact (sharedDependence_iff k _ _).mpr (sharedModel_dependence pick) F hdep
  · exact sharedModel_ordinary pick i hi
  · exact sharedModel_seedTiles pick t

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 3 k).radices.prod)

local instance sharedDeckAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

local notation "S" => sharedRefinement hk c

private theorem sharedColumn_at (i : Column (S).system) (x : Plane) :
    sharedLineValue k (sharedColumnRow hk c i) x = lineValue (S).system i x := by
  change x.2 + ((tailSlopes k).getD i.val 0 : ℤ)*x.1 =
    x.2 + (S).system.slope i*x.1
  rw [sharedColumn_slope hk c i]

private def sharedPickerOfWord (W : WordArray (S).system) : SharedPicker k :=
  fun i hi z =>
    let col := sharedColumnOfRow hk c i hi
    have he : sharedColumnRow hk c col = i := Fin.ext rfl
    he ▸ sharedColumnLabel hk c col (W col z)

@[simp] private theorem sharedPickerOfWord_column (W : WordArray (S).system) (i : Column (S).system)
    (z : ℤ) : sharedPickerOfWord hk c W (sharedColumnRow hk c i) (sharedColumnRow_lt hk c i) z =
      sharedColumnLabel hk c i (W i z) := by
  unfold sharedPickerOfWord
  rfl

private theorem modelActivity_ordinary (W : WordArray (S).system) (x : Plane)
    (i : Column (S).system) (v : Letter (S).system i) :
    DigitActive (sharedPrivateAt (sharedModel (sharedPickerOfWord hk c W)) x (sharedColumnRow hk c i))
      (sharedDigitSubgroup (sharedColumnRow hk c i) (sharedColumnLabel hk c i v)) ↔
      v = W i (lineValue (S).system i x) := by
  rw [sharedModel_ordinaryActive (sharedPickerOfWord hk c W) _ (sharedColumnRow_lt hk c i),
    sharedColumn_at hk c,sharedPickerOfWord_column]
  exact (sharedColumnLabel hk c i).injective.eq_iff

private theorem ordinaryCoverage (o : SharedOutput k)
    (h : ∀ F ∈ sharedActivationCodes (sharedRows k) (tailSlopes k), sharedHolds k o F)
    (hd : HasSharedDependence k (tailSlopes k) o) (i : Column (S).system) (x : Plane) :
    ∃ j : SharedLabel (sharedColumnRow hk c i),
      DigitActive (sharedPrivateAt o x (sharedColumnRow hk c i))
        (sharedDigitSubgroup (sharedColumnRow hk c i) j) :=
  ordinary_active _ (sharedColumnRow_lt hk c i) hd
    (h _ ((sharedActivation_members k _).mpr (Or.inl ⟨_,sharedColumnRow_lt hk c i,rfl⟩))) x

private theorem patternActivity (o : SharedOutput k) (hd : HasSharedDependence k (tailSlopes k) o)
    (q : PartialTest (S).system) (hne : q.columns.Nonempty) :
    letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr hne).ne'⟩
    (∀ F ∈ sharedCycle (sharedRows k)
      (sharedAssignments (sharedPatternCycle hk c q) (sharedPatternLabel hk c q)), sharedHolds k o F) ↔
      ∀ x, ∃ i : q.columns,
        ¬ DigitActive (sharedPrivateAt o x (sharedColumnRow hk c i.val))
          (sharedDigitSubgroup (sharedColumnRow hk c i.val) (sharedColumnLabel hk c i.val (q.label i))) := by
  letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr hne).ne'⟩
  dsimp only [sharedHolds]
  rw [sharedCycle_iff _ _ o (sharedPrivateAt o) (fun x a i => hd.factorLow x a i)]
  constructor
  · intro h x
    obtain ⟨j,hj⟩ := h x
    exact ⟨testEquiv q ((ZMod.finEquiv q.columns.card).symm j),hj⟩
  · intro h x
    obtain ⟨i,hi⟩ := h x
    refine ⟨(ZMod.finEquiv q.columns.card) ((testEquiv q).symm i),?_⟩
    let prop (j : q.columns) : Prop :=
      ¬ DigitActive (sharedPrivateAt o x (sharedColumnRow hk c j.val))
        (sharedDigitSubgroup (sharedColumnRow hk c j.val) (sharedColumnLabel hk c j.val (q.label j)))
    change prop (testEquiv q ((ZMod.finEquiv q.columns.card).symm
      ((ZMod.finEquiv q.columns.card) ((testEquiv q).symm i))))
    rw [(ZMod.finEquiv q.columns.card).symm_apply_apply,(testEquiv q).apply_symm_apply]
    exact hi


def sharedSeedActive {k : ℕ} (o : SharedOutput k) (t : Fin 2) (x : Plane) : Prop :=
  DigitActive (sharedPrivateAt o x (sharedSeedRow k t))
    (sharedDigitSubgroup (sharedSeedRow k t) (sharedSeedLabel k t))

def sharedColumnActive (o : SharedOutput k) (i : Column (S).system)
    (v : Letter (S).system i) (x : Plane) : Prop :=
  DigitActive (sharedPrivateAt o x (sharedColumnRow hk c i))
    (sharedDigitSubgroup (sharedColumnRow hk c i) (sharedColumnLabel hk c i v))

private theorem seedActivity (o : SharedOutput k) (hd : HasSharedDependence k (tailSlopes k) o)
    (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i) :
    (∀ F ∈ sharedCycle (sharedRows k)
      (sharedAssignments (sharedSeedCycle hk c t i) (sharedSeedCycleLabel hk c t i v)),
      sharedHolds k o F) ↔
      ∀ x, ¬ (sharedSeedActive o t x ∧ sharedColumnActive hk c o i v x) := by
  dsimp only [sharedHolds]
  rw [sharedCycle_iff _ _ o (sharedPrivateAt o) (fun x a i => hd.factorLow x a i)]
  constructor
  · intro h x ha
    obtain ⟨j,hj⟩ := h x
    fin_cases j
    · exact hj ha.1
    · exact hj ha.2
  · intro h x
    by_cases ht : sharedSeedActive o t x
    · exact ⟨1,fun hi => h x ⟨ht,hi⟩⟩
    · exact ⟨0,ht⟩

private def sharedZeroOutput (k : ℕ) : SharedOutput k := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

private theorem sharedZero_cycle {t : ℕ} [NeZero t] (cy : ZMod t ↪ SharedRow k)
    (lab : ∀ j, SharedLabel (cy j)) (F : CyclicTile)
    (hF : F ∈ sharedCycle (sharedRows k) (sharedAssignments cy lab)) :
    sharedHolds k (sharedZeroOutput k) F := by
  apply (sharedCycle_iff cy lab (sharedZeroOutput k) (fun _ _ _ => 0) (fun _ _ _ => rfl)).mpr _ F hF
  intro x
  exact ⟨0,fun ⟨_,_,_,hn⟩ => hn rfl⟩

private theorem testTemplates_iff (hn : 0 < T.length)
    (hcap : T.length ≤ (radixLayoutProfile 3 k).radices.prod)
    (hc : c = code T _ hn hcap) (xs : GuardedAssignments) :
    xs ∈ sharedTests T k ↔
      xs ∈ tailSeedTests k ∨ ∃ b ∈ patterns c, expandMask 3 k (testMask c b) = xs := by
  subst c
  have hcode : (radixLayoutProfile 3 k).radices.prod = 3^k := by
    simp [radixLayoutProfile,List.prod_replicate]
  unfold sharedTests
  simp only [List.mem_append,List.mem_map]
  apply or_congr_right
  constructor
  · rintro ⟨m,hm,rfl⟩
    rw [← hcode,rawMask_membership hn hcap] at hm
    obtain ⟨b,hb,rfl⟩ := hm
    exact ⟨b,hb,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    refine ⟨testMask _ b,?_,rfl⟩
    rw [← hcode,rawMask_membership hn hcap]
    exact ⟨b,hb,rfl⟩

include hk in
private theorem sharedExclusions_satisfiable (hn : 0 < T.length)
    (hcap : T.length ≤ (radixLayoutProfile 3 k).radices.prod) (hc : c = code T _ hn hcap)
    (xs : GuardedAssignments) (hxs : xs ∈ sharedTests T k) :
    ∀ F ∈ sharedCycle (sharedRows k) xs, sharedHolds k (sharedZeroOutput k) F := by
  rcases (testTemplates_iff c hn hcap hc xs).mp hxs with hs | ⟨b,_,rfl⟩
  · obtain ⟨t,i,v,_,rfl⟩ := (tailSeedTests_iff hk c xs).mp hs
    exact sharedZero_cycle (sharedSeedCycle hk c t i) (sharedSeedCycleLabel hk c t i v)
  · let q := (S).expand b
    rw [sharedPattern_indices hk c b]
    change (∀ F ∈ sharedCycle (sharedRows k) (dite q.columns.Nonempty _ _), _)
    by_cases h : q.columns.Nonempty
    · letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr h).ne'⟩
      rw [dif_pos h]
      exact sharedZero_cycle (sharedPatternCycle hk c q) (sharedPatternLabel hk c q)
    · rw [dif_neg h]
      simp [sharedCycle]


include hk in
private theorem sharedSound (o : SharedOutput k)
    (hd : HasSharedDependence k (tailSlopes k) o)
    (ha : ∀ F ∈ sharedActivationCodes (sharedRows k) (tailSlopes k), sharedHolds k o F)
    (hseed : ∀ xs ∈ tailSeedTests k, ∀ F ∈ sharedCycle (sharedRows k) xs, sharedHolds k o F)
    (hpat : ∀ b ∈ patterns c, ∀ F ∈ sharedCycle (sharedRows k) (expandMask 3 k (testMask c b)),
      sharedHolds k o F) : LeanWang.TilesPlane T := by
  let W : WordArray (S).system := fun i l =>
    (sharedColumnLabel hk c i).symm ((ordinaryCoverage hk c o ha hd i (0,l)).choose)
  have hactive (x : Plane) (i : Column (S).system) :
      sharedColumnActive hk c o i (W i (lineValue (S).system i x)) x := by
    let l := lineValue (S).system i x
    let j := sharedColumnRow hk c i
    have hline : sharedPrivateAt o x j = sharedPrivateAt o (0,l) j := by
      funext d
      apply hd.privateAt_line j (sharedColumnRow_lt hk c i)
      rw [show (x.2 + ((tailSlopes k).getD j 0 : ℤ)*x.1) = l from sharedColumn_at hk c i x]
      simp
    unfold sharedColumnActive
    change DigitActive (sharedPrivateAt o x j) _
    rw [hline]
    have h := (ordinaryCoverage hk c o ha hd i (0,l)).choose_spec
    exact (by simpa only [W,AddEquiv.apply_symm_apply,Equiv.apply_symm_apply] using h)
  apply wang_of_refined_selection c (S) W
  · intro t
    obtain ⟨x,hx⟩ := seed_active hd t
      (ha _ ((sharedActivation_members k _).mpr (Or.inr ⟨t,rfl⟩)))
    refine ⟨x,fun i => ?_⟩
    by_contra h
    let v := W i (lineValue (S).system i x)
    let xs := sharedAssignments (sharedSeedCycle hk c t i) (sharedSeedCycleLabel hk c t i v)
    have hm := (tailSeedTests_iff hk c xs).mpr ⟨t,i,v,h,rfl⟩
    exact (seedActivity hk c o hd t i v).mp (hseed xs hm) x ⟨hx,hactive x i⟩
  · intro x q hq hne hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    let q := (S).expand b
    have hp := hpat b hb
    rw [sharedPattern_indices hk c b] at hp
    change (∀ F ∈ sharedCycle (sharedRows k) (dite q.columns.Nonempty _ _),_) at hp
    rw [dif_pos hne] at hp
    obtain ⟨i,hi⟩ := (patternActivity hk c o hd q hne).mp hp x
    apply hi
    have eqi : W i.val (lineValue (S).system i.val x) = q.label i := hm i
    simpa only [sharedColumnActive,eqi] using hactive x i.val

include hk in
private theorem sharedComplete (h : LeanWang.TilesPlane T) :
    ∃ o : SharedOutput k,
      (∀ F ∈ sharedKernel k :: (sharedDependence (sharedRows k) (tailSlopes k) ++
        sharedActivationCodes (sharedRows k) (tailSlopes k)), sharedHolds k o F) ∧
      (∀ xs ∈ tailSeedTests k, ∀ F ∈ sharedCycle (sharedRows k) xs, sharedHolds k o F) ∧
      (∀ b ∈ patterns c, ∀ F ∈ sharedCycle (sharedRows k) (expandMask 3 k (testMask c b)),
        sharedHolds k o F) := by
  obtain ⟨W,hW,hs⟩ := exists_wordArray_of_wang c h
  let V := (S).packArray W
  let pick := sharedPickerOfWord hk c V
  let o := sharedModel pick
  have hd : HasSharedDependence k (tailSlopes k) o := sharedModel_dependence pick
  have hword (x : Plane) : Allowed (system c)
      ((S).unpackWord (fun i => V i (lineValue (S).system i x))) := by
    have hm := (S).pack_lineRule hW x
    exact hm
  have hsv (t : Fin 2) (x : Plane)
      (hx : SharedSeed.residue seedModel.system x ∈ seedActiveRegion seedModel.system t) :
      ∀ i, LetterSeedSet (S).system t i (V i (lineValue (S).system i x)) :=
    (S).pack_seed (fun i => hs t i x hx)
  have hact (x : Plane) (i : Column (S).system) (v : Letter (S).system i) :
      sharedColumnActive hk c o i v x ↔ v = V i (lineValue (S).system i x) :=
    modelActivity_ordinary hk c V x i v
  refine ⟨o,sharedBaseline_holds k pick,?_,?_⟩
  · intro xs hx
    obtain ⟨t,i,v,hv,rfl⟩ := (tailSeedTests_iff hk c xs).mp hx
    apply (seedActivity hk c o hd t i v).mpr
    intro x hboth
    have hr := (sharedModel_seedActive pick t x).mp hboth.1
    exact hv ((hact x i v).mp hboth.2 ▸ hsv t x hr i)
  · intro b hb
    let q := (S).expand b
    rw [sharedPattern_indices hk c b]
    change (∀ F ∈ sharedCycle (sharedRows k) (dite q.columns.Nonempty _ _),_)
    by_cases hne : q.columns.Nonempty
    · rw [dif_pos hne]
      apply (patternActivity hk c o hd q hne).mpr
      intro x
      have hn : ¬ q.Matches (fun i => V i (lineValue (S).system i x)) :=
        fun hm => patterns_sound c b hb _ (hword x) (((S).expand_matches b _).mp hm)
      by_contra! hc
      exact hn (fun i => ((hact x i.val (q.label i)).mp (hc i)).symm)
    · rw [dif_neg hne]
      simp [sharedCycle]


open Compiler.Size in
theorem sharedTailCore_facts (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    sharedTailCore T ≠ [] ∧ FaceConnected (sharedTailCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sharedTailCore T)) ∧
    ((sharedTailCore T).length : ℝ) ≤ sharedUsefulBound T.length := by
  let k := guardedTrits T.length
  have hk : 0 < k := (by decide : 0 < 20).trans_le (guardedTrits_ge hn)
  have hpos : 0 < T.length := (by decide : 0 < 3^21).trans hn
  have hcap : T.length ≤ (radixLayoutProfile 3 k).radices.prod := by
    simpa only [radixLayoutProfile,List.prod_replicate] using guardedTrits_capacity T.length
  let c := code T _ hpos hcap
  let rs := sharedRows k
  let L := sharedLayout k
  let tests := sharedTests T k
  let Fs := sharedRawDeck rs (tailSlopes k) tests
  let testMem := testTemplates_iff c hpos hcap rfl
  have hraw (F : CyclicTile) : F ∈ Fs ↔
      F = sharedKernel k ∨ F ∈ sharedDependence rs (tailSlopes k) ∨
        F ∈ sharedActivationCodes rs (tailSlopes k) ∨ ∃ xs ∈ tests, F ∈ sharedCycle rs xs := by
    simp only [Fs,sharedRawDeck,sharedKernel,rs,List.mem_cons,List.mem_append,List.mem_flatMap]
    tauto
  have hcycles (o : SharedOutput k)
      (h : ∀ xs ∈ tests, ∀ F ∈ sharedCycle rs xs, sharedHolds k o F) :
      (∀ xs ∈ tailSeedTests k, ∀ F ∈ sharedCycle rs xs, sharedHolds k o F) ∧
      (∀ b ∈ patterns c, ∀ F ∈ sharedCycle rs (expandMask 3 k (testMask c b)), sharedHolds k o F) := by
    exact ⟨fun xs hxs => h xs ((testMem xs).mpr (Or.inl hxs)),
      fun b hb => h _ ((testMem _).mpr (Or.inr ⟨b,hb,rfl⟩))⟩
  have hlogical :
      LeanWang.TilesPlane T ↔ ∃ A : Set (SharedCoordinates.Ambient L),
        ∀ F ∈ Fs, FiniteCompiler.Tiles (F.toFinset.image (decodePoint L)) A := by
    constructor
    · intro h
      obtain ⟨o,hb,hs,hp⟩ := sharedComplete hk c h
      refine ⟨Set.range (SharedCoordinates.point L o),fun F hF => ?_⟩
      change sharedHolds k o F
      rcases (hraw F).mp hF with rfl | hd | ha | ⟨xs,hxs,hF⟩
      · exact sharedKernel_holds k o
      · exact hb F (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hd))))
      · exact hb F (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr ha))))
      · rcases (testMem xs).mp hxs with hs' | ⟨b,hb,rfl⟩
        · exact hs xs hs' F hF
        · exact hp b hb F hF
    · rintro ⟨A,hA⟩
      obtain ⟨o,rfl⟩ := (sharedKernel_iff k A).mp (hA _ ((hraw _).mpr (Or.inl rfl)))
      have hd := (sharedDependence_iff k _ o).mp (fun F hF => hA F ((hraw F).mpr (Or.inr (Or.inl hF))))
      have ha : ∀ F ∈ sharedActivationCodes rs (tailSlopes k), sharedHolds k o F :=
        fun F hF => hA F ((hraw F).mpr (Or.inr (Or.inr (Or.inl hF))))
      obtain ⟨hs,hp⟩ := hcycles o
        (fun xs hxs F hF => hA F ((hraw F).mpr (Or.inr (Or.inr (Or.inr ⟨xs,hxs,hF⟩)))))
      exact sharedSound hk c o hd ha hs hp
  let pick : SharedPicker k := fun i hi _ => ⟨0,by
    have he : i.val < 18+2*k := by have := sharedRows_length k; omega
    rw [sharedRows_arity hk i.val he,radixLayout_arity hk (by simpa using he)]
    split_ifs <;> decide⟩
  have hcert (F : CyclicTile) (hF : F ∈ Fs) : F ≠ [] ∧
      (cyclicTileSet (sharedOrder rs) F).card = sharedMass rs := by
    apply sharedRaw_mass_of_tiles k F
    rcases (hraw F).mp hF with rfl | hd | ha | ⟨xs,hxs,hF⟩
    · exact ⟨sharedModel pick,sharedKernel_holds k _⟩
    · exact ⟨sharedModel pick,
        (sharedDependence_iff k _ _).mpr (sharedModel_dependence pick) F hd⟩
    · exact ⟨sharedModel pick,sharedBaseline_holds k pick F
        (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr ha))))⟩
    · exact ⟨sharedZeroOutput k,sharedExclusions_satisfiable hk c hpos hcap rfl xs hxs F hF⟩
  obtain ⟨hne,hconn,hgeom,hsize⟩ := sharedTailCore_of_deck_geometry T hn
    (fun F hF => (hcert F hF).1) (fun F hF => (hcert F hF).2.le) (sharedRawDeck_strip k tests)
  refine ⟨hne,hconn,?_,hsize⟩
  have hc := cyclic_deck_iff L (sharedLayoutCRT k) Fs
  have hc' : (∃ B : Set (Plane × ZMod (sharedOrder rs)),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet (sharedOrder rs) (Fs.getD i.val [])) B) ↔
      (∃ A : Set (SharedCoordinates.Ambient L),
        ∀ F ∈ Fs, FiniteCompiler.Tiles (F.toFinset.image (decodePoint L)) A) := by
    have eqO : order L = sharedOrder rs := sharedLayout_order k
    have he := congrArg (fun n : ℕ => ∃ B : Set (Plane × ZMod n),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet n (Fs.getD i.val [])) B) eqO
    exact (iff_of_eq he).symm.trans hc
  exact hlogical.trans (hc'.symm.trans hgeom)

end
end TranslationTiling.FiniteCompiler.Packed
