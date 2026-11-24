import TranslationTiling.FiniteCompiler.Effective.FourValueSelection
import TranslationTiling.FiniteCompiler.Effective.FourValueStrip

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance fourValueDeckCorrectFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

def fourValueKernel (k : ℕ) :=
  kernelCodes (sharedOrder (fourValueRows k)) (guardedModuli (fourValueRows k))

theorem fourValueKernel_iff (k : ℕ) (A : Set (SharedCoordinates.Ambient (fourValueLayout k))) :
    FiniteCompiler.Tiles ((fourValueKernel k).toFinset.image (decodePoint (fourValueLayout k))) A ↔
      ∃ o : FourValueOutputGraph k, Set.range (SharedCoordinates.point (fourValueLayout k) o) = A := by
  unfold fourValueKernel
  rw [← fourValueLayout_order k]
  exact tiles_decoded_kernel_iff_graph (fourValueLayout k) (fourValueLayoutCRT k) _
    (fourValueModuli_membership k) A

theorem fourValueKernel_holds (k : ℕ) (o : FourValueOutputGraph k) :
    fourValueHolds k o (fourValueKernel k) :=
  (fourValueKernel_iff k _).mpr ⟨o,rfl⟩


theorem fourValueBaseline_holds (k : ℕ) (pick : FourValuePicker k) (F : CyclicTile)
    (hF : F ∈ fourValueKernel k ::
      (sharedDependence (fourValueRows k) (tailSlopes k) ++ fourValueActivation k)) :
    fourValueHolds k (fourValueModel pick) F := by
  simp only [List.mem_cons,List.mem_append,fourValueActivation_members] at hF
  rcases hF with rfl | hd | (⟨i,hi,rfl⟩ | ⟨w,rfl⟩) | ⟨t,rfl⟩
  · exact fourValueKernel_holds k _
  · exact (fourValueDependence_iff k _ _).mpr (fourValueModel_dependence pick) F hd
  · exact fourValueModel_fixed_tiles pick i hi
  · exact fourValueModel_wang_tiles pick w
  · exact fourValueModel_seed_tiles pick t

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance fourValueDeckAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

local notation "S" => fourValueRefinement hk c


private def fourValueZeroOutput (k : ℕ) : FourValueOutputGraph k := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

private theorem fourValueZero_dep (k : ℕ) :
    HasFourValueDependence k (tailSlopes k) (fourValueZeroOutput k) :=
  ⟨fun _ _ _ _ => rfl,fun _ _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private theorem testTemplates_iff (hn : 0 < T.length)
    (hcap : T.length ≤ (radixLayoutProfile 4 k).radices.prod)
    (hc : c = code T _ hn hcap) (xs : GuardedAssignments) :
    xs ∈ fourValueTests T k ↔
      xs ∈ tailSeedTests k ∨ ∃ b ∈ patterns c, expandMask 4 k (testMask c b) = xs := by
  subst c
  have hcode : (radixLayoutProfile 4 k).radices.prod = 4^k := by
    simp [radixLayoutProfile,List.prod_replicate]
  unfold fourValueTests
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
private theorem fourValueExclusions_satisfiable (hn : 0 < T.length)
    (hcap : T.length ≤ (radixLayoutProfile 4 k).radices.prod) (hc : c = code T _ hn hcap)
    (xs : GuardedAssignments) (hxs : xs ∈ fourValueTests T k) :
    ∀ F ∈ fourValueCycle k xs, fourValueHolds k (fourValueZeroOutput k) F := by
  rcases (testTemplates_iff c hn hcap hc xs).mp hxs with hs | ⟨b,_,rfl⟩
  · obtain ⟨t,i,v,_,rfl⟩ := (fourValueTailSeedTests_iff hk c xs).mp hs
    apply (fourValueSeedActivity hk c _ (fourValueZero_dep k) t i v).mpr
    intro x h
    obtain ⟨a,b,_,hab⟩ := h.1
    exact hab rfl
  · let q := (S).expand b
    rw [fourValuePattern_indices hk c b]
    change (∀ F ∈ fourValueCycle k (dite q.columns.Nonempty _ _), _)
    by_cases h : q.columns.Nonempty
    · letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr h).ne'⟩
      rw [dif_pos h]
      apply (fourValuePatternActivity hk c _ (fourValueZero_dep k) q h).mpr
      intro x
      refine ⟨⟨h.choose,h.choose_spec⟩,fun ⟨a,b,_,hab⟩ => hab rfl⟩
    · rw [dif_neg h]
      simp [fourValueCycle]


include hk in
private theorem fourValueSound (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o)
    (ha : ∀ F ∈ fourValueActivation k, fourValueHolds k o F)
    (hseed : ∀ xs ∈ tailSeedTests k, ∀ F ∈ fourValueCycle k xs, fourValueHolds k o F)
    (hpat : ∀ b ∈ patterns c, ∀ F ∈ fourValueCycle k (expandMask 4 k (testMask c b)),
      fourValueHolds k o F) : LeanWang.TilesPlane T := by
  let W : WordArray (S).system := fun i l => (fourValueColumn_coverage hk c o ha hd i (0,l)).choose
  have hactive (x : Plane) (i : Column (S).system) :
      fourValueColumnActive hk c o i (W i (lineValue (S).system i x)) x := by
    apply (fourValueColumn_active_line hk c o hd i _ x).mpr
    exact (fourValueColumn_coverage hk c o ha hd i (0,lineValue (S).system i x)).choose_spec
  apply wang_of_refined_selection c (S) W
  · intro t
    obtain ⟨x,hx⟩ := fourValue_seed_active hd t
      (ha _ ((fourValueActivation_members k _).mpr (Or.inr ⟨t,rfl⟩)))
    refine ⟨x,fun i => ?_⟩
    by_contra h
    let v := W i (lineValue (S).system i x)
    let xs := fourValueAssignments (fourValueSeedCycle hk c t i) (fourValueSeedCycleLabel hk c t i v)
    have hm := (fourValueTailSeedTests_iff hk c xs).mpr ⟨t,i,v,h,rfl⟩
    exact (fourValueSeedActivity hk c o hd t i v).mp (hseed xs hm) x ⟨hx,hactive x i⟩
  · intro x q hq hne hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    let q := (S).expand b
    have hp := hpat b hb
    rw [fourValuePattern_indices hk c b] at hp
    change (∀ F ∈ fourValueCycle k (dite q.columns.Nonempty _ _),_) at hp
    rw [dif_pos hne] at hp
    obtain ⟨i,hi⟩ := (fourValuePatternActivity hk c o hd q hne).mp hp x
    apply hi
    have eqi : W i.val (lineValue (S).system i.val x) = q.label i := hm i
    simpa only [eqi] using hactive x i.val

include hk in
private theorem fourValueComplete (h : LeanWang.TilesPlane T) :
    ∃ o : FourValueOutputGraph k,
      (∀ F ∈ fourValueKernel k :: (sharedDependence (fourValueRows k) (tailSlopes k) ++
        fourValueActivation k), fourValueHolds k o F) ∧
      (∀ xs ∈ tailSeedTests k, ∀ F ∈ fourValueCycle k xs, fourValueHolds k o F) ∧
      (∀ b ∈ patterns c, ∀ F ∈ fourValueCycle k (expandMask 4 k (testMask c b)),
        fourValueHolds k o F) := by
  obtain ⟨W,hW,hs⟩ := exists_wordArray_of_wang c h
  let V := (S).packArray W
  let pick := fourValuePickerOfWord hk c V
  let o := fourValueModel pick
  have hd : HasFourValueDependence k (tailSlopes k) o := fourValueModel_dependence pick
  have hword (x : Plane) : Allowed (system c)
      ((S).unpackWord (fun i => V i (lineValue (S).system i x))) := by
    have hm := (S).pack_lineRule hW x
    exact hm
  have hsv (t : Fin 2) (x : Plane)
      (hx : SharedSeed.residue seedModel.system x ∈ seedActiveRegion seedModel.system t) :
      ∀ i, LetterSeedSet (S).system t i (V i (lineValue (S).system i x)) :=
    (S).pack_seed (fun i => hs t i x hx)
  have hact (x : Plane) (i : Column (S).system) (v : Letter (S).system i) :
      fourValueColumnActive hk c o i v x ↔ v = V i (lineValue (S).system i x) :=
    fourValueModel_column_activity hk c V x i v
  refine ⟨o,fourValueBaseline_holds k pick,?_,?_⟩
  · intro xs hx
    obtain ⟨t,i,v,hv,rfl⟩ := (fourValueTailSeedTests_iff hk c xs).mp hx
    apply (fourValueSeedActivity hk c o hd t i v).mpr
    intro x hboth
    have hr := (fourValueModel_seed_active pick t x).mp hboth.1
    exact hv ((hact x i v).mp hboth.2 ▸ hsv t x hr i)
  · intro b hb
    let q := (S).expand b
    rw [fourValuePattern_indices hk c b]
    change (∀ F ∈ fourValueCycle k (dite q.columns.Nonempty _ _),_)
    by_cases hne : q.columns.Nonempty
    · rw [dif_pos hne]
      apply (fourValuePatternActivity hk c o hd q hne).mpr
      intro x
      have hn : ¬ q.Matches (fun i => V i (lineValue (S).system i x)) :=
        fun hm => patterns_sound c b hb _ (hword x) (((S).expand_matches b _).mp hm)
      by_contra! hc
      exact hn (fun i => ((hact x i.val (q.label i)).mp (hc i)).symm)
    · rw [dif_neg hne]
      simp [fourValueCycle]


open Compiler.Size in
theorem fourValueTailCore_facts (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    fourValueTailCore T ≠ [] ∧ FaceConnected (fourValueTailCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (fourValueTailCore T)) ∧
    ((fourValueTailCore T).length : ℝ) ≤ fourValueBound T.length := by
  let k := residueDigits T.length
  have hk : 0 < k := by unfold k residueDigits; omega
  have hpos : 0 < T.length := (by decide : 0 < 3^21).trans hn
  have hcap : T.length ≤ (radixLayoutProfile 4 k).radices.prod := by
    simpa only [radixLayoutProfile,List.prod_replicate] using residueDigits_capacity T.length
  let c := code T _ hpos hcap
  let rs := fourValueRows k
  let L := fourValueLayout k
  let tests := fourValueTests T k
  let Fs := fourValueRawDeck T k
  let testMem := testTemplates_iff c hpos hcap rfl
  have hraw (F : CyclicTile) : F ∈ Fs ↔
      F = fourValueKernel k ∨ F ∈ sharedDependence rs (tailSlopes k) ∨
        F ∈ fourValueActivation k ∨ ∃ xs ∈ tests, F ∈ fourValueCycle k xs := by
    simp only [Fs,fourValueRawDeck,fourValueKernel,rs,tests,List.mem_cons,List.mem_append,List.mem_flatMap,or_assoc]
  have hcycles (o : FourValueOutputGraph k)
      (h : ∀ xs ∈ tests, ∀ F ∈ fourValueCycle k xs, fourValueHolds k o F) :
      (∀ xs ∈ tailSeedTests k, ∀ F ∈ fourValueCycle k xs, fourValueHolds k o F) ∧
      (∀ b ∈ patterns c, ∀ F ∈ fourValueCycle k (expandMask 4 k (testMask c b)), fourValueHolds k o F) := by
    exact ⟨fun xs hxs => h xs ((testMem xs).mpr (Or.inl hxs)),
      fun b hb => h _ ((testMem _).mpr (Or.inr ⟨b,hb,rfl⟩))⟩
  have hlogical :
      LeanWang.TilesPlane T ↔ ∃ A : Set (SharedCoordinates.Ambient L),
        ∀ F ∈ Fs, FiniteCompiler.Tiles (F.toFinset.image (decodePoint L)) A := by
    constructor
    · intro h
      obtain ⟨o,hb,hs,hp⟩ := fourValueComplete hk c h
      refine ⟨Set.range (SharedCoordinates.point L o),fun F hF => ?_⟩
      change fourValueHolds k o F
      rcases (hraw F).mp hF with rfl | hd | ha | ⟨xs,hxs,hF⟩
      · exact fourValueKernel_holds k o
      · exact hb F (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hd))))
      · exact hb F (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr ha))))
      · rcases (testMem xs).mp hxs with hs' | ⟨b,hb,rfl⟩
        · exact hs xs hs' F hF
        · exact hp b hb F hF
    · rintro ⟨A,hA⟩
      obtain ⟨o,rfl⟩ := (fourValueKernel_iff k A).mp (hA _ ((hraw _).mpr (Or.inl rfl)))
      have hd := (fourValueDependence_iff k _ o).mp (fun F hF => hA F ((hraw F).mpr (Or.inr (Or.inl hF))))
      have ha : ∀ F ∈ fourValueActivation k, fourValueHolds k o F :=
        fun F hF => hA F ((hraw F).mpr (Or.inr (Or.inr (Or.inl hF))))
      obtain ⟨hs,hp⟩ := hcycles o
        (fun xs hxs F hF => hA F ((hraw F).mpr (Or.inr (Or.inr (Or.inr ⟨xs,hxs,hF⟩)))))
      exact fourValueSound hk c o hd ha hs hp
  let pick : FourValuePicker k := {
    fixed := fun i hi _ => ⟨0,by
      rw [fourValueRows_arity hk i.val hi,radixLayout_arity hk (by simp; omega)]
      split_ifs <;> decide⟩
    wang := fun _ _ => ⟨labelIndex 0,labelIndex_ne 0⟩ }
  have hcert (F : CyclicTile) (hF : F ∈ Fs) : F ≠ [] ∧
      (cyclicTileSet (sharedOrder rs) F).card = sharedMass rs := by
    apply fourValueRaw_mass_of_tiles k F
    rcases (hraw F).mp hF with rfl | hd | ha | ⟨xs,hxs,hF⟩
    · exact ⟨fourValueModel pick,fourValueKernel_holds k _⟩
    · exact ⟨fourValueModel pick,
        (fourValueDependence_iff k _ _).mpr (fourValueModel_dependence pick) F hd⟩
    · exact ⟨fourValueModel pick,fourValueBaseline_holds k pick F
        (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr ha))))⟩
    · exact ⟨fourValueZeroOutput k,fourValueExclusions_satisfiable hk c hpos hcap rfl xs hxs F hF⟩
  obtain ⟨hne,hconn,hgeom,hsize⟩ := fourValueTailCore_of_deck_geometry T hn
    (fun F hF => (hcert F hF).1) (fun F hF => (hcert F hF).2.le) (fourValueRawDeck_strip T k)
  refine ⟨hne,hconn,?_,hsize⟩
  have hc := cyclic_deck_iff L (fourValueLayoutCRT k) Fs
  have hc' : (∃ B : Set (Plane × ZMod (sharedOrder rs)),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet (sharedOrder rs) (Fs.getD i.val [])) B) ↔
      (∃ A : Set (SharedCoordinates.Ambient L),
        ∀ F ∈ Fs, FiniteCompiler.Tiles (F.toFinset.image (decodePoint L)) A) := by
    have eqO : order L = sharedOrder rs := fourValueLayout_order k
    have he := congrArg (fun n : ℕ => ∃ B : Set (Plane × ZMod n),
      ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet n (Fs.getD i.val [])) B) eqO
    exact (iff_of_eq he).symm.trans hc
  exact hlogical.trans (hc'.symm.trans hgeom)

end
end TranslationTiling.FiniteCompiler.Packed
