import TranslationTiling.Compiler.EffectiveActivationOffsets
import TranslationTiling.Compiler.EffectivePartition
import TranslationTiling.Compiler.EffectiveGraphTiles
import TranslationTiling.Compiler.EffectiveLattice

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

/-- Canonical numerical Chinese-remainder assembly. -/
def mergeResidues (N q x y : ℕ) : ℕ := residueSearch (N * q) [(N, x), (q, y)]

theorem mergeResidues_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => mergeResidues z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hd : Primrec (fun z : ℕ × ℕ × ℕ × ℕ =>
      (z.1 * z.2.1, [(z.1, z.2.2.1), (z.2.1, z.2.2.2)])) := by fun_prop
  have h := residueSearch_primrec.comp hd
  exact h

@[fun_prop] theorem mergeResiduesRule {α : Type*} [Primcodable α] {N q x y : α → ℕ}
    (hN : Primrec N) (hq : Primrec q) (hx : Primrec x) (hy : Primrec y) :
    Primrec (fun z => mergeResidues (N z) (q z) (x z) (y z)) :=
  mergeResidues_primrec.comp (hN.pair (hq.pair (hx.pair hy)))

theorem mergeResidues_correct {N q : ℕ} [NeZero N] [NeZero q]
    (hcop : Nat.Coprime N q) (x y : ℕ) :
    mergeResidues N q x y = ((ZMod.chineseRemainder hcop).symm
      ((x : ZMod N), (y : ZMod q))).val := by
  apply residueSearch_of_equiv (ZMod.chineseRemainder hcop).toEquiv
  intro n
  have he : ZMod.chineseRemainder hcop (n : ZMod (N * q)) =
      ((n : ZMod N), (n : ZMod q)) := by rw [map_natCast]; rfl
  change Congruences [(N, x), (q, y)] n ↔
    ZMod.chineseRemainder hcop (n : ZMod (N * q)) = ((x : ZMod N), (y : ZMod q))
  rw [he]
  simp only [Congruences, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true, Prod.mk.injEq, ← (ZMod.val_injective N).eq_iff,
    ← (ZMod.val_injective q).eq_iff, ZMod.val_natCast]

noncomputable def stackCyclicEquiv {N q : ℕ} (hcop : Nat.Coprime N q) :
    ((Plane × ZMod N) × ZMod q) ≃+ (Plane × ZMod (N * q)) :=
  AddEquiv.prodAssoc.trans (AddEquiv.prodCongr (AddEquiv.refl Plane)
    (ZMod.chineseRemainder hcop).toAddEquiv.symm)

theorem mergePoint_correct {N q : ℕ} [NeZero N] [NeZero q]
    (hcop : Nat.Coprime N q) (f : NumericalPoint) (j : ℕ) :
    cyclicPoint (N * q) (f.1, mergeResidues N q f.2 j) =
      stackCyclicEquiv hcop (cyclicPoint N f, (j : ZMod q)) := by
  rw [mergeResidues_correct hcop]
  exact Prod.ext rfl (ZMod.natCast_zmod_val _)

abbrev StackData := ℕ × PartitionCertificate × List (List NumericalPoint)

/-- Stack a variable finite family using its numerical coloring certificate. -/
def stackCodes (d : StackData) : List NumericalPoint :=
  (List.range d.2.2.length).flatMap fun i =>
    (d.2.2.getD i []).flatMap fun f =>
      ((List.range d.2.1.1).filter fun j => decide (d.2.1.2.getD j 0 = i)).map fun j =>
        (f.1, mergeResidues d.1 d.2.1.1 f.2 j)

theorem stackCodes_primrec : Primrec stackCodes := by
  unfold stackCodes
  fun_prop

noncomputable def stackParts (s q : ℕ) [NeZero q] (cs : List ℕ) : Fin s → Finset (ZMod q) :=
  fun i => Finset.univ.filter fun j => cs.getD j.val 0 = i.val

theorem stackCodes_correct {N q : ℕ} [NeZero N] [NeZero q]
    (hcop : Nat.Coprime N q) (cs : List ℕ) (Fs : List (List NumericalPoint)) :
    cyclicTileSet (N * q) (stackCodes (N, (q, cs), Fs)) =
      (Stacking.stack (fun i : Fin Fs.length => cyclicTileSet N (Fs.getD i.val []))
        (stackParts Fs.length q cs)).image (stackCyclicEquiv hcop) := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨i, hi, p, hp, j, hj, rfl⟩ := (by
      simpa only [List.mem_toFinset, stackCodes, List.mem_flatMap, List.mem_map] using hf :
        ∃ i ∈ List.range Fs.length, ∃ p ∈ Fs.getD i [],
          ∃ j ∈ (List.range q).filter (fun j => decide (cs.getD j 0 = i)),
            (p.1, mergeResidues N q p.2 j) = f)
    have hjq := List.mem_range.mp (List.mem_filter.mp hj).1
    have hjc := of_decide_eq_true (List.mem_filter.mp hj).2
    apply Finset.mem_image.mpr
    refine ⟨(cyclicPoint N p, (j : ZMod q)), Stacking.mem_stack.mpr ?_,
      (mergePoint_correct hcop p j).symm⟩
    refine ⟨⟨i, List.mem_range.mp hi⟩, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr hp, rfl⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hjq] using hjc
  · intro hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨i, hf, he⟩ := Stacking.mem_stack.mp hp
    obtain ⟨f, hf, hpoint⟩ := Finset.mem_image.mp hf
    have hc := (Finset.mem_filter.mp he).2
    have hmerge : cyclicPoint (N * q) (f.1, mergeResidues N q f.2 p.2.val) =
        stackCyclicEquiv hcop p := by
      rw [mergePoint_correct hcop, ZMod.natCast_zmod_val, hpoint]
    apply Finset.mem_image.mpr
    refine ⟨(f.1, mergeResidues N q f.2 p.2.val), List.mem_toFinset.mpr ?_, hmerge⟩
    apply List.mem_flatMap.mpr
    refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr ?_⟩
    refine ⟨f, List.mem_toFinset.mp hf, List.mem_map.mpr ?_⟩
    refine ⟨p.2.val, List.mem_filter.mpr ⟨List.mem_range.mpr (ZMod.val_lt p.2), ?_⟩, rfl⟩
    exact decide_eq_true hc

/-- Stack data are selected by a total computable coloring search. -/
noncomputable def stackCompiler (d : ℕ × List (List NumericalPoint)) :
    ℕ × List NumericalPoint :=
  let c := partitionCertificate (d.2.length - 1, d.1)
  (d.1 * c.1, stackCodes (d.1, c, d.2))

theorem stackCompiler_computable : Computable stackCompiler := by
  have hp : Primrec (fun d : ℕ × List (List NumericalPoint) => (d.2.length - 1, d.1)) := by fun_prop
  have hc := partitionCertificate_computable.comp hp.to_comp
  have hinput := Computable.fst.pair (hc.pair Computable.snd)
  have hstack := stackCodes_primrec.to_comp.comp hinput
  have hq := Computable.fst.comp hc
  have horder := Primrec.nat_mul.to_comp.comp Computable.fst hq
  have hresult := horder.pair hstack
  exact hresult

theorem stackCompiler_pos (N : ℕ) (hN : 0 < N) (Fs : List (List NumericalPoint)) :
    0 < (stackCompiler (N, Fs)).1 := by
  have hc := partitionCertificate_valid (Fs.length - 1, N)
  exact Nat.mul_pos hN hc.1.pos

theorem stackCompiler_nonempty (N : ℕ) (Fs : List (List NumericalPoint))
    (hs : 0 < Fs.length) (hF : ∃ i : Fin Fs.length, Fs.getD i.val [] ≠ []) :
    (stackCompiler (N, Fs)).2 ≠ [] := by
  let c := partitionCertificate (Fs.length - 1, N)
  have hc : PartitionValid (Fs.length - 1) N c := partitionCertificate_valid _
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  obtain ⟨i, hi⟩ := hF
  have hcount : Fs.length - 1 + 1 = Fs.length := by omega
  let ν : Fin (Fs.length - 1 + 1) := ⟨i.val, by rw [hcount]; exact i.isLt⟩
  obtain ⟨j, hj⟩ := (certificateParts_correct _ _ _ hc).2.nonempty ν
  have hcolor : c.2.getD j.val 0 = i.val := (Finset.mem_filter.mp hj).2
  have hraw : ∃ f, f ∈ Fs.getD i.val [] := by
    cases he : Fs.getD i.val [] with
    | nil => exact False.elim (hi he)
    | cons f fs => exact ⟨f, by simp only [he, List.mem_cons_self]⟩
  obtain ⟨f, hf⟩ := hraw
  have hmem : (f.1, mergeResidues N c.1 f.2 j.val) ∈ stackCodes (N, c, Fs) := by
    apply List.mem_flatMap.mpr
    refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr ?_⟩
    refine ⟨f, hf, List.mem_map.mpr ?_⟩
    exact ⟨j.val, List.mem_filter.mpr ⟨List.mem_range.mpr (ZMod.val_lt j),
      decide_eq_true hcolor⟩, rfl⟩
  intro he
  change stackCodes (N, c, Fs) = [] at he
  simp only [he, List.not_mem_nil] at hmem

/-- The searched coloring gives the tiling equivalence for any nonempty finite
family of nonempty tiles. No tilability test occurs in the compiler. -/
theorem stackCompiler_correct (N : ℕ) (hN : 0 < N)
    (Fs : List (List NumericalPoint)) (hs : 0 < Fs.length)
    :
    (∃ A : Set (Plane × ZMod N), ∀ i : Fin Fs.length,
      Tiles (cyclicTileSet N (Fs.getD i.val [])) A) ↔
    ∃ B : Set (Plane × ZMod (stackCompiler (N, Fs)).1),
      Tiles (cyclicTileSet (stackCompiler (N, Fs)).1 (stackCompiler (N, Fs)).2) B := by
  let c := partitionCertificate (Fs.length - 1, N)
  have hc : PartitionValid (Fs.length - 1) N c := partitionCertificate_valid _
  have hq := hc.1
  have hlarge := hc.2.1
  letI : NeZero N := ⟨hN.ne'⟩
  letI : NeZero c.1 := ⟨hq.ne_zero⟩
  have hcount : Fs.length - 1 + 1 = Fs.length := by omega
  have hparts : Stacking.IsColorPartition (stackParts Fs.length c.1 c.2) ∧
      Stacking.HasFullDifferences (stackParts Fs.length c.1 c.2) := by
    have h : Stacking.IsColorPartition
        (fun i : Fin (Fs.length - 1 + 1) => (Finset.univ : Finset (ZMod c.1)).filter
          (fun j => c.2.getD j.val 0 = i.val)) ∧
        Stacking.HasFullDifferences
        (fun i : Fin (Fs.length - 1 + 1) => (Finset.univ : Finset (ZMod c.1)).filter
          (fun j => c.2.getD j.val 0 = i.val)) := certificateParts_correct _ _ _ hc
    rw [hcount] at h
    exact h
  have hcop : Nat.Coprime N c.1 := by
    apply Nat.Coprime.symm
    apply (hq.coprime_iff_not_dvd).mpr
    intro hd
    exact (not_le_of_gt hlarge) (Nat.le_of_dvd hN hd)
  have hEs := hparts.2.nonempty
  have hstack := Stacking.exists_tiles_stack_iff
    (F := fun i : Fin Fs.length => cyclicTileSet N (Fs.getD i.val []))
    hparts.1 hparts.2 hEs
  have he := stackCodes_correct hcop c.2 Fs
  have himage := exists_covers_image_iff (stackCyclicEquiv hcop)
    (Stacking.stack (fun i : Fin Fs.length => cyclicTileSet N (Fs.getD i.val []))
      (stackParts Fs.length c.1 c.2))
  have hfinal := hstack.trans himage
  rw [← he] at hfinal
  exact hfinal

end TranslationTiling.Compiler.Effective
