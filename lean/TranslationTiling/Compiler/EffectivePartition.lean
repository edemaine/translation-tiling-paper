import TranslationTiling.Compiler.EffectiveArithmetic
import TranslationTiling.Proofs.ComputableSearch
import TranslationTiling.Proofs.FullDifferencePartition
import TranslationTiling.Proofs.StackingContributions

set_option maxRecDepth 1000

namespace TranslationTiling.Compiler.Effective

/-- A cyclic coloring is encoded by its prime modulus and a list of color indices. -/
abbrev PartitionCertificate := ℕ × List ℕ

instance (priority := 2000) partitionCertificateEncodable : Encodable PartitionCertificate :=
  (inferInstance : Primcodable PartitionCertificate).toEncodable

private abbrev DifferenceParams := PartitionCertificate × (ℕ × ℕ)

def DifferenceWitness (q : ℕ) (cs : List ℕ) (i d x y : ℕ) : Prop :=
  cs.getD x 0 = i ∧ cs.getD y 0 = i ∧ x % q = (y + d) % q

def FullDifferenceTest (q : ℕ) (cs : List ℕ) (i d : ℕ) : Prop :=
  ∃ x ∈ List.range q, ∃ y ∈ List.range q, DifferenceWitness q cs i d x y

def PartitionValid (s lower : ℕ) (c : PartitionCertificate) : Prop :=
  c.1.Prime ∧ lower < c.1 ∧ c.2.length = c.1 ∧
    (∀ x ∈ List.range c.1, c.2.getD x 0 < s + 1) ∧
    ∀ i ∈ List.range (s + 1), ∀ d ∈ List.range c.1,
      FullDifferenceTest c.1 c.2 i d

instance (s lower : ℕ) (c : PartitionCertificate) : Decidable (PartitionValid s lower c) := by
  unfold PartitionValid FullDifferenceTest DifferenceWitness
  infer_instance

private theorem fullDifferenceTest_primrec :
    PrimrecPred (fun z : PartitionCertificate × (ℕ × ℕ) =>
      FullDifferenceTest z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hpair : PrimrecPred (fun z : (DifferenceParams × ℕ) × ℕ =>
      DifferenceWitness z.1.1.1.1 z.1.1.1.2 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) := by
    unfold DifferenceWitness
    fun_prop
  have hy : PrimrecPred (fun z : DifferenceParams × ℕ =>
      ∃ y ∈ List.range z.1.1.1,
        DifferenceWitness z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2 y) :=
    someList (by fun_prop) hpair
  exact someList (by fun_prop) hy

@[fun_prop] theorem fullDifferenceTest_rule {α : Type*} [Primcodable α]
    {q i d : α → ℕ} {cs : α → List ℕ}
    (hq : Primrec q) (hc : Primrec cs) (hi : Primrec i) (hd : Primrec d) :
    PrimrecPred (fun a => FullDifferenceTest (q a) (cs a) (i a) (d a)) :=
  fullDifferenceTest_primrec.comp ((hq.pair hc).pair (hi.pair hd))

theorem partitionValid_primrec :
    PrimrecPred (fun z : (ℕ × ℕ) × PartitionCertificate =>
      PartitionValid z.1.1 z.1.2 z.2) := by
  have hp : PrimrecPred (fun z : (ℕ × ℕ) × PartitionCertificate => z.2.1.Prime) :=
    nat_prime_primrec.comp (by fun_prop)
  unfold PartitionValid
  exact hp.and (by fun_prop)

theorem exists_partitionCertificate (s lower : ℕ) :
    ∃ c, PartitionValid s lower c := by
  classical
  obtain ⟨q, hq, hl, _, E, _, hpart, hfull⟩ :=
    Stacking.exists_fresh_prime_fullDifference_partition (s + 1) (by omega) ∅ lower
  letI : NeZero q := ⟨hq.ne_zero⟩
  let color : ZMod q → Fin (s + 1) := fun x => Classical.choose (hpart x)
  have hcolor (x : ZMod q) : x ∈ E (color x) := (Classical.choose_spec (hpart x)).1
  have hcolor_eq (x : ZMod q) (i : Fin (s + 1)) (hx : x ∈ E i) : color x = i :=
    ((hpart x).unique (hcolor x) hx)
  let cs := List.ofFn fun k : Fin q => (color (k.val : ZMod q)).val
  have hget (x : ℕ) (hx : x < q) : cs.getD x 0 = (color (x : ZMod q)).val := by
    simp [cs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx]
  refine ⟨(q, cs), hq, hl, by simp [cs], ?_, ?_⟩
  · intro x hx
    rw [hget x (List.mem_range.mp hx)]
    exact (color (x : ZMod q)).isLt
  · intro i hi d hd
    obtain ⟨x, hx, y, hy, he⟩ := hfull ⟨i, List.mem_range.mp hi⟩ (d : ZMod q)
    refine ⟨x.val, List.mem_range.mpr (ZMod.val_lt x),
      y.val, List.mem_range.mpr (ZMod.val_lt y), ?_, ?_, ?_⟩
    · rw [hget x.val (ZMod.val_lt x), ZMod.natCast_zmod_val, hcolor_eq x _ hx]
    · rw [hget y.val (ZMod.val_lt y), ZMod.natCast_zmod_val, hcolor_eq y _ hy]
    · have hxy : (x.val : ZMod q) = ((y.val + d : ℕ) : ZMod q) := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        simpa only [add_comm] using sub_eq_iff_eq_add.mp he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hxy

def decodePartitionCertificate (n : ℕ) : PartitionCertificate :=
  (Encodable.decode n).getD (0, [])

theorem decodePartitionCertificate_primrec : Primrec decodePartitionCertificate :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

private theorem exists_partitionCode (z : ℕ × ℕ) :
    ∃ n, PartitionValid z.1 z.2 (decodePartitionCertificate n) := by
  obtain ⟨c, hc⟩ := exists_partitionCertificate z.1 z.2
  refine ⟨Encodable.encode c, ?_⟩
  change PartitionValid z.1 z.2
    ((Encodable.decode (α := PartitionCertificate) (Encodable.encode c)).getD (0, []))
  rw [Encodable.encodek]
  exact hc

/-- The least finite coloring passing the arithmetic checker. -/
noncomputable def partitionCode (z : ℕ × ℕ) : ℕ :=
  leastWitness (fun z n => PartitionValid z.1 z.2 (decodePartitionCertificate n))
    exists_partitionCode z

theorem partitionCode_computable : Computable partitionCode :=
  leastWitness_computable _
    ((partitionValid_primrec.comp
      (Primrec.pair Primrec.fst (decodePartitionCertificate_primrec.comp Primrec.snd))).computablePred) _

noncomputable def partitionCertificate (z : ℕ × ℕ) : PartitionCertificate :=
  decodePartitionCertificate (partitionCode z)

theorem partitionCertificate_computable : Computable partitionCertificate :=
  decodePartitionCertificate_primrec.to_comp.comp partitionCode_computable

theorem partitionCertificate_valid (z : ℕ × ℕ) :
    PartitionValid z.1 z.2 (partitionCertificate z) := by
  unfold partitionCertificate partitionCode leastWitness
  exact @Nat.find_spec (fun n => PartitionValid z.1 z.2 (decodePartitionCertificate n))
    (Classical.decPred _) (exists_partitionCode z)

noncomputable def certificateParts (s q : ℕ) [NeZero q] (cs : List ℕ) :
    Fin (s + 1) → Finset (ZMod q) := fun i =>
  Finset.univ.filter fun x => cs.getD x.val 0 = i.val

theorem certificateParts_correct (s lower : ℕ) (c : PartitionCertificate)
    (hc : PartitionValid s lower c) :
    letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
    Stacking.IsColorPartition (certificateParts s c.1 c.2) ∧
      Stacking.HasFullDifferences (certificateParts s c.1 c.2) := by
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  obtain ⟨_, _, _, hbound, hfull⟩ := hc
  constructor
  · intro x
    have hx := hbound x.val (List.mem_range.mpr (ZMod.val_lt x))
    refine ⟨⟨c.2.getD x.val 0, hx⟩, by simp [certificateParts], ?_⟩
    intro i hi
    apply Fin.ext
    exact (Finset.mem_filter.mp hi).2.symm
  · intro i d
    obtain ⟨x, hx, y, hy, hxi, hyi, he⟩ :=
      hfull i.val (List.mem_range.mpr i.isLt) d.val (List.mem_range.mpr (ZMod.val_lt d))
    have hxq := List.mem_range.mp hx
    have hyq := List.mem_range.mp hy
    refine ⟨(x : ZMod c.1), ?_, (y : ZMod c.1), ?_, ?_⟩
    · simpa [certificateParts, ZMod.val_natCast, Nat.mod_eq_of_lt hxq] using hxi
    · simpa [certificateParts, ZMod.val_natCast, Nat.mod_eq_of_lt hyq] using hyi
    · have hxy : (x : ZMod c.1) = ((y + d.val : ℕ) : ZMod c.1) := by
        apply ZMod.val_injective c.1
        simpa only [ZMod.val_natCast] using he
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at hxy
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hxy)

/-- The computably searched certificate supplies precisely the partition needed
by stacking, for any positive number of equations. -/
theorem effective_partition (s : ℕ) (hs : 0 < s) (lower : ℕ) :
    ∃ q : ℕ, q.Prime ∧ lower < q ∧
      ∃ E : Fin s → Finset (ZMod q),
        Stacking.IsColorPartition E ∧ Stacking.HasFullDifferences E := by
  let c := partitionCertificate (s - 1, lower)
  have hc := partitionCertificate_valid (s - 1, lower)
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  have hsize : s - 1 + 1 = s := by omega
  let e : Fin (s - 1 + 1) ≃ Fin s := finCongr hsize
  let P := certificateParts (s - 1) c.1 c.2
  obtain ⟨hpart, hfull⟩ := certificateParts_correct (s - 1) lower c hc
  refine ⟨c.1, hc.1, hc.2.1, (fun i => P (e.symm i)), ?_, ?_⟩
  · intro x
    obtain ⟨i, hi, hu⟩ := hpart x
    refine ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi, ?_⟩
    intro j hj
    have hji : e.symm j = i := hu _ hj
    exact (e.apply_symm_apply j).symm.trans (congrArg e hji)
  · intro i d
    exact hfull (e.symm i) d

end TranslationTiling.Compiler.Effective
