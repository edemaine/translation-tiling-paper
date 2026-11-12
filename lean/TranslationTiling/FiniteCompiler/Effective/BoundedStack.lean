import TranslationTiling.Compiler.EffectiveStacking
import TranslationTiling.Compiler.ClosedStackBound
import TranslationTiling.FiniteCompiler.StackBound
import TranslationTiling.FiniteCompiler.Effective.BitCode

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section

private theorem exists_bounded_partition (s lower X : ℕ)
    (hs : s + 1 ≤ X) (hN : lower ≤ X) :
    ∃ c : PartitionCertificate, PartitionValid s lower c ∧ c.1 ≤ 2 * (8 * X ^ 5 + X + 3) := by
  classical
  let threshold := 8 * X ^ 5 + X + 3
  obtain ⟨q,hq,hqlarge,hqbound⟩ := Nat.bertrand threshold (by dsimp [threshold]; omega)
  have hlarge : lower < q := by dsimp [threshold] at hqlarge; omega
  have hbig : 8 * (s + 1) ^ 5 + 3 ≤ q := by
    have hp := Nat.pow_le_pow_left hs 5
    dsimp [threshold] at hqlarge
    omega
  obtain ⟨E,hpart,hfull⟩ := Compiler.Size.partition_at_prime (s + 1) q (by omega) hq hbig
  letI : NeZero q := ⟨hq.ne_zero⟩
  let color : ZMod q → Fin (s + 1) := fun x => Classical.choose (hpart x)
  have hcolor (x : ZMod q) : x ∈ E (color x) := (Classical.choose_spec (hpart x)).1
  have hcolor_eq (x : ZMod q) (i : Fin (s + 1)) (hx : x ∈ E i) : color x = i :=
    ((hpart x).unique (hcolor x) hx)
  let cs := List.ofFn fun k : Fin q => (color (k.val : ZMod q)).val
  have hget (x : ℕ) (hx : x < q) : cs.getD x 0 = (color (x : ZMod q)).val := by
    simp [cs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx]
  refine ⟨(q, cs), ?_, hqbound⟩
  refine ⟨hq, hlarge, by simp [cs], ?_, ?_⟩
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

/-- The extra bound on the searched certificate preserves the optimized
stacking modulus estimate. -/
def BoundedPartitionValid (d : ℕ × ℕ × ℕ) (c : PartitionCertificate) : Prop :=
  if d.1 + 1 ≤ d.2.2 ∧ d.2.1 ≤ d.2.2 then
    PartitionValid d.1 d.2.1 c ∧ c.1 ≤ 2 * (8 * d.2.2 ^ 5 + d.2.2 + 3)
  else c = (0,[])

instance (d : ℕ × ℕ × ℕ) (c : PartitionCertificate) : Decidable (BoundedPartitionValid d c) := by
  unfold BoundedPartitionValid
  infer_instance

theorem boundedPartitionValid_primrec :
    PrimrecPred (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate => BoundedPartitionValid z.1 z.2) := by
  have hr : PrimrecPred (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate =>
      z.1.1 + 1 ≤ z.1.2.2 ∧ z.1.2.1 ≤ z.1.2.2) := by fun_prop
  have hproj : Primrec (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate =>
      ((z.1.1,z.1.2.1),z.2)) := by fun_prop
  have hp : PrimrecPred (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate =>
      PartitionValid z.1.1 z.1.2.1 z.2) := partitionValid_primrec.comp hproj
  have hb : PrimrecPred (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate =>
      z.2.1 ≤ 2 * (8 * z.1.2.2 ^ 5 + z.1.2.2 + 3)) := by fun_prop
  have hd : PrimrecPred (fun z : (ℕ × ℕ × ℕ) × PartitionCertificate => z.2 = (0,[])) := by
    fun_prop
  apply ((hr.and (hp.and hb)).or (hr.not.and hd)).of_eq
  intro z
  unfold BoundedPartitionValid
  by_cases h : z.1.1 + 1 ≤ z.1.2.2 ∧ z.1.2.1 ≤ z.1.2.2 <;>
    simp only [h, ↓reduceIte, not_true_eq_false, not_false_eq_true, true_and, false_and,
      false_or, or_false]

private theorem exists_boundedPartitionCode (d : ℕ × ℕ × ℕ) :
    ∃ n, BoundedPartitionValid d (decodePartitionCertificate n) := by
  classical
  by_cases h : d.1 + 1 ≤ d.2.2 ∧ d.2.1 ≤ d.2.2
  · obtain ⟨c,hc⟩ := exists_bounded_partition d.1 d.2.1 d.2.2 h.1 h.2
    refine ⟨Encodable.encode c,?_⟩
    simpa only [BoundedPartitionValid, if_pos h, decodePartitionCertificate,
      Encodable.encodek, Option.getD_some] using hc
  · refine ⟨Encodable.encode (0,([] : List ℕ)),?_⟩
    simp only [BoundedPartitionValid, if_neg h, decodePartitionCertificate,
      Encodable.encodek, Option.getD_some]

def boundedPartitionCode (d : ℕ × ℕ × ℕ) : ℕ :=
  leastWitness (fun d n => BoundedPartitionValid d (decodePartitionCertificate n))
    exists_boundedPartitionCode d

theorem boundedPartitionCode_computable : Computable boundedPartitionCode :=
  leastWitness_computable _
    ((boundedPartitionValid_primrec.comp
      (Primrec.fst.pair (decodePartitionCertificate_primrec.comp Primrec.snd))).computablePred) _

def boundedPartition (d : ℕ × ℕ × ℕ) : PartitionCertificate :=
  decodePartitionCertificate (boundedPartitionCode d)

theorem boundedPartition_computable : Computable boundedPartition :=
  decodePartitionCertificate_primrec.to_comp.comp boundedPartitionCode_computable

theorem boundedPartition_valid (d : ℕ × ℕ × ℕ) : BoundedPartitionValid d (boundedPartition d) := by
  unfold boundedPartition boundedPartitionCode leastWitness
  exact @Nat.find_spec (fun n => BoundedPartitionValid d (decodePartitionCertificate n))
    (Classical.decPred _) (exists_boundedPartitionCode d)

/-- Numerical stacking with a checked polynomial modulus bound. -/
def boundedStack (d : ℕ × ℕ × List CyclicTile) : CyclicTileData :=
  let c := boundedPartition (d.2.2.length - 1,d.2.1,d.1)
  (d.2.1 * c.1, stackCodes (d.2.1,c,d.2.2))

theorem boundedStack_computable : Computable boundedStack := by
  have hp : Primrec (fun d : ℕ × ℕ × List CyclicTile => (d.2.2.length - 1,d.2.1,d.1)) := by
    fun_prop
  have hc := boundedPartition_computable.comp hp.to_comp
  have horder := Primrec.nat_mul.to_comp.comp (Computable.fst.comp Computable.snd)
    (Computable.fst.comp hc)
  have hdata := (Computable.fst.comp Computable.snd).pair
    (hc.pair (Computable.snd.comp Computable.snd))
  exact horder.pair (stackCodes_primrec.to_comp.comp hdata)

/-- The original stacking proof works with any valid numerical certificate. -/
theorem stackCodes_correct_valid (N : ℕ) (hN : 0 < N) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (c : PartitionCertificate) (hc : PartitionValid (Fs.length - 1) N c) :
    (∃ A : Set (Plane × ZMod N), ∀ i : Fin Fs.length,
      Tiles (cyclicTileSet N (Fs.getD i.val [])) A) ↔
    ∃ B : Set (Plane × ZMod (N * c.1)),
      Tiles (cyclicTileSet (N * c.1) (stackCodes (N,c,Fs))) B := by
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

theorem boundedPartition_spec (s N X : ℕ) (hs : s + 1 ≤ X) (hN : N ≤ X) :
    PartitionValid s N (boundedPartition (s,N,X)) ∧
      (boundedPartition (s,N,X)).1 ≤ 2 * (8 * X ^ 5 + X + 3) := by
  have h := boundedPartition_valid (s,N,X)
  simpa only [BoundedPartitionValid, if_pos (And.intro hs hN)] using h

theorem boundedStack_correct (X N : ℕ) (hN : 0 < N) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (hX : Fs.length ≤ X) (hNX : N ≤ X) :
    (∃ A : Set (Plane × ZMod N), ∀ i : Fin Fs.length,
      Tiles (cyclicTileSet N (Fs.getD i.val [])) A) ↔
    ∃ B : Set (Plane × ZMod (boundedStack (X,N,Fs)).1),
      Tiles (cyclicTileSet (boundedStack (X,N,Fs)).1 (boundedStack (X,N,Fs)).2) B := by
  exact stackCodes_correct_valid N hN Fs hs _
    (boundedPartition_spec (Fs.length - 1) N X (by omega) hNX).1

theorem boundedStack_modulus_bound (X N : ℕ) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (hX : Fs.length ≤ X) (hNX : N ≤ X) :
    (boundedStack (X,N,Fs)).1 ≤ Size.stackPolynomial X := by
  have hq := (boundedPartition_spec (Fs.length - 1) N X (by omega) hNX).2
  exact Nat.mul_le_mul hNX hq

theorem boundedStack_pos (X N : ℕ) (hN : 0 < N) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (hX : Fs.length ≤ X) (hNX : N ≤ X) :
    0 < (boundedStack (X,N,Fs)).1 :=
  Nat.mul_pos hN (boundedPartition_spec (Fs.length - 1) N X (by omega) hNX).1.1.pos

end
end TranslationTiling.FiniteCompiler.Effective
