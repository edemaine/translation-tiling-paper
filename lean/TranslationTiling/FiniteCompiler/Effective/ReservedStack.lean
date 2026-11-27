import TranslationTiling.FiniteCompiler.Effective.FreshStack
import TranslationTiling.Proofs.BlockDifferenceBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section

def reservedThreshold (X P : ℕ) : ℕ := 20*X^2*Stacking.differenceLog X+P+3

def reservedCap (X P : ℕ) : ℕ := 2*reservedThreshold X P

def reservedPrimeThreshold (X P : ℕ) : ℕ :=
  (if 2313≤X then 10 else 20)*X^2*Stacking.differenceLog X+P+3

theorem reservedPrimeThreshold_le (X P : ℕ) :
    reservedPrimeThreshold X P ≤ reservedThreshold X P := by
  unfold reservedPrimeThreshold reservedThreshold
  split <;> gcongr <;> decide

def reservedPrimeCap (X P : ℕ) : ℕ := primeAbove (reservedPrimeThreshold X P + 1)

theorem reservedPrimeCap_le_of_prime {X P q : ℕ}
    (hq : q.Prime) (h : reservedPrimeThreshold X P < q) : reservedPrimeCap X P ≤ q := by
  unfold reservedPrimeCap primeAbove leastWitness
  exact @Nat.find_min' (fun z => z.Prime ∧ reservedPrimeThreshold X P + 1 ≤ z)
    (Classical.decPred _) _ q ⟨hq,h⟩

theorem reservedPrimeCap_le_twice_threshold (X P : ℕ) :
    reservedPrimeCap X P ≤ 2*reservedPrimeThreshold X P := by
  obtain ⟨q,hq,hlo,hhi⟩ := Nat.bertrand (reservedPrimeThreshold X P)
    (by unfold reservedPrimeThreshold; omega)
  exact (reservedPrimeCap_le_of_prime hq hlo).trans hhi

theorem reservedPrimeCap_le_reservedCap (X P : ℕ) : reservedPrimeCap X P ≤ reservedCap X P :=
  (reservedPrimeCap_le_twice_threshold X P).trans (Nat.mul_le_mul_left 2 (reservedPrimeThreshold_le X P))

theorem reservedPrimeCap_lt (X P : ℕ) : reservedPrimeThreshold X P < reservedPrimeCap X P :=
  (primeAbove_spec _).2

theorem reservedPrimeCap_prime (X P : ℕ) : (reservedPrimeCap X P).Prime :=
  (primeAbove_spec _).1

abbrev ReserveData := FreshPartitionData × ℕ × ℕ

def ReserveReady (d : ReserveData) : Prop :=
  FreshReady d.1 ∧ d.2.1<d.1.1+1 ∧ 5≤Stacking.differenceLog d.1.2.2.2 ∧
    d.1.2.2.1+3≤2*d.1.2.2.2^2

def Reserves (c : PartitionCertificate) (i R : ℕ) : Prop :=
  ∀ j ∈ List.range ((c.1+2)/3), c.2.getD ((R*(3*j))%c.1) 0=i

private def ReserveReadyAt (d : ReserveData) (q : ℕ) : Prop :=
  ReserveReady d ∧ q.Prime ∧ reservedPrimeThreshold d.1.2.2.2 d.1.2.2.1 < q ∧
    q ≤ 2*reservedPrimeThreshold d.1.2.2.2 d.1.2.2.1

private def ReservedValid (d : ReserveData × ℕ) (c : PartitionCertificate) : Prop :=
  if ReserveReadyAt d.1 d.2 then PartitionValid d.1.1.1 d.1.1.2.2.1 c ∧
    c.1 = d.2 ∧ Reserves c d.1.2.1 d.1.2.2
  else c=(0,[])

@[fun_prop] theorem reserveReady_primrec : PrimrecPred ReserveReady := by
  unfold ReserveReady Stacking.differenceLog
  have h := freshReady_primrec.comp (Primrec.fst : Primrec (Prod.fst : ReserveData → FreshPartitionData))
  have hl := natLog_primrec 2 (by decide)
  fun_prop

@[fun_prop] theorem reserves_primrec :
    PrimrecPred (fun z : PartitionCertificate × ℕ × ℕ => Reserves z.1 z.2.1 z.2.2) := by
  unfold Reserves
  fun_prop

@[fun_prop] private theorem reservedPrimeThreshold_primrec :
    Primrec (fun d : ℕ × ℕ => reservedPrimeThreshold d.1 d.2) := by
  unfold reservedPrimeThreshold Stacking.differenceLog
  have hl := natLog_primrec 2 (by decide)
  fun_prop

private theorem reserveReadyAt_primrec :
    PrimrecPred (fun d : ReserveData × ℕ => ReserveReadyAt d.1 d.2) := by
  have hr := reserveReady_primrec.comp (Primrec.fst : Primrec (Prod.fst : ReserveData × ℕ → ReserveData))
  have hp := nat_prime_primrec.comp (Primrec.snd : Primrec (Prod.snd : ReserveData × ℕ → ℕ))
  have hM : Primrec (fun d : ReserveData × ℕ => reservedPrimeThreshold d.1.1.2.2.2 d.1.1.2.2.1) := by
    exact reservedPrimeThreshold_primrec.comp (show Primrec (fun d : ReserveData × ℕ => (d.1.1.2.2.2,d.1.1.2.2.1)) by fun_prop)
  unfold ReserveReadyAt
  exact hr.and (hp.and ((Primrec.nat_lt.comp hM Primrec.snd).and
    (Primrec.nat_le.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hM))))

private theorem reservedValid_primrec :
    PrimrecPred (fun z : (ReserveData × ℕ) × PartitionCertificate => ReservedValid z.1 z.2) := by
  have hr := reserveReadyAt_primrec.comp
    (Primrec.fst : Primrec (Prod.fst : (ReserveData × ℕ) × PartitionCertificate → ReserveData × ℕ))
  have hp := partitionValid_primrec.comp (show
    Primrec (fun z : (ReserveData × ℕ) × PartitionCertificate => ((z.1.1.1.1,z.1.1.1.2.2.1),z.2))
    by fun_prop)
  have hb : PrimrecPred (fun z : (ReserveData × ℕ) × PartitionCertificate => z.2.1=z.1.2) := by
    fun_prop
  have hs := reserves_primrec.comp (show Primrec (fun z : (ReserveData × ℕ) × PartitionCertificate =>
    (z.2,z.1.1.2.1,z.1.1.2.2)) by fun_prop)
  have hd : PrimrecPred (fun z : (ReserveData × ℕ) × PartitionCertificate => z.2=(0,[])) := by fun_prop
  apply ((hr.and (hp.and (hb.and hs))).or (hr.not.and hd)).of_eq
  intro z
  unfold ReservedValid
  by_cases h : ReserveReadyAt z.1.1 z.1.2 <;> simp [h]

private theorem exists_reserved_partition_at (s P X i R q : ℕ) (hs : s+1≤X) (hi : i<s+1)
    (hL : 5≤Stacking.differenceLog X) (hP : P+3≤2*X^2)
    (hq : q.Prime) (hlo : reservedPrimeThreshold X P < q) (hhi : q ≤ 2*reservedPrimeThreshold X P) :
    ∃ c : PartitionCertificate, PartitionValid s P c ∧ c.1=q ∧ Reserves c i R := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hlarge : P<q := by unfold reservedPrimeThreshold at hlo; omega
  let f (j : ℕ) : ZMod q := (R*(3*j):ℕ)
  let D := (Finset.range ((q+2)/3)).image f
  have hD : D.card≤(q+2)/3 := Finset.card_image_le.trans (by simp)
  have hpart : ∃ E : Fin (s+1) → Finset (ZMod q),
      Stacking.IsColorPartition E ∧ Stacking.HasFullDifferences E ∧ D⊆E ⟨i,hi⟩ := by
    by_cases hX : 2313≤X
    · simp only [reservedPrimeThreshold,if_pos hX] at hlo hhi
      exact Stacking.partition_reserved_blocks (s+1) X P q (by omega) hs hX hP hq hlo hhi D hD ⟨i,hi⟩
    · simp only [reservedPrimeThreshold,if_neg hX] at hlo hhi
      exact Stacking.partition_reserved (s+1) X P q (by omega) hs hP hL hq hlo hhi D hD ⟨i,hi⟩
  obtain ⟨E,hE,hfull,hreserve⟩ := hpart
  obtain ⟨cs,hcs,hmem⟩ := partition_certificate_of_membership s P q hq hlarge E hE hfull
  refine ⟨(q,cs),hcs,rfl,?_⟩
  intro j hj
  have hm := hreserve (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (List.mem_range.mp hj),rfl⟩)
  simpa only [f,ZMod.val_natCast] using hmem (f j) ⟨i,hi⟩ hm

theorem exists_reserved_partition (s P X i R : ℕ) (hs : s+1≤X) (hi : i<s+1)
    (hL : 5≤Stacking.differenceLog X) (hP : P+3≤2*X^2) :
    ∃ c : PartitionCertificate, PartitionValid s P c ∧ c.1≤reservedCap X P ∧ Reserves c i R := by
  obtain ⟨c,hc,hq,hres⟩ := exists_reserved_partition_at s P X i R (reservedPrimeCap X P)
    hs hi hL hP (reservedPrimeCap_prime X P) (reservedPrimeCap_lt X P)
    (reservedPrimeCap_le_twice_threshold X P)
  exact ⟨c,hc,hq.le.trans (reservedPrimeCap_le_reservedCap X P),hres⟩

private theorem exists_reservedPartitionCode (d : ReserveData × ℕ) :
    ∃ n, ReservedValid d (decodePartitionCertificate n) := by
  by_cases h : ReserveReadyAt d.1 d.2
  · obtain ⟨hr,hq,hlo,hhi⟩ := h
    obtain ⟨c,hc⟩ := exists_reserved_partition_at d.1.1.1 d.1.1.2.2.1 d.1.1.2.2.2
      d.1.2.1 d.1.2.2 d.2 hr.1.2.1 hr.2.1 hr.2.2.1 hr.2.2.2 hq hlo hhi
    refine ⟨Encodable.encode c,?_⟩
    simpa only [ReservedValid,if_pos (show ReserveReadyAt d.1 d.2 from ⟨hr,hq,hlo,hhi⟩),
      decodePartitionCertificate,Encodable.encodek,Option.getD_some] using hc
  · exact ⟨Encodable.encode (0,([]:List ℕ)),by simp [ReservedValid,h,decodePartitionCertificate]⟩

private def reserveWithPrime (d : ReserveData) : ReserveData × ℕ :=
  (d,reservedPrimeCap d.1.2.2.2 d.1.2.2.1)

def reservedPartition (d : ReserveData) : PartitionCertificate :=
  decodePartitionCertificate (leastWitness (fun d n => ReservedValid d (decodePartitionCertificate n))
    exists_reservedPartitionCode (reserveWithPrime d))

theorem reservedPartition_computable : Computable reservedPartition := by
  have h : Primrec (fun d : ReserveData => reservedPrimeThreshold d.1.2.2.2 d.1.2.2.1+1) := by
    exact Primrec.succ.comp (reservedPrimeThreshold_primrec.comp (show Primrec (fun d : ReserveData => (d.1.2.2.2,d.1.2.2.1)) by fun_prop))
  have hd : Computable reserveWithPrime := Computable.id.pair (primeAbove_computable.comp h.to_comp)
  exact (decodePartitionCertificate_primrec.to_comp.comp
    (leastWitness_computable _ ((reservedValid_primrec.comp
      (Primrec.fst.pair (decodePartitionCertificate_primrec.comp Primrec.snd))).computablePred) _)).comp hd

theorem reservedPartition_prime_spec (d : ReserveData) (h : ReserveReady d) :
    PartitionValid d.1.1 d.1.2.2.1 (reservedPartition d) ∧
    d.1.2.1.Coprime (reservedPartition d).1 ∧
    (reservedPartition d).1≤reservedPrimeCap d.1.2.2.2 d.1.2.2.1 ∧
    Reserves (reservedPartition d) d.2.1 d.2.2 := by
  have hv : ReservedValid (reserveWithPrime d) (reservedPartition d) := by
    unfold reservedPartition leastWitness
    exact @Nat.find_spec (fun n => ReservedValid (reserveWithPrime d) (decodePartitionCertificate n))
      (Classical.decPred _) (exists_reservedPartitionCode (reserveWithPrime d))
  have hr : ReserveReadyAt (reserveWithPrime d).1 (reserveWithPrime d).2 :=
    ⟨h,reservedPrimeCap_prime ..,reservedPrimeCap_lt ..,reservedPrimeCap_le_twice_threshold ..⟩
  simp only [ReservedValid] at hv
  rw [if_pos hr] at hv
  exact ⟨hv.1,coprime_of_primeBound h.1.1 h.1.2.2.2 hv.1.1 hv.1.2.1,hv.2.1.le,hv.2.2⟩

theorem reservedPartition_spec (d : ReserveData) (h : ReserveReady d) :
    PartitionValid d.1.1 d.1.2.2.1 (reservedPartition d) ∧
    d.1.2.1.Coprime (reservedPartition d).1 ∧
    (reservedPartition d).1≤reservedCap d.1.2.2.2 d.1.2.2.1 ∧
    Reserves (reservedPartition d) d.2.1 d.2.2 := by
  obtain ⟨hv,hcop,hq,hres⟩ := reservedPartition_prime_spec d h
  exact ⟨hv,hcop,hq.trans (reservedPrimeCap_le_reservedCap ..),hres⟩

/-- Every forward interval of the given length meets the column at horizontal zero. -/
def HasForwardColumn (d : CyclicTileData) (U : ℕ) : Prop :=
  ∀ z : ℕ, ∃ v : ℕ, z≤v ∧ v≤z+U ∧
    ((0:Plane),(v:ZMod d.1))∈cyclicTileSet d.1 d.2

theorem stack_hasForwardColumn (N P : ℕ) (Fs : List CyclicTile) (c : PartitionCertificate)
    (hc : PartitionValid (Fs.length-1) P c) (hcop : Nat.Coprime N c.1)
    (hN : 0<N) (i : Fin Fs.length) (R : ℕ) (hR : 0<R)
    (hr : Reserves c i.val R)
    (hker : ∀ k : ℤ, (((0:Plane),((R:ℤ)*k:ℤ)) : Plane × ZMod N)∈
      cyclicTileSet N (Fs.getD i.val [])) :
    HasForwardColumn (N*c.1,stackCodes (N,c,Fs)) (3*R) := by
  letI : NeZero N := ⟨hN.ne'⟩
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  intro z
  let q := c.1
  let j := z/R+1
  let r := j%q
  let next := 3*((r+2)/3)
  have hq : 0<q := hc.1.pos
  have hrq : r<q := Nat.mod_lt _ hq
  have hn : r≤next ∧ next≤r+2 := by dsimp [next]; omega
  let t := if next<q then next else q
  have ht : r≤t ∧ t≤r+2 := by dsimp only [t]; split <;> omega
  let k := q*(j/q)+t
  have hk : j≤k ∧ k≤j+2 := by
    have hh : r+q*(j/q)=j := Nat.mod_add_div _ _
    dsimp only [k]
    omega
  have hkr : ∃ l< (q+2)/3, (k:ZMod q)=((3*l:ℕ):ZMod q) := by
    unfold k t
    push_cast
    simp only [ZMod.natCast_self,zero_mul,zero_add]
    split
    · rename_i hh
      refine ⟨(r+2)/3,?_ ,by simp [next,Nat.cast_mul]⟩
      dsimp [next] at hh
      omega
    · exact ⟨0,by omega,by simp⟩
  refine ⟨R*k,?_,?_,?_⟩
  · have h := Nat.mul_le_mul_left R hk.1
    have h' := Nat.mod_add_div z R
    have hz := Nat.mod_lt z hR
    dsimp only [j] at h
    rw [Nat.mul_add,Nat.mul_one] at h
    omega
  · calc
      R*k ≤ R*(j+2) := Nat.mul_le_mul_left _ hk.2
      _ = R*(z/R)+3*R := by rw [show j+2=z/R+3 from rfl, Nat.mul_add, Nat.mul_comm R 3]
      _ ≤ z+3*R := Nat.add_le_add_right (Nat.mul_div_le z R) _
  · obtain ⟨l,hl,he⟩ := hkr
    rw [stackCodes_correct hcop c.2 Fs]
    let e := ZMod.chineseRemainder hcop
    have hval : ((R*k:ℕ):ZMod q)=((R*(3*l):ℕ):ZMod q) := by simp only [Nat.cast_mul,he]
    refine Finset.mem_image.mpr
      ⟨(((0:Plane),((R*k:ℕ):ZMod N)),((R*k:ℕ):ZMod q)),?_,?_⟩
    · apply Stacking.mem_stack.mpr
      refine ⟨i,?_,?_⟩
      · exact_mod_cast hker k
      · simp only [stackParts,Finset.mem_filter,Finset.mem_univ,true_and,hval,ZMod.val_natCast]
        exact hr l (List.mem_range.mpr hl)
    · have h : e.symm (((R*k:ℕ):ZMod N),((R*k:ℕ):ZMod q)) =
          ((R*k:ℕ):ZMod (N*q)) := by
        apply e.symm_apply_eq.mpr
        rw [map_natCast]
        rfl
      exact Prod.ext (rfl : (0:Plane)=0) h

end
end TranslationTiling.FiniteCompiler.Effective
