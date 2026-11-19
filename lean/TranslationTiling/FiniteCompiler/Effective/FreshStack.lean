import TranslationTiling.FiniteCompiler.Effective.MixedInput
import TranslationTiling.FiniteCompiler.Effective.BoundedStack
import TranslationTiling.FiniteCompiler.Effective.StackSupport
import TranslationTiling.Proofs.LogDifferenceBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Every prime divisor of the finite factor is below this numerical cap. -/
def PrimeBound (N P : ℕ) : Prop :=
  ∀ p ∈ List.range (N+1), ¬p.Prime ∨ ¬p ∣ N ∨ p ≤ P

@[fun_prop] theorem primeBound_primrec : PrimrecPred (fun z : ℕ × ℕ => PrimeBound z.1 z.2) := by
  unfold PrimeBound
  simp only [Nat.dvd_iff_mod_eq_zero]
  fun_prop

theorem coprime_of_primeBound {N P q : ℕ} (hN : 0<N) (hP : PrimeBound N P)
    (hq : q.Prime) (hlarge : P<q) : Nat.Coprime N q := by
  apply Nat.Coprime.symm
  apply (hq.coprime_iff_not_dvd).mpr
  intro hd
  have hle := Nat.le_of_dvd hN hd
  have hp := ((hP q (List.mem_range.mpr (by omega))).resolve_left (not_not.mpr hq)).resolve_left (not_not.mpr hd)
  omega

def freshCap (X P : ℕ) : ℕ := 2*Stacking.logPartitionThreshold X P

theorem partition_certificate (s P q : ℕ) (hq : q.Prime) (hlarge : P<q)
    (E : Fin (s+1) → Finset (ZMod q)) (hpart : Stacking.IsColorPartition E)
    (hfull : Stacking.HasFullDifferences E) :
    ∃ cs, PartitionValid s P (q,cs) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  let color : ZMod q → Fin (s+1) := fun x => Classical.choose (hpart x)
  have hcolor (x : ZMod q) : x ∈ E (color x) := (Classical.choose_spec (hpart x)).1
  have hcolor_eq (x : ZMod q) (i : Fin (s+1)) (hx : x ∈ E i) : color x=i :=
    (hpart x).unique (hcolor x) hx
  let cs := List.ofFn fun k : Fin q => (color (k.val:ZMod q)).val
  have hget (x : ℕ) (hx : x<q) : cs.getD x 0 = (color (x:ZMod q)).val := by
    simp [cs,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hx]
  refine ⟨cs,⟨hq,hlarge,by simp [cs],?_,?_⟩⟩
  · intro x hx
    rw [hget x (List.mem_range.mp hx)]
    exact (color (x:ZMod q)).isLt
  · intro i hi d hd
    obtain ⟨x,hx,y,hy,he⟩ := hfull ⟨i,List.mem_range.mp hi⟩ (d:ZMod q)
    refine ⟨x.val,List.mem_range.mpr (ZMod.val_lt x),y.val,List.mem_range.mpr (ZMod.val_lt y),?_,?_,?_⟩
    · rw [hget x.val (ZMod.val_lt x),ZMod.natCast_zmod_val,hcolor_eq x _ hx]
    · rw [hget y.val (ZMod.val_lt y),ZMod.natCast_zmod_val,hcolor_eq y _ hy]
    · have hh : (x.val:ZMod q)=((y.val+d:ℕ):ZMod q) := by
        rw [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
        simpa only [add_comm] using sub_eq_iff_eq_add.mp he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hh

private theorem exists_fresh_partition (s N P X : ℕ) (hN : 0<N) (hs : s+1≤X)
    (hP : P≤X^2) (hpr : PrimeBound N P) :
    ∃ c : PartitionCertificate, PartitionValid s P c ∧ Nat.Coprime N c.1 ∧ c.1 ≤ freshCap X P := by
  let threshold := Stacking.logPartitionThreshold X P
  obtain ⟨q,hq,hqlarge,hqbound⟩ := Nat.bertrand threshold (by dsimp [threshold,Stacking.logPartitionThreshold]; omega)
  have hlarge : P<q := by dsimp [threshold,Stacking.logPartitionThreshold] at hqlarge; omega
  have hcop := coprime_of_primeBound hN hpr hq hlarge
  obtain ⟨E,hpart,hfull⟩ := Stacking.partition_logarithmic (s+1) X P q (by omega) hs hP hq hqlarge hqbound
  obtain ⟨cs,hcs⟩ := partition_certificate s P q hq hlarge E hpart hfull
  exact ⟨(q,cs),hcs,hcop,hqbound⟩

abbrev FreshPartitionData := ℕ × ℕ × ℕ × ℕ

def FreshReady (d : FreshPartitionData) : Prop :=
  0<d.2.1 ∧ d.1+1≤d.2.2.2 ∧ d.2.2.1≤d.2.2.2^2 ∧ PrimeBound d.2.1 d.2.2.1

@[fun_prop] theorem freshReady_primrec : PrimrecPred FreshReady := by
  unfold FreshReady
  have hp : PrimrecPred (fun d : FreshPartitionData => PrimeBound d.2.1 d.2.2.1) := primeBound_primrec.comp (show Primrec (fun d : FreshPartitionData => (d.2.1,d.2.2.1)) by fun_prop)
  fun_prop

def FreshPartitionValid (d : FreshPartitionData) (c : PartitionCertificate) : Prop :=
  if FreshReady d then PartitionValid d.1 d.2.2.1 c ∧ c.1≤freshCap d.2.2.2 d.2.2.1
  else c=(0,[])

instance (d : FreshPartitionData) (c : PartitionCertificate) : Decidable (FreshPartitionValid d c) := by
  unfold FreshPartitionValid FreshReady PrimeBound
  infer_instance

@[fun_prop] theorem freshPartitionValid_primrec :
    PrimrecPred (fun z : FreshPartitionData × PartitionCertificate => FreshPartitionValid z.1 z.2) := by
  have hr : PrimrecPred (fun z : FreshPartitionData × PartitionCertificate => FreshReady z.1) := freshReady_primrec.comp Primrec.fst
  have hp : PrimrecPred (fun z : FreshPartitionData × PartitionCertificate => PartitionValid z.1.1 z.1.2.2.1 z.2) :=
    partitionValid_primrec.comp (show Primrec (fun z : FreshPartitionData × PartitionCertificate => ((z.1.1,z.1.2.2.1),z.2)) by fun_prop)
  have hb : PrimrecPred (fun z : FreshPartitionData × PartitionCertificate => z.2.1≤freshCap z.1.2.2.2 z.1.2.2.1) := by
    unfold freshCap Stacking.logPartitionThreshold Stacking.differenceLog
    have hl := natLog_primrec 2 (by decide)
    fun_prop
  have hd : PrimrecPred (fun z : FreshPartitionData × PartitionCertificate => z.2=(0,[])) := by fun_prop
  apply ((hr.and (hp.and hb)).or (hr.not.and hd)).of_eq
  intro z
  unfold FreshPartitionValid
  by_cases h : FreshReady z.1 <;> simp [h]

private theorem exists_freshPartitionCode (d : FreshPartitionData) :
    ∃ n, FreshPartitionValid d (decodePartitionCertificate n) := by
  by_cases h : FreshReady d
  · obtain ⟨c,hc⟩ := exists_fresh_partition d.1 d.2.1 d.2.2.1 d.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2
    refine ⟨Encodable.encode c,?_⟩
    simpa only [FreshPartitionValid,if_pos h,decodePartitionCertificate,Encodable.encodek,Option.getD_some] using And.intro hc.1 hc.2.2
  · refine ⟨Encodable.encode (0,([]:List ℕ)),?_⟩
    simp [FreshPartitionValid,h,decodePartitionCertificate]

def freshPartitionCode (d : FreshPartitionData) : ℕ :=
  leastWitness (fun d n => FreshPartitionValid d (decodePartitionCertificate n)) exists_freshPartitionCode d

theorem freshPartitionCode_computable : Computable freshPartitionCode :=
  leastWitness_computable _ ((freshPartitionValid_primrec.comp
    (Primrec.fst.pair (decodePartitionCertificate_primrec.comp Primrec.snd))).computablePred) _

def freshPartition (d : FreshPartitionData) : PartitionCertificate := decodePartitionCertificate (freshPartitionCode d)

theorem freshPartition_computable : Computable freshPartition :=
  decodePartitionCertificate_primrec.to_comp.comp freshPartitionCode_computable

theorem freshPartition_spec (d : FreshPartitionData) (h : FreshReady d) :
    PartitionValid d.1 d.2.2.1 (freshPartition d) ∧ Nat.Coprime d.2.1 (freshPartition d).1 ∧
      (freshPartition d).1≤freshCap d.2.2.2 d.2.2.1 := by
  have hv : FreshPartitionValid d (freshPartition d) := by
    unfold freshPartition freshPartitionCode leastWitness
    exact @Nat.find_spec _ (Classical.decPred _) (exists_freshPartitionCode d)
  have hc : PartitionValid d.1 d.2.2.1 (freshPartition d) ∧ (freshPartition d).1 ≤ freshCap d.2.2.2 d.2.2.1 := by
    simpa only [FreshPartitionValid,if_pos h] using hv
  exact ⟨hc.1,coprime_of_primeBound h.1 h.2.2.2 hc.1.1 hc.1.2.1,hc.2⟩

abbrev FreshStackData := ℕ × ℕ × ℕ × List CyclicTile

def freshStack (d : FreshStackData) : CyclicTileData :=
  let c := freshPartition (d.2.2.2.length-1,d.2.1,d.2.2.1,d.1)
  (d.2.1*c.1,stackCodes (d.2.1,c,d.2.2.2))

theorem freshStack_computable : Computable freshStack := by
  have hp : Primrec (fun d : FreshStackData => (d.2.2.2.length-1,d.2.1,d.2.2.1,d.1)) := by fun_prop
  have hc := freshPartition_computable.comp hp.to_comp
  have horder := Primrec.nat_mul.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.fst.comp hc)
  have hd := (Computable.fst.comp Computable.snd).pair (hc.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  exact horder.pair (stackCodes_primrec.to_comp.comp hd)

theorem stackCodes_correct_coprime (N P : ℕ) (hN : 0 < N) (Fs : List CyclicTile)
    (hs : 0 < Fs.length) (c : PartitionCertificate) (hc : PartitionValid (Fs.length - 1) P c) (hcop : Nat.Coprime N c.1) :
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


theorem freshStack_facts (X N P : ℕ) (Fs : List CyclicTile) (hN : 0<N)
    (hs : 0<Fs.length) (hX : Fs.length≤X) (hP : P≤X^2) (hpr : PrimeBound N P)
    (hne : ∀ F ∈ Fs, F≠[]) :
    0<(freshStack (X,N,P,Fs)).1 ∧ (freshStack (X,N,P,Fs)).2≠[] ∧
    (freshStack (X,N,P,Fs)).1≤N*freshCap X P ∧
    ((∃ A : Set (Plane × ZMod N), ∀ i : Fin Fs.length, Tiles (cyclicTileSet N (Fs.getD i.val [])) A) ↔
      ∃ B : Set (Plane × ZMod (freshStack (X,N,P,Fs)).1),
        Tiles (cyclicTileSet (freshStack (X,N,P,Fs)).1 (freshStack (X,N,P,Fs)).2) B) := by
  have hr : FreshReady (Fs.length-1,N,P,X) := ⟨hN,by change Fs.length-1+1≤X; omega,hP,hpr⟩
  have hc := freshPartition_spec (Fs.length-1,N,P,X) hr
  refine ⟨Nat.mul_pos hN hc.1.1.pos,stackCodes_nonempty N _ Fs hs hc.1 hne,
    Nat.mul_le_mul_left N hc.2.2,?_⟩
  exact stackCodes_correct_coprime N P hN Fs hs _ hc.1 hc.2.1

end
end TranslationTiling.FiniteCompiler.Effective
