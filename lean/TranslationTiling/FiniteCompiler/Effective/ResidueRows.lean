import TranslationTiling.FiniteCompiler.Effective.PackedParameterData
import Mathlib.Combinatorics.Pigeonhole

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective
open scoped Classical

noncomputable section

set_option maxRecDepth 10000
set_option exponentiation.threshold 20000

/-- A common residue class supplies one useful prime and four digit primes. -/
private theorem residueRow (b : ℕ) (hb : 0 < b) (s : Finset ℕ) (hs : b*4 < s.card) :
    ∃ a ∈ s, ∃ ds : List ℕ, ds.length = 4 ∧ (a::ds).Nodup ∧
      ∀ d ∈ ds, d ∈ s ∧ a < d ∧ d % b = a % b := by
  obtain ⟨r, _, hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun d : ℕ => d % b) (s := s) (t := Finset.range b) (n := 4)
    (fun d _ => Finset.mem_range.mpr (Nat.mod_lt d hb)) (by simpa using hs)
  obtain ⟨q,hq,hcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ _ from hr)
  let a := q.min' (Finset.card_pos.mp (by omega))
  have ha : a ∈ q := Finset.min'_mem _ _
  have hmem (d : ℕ) (hd : d ∈ q) := Finset.mem_filter.mp (hq hd)
  refine ⟨a,(hmem _ ha).1,(q.erase a).toList,?_ ,?_ ,?_⟩
  · rw [Finset.length_toList, Finset.card_erase_of_mem ha, hcard]
  · apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  · intro d hd
    obtain ⟨hne,hdq⟩ := Finset.mem_erase.mp (Finset.mem_toList.mp hd)
    exact ⟨(hmem _ hdq).1,lt_of_le_of_ne (q.min'_le _ hdq) (Ne.symm hne),
      (hmem _ hdq).2.trans (hmem _ ha).2.symm⟩

private def rowExtras (row : ℕ × ℕ × List ℕ) := row.1 :: row.2.2

private def residueRowOK (x : ℕ) (row : ℕ × ℕ × List ℕ) : Prop :=
  row.2.1 ≤ x ∧ row.2.2.length = 4 ∧
    ∀ d ∈ row.2.2, row.1 < d ∧ d % row.2.1 = row.1 % row.2.1

private theorem residueRowOK_primrec :
    PrimrecPred (fun z : ℕ × (ℕ × ℕ × List ℕ) => residueRowOK z.1 z.2) := by
  unfold residueRowOK
  apply PrimrecPred.and (by fun_prop)
  apply PrimrecPred.and (by fun_prop)
  apply allList (by fun_prop)
  fun_prop

private def usedPrimes (rs : GuardedRows) : List ℕ :=
  rs.flatMap (fun (a,b,ds) => a::b::ds)

private def fixedRows : GuardedRows :=
  (List.range 18).map (fun i =>
    (profile1.a i,profile1.b i,(profile1.row i).map Prod.fst))

private def fixedSeeds : GuardedRows := [(2,1229,[1231]),(3,773,[797])]

private def reserve : List ℕ := 5::7::usedPrimes (fixedRows ++ fixedSeeds)

private theorem reserve_length : reserve.length = 134 := by decide +kernel
private theorem reserve_nodup : reserve.Nodup := by decide +kernel

private def reserveRowOK (k : ℕ) (rs : GuardedRows) : Prop :=
  let x := guardedPrimeCap (2*k+134)
  let P := guardedPrimeCap (4*x+12*k+134)
  rs.length = 2*k ∧
  (∀ row ∈ rs, residueRowOK x row) ∧
  (reserve ++ usedPrimes rs).Nodup ∧
  ∀ p ∈ usedPrimes rs, p.Prime ∧ p ≤ P

private theorem usedPrimes_primrec : Primrec usedPrimes := by
  unfold usedPrimes
  fun_prop

private theorem reserveRowOK_primrec :
    PrimrecPred (fun z : ℕ × GuardedRows => reserveRowOK z.1 z.2) := by
  unfold reserveRowOK
  dsimp only
  apply PrimrecPred.and (by fun_prop)
  apply PrimrecPred.and
  · apply allList (by fun_prop)
    exact residueRowOK_primrec.comp (show Primrec (fun z : (ℕ × GuardedRows) × (ℕ × ℕ × List ℕ) => (guardedPrimeCap (2*z.1.1+134),z.2)) by fun_prop)
  apply PrimrecPred.and
  · have h : Primrec (fun z : ℕ × GuardedRows => reserve ++ usedPrimes z.2) := by
      have := usedPrimes_primrec.comp (Primrec.snd : Primrec (Prod.snd : ℕ × GuardedRows → GuardedRows))
      fun_prop
    rw [show (fun z : ℕ × GuardedRows => (reserve ++ usedPrimes z.2).Nodup) =
        fun z => ∀ q ∈ reserve ++ usedPrimes z.2, (reserve ++ usedPrimes z.2).count q = 1 by
      funext z
      exact propext List.nodup_iff_count_eq_one]
    apply allList h
    apply Primrec.eq.comp _ (Primrec.const 1)
    have hf := filterList (h.comp (Primrec.fst : Primrec (Prod.fst : (ℕ × GuardedRows) × ℕ → _)))
      (p := fun z q => q = z.2) (by fun_prop)
    apply (Primrec.list_length.comp hf).of_eq
    intro z
    rw [List.count_eq_length_filter]
    congr 2
  · apply allList (usedPrimes_primrec.comp Primrec.snd)
    exact (nat_prime_primrec.comp Primrec.snd).and (by fun_prop)

private theorem rowsFromUseful (x P : ℕ) (bs : List ℕ) (S : Finset ℕ)
    (hb : bs.Nodup) (hbp : ∀ b ∈ bs, b.Prime ∧ b ≤ x ∧ b ≤ P ∧ b ∈ S)
    (hcount : 4*x+S.card+5*bs.length ≤ Nat.primeCounting P) :
    ∃ rs : GuardedRows, rs.length = bs.length ∧ rs.map (fun row => row.2.1) = bs ∧
      (∀ row ∈ rs, residueRowOK x row) ∧
      (rs.flatMap rowExtras).Nodup ∧
      ∀ q ∈ rs.flatMap rowExtras, q.Prime ∧ q ≤ P ∧ q ∉ S := by
  induction bs generalizing S with
  | nil => exact ⟨[],rfl,rfl,by simp,by simp,by simp⟩
  | cons b bs ih =>
    obtain ⟨hbp₁,hbx,hbP,hbS⟩ := hbp b (by simp)
    let s := P.primesLE \ S
    have hs : b*4 < s.card := by
      have h := Finset.le_card_sdiff S P.primesLE
      rw [Nat.primesLE_card_eq_primeCounting] at h
      simp only [List.length_cons] at hcount
      change _ < (P.primesLE \ S).card
      omega
    obtain ⟨a,ha,ds,hdL,hdN,hd⟩ := residueRow b hbp₁.pos s hs
    have hds : ∀ q ∈ a::ds, q ∈ s := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact ha
      · exact (hd _ hq).1
    let S' := S ∪ (a::ds).toFinset
    have hS' : S'.card ≤ S.card+5 := by
      have h := Finset.card_union_le S (a::ds).toFinset
      have h' := List.toFinset_card_le (a::ds)
      simp only [List.length_cons,hdL] at h'
      change (S ∪ (a::ds).toFinset).card ≤ _
      omega
    obtain ⟨rs,hrs,hbs,hgood,hn,hex⟩ := ih S' (List.nodup_cons.mp hb).2
      (fun q hq => by
        obtain ⟨hp,hx,hP,hS⟩ := hbp q (List.mem_cons_of_mem _ hq)
        exact ⟨hp,hx,hP,Finset.mem_union_left _ hS⟩) (by simp only [List.length_cons] at hcount; omega)
    refine ⟨(a,b,ds)::rs, by simp [hrs], by simp [hbs],?_, ?_,?_⟩
    · intro row hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact ⟨hbx,hdL,fun d h => ⟨(hd d h).2.1,(hd d h).2.2⟩⟩
      · exact hgood _ hm
    · simp only [List.flatMap_cons,rowExtras,List.nodup_append']
      exact ⟨hdN,hn, by
        intro q hq hv
        exact (hex _ hv).2.2 (Finset.mem_union_right _ (List.mem_toFinset.mpr hq))⟩
    · intro q hq
      simp only [List.flatMap_cons,List.mem_append] at hq
      rcases hq with hq|hq
      · have h := Finset.mem_sdiff.mp (hds _ hq)
        have hp := Nat.mem_primesLE.mp h.1
        exact ⟨hp.2,hp.1,h.2⟩
      · obtain ⟨hp,hP,hnS⟩ := hex _ hq
        exact ⟨hp,hP,fun h => hnS (Finset.mem_union_left _ h)⟩

private theorem usedPrimes_perm (rs : GuardedRows) :
    (usedPrimes rs).Perm (rs.map (fun row => row.2.1) ++ rs.flatMap rowExtras) := by
  induction rs with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨a,b,ds⟩
    change ((a::b::ds) ++ usedPrimes rows).Perm
      (b :: ((rows.map (fun row => row.2.1)) ++ ((a::ds) ++ rows.flatMap rowExtras)))
    apply (List.Perm.cons a (List.Perm.cons b (List.Perm.append_left ds ih))).trans
    have h := List.perm_append_comm (l₁ := a::ds) (l₂ := rows.map (fun row => row.2.1))
    exact (List.Perm.swap b a _).trans (List.Perm.cons b (by
      simpa only [List.cons_append,List.append_assoc] using h.append_right (rows.flatMap rowExtras)))

private theorem existsResidueRows (k : ℕ) : ∃ rs, reserveRowOK k rs := by
  let x := guardedPrimeCap (2*k+134)
  let P := guardedPrimeCap (4*x+12*k+134)
  have hx := guardedPrimeCap_count (m := 2*k+134) (by omega)
  have hP := guardedPrimeCap_count (m := 4*x+12*k+134) (by omega)
  change 2*k+134 ≤ Nat.primeCounting x at hx
  change 4*x+12*k+134 ≤ Nat.primeCounting P at hP
  have hxP : x ≤ P := by
    unfold P guardedPrimeCap
    have h := Nat.le_mul_of_pos_right (4*(4*x+12*k+134))
      (show 0 < Nat.log 2 (4*x+12*k+134)+1 by omega)
    omega
  let s := x.primesLE \ reserve.toFinset
  have hlen := List.toFinset_card_le reserve
  rw [reserve_length] at hlen
  have hs : 2*k ≤ s.card := by
    have h := Finset.le_card_sdiff reserve.toFinset x.primesLE
    rw [Nat.primesLE_card_eq_primeCounting] at h
    change _ ≤ (x.primesLE \ reserve.toFinset).card
    omega
  obtain ⟨b,hb,hbcard⟩ := Finset.exists_subset_card_eq hs
  let S := reserve.toFinset ∪ b
  have hS : S.card ≤ 134+2*k := by
    have h := Finset.card_union_le reserve.toFinset b
    change (reserve.toFinset ∪ b).card ≤ _
    omega
  have hbdata (q : ℕ) (hq : q ∈ b.toList) : q.Prime ∧ q ≤ x ∧ q ≤ P ∧ q ∈ S := by
    have hi := Finset.mem_toList.mp hq
    have hp := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp (hb hi)).1
    exact ⟨hp.2,hp.1,hp.1.trans hxP,Finset.mem_union_right _ hi⟩
  obtain ⟨rs,hlen',hm,hrow,hn,hex⟩ := rowsFromUseful x P b.toList S
    (Finset.nodup_toList _) hbdata (by rw [Finset.length_toList,hbcard]; omega)
  have hperm := usedPrimes_perm rs
  rw [hm] at hperm
  refine ⟨rs,hlen'.trans (by simp [hbcard]),hrow,?_ ,?_⟩
  · apply (hperm.append_left reserve).nodup_iff.mpr
    rw [← List.append_assoc,List.nodup_append',List.nodup_append']
    refine ⟨⟨reserve_nodup,Finset.nodup_toList _,?_⟩,hn,?_⟩
    · intro q hq hv
      exact (Finset.mem_sdiff.mp (hb (Finset.mem_toList.mp hv))).2 (List.mem_toFinset.mpr hq)
    · intro q hq hv
      apply (hex _ hv).2.2
      rcases List.mem_append.mp hq with hq|hq
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hq)
      · exact Finset.mem_union_right _ (Finset.mem_toList.mp hq)
  · intro q hq
    rcases List.mem_append.mp (hperm.mem_iff.mp hq) with hq|hq
    · exact ⟨(hbdata _ hq).1,(hbdata _ hq).2.2.1⟩
    · exact ⟨(hex _ hq).1,(hex _ hq).2.1⟩

private def decodeRows (c : ℕ) : GuardedRows :=
  (Encodable.decode c).getD []

private theorem decodeRows_primrec : Primrec decodeRows :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem existsResidueCode (k : ℕ) : ∃ c, reserveRowOK k (decodeRows c) := by
  obtain ⟨rs,h⟩ := existsResidueRows k
  exact ⟨Encodable.encode rs, by simpa [decodeRows,Encodable.encodek] using h⟩

def residueRows (k : ℕ) : GuardedRows :=
  decodeRows (leastWitness (fun k c => reserveRowOK k (decodeRows c)) existsResidueCode k)

theorem residueRows_computable : Computable residueRows :=
  decodeRows_primrec.to_comp.comp
    (leastWitness_computable _ ((reserveRowOK_primrec.comp
      (Primrec.fst.pair (decodeRows_primrec.comp Primrec.snd))).computablePred) _)

private theorem residueRows_valid (k : ℕ) : reserveRowOK k (residueRows k) :=
  @Nat.find_spec _ (Classical.decPred _) (existsResidueCode k)


abbrev CertifiedRow := ℕ × ℕ × List (ℕ × ℕ × ℕ)

private def rowNumbers (r : CertifiedRow) : ℕ × ℕ × List ℕ :=
  (r.1,r.2.1,r.2.2.map Prod.fst)

private def wangCertificate (r : ℕ × ℕ × List ℕ) : CertifiedRow :=
  (r.1,r.2.1,r.2.2.map (fun d => (d,1,d/r.2.1-r.1/r.2.1)))

private def originalCertificate (i : ℕ) : CertifiedRow :=
  (profile1.a i,profile1.b i,profile1.row i)

private def fixedCertificates := (List.range 18).map originalCertificate
private def seedCertificates := [originalCertificate 20,originalCertificate 21]

private def certificates (k : ℕ) :=
  fixedCertificates ++ (residueRows k).map wangCertificate ++ seedCertificates

def residueData (k : ℕ) : GuardedRows :=
  fixedRows ++ residueRows k ++ fixedSeeds

def residueProfile (k : ℕ) : Profile :=
  ⟨List.replicate k 4,(certificates k).map (fun row => (row.1,row.2.1)),
    (certificates k).map (fun row => row.2.2)⟩

theorem residueData_computable : Computable residueData := by
  unfold residueData
  have append : Primrec (fun z : GuardedRows × GuardedRows => z.1 ++ z.2) := Primrec.list_append
  have arithmetic : Computable (fun _ : ℕ => fixedRows) := Computable.const fixedRows
  have seeds : Computable (fun _ : ℕ => fixedSeeds) := Computable.const fixedSeeds
  exact append.to_comp.comp (arithmetic.pair (append.to_comp.comp (residueRows_computable.pair seeds)))

private theorem certificates_length (k : ℕ) : (certificates k).length = 18+2*k+2 := by
  have h := (residueRows_valid k).1
  simp [certificates,fixedCertificates,seedCertificates,h,Nat.add_assoc]

private theorem certificates_numbers (k : ℕ) :
    (certificates k).map rowNumbers = residueData k := by
  have he : ∀ r, rowNumbers (wangCertificate r) = r := by intro ⟨a,b,ds⟩; simp [rowNumbers,wangCertificate,List.map_map,Function.comp_def]
  simp only [certificates,residueData,List.map_append,List.map_map]
  have h : rowNumbers ∘ wangCertificate = id := funext he
  rw [h,List.map_id]
  rfl

theorem residueProfile_width (k : ℕ) : (residueProfile k).width = 18+2*k := by
  simp [residueProfile,Profile.width]

private theorem certificate_get (k i : ℕ) (hi : i < (certificates k).length) :
    ((residueProfile k).a i,(residueProfile k).b i,(residueProfile k).row i) =
      (certificates k)[i] := by
  simp [Profile.a,Profile.b,Profile.row,residueProfile,List.getD_eq_getElem?_getD,hi]

private theorem cert_arithmetic (k i : ℕ) (hi : i < 18)
    (hi' : i < (certificates k).length) : (certificates k)[i] = originalCertificate i := by
  simp [certificates,fixedCertificates,List.getElem_append_left,hi]

private theorem cert_wang (k i : ℕ) (hl : 18 ≤ i) (hu : i < 18+2*k)
    (hi : i < (certificates k).length) :
    ∃ r ∈ residueRows k, (certificates k)[i] = wangCertificate r := by
  have h := (residueRows_valid k).1
  have hj : i-18 < (residueRows k).length := by omega
  refine ⟨(residueRows k)[i-18],List.getElem_mem _,?_⟩
  have hf : fixedCertificates.length = 18 := by decide
  have ho : (certificates k)[i]? = some (wangCertificate (residueRows k)[i-18]) := by
    unfold certificates
    rw [List.append_assoc]
    rw [List.getElem?_append_right (by omega : fixedCertificates.length ≤ i),hf]
    rw [List.getElem?_append_left (by simpa using hj)]
    simp [List.getElem?_eq_getElem hj]
  rw [List.getElem?_eq_getElem hi] at ho
  exact Option.some.inj ho

private theorem cert_seed (k i : ℕ) (hl : 18+2*k ≤ i)
    (hi : i < (certificates k).length) :
    (certificates k)[i] = originalCertificate (20+(i-(18+2*k))) := by
  have h := (residueRows_valid k).1
  have he : i-(18+2*k) < 2 := by rw [certificates_length] at hi; omega
  have hf : fixedCertificates.length = 18 := by decide
  have hmap : ((residueRows k).map wangCertificate).length = 2*k := by simpa
  have ho : (certificates k)[i]? = some (originalCertificate (20+(i-(18+2*k)))) := by
    unfold certificates
    rw [List.append_assoc]
    rw [List.getElem?_append_right (by omega : fixedCertificates.length ≤ i),hf]
    rw [List.getElem?_append_right (by omega : ((residueRows k).map wangCertificate).length ≤ i-18),
      hmap,Nat.sub_sub]
    generalize i-(18+2*k) = j at *
    interval_cases j <;> rfl
  rw [List.getElem?_eq_getElem hi] at ho
  exact Option.some.inj ho

private theorem represented {a b d : ℕ} (_hb : 0 < b) (had : a < d)
    (hmod : d%b = a%b) : 0 < d/b-a/b ∧ d = a+(d/b-a/b)*b := by
  have ha := Nat.mod_add_div a b
  have hd := Nat.mod_add_div d b
  rw [hmod,mul_comm b] at hd
  rw [mul_comm b] at ha
  have hq : a/b < d/b := by
    by_contra! h
    have := Nat.mul_le_mul_right b h
    omega
  exact ⟨by omega,by rw [Nat.sub_mul]; have := Nat.mul_le_mul_right b hq.le; omega⟩

private theorem fixedInfo (i : ℕ) (hi : i < 18 ∨ i=20 ∨ i=21) :
    let r := originalCertificate i
    r.2.2.length = profile1.arity i ∧
    ∀ d ∈ r.2.2, 0 < d.2.1 ∧ 0 < d.2.2 ∧ d.1 = d.2.1*r.1+d.2.2*r.2.1 := by
  apply profile1_valid.2.2.2.2.1
  exact List.mem_range.mpr (by change i < 22; omega)

private theorem profile_primes_perm (r : List CertifiedRow) :
    ((r.flatMap fun z => [z.1,z.2.1]) ++ (r.flatMap fun z => z.2.2.map Prod.fst)).Perm
      (usedPrimes (r.map rowNumbers)) := by
  induction r with
  | nil => rfl
  | cons v vs ih =>
    rcases v with ⟨a,b,ds⟩
    simp only [List.flatMap_cons,List.map_cons,usedPrimes,rowNumbers,List.cons_append,List.nil_append]
    apply List.Perm.cons a
    apply List.Perm.cons b
    have h := (List.perm_append_comm (l₁ := vs.flatMap (fun z => [z.1,z.2.1]))
      (l₂ := ds.map Prod.fst)).append_right (vs.flatMap (fun z => z.2.2.map Prod.fst))
    exact (by simpa only [List.append_assoc] using h.trans (by
      simpa only [List.append_assoc,usedPrimes] using ih.append_left (ds.map Prod.fst)))

private theorem residueProfile_primes_perm (k : ℕ) :
    (residueProfile k).primes.Perm (usedPrimes (residueData k)) := by
  unfold residueProfile Profile.primes
  simp only [List.flatMap_map,Function.comp_def]
  rw [← certificates_numbers]
  exact profile_primes_perm _

theorem residueData_valid_prime (k : ℕ) :
    ∀ q ∈ usedPrimes (residueData k), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧
      q ≤ guardedPrimeCap (4*guardedPrimeCap (2*k+134)+12*k+134) := by
  let P := guardedPrimeCap (4*guardedPrimeCap (2*k+134)+12*k+134)
  have hlarge : 1619 ≤ P := by
    have hx : 536 ≤ guardedPrimeCap (2*k+134) := by
      unfold guardedPrimeCap
      have := Nat.le_mul_of_pos_right (4*(2*k+134)) (show 0 < Nat.log 2 (2*k+134)+1 by omega)
      omega
    unfold P guardedPrimeCap
    have hh := Nat.le_mul_of_pos_right (4*(4*guardedPrimeCap (2*k+134)+12*k+134))
      (show 0 < Nat.log 2 (4*guardedPrimeCap (2*k+134)+12*k+134)+1 by omega)
    exact (show 1619 ≤ 4*(4*guardedPrimeCap (2*k+134)+12*k+134) by omega).trans hh
  have hfixed : ∀ q ∈ usedPrimes (fixedRows++fixedSeeds),
      q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 1619 := by decide +kernel
  obtain ⟨_,_,hn,hp⟩ := residueRows_valid k
  intro q hq
  simp only [residueData,usedPrimes,List.flatMap_append,List.mem_append] at hq
  rcases hq with (h|h)|h
  · have h' := hfixed q (by simp only [usedPrimes,List.flatMap_append,List.mem_append]; exact Or.inl h)
    exact ⟨h'.1,h'.2.1,h'.2.2.1,h'.2.2.2.trans hlarge⟩
  · have hh := hp q h
    have hnot : q ∉ reserve := fun hm => ((List.nodup_append'.mp hn).2.2 hm h)
    exact ⟨hh.1,fun he => hnot (by subst q; simp [reserve]),
      fun he => hnot (by subst q; simp [reserve]),hh.2⟩
  · have h' := hfixed q (by simp only [usedPrimes,List.flatMap_append,List.mem_append]; exact Or.inr h)
    exact ⟨h'.1,h'.2.1,h'.2.2.1,h'.2.2.2.trans hlarge⟩

private theorem residueData_nodup (k : ℕ) : (usedPrimes (residueData k)).Nodup := by
  have hn := (residueRows_valid k).2.2.1
  have h : (usedPrimes (fixedRows ++ fixedSeeds) ++ usedPrimes (residueRows k)).Nodup := by
    simpa [reserve] using (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
  simp only [residueData,usedPrimes,List.flatMap_append] at *
  rw [List.append_assoc]
  exact ((List.Perm.append_left _ List.perm_append_comm).nodup_iff.mpr (by rwa [← List.append_assoc]))

theorem residueProfile_valid (k : ℕ) :
    Valid (residueProfile k) (guardedPrimeCap (4*guardedPrimeCap (2*k+134)+12*k+134)) := by
  let p := residueProfile k
  have hw : p.width = 18+2*k := residueProfile_width k
  have hcert := certificates_length k
  have hfixed (i : ℕ) (hi : i < 18) : p.arity i = profile1.arity i := by
    unfold Profile.arity
    split_ifs <;> rfl
  have hseed (i : ℕ) (hi : p.width ≤ i) : p.arity i = 1 := by
    unfold Profile.arity
    split_ifs <;> omega
  have hwn (i : ℕ) (hl : 18 ≤ i) (hu : i < p.width) : p.arity i = 4 := by
    unfold Profile.arity
    rw [if_neg (by omega),if_neg (by omega),if_pos hu]
    have hk : 0 < k := by omega
    simp [p,residueProfile,List.getD_eq_getElem?_getD, Nat.mod_lt _ hk]
  refine ⟨?_,?_,(residueProfile_primes_perm k).nodup_iff.mpr (residueData_nodup k),
    fun q hq => residueData_valid_prime k q ((residueProfile_primes_perm k).mem_iff.mp hq),?_,?_⟩
  · simp [p,residueProfile,hcert,Profile.width]
  · simp [p,residueProfile,hcert,Profile.width]
  · intro i hi
    have hilt : i < p.width+2 := List.mem_range.mp hi
    have he : i < (certificates k).length := by omega
    have h := certificate_get k i he
    change (p.a i,p.b i,p.row i) = _ at h
    have goalOf (r : CertifiedRow) (eq : (p.a i,p.b i,p.row i) = r)
        (hr : r.2.2.length = p.arity i ∧ ∀ d ∈ r.2.2,
          0 < d.2.1 ∧ 0 < d.2.2 ∧ d.1 = d.2.1*r.1+d.2.2*r.2.1) :
        (p.row i).length = p.arity i ∧ ∀ d ∈ p.row i,
          0 < d.2.1 ∧ 0 < d.2.2 ∧ d.1 = d.2.1*p.a i+d.2.2*p.b i := by
      rw [← eq] at hr
      exact hr
    by_cases ha : i < 18
    · apply goalOf _ (h.trans (cert_arithmetic k i ha he))
      rw [hfixed _ ha]
      exact fixedInfo i (Or.inl ha)
    · by_cases hf : i < p.width
      · obtain ⟨r,hr,er⟩ := cert_wang k i (by omega) (by omega) he
        apply goalOf _ (h.trans er)
        obtain ⟨_,hL,hrep⟩ := (residueRows_valid k).2.1 r hr
        have hb : 0 < r.2.1 := by
          have hm : r.2.1 ∈ usedPrimes (residueRows k) :=
            List.mem_flatMap.mpr ⟨r,hr,by simp⟩
          exact ((residueRows_valid k).2.2.2 _ hm).1.pos
        refine ⟨by rw [hwn _ (by omega) hf]; simpa [wangCertificate] using hL,?_⟩
        intro d hd
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
        obtain ⟨hp,heq⟩ := represented hb (hrep q hq).1 (hrep q hq).2
        exact ⟨Nat.one_pos,hp,by simpa [wangCertificate] using heq⟩
      · apply goalOf _ (h.trans (cert_seed k i (by omega) he))
        have hj : i-(18+2*k) < 2 := by omega
        rw [hseed _ (by omega)]
        generalize i-(18+2*k)=j at *
        interval_cases j <;> exact fixedInfo _ (by decide)
  · intro t ht
    have ht' := List.mem_range.mp ht
    have he : p.width+t < (certificates k).length := by omega
    have h := (certificate_get k (p.width+t) he).trans (cert_seed k _ (by omega) he)
    have hi : p.width+t-(18+2*k) = t := by omega
    rw [hi] at h
    have ha := congrArg Prod.fst h
    have hb := congrArg (fun q : CertifiedRow => q.2.1) h
    change p.a (p.width+t) = _ at ha
    change p.b (p.width+t) = _ at hb
    rw [ha,hb]
    interval_cases t <;> decide

private theorem residue_order_formula (rs : GuardedRows) :
    guardedOrder rs = 1225*(rs.map (fun r => r.2.2.prod^2*r.1*r.2.1)).prod := by
  unfold guardedOrder
  congr 2
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < rs.length := by simpa using hj
    simp [rowA,rowB,rowR,rowDigits,List.getD_eq_getElem?_getD,h]

private theorem row_prod_bound (x P : ℕ) (rs : GuardedRows)
    (h : ∀ r ∈ rs, residueRowOK x r ∧ ∀ q ∈ r.1::r.2.2, q ≤ P) :
    (rs.map (fun r => r.2.2.prod^2*r.1*r.2.1)).prod ≤ (P^9*x)^rs.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have hd : r.2.2.prod ≤ P^4 := by
      have hh (l : List ℕ) (hl : ∀ q ∈ l, q ≤ P) : l.prod ≤ P^l.length := by
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.prod_cons,List.length_cons,pow_succ']
          exact Nat.mul_le_mul (hl a (by simp)) (ih (fun q hq => hl q (by simp [hq])))
      have hh' := hh r.2.2 (fun q hq => hr.2 q (by simp [hq]))
      rwa [hr.1.2.1] at hh'
    have ha := hr.2 r.1 (by simp)
    have hmain : r.2.2.prod^2*r.1*r.2.1 ≤ P^9*x := by
      calc
        _ ≤ (P^4)^2*P*x := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) ha) hr.1.1
        _ = _ := by ring
    simp only [List.map_cons,List.prod_cons,List.length_cons]
    exact (Nat.mul_le_mul hmain (ih (fun q hq => h q (by simp [hq])))).trans_eq (pow_succ' _ _).symm

theorem residueData_order_bound (k : ℕ) :
    guardedOrder (residueData k) ≤ 2^1878 *
      (guardedPrimeCap (4*guardedPrimeCap (2*k+134)+12*k+134))^(18*k) *
      (guardedPrimeCap (2*k+134))^(2*k) := by
  let x := guardedPrimeCap (2*k+134)
  let P := guardedPrimeCap (4*x+12*k+134)
  change _ ≤ 2^1878*P^(18*k)*x^(2*k)
  obtain ⟨hL,hr,_,hp⟩ := residueRows_valid k
  have hl := row_prod_bound x P (residueRows k) (by
    intro r hm
    refine ⟨hr r hm,fun q hq => (hp q (List.mem_flatMap.mpr ⟨r,hm,?_⟩)).2⟩
    exact (List.mem_cons.mp hq).elim (fun he => he ▸ by simp) (fun he => by simp [he]))
  rw [hL,mul_pow,← pow_mul] at hl
  have hf : 1225*(fixedRows.map (fun r => r.2.2.prod^2*r.1*r.2.1)).prod *
      (fixedSeeds.map (fun r => r.2.2.prod^2*r.1*r.2.1)).prod ≤ 2^1878 := by decide +kernel
  simp only [residue_order_formula,residueData,List.map_append,List.prod_append]
  calc
    _ = (1225*_*(fixedSeeds.map _).prod) * ((residueRows k).map _).prod := by ac_rfl
    _ ≤ 2^1878*(P^(9*(2*k))*x^(2*k)) := Nat.mul_le_mul hf hl
    _ = _ := by ring

/-- The numeric rows have the same indexing as the typed profile. -/
theorem residueData_at (k i : ℕ) (hi : i < (residueProfile k).width+2) :
    (residueData k).getD i (0,0,[]) =
      ((residueProfile k).a i,(residueProfile k).b i,((residueProfile k).row i).map Prod.fst) := by
  have hd : i < (certificates k).length := by rw [certificates_length, ← residueProfile_width] ; exact hi
  rw [← certificates_numbers, List.getD_eq_getElem _ _ (by simpa using hd),List.getElem_map]
  rw [← certificate_get k i hd]
  rfl

theorem residueData_length (k : ℕ) : (residueData k).length = (residueProfile k).width+2 := by
  rw [← certificates_numbers,List.length_map,certificates_length,residueProfile_width]

theorem residueProfile_radius (k : ℕ) (P x : ℕ)
    (hP : P = guardedPrimeCap (4*guardedPrimeCap (2*k+134)+12*k+134))
    (hx : x = guardedPrimeCap (2*k+134)) :
    (∀ i : Fin (residueProfile k).width,
      2*((residueProfile k).r i.val*(residueProfile k).a i.val*(residueProfile k).b i.val) ≤ 2^70+2*P^5*x) ∧
    (∀ t : Fin 2, 2*(3-t.val)*(residueProfile k).r ((residueProfile k).width+t.val) *
      ((residueProfile k).a ((residueProfile k).width+t.val) *
        (residueProfile k).b ((residueProfile k).width+t.val))^2 * 35^3 ≤ 2^70+2*P^5*x) := by
  let p := residueProfile k
  have hw : p.width=18+2*k := residueProfile_width k
  have hlen := certificates_length k
  constructor
  · intro i
    have hi : i.val < p.width := i.isLt
    have hci : i.val < (certificates k).length := by omega
    have h := certificate_get k i.val hci
    let f (r : CertifiedRow) := 2*((r.2.2.map Prod.fst).prod*r.1*r.2.1)
    change f (p.a i.val,p.b i.val,p.row i.val) ≤ _
    rw [h]
    by_cases hi18 : i.val<18
    · rw [cert_arithmetic k _ hi18 hci]
      have hb : ∀ j ∈ List.range 18, f (originalCertificate j) ≤ 2^70 := by decide +kernel
      exact (hb _ (List.mem_range.mpr hi18)).trans (Nat.le_add_right _ _)
    · obtain ⟨r,hr,he⟩ := cert_wang k i.val (by omega) (by omega) hci
      rw [he]
      have hq (q : ℕ) (hq : q ∈ r.1::r.2.2) : q ≤ P := by
        rw [hP]
        apply ((residueRows_valid k).2.2.2 q (List.mem_flatMap.mpr ⟨r,hr,?_⟩)).2
        simp only [List.mem_cons] at ⊢ hq
        tauto
      obtain ⟨hb,hd, _⟩ := (residueRows_valid k).2.1 r hr
      rw [← hx] at hb
      have hprod (ds : List ℕ) (hs : ∀ q ∈ ds, q ≤ P) : ds.prod ≤ P^ds.length := by
        induction ds with
        | nil => simp
        | cons q ds ih =>
          simp only [List.prod_cons,List.length_cons,pow_succ']
          exact Nat.mul_le_mul (hs q (by simp)) (ih (fun d hd => hs d (by simp [hd])))
      have he' := hprod r.2.2 (fun q hq' => hq q (by simp [hq']))
      rw [hd] at he'
      have hf : f (wangCertificate r) = 2*(r.2.2.prod*r.1*r.2.1) := by
        simp [f,wangCertificate,List.map_map,Function.comp_def]
      rw [hf]
      calc
        _ ≤ 2*(P^4*P*x) := Nat.mul_le_mul_left 2
          (Nat.mul_le_mul (Nat.mul_le_mul he' (hq r.1 (by simp))) hb)
        _ ≤ _ := by rw [← pow_succ, ← Nat.mul_assoc]; exact Nat.le_add_left _ _
  · intro t
    have ht := t.isLt
    have hi : p.width+t.val < (certificates k).length := by omega
    have he := (certificate_get k (p.width+t.val) hi).trans (cert_seed k _ (by omega) hi)
    rw [show p.width+t.val-(18+2*k)=t.val by omega] at he
    let f (r : CertifiedRow) := 2*(3-t.val)*(r.2.2.map Prod.fst).prod*(r.1*r.2.1)^2*35^3
    change f (p.a (p.width+t.val),p.b (p.width+t.val),p.row (p.width+t.val)) ≤ _
    rw [he]
    exact (show f (originalCertificate (20+t.val)) ≤ 2^70 by fin_cases t <;> decide).trans
      (Nat.le_add_right _ _)

end
end TranslationTiling.FiniteCompiler.Packed
