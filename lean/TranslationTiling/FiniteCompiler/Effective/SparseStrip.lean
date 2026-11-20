import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.ReservedStripLift

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective Compiler.StripLift
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] inputOrder EncodingParameters.cyclicOrder
  parameterCertificate parameters sparseFamily compactHorizontal familyCyclic
set_option exponentiation.threshold 20000

private theorem raw_inputOrder (T : System) :
    (rawModuli (parameterData T)).prod=inputOrder (parameters T) := by
  have he : (channelKeys T.width).toFinset = Finset.univ.image (channelKey (T := T)) := by
    ext k
    simp only [List.mem_toFinset,mem_channelKeys,Finset.mem_image,Finset.mem_univ,true_and]
  unfold rawModuli
  change ((channelKeys T.width).map (rawR (parameterData T))).prod=_
  rw [←List.prod_toFinset _ (channelKeys_nodup T.width),he,
    Finset.prod_image (channelKey_injective T).injOn]
  simp only [rawR_eq,inputOrder]

private abbrev StripFamilyData := (ParameterData × List CyclicTile) × ℕ

private def kernelCode (p : ParameterData) : CyclicTile :=
  canonicalTile (rawHorizontal p) (rawOrder p) (kernelCodes (rawOrder p) (rawModuli p))

private theorem kernelCode_primrec : Primrec kernelCode := by
  unfold kernelCode
  exact canonicalTile_primrec.comp
    ((rawHorizontal_primrec.pair rawOrder_primrec).pair
      (kernelCodes_primrec.comp (rawOrder_primrec.pair rawModuli_primrec)))

private def kernelIndex (p : ParameterData) (Fs : List CyclicTile) : ℕ :=
  Fs.idxOf (kernelCode p)

private def reserveData (d : ParameterData × List CyclicTile) : ReserveData :=
  let P := max (d.1.1+2) 256
  ((d.2.length-1,rawOrder d.1,P^4,max d.2.length (P^2)),kernelIndex d.1 d.2,(rawModuli d.1).prod)

private theorem reserveData_primrec : Primrec reserveData := by
  unfold reserveData
  have hk := kernelCode_primrec.comp (Primrec.fst : Primrec (Prod.fst : ParameterData × List CyclicTile → ParameterData))
  have hi : Primrec (fun d : ParameterData × List CyclicTile => kernelIndex d.1 d.2) := by
    refine (Primrec.list_idxOf.comp hk Primrec.snd).of_eq (fun d => ?_)
    unfold kernelIndex List.idxOf
    congr 1
    funext x
    simp [beq_eq_decide]
  have hR := product_primrec.comp (rawModuli_primrec.comp
    (Primrec.fst : Primrec (Prod.fst : ParameterData × List CyclicTile → ParameterData)))
  have hdata : Primrec (fun d : ParameterData × List CyclicTile =>
      let P := max (d.1.1+2) 256
      (d.2.length-1,rawOrder d.1,P^4,max d.2.length (P^2))) := by fun_prop
  exact hdata.pair (hi.pair hR)

private def stripFamilyTileAt (z : StripFamilyData) : Tile 3 :=
  let d := reserveData z.1
  let c := reservedPartition d
  let data := (d.1.2.1*c.1,stackCodes (d.1.2.1,c,z.1.2))
  Rails.Strips.assemble (integerTile data) z.2 (3*d.2.2+1)

private theorem stripFamilyTileAt_computable : Computable stripFamilyTileAt := by
  have hd := reserveData_primrec.comp (Primrec.fst : Primrec (Prod.fst : StripFamilyData → _))
  have hc := reservedPartition_computable.comp hd.to_comp
  have hp : Primrec (fun z : StripFamilyData × PartitionCertificate =>
      ((reserveData z.1.1).1.2.1*z.2.1,stackCodes ((reserveData z.1.1).1.2.1,z.2,z.1.1.2))) := by
    have hh := hd.comp (Primrec.fst : Primrec (Prod.fst : StripFamilyData × PartitionCertificate → _))
    exact (by fun_prop : Primrec (fun z : StripFamilyData × PartitionCertificate =>
      (reserveData z.1.1).1.2.1*z.2.1)).pair
        (stackCodes_primrec.comp (by fun_prop))
  have ht := Compiler.integerTile_primrec.to_comp.comp (hp.to_comp.comp (Computable.id.pair hc))
  have hr : Primrec (fun z : StripFamilyData => 3*(reserveData z.1).2.2+1) := by fun_prop
  exact (Rails.Strips.assemble_computable.comp (ht.pair (Computable.snd.pair hr.to_comp))).of_eq
    (fun _ => rfl)

def sparseStripCore (T : LeanWang.TileSet) : Tile 3 :=
  let p := parameterData (SparseTernary.system T)
  stripFamilyTileAt ((p,sparseFamily T),compactHorizontal p)

theorem sparseStripCore_computable : Computable sparseStripCore := by
  have hp := sparseParameterData_computable
  exact stripFamilyTileAt_computable.comp ((hp.pair sparseFamily_computable).pair
    (compactHorizontal_primrec.to_comp.comp hp))

private theorem sparse_strip (T : LeanWang.TileSet) :
    ∀ F∈sparseFamily T, ∀ f∈F,
      TestSupport (compactHorizontal (parameterData (SparseTernary.system T))) f.1 := by
  intro F hF f hf
  let E := parameters (SparseTernary.system T)
  have hm : F.toFinset.image (decodeNumericalPoint E) ∈ SparseTernary.testFamily E := by
    rw [←sparseFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  have hg : decodeNumericalPoint E f ∈ F.toFinset.image (decodeNumericalPoint E) :=
    Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩
  change TestSupport _ (decodeNumericalPoint E f).1
  rcases Finset.mem_union.mp hm with hh|hh
  · exact test_strip E (compactHorizontal_support (SparseTernary.system T) rfl (SparseTernary.slope_bound T))
      (sparseSystem_nonnegative T) (SparseTernary.slope_bound T) hh hg
  · obtain ⟨j,_,hh⟩ := Finset.mem_biUnion.mp hh
    have hm' := Finset.mem_singleton.mp hh
    rw [hm'] at hg
    have hz : (decodeNumericalPoint E f).1=0 := congrArg Prod.fst ((mem_offsetTile E _ _).mp hg)
    simp [TestSupport,hz]

private theorem sparse_kernel (T : LeanWang.TileSet) :
    let S := SparseTernary.system T
    let F := kernelCode (parameterData S)
    F∈sparseFamily T ∧ ∀ k : ℤ,
      (((0:Plane), ((inputOrder (parameters S):ℤ)*k : ℤ)) :
        Plane × ZMod (parameters S).cyclicOrder) ∈ cyclicTileSet (parameters S).cyclicOrder F := by
  let S := SparseTernary.system T
  let p := parameterData S
  let K := kernelCodes (rawOrder p) (rawModuli p)
  let E := parameters S
  have hm : K∈rawSparseFamily T := by
    unfold rawSparseFamily rawFamily sparseInput
    simp [K,p,S]
  have hC : kernelCode p∈sparseFamily T := by
    unfold sparseFamily canonicalFamily
    exact List.mem_dedup.mpr (List.mem_map.mpr ⟨K,hm,rfl⟩)
  refine ⟨hC,fun k => ?_⟩
  have he := decodedTile_eq_image E K
  rw [rawKernel_correct S] at he
  have hker := kernel_column E k
  rw [he,Finset.image_image] at hker
  have horder : rawOrder p=E.cyclicOrder := rawOrder_eq S
  have hcanon := canonicalTile_correct (rawHorizontal p) (rawOrder p) (horder.symm ▸ E.cyclicOrder_pos) K
    (fun f hf => by
      obtain ⟨hx,hy⟩ := rawSparseFamily_horizontal T K hm f hf
      change f.1.1.natAbs≤rawHorizontal p at hx
      change f.1.2.natAbs≤rawHorizontal p at hy
      exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩)
  change ((0:Plane),_) ∈ cyclicTileSet E.cyclicOrder (kernelCode p)
  have hmap : (ambientCyclicEquiv E ∘ (ambientCyclicEquiv E).symm)=id := by funext x; simp
  rw [hmap,Finset.image_id] at hker
  unfold kernelCode
  have he' : cyclicTileSet E.cyclicOrder (canonicalTile (rawHorizontal p) (rawOrder p) K) =
      cyclicTileSet E.cyclicOrder K := by
    exact Eq.mp (congrArg (fun m =>
      cyclicTileSet m (canonicalTile (rawHorizontal p) (rawOrder p) K)=cyclicTileSet m K) horder) hcanon
  rw [show kernelCodes (rawOrder p) (rawModuli p)=K from rfl,he']
  exact hker

theorem sparseStripCore_facts (T : LeanWang.TileSet) (hn : 0<T.length) :
    sparseStripCore T≠[] ∧ FaceConnected (sparseStripCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sparseStripCore T)) ∧
    (sparseStripCore T).length≤reservedVolumeCap 175
      (fun _ => compactHorizontal (parameterData (SparseTernary.system T)))
      (inputOrder (parameters (SparseTernary.system T))) (MassSize.mass (parameters (SparseTernary.system T)))
      (freshCap (max (sparseFamily T).length (primeBudget (SparseTernary.system T)^2))
        (primeBudget (SparseTernary.system T)^4)) := by
  let S := SparseTernary.system T
  let E := parameters S
  let Fs := sparseFamily T
  let N := E.cyclicOrder
  let R := inputOrder E
  let H := compactHorizontal (parameterData S)
  let P := primeBudget S
  let X := max Fs.length (P^2)
  have hN : 0<N := E.cyclicOrder_pos
  have hf := sparseFamily_budget T hn
  have hs : 0<Fs.length := hf.length_pos
  have hP : P^4≤X^2 := by
    rw [show P^4=(P^2)^2 by rw [←pow_mul]]
    exact Nat.pow_le_pow_left (le_max_right Fs.length (P^2)) 2
  have hpr := BudgetSize.cyclicOrder_primeBound E rfl (parameters_bounded_budget S rfl) (le_max_right _ _)
  have hX : P^2≤X := le_max_right _ _
  have hX' : 65536≤X := (Nat.pow_le_pow_left (le_max_right _ _) 2).trans hX
  have hl : 5≤Stacking.differenceLog X := by
    unfold Stacking.differenceLog
    have hh := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : 2*X≠0)).mpr (show 2^4≤2*X by omega)
    omega
  have hlarge : P^4+3≤2*X^2 := by
    have h := (by decide : 3≤65536^2).trans (Nat.pow_le_pow_left hX' 2)
    omega
  obtain ⟨hk,hkernel⟩ := sparse_kernel T
  have hidx : kernelIndex (parameterData S) Fs<Fs.length := by
    unfold kernelIndex
    exact List.idxOf_lt_length_of_mem hk
  let i : Fin Fs.length := ⟨kernelIndex (parameterData S) Fs,hidx⟩
  let d : ReserveData := ((Fs.length-1,N,P^4,X),i.val,R)
  have hr : ReserveReady d := ⟨⟨hN,by dsimp [d,X]; omega,hP,hpr⟩,by dsimp [d]; have := i.isLt; omega,hl,hlarge⟩
  let c := reservedPartition d
  obtain ⟨hc,hcop,hcap,hres⟩ := reservedPartition_spec d hr
  change c.1≤reservedCap X (P^4) at hcap
  have hcap' : c.1≤freshCap X (P^4) := hcap.trans (by
    unfold reservedCap reservedThreshold freshCap Stacking.logPartitionThreshold
    have h := Nat.zero_le (44*X^2*Stacking.differenceLog X)
    nlinarith only [h])
  let data : CyclicTileData := (N*c.1,stackCodes (N,c,Fs))
  have hdata : reserveData (parameterData S,Fs)=d := by
    unfold reserveData
    rw [rawOrder_eq,raw_inputOrder]
    rfl
  have heq : sparseStripCore T = Rails.Strips.assemble (integerTile data) H (3*R+1) := by
    unfold sparseStripCore stripFamilyTileAt
    dsimp only
    change (let a := reserveData (parameterData S,Fs)
            Rails.Strips.assemble (integerTile (a.1.2.1*(reservedPartition a).1,
              stackCodes (a.1.2.1,reservedPartition a,Fs))) H (3*a.2.2+1)) = _
    rw [hdata]
  have hpos : 0<data.1 := Nat.mul_pos hN hc.1.pos
  have hne := stackCodes_nonempty N c Fs hs hc hf.nonempty
  have hcol : HasForwardColumn data (3*R) := by
    apply stack_hasForwardColumn N (P^4) Fs c hc hcop hN i R (inputOrder_pos E) hres
    rw [List.getD_eq_getElem _ _ i.isLt]
    have hget : Fs[i.val]=kernelCode (parameterData S) := by
      dsimp only [i,kernelIndex]
      apply List.getElem_idxOf
    rw [hget]
    exact hkernel
  have hgap : 3*R<2*data.1 := by
    have hR : R≤N := Nat.le_of_dvd hN (inputOrder_dvd E)
    have hRpos : 0<R := inputOrder_pos E
    have hq : P^4<c.1 := hc.2.1
    have hq' : 3<c.1 := lt_of_lt_of_le (by
      exact (by decide : 3<256^4).trans_le (Nat.pow_le_pow_left (le_max_right _ _) _)) hq.le
    have hm := Nat.mul_le_mul_right c.1 hR
    have hreq : 3*R<R*c.1 := by
      simpa only [Nat.mul_comm c.1 R] using Nat.mul_lt_mul_of_pos_right hq' hRpos
    change _<2*(N*c.1)
    omega
  have hsupport : ∀ f∈data.2, TestSupportAt 175 (fun _ => H) f.1 := by
    intro f hf'
    rcases stack_strip N c Fs H (sparse_strip T) f hf' with ⟨hx,hy|⟨s,hs',hy⟩⟩
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr ⟨s,by omega,hx,hy⟩
  have hconn := connected_forward data 175 (fun _ => H) _ hpos hgap hcol hsupport
  have hcorrect := Rails.SlotAssembly.correct _ (Rails.Strips.valid H) (integerTile data)
    (Rails.Strips.railHeight (3*R+1))
  rw [heq]
  refine ⟨Rails.SlotAssembly.nonempty _ (Rails.Strips.valid H) _ _
    (integerTile_nonempty data hne),hconn,?_,?_⟩
  · exact (SparseTernary.finite_system_iff_wang E).trans ((sparse_family_solution_iff T).trans
      ((stackCodes_correct_coprime N (P^4) hN Fs hs c hc hcop).trans
        ((integerTile_correct MSS.rigidity data hpos hne).trans hcorrect.symm)))
  · exact reservedVolume data hpos 175 (fun _ => H) R _ c.1 _ hcap'
      (stack_mass N (P^4) hN Fs hs c hc hcop _ hf.mass)


private theorem inputOrder_budget (T : System) (hB : T.alphabet=3) :
    inputOrder (parameters T)≤primeBudget T^(9*T.width+8) := by
  let P := primeBudget T
  have hp := parameters_bounded_budget T hB
  unfold inputOrder
  rw [Fintype.prod_sum_type]
  calc
    _ ≤ (∏ _n : Column T, P^9)*(∏ _t : Fin 2, P^4) :=
      Nat.mul_le_mul (Finset.prod_le_prod fun n _ => BudgetSize.r_le_nine _ (le_max_right _ _) hB hp _)
        (Finset.prod_le_prod fun t _ => BudgetSize.seed_r_le _ hp t)
    _ = _ := by simp [P,Column,←pow_mul,←pow_add]

theorem sparseStripCore_channel_bound (T : LeanWang.TileSet) (hn : 0<T.length) :
    (sparseStripCore T).length≤primeBudget (SparseTernary.system T)^(21*(SparseTernary.system T).width+78)*
      3^(4*(SparseTernary.system T).width+4) := by
  let S := SparseTernary.system T
  let E := parameters S
  let w := S.width
  let P := primeBudget S
  let H := compactHorizontal (parameterData S)
  let R := inputOrder E
  let J := MassSize.mass E
  let L := freshCap (max (sparseFamily T).length (P^2)) (P^4)
  have hw : 48≤w := by have := SparseTernary.raw_width_le T.length; exact le_trans (by omega) this
  have hP : 256≤P := le_max_right _ _
  have hHlo : 175≤H := by
    have hh := (compactHorizontal_support S rfl (SparseTernary.slope_bound T)).modulus
    simpa [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] using hh
  have hH : H≤P^16 := compactHorizontal_le S
  have hR : R≤P^(9*w+8) := inputOrder_budget S rfl
  have hJ : J≤P^(12*w+20) := MassSize.mass_bound E rfl (parameters_bounded_budget S rfl)
  have hL : L≤P^3*3^(2*w+2) := family_freshCap_bound S _ (sparseFamily_budget T hn) hw
  have hM : max (H^2) (R*L)≤P^(9*w+11)*3^(2*w+2) := by
    apply max_le
    · apply (Nat.pow_le_pow_left hH 2).trans
      rw [←pow_mul]
      exact (Nat.pow_le_pow_right (by omega : 1≤P) (by omega : 16*2≤9*w+11)).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    · calc
        _ ≤ P^(9*w+8)*(P^3*3^(2*w+2)) := Nat.mul_le_mul hR hL
        _ = _ := by rw [←mul_assoc,←pow_add]
  have hmass : J*L≤P^(12*w+23)*3^(2*w+2) := by
    calc
      _ ≤ P^(12*w+20)*(P^3*3^(2*w+2)) := Nat.mul_le_mul hJ hL
      _ = _ := by rw [←mul_assoc,←pow_add]
  have hK : 2^24*549072*8003^4≤P^12 :=
    (by norm_num : 2^24*549072*8003^4≤256^12).trans (Nat.pow_le_pow_left hP 12)
  apply (sparseStripCore_facts T hn).2.2.2.trans
  have hl4 : 4≤L := by unfold L freshCap Stacking.logPartitionThreshold; omega
  apply (reservedVolumeCap_le _ _ _ _ (inputOrder_pos E) hl4).trans
  apply (volumeCap_coarse H R J L hHlo).trans
  calc
    _ = (2^24*549072*8003^4)*H^2*(J*L)*max (H^2) (R*L) := by ring
    _ ≤ P^12*(P^16)^2*(P^(12*w+23)*3^(2*w+2))*(P^(9*w+11)*3^(2*w+2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.pow_le_pow_left hH 2)) hmass) hM
    _ = _ := by
      change _ = P^(21*w+78)*3^(4*w+4)
      simp only [mul_pow,←pow_mul]
      ring_nf

private theorem volume_mono {H R J L L' : ℕ} (hL : L≤L') :
    reservedVolumeCap 175 (fun _ => H) R J L≤reservedVolumeCap 175 (fun _ => H) R J L' := by
  dsimp only [reservedVolumeCap]
  gcongr

private theorem small_cap (T : LeanWang.TileSet) (hn : 0<T.length) (i : Fin 5)
    (hw : (SparseTernary.system T).width=SmallProfiles.width i) :
    (sparseStripCore T).length≤reservedVolumeCap 175 (fun _ => SmallProfiles.horizontal i)
      ((SmallProfiles.profile i).order (SmallProfiles.width i) /
        (SmallProfiles.profile i).mass (SmallProfiles.width i))
      ((SmallProfiles.profile i).mass (SmallProfiles.width i)) (2^15*3^(2*SmallProfiles.width i+2)) := by
  let S := SparseTernary.system T
  have hW : 48≤S.width := by change 48≤(SparseTernary.system T).width; rw [hw]; fin_cases i <;> decide
  have hW' : S.width≤112 := by change (SparseTernary.system T).width≤112; rw [hw]; fin_cases i <;> decide
  have hl := family_small_freshCap_bound S _ (sparseFamily_budget T hn) hW hW'
  have hb := (sparseStripCore_facts T hn).2.2.2
  rw [compactHorizontal_small _ i hw rfl,inputOrder_eq_div,
    parameters_small_order _ i hw rfl,parameters_small_mass _ i hw rfl] at hb
  change _≤2^15*3^(2*(SparseTernary.system T).width+2) at hl
  rw [hw] at hl hb
  exact hb.trans (volume_mono hl)

theorem sparseStripCore_width64 (T : LeanWang.TileSet) (hn : 0<T.length)
    (hw : (SparseTernary.system T).width=64) : (sparseStripCore T).length≤2^5636 :=
  (small_cap T hn 1 hw).trans (by decide +kernel)

theorem sparseStripCore_width80 (T : LeanWang.TileSet) (hn : 0<T.length)
    (hw : (SparseTernary.system T).width=80) : (sparseStripCore T).length≤2^7218 :=
  (small_cap T hn 2 hw).trans (by decide +kernel)

end
end TranslationTiling.FiniteCompiler.Effective
