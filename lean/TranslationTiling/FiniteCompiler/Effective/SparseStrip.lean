import TranslationTiling.FiniteCompiler.StripVolume

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

private def stripFamilyTileAt (z : StripFamilyData) : Tile 3 :=
  let p := z.1.1
  let data := familyCyclic z.1
  Rails.Strips.assemble (integerTile data) z.2 ((rawModuli p).prod*(data.1/rawOrder p))

private def stripAssemblyData (z : ParameterData × ℕ × CyclicTileData) :
    Tile 3 × ℕ × ℕ :=
  (integerTile z.2.2,z.2.1,(rawModuli z.1).prod*(z.2.2.1/rawOrder z.1))

private theorem stripAssemblyData_primrec : Primrec stripAssemblyData := by
  have hp : Primrec (fun z : ParameterData × ℕ × CyclicTileData => z.1) := Primrec.fst
  have hd : Primrec (fun z : ParameterData × ℕ × CyclicTileData => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hq : Primrec (fun z : ParameterData × ℕ × CyclicTileData => z.2.2.1) :=
    Primrec.fst.comp hd
  have hR : Primrec (fun z : ParameterData × ℕ × CyclicTileData => (rawModuli z.1).prod) :=
    product_primrec.comp (rawModuli_primrec.comp hp)
  exact (integerTile_primrec.comp hd).pair
    ((Primrec.fst.comp Primrec.snd).pair (natMul hR (natDiv hq (rawOrder_primrec.comp hp))))

private theorem stripFamilyTileAt_computable : Computable stripFamilyTileAt := by
  have hd : Computable (fun z : StripFamilyData => familyCyclic z.1) :=
    familyCyclic_computable.comp (g:=Prod.fst) Computable.fst
  have hp : Primrec (fun z : StripFamilyData => z.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Computable (fun z : StripFamilyData =>
      (z.1.1,z.2,familyCyclic z.1)) := hp.to_comp.pair (Computable.snd.pair hd)
  have hs : Computable (fun z : StripFamilyData =>
      stripAssemblyData (z.1.1,z.2,familyCyclic z.1)) :=
    stripAssemblyData_primrec.to_comp.comp (f:=stripAssemblyData) ht
  exact (Rails.Strips.assemble_computable.comp
    (f:=fun z : Tile 3 × ℕ × ℕ => Rails.Strips.assemble z.1 z.2.1 z.2.2)
    (g:=fun z : StripFamilyData => stripAssemblyData (z.1.1,z.2,familyCyclic z.1)) hs).of_eq
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
    ∃ F∈sparseFamily T, ∀ k : ℤ,
      (((0:Plane), ((inputOrder (parameters (SparseTernary.system T)):ℤ)*k : ℤ)) :
        Plane × ZMod (parameters (SparseTernary.system T)).cyclicOrder) ∈
      cyclicTileSet (parameters (SparseTernary.system T)).cyclicOrder F := by
  let E := parameters (SparseTernary.system T)
  have hk : kernelTile E∈decodedFamily E (sparseFamily T) := by
    rw [sparseFamily_correct]
    exact Finset.mem_union_left _ (kernelTile_mem_testTiles _)
  obtain ⟨F,hF,hEq⟩ := (mem_decodedFamily _ _ _).mp hk
  refine ⟨F,hF,fun k => ?_⟩
  have he := decodedTile_eq_image E F
  rw [hEq] at he
  have hmem := kernel_column E k
  rw [he,Finset.image_image] at hmem
  simpa using hmem

theorem sparseStripCore_facts (T : LeanWang.TileSet) (hn : 0<T.length) :
    sparseStripCore T≠[] ∧ FaceConnected (sparseStripCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sparseStripCore T)) ∧
    (sparseStripCore T).length≤volumeCap
      (compactHorizontal (parameterData (SparseTernary.system T)))
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
  have hr : FreshReady (Fs.length-1,N,P^4,X) := ⟨hN,by dsimp [X]; omega,hP,hpr⟩
  let c := freshPartition (Fs.length-1,N,P^4,X)
  have hc : PartitionValid (Fs.length-1) (P^4) c ∧ N.Coprime c.1 ∧ c.1≤freshCap X (P^4) :=
    freshPartition_spec _ hr
  let data : CyclicTileData := (N*c.1,stackCodes (N,c,Fs))
  have hdata : familyCyclic (parameterData S,Fs)=data := by
    unfold familyCyclic
    rw [rawOrder_eq]
    rfl
  have heq : sparseStripCore T = Rails.Strips.assemble (integerTile data) H (R*c.1) := by
    unfold sparseStripCore stripFamilyTileAt
    change Rails.Strips.assemble (integerTile (familyCyclic (parameterData S,Fs))) H _=_
    rw [hdata,raw_inputOrder,rawOrder_eq]
    have he : data.1/N=c.1 := by dsimp [data]; rw [Nat.mul_div_cancel_left _ hN]
    rw [he]
  have hpos : 0<data.1 := Nat.mul_pos hN hc.1.1.pos
  have hR : 0<R*c.1 := Nat.mul_pos (inputOrder_pos E) hc.1.1.pos
  have hdvd : R*c.1∣data.1 := mul_dvd_mul_right (inputOrder_dvd E) c.1
  have hne := stackCodes_nonempty N c Fs hs hc.1 hf.nonempty
  obtain ⟨F,hF,hkernel⟩ := sparse_kernel T
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hF
  have hcol : HasColumn data (R*c.1) := by
    apply stack_hasColumn N (P^4) Fs c hc.1 hc.2.1 hN ⟨i,hi⟩ R
    rw [List.getD_eq_getElem _ _ hi,he]
    exact hkernel
  have hconn := StripLift.connected data H _ hR hpos hdvd hcol
    (stack_strip N c Fs H (sparse_strip T))
  have hcorrect := Rails.SlotAssembly.correct _ (Rails.Strips.valid H) (integerTile data)
    (Rails.Strips.railHeight (R*c.1))
  rw [heq]
  refine ⟨Rails.SlotAssembly.nonempty _ (Rails.Strips.valid H) _ _
    (integerTile_nonempty data hne),hconn,?_,?_⟩
  · exact (SparseTernary.finite_system_iff_wang E).trans ((sparse_family_solution_iff T).trans
      ((stackCodes_correct_coprime N (P^4) hN Fs hs c hc.1 hc.2.1).trans
        ((integerTile_correct MSS.rigidity data hpos hne).trans hcorrect.symm)))
  · exact volume data hpos H R _ c.1 _ hc.2.2
      (stack_mass N (P^4) hN Fs hs c hc.1 hc.2.1 _ hf.mass)


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
    volumeCap H R J L≤volumeCap H R J L' := by
  dsimp only [volumeCap,shellCap,Rails.Strips.railHeight]
  gcongr

private theorem small_cap (T : LeanWang.TileSet) (hn : 0<T.length) (i : Fin 5)
    (hw : (SparseTernary.system T).width=SmallProfiles.width i) :
    (sparseStripCore T).length≤volumeCap (SmallProfiles.horizontal i)
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
    (hw : (SparseTernary.system T).width=64) : (sparseStripCore T).length≤2^5856 :=
  (small_cap T hn 1 hw).trans (by decide +kernel)

theorem sparseStripCore_width80 (T : LeanWang.TileSet) (hn : 0<T.length)
    (hw : (SparseTernary.system T).width=80) : (sparseStripCore T).length≤2^7488 :=
  (small_cap T hn 2 hw).trans (by decide +kernel)

end
end TranslationTiling.FiniteCompiler.Effective
