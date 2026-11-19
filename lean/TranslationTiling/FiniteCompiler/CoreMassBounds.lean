import TranslationTiling.FiniteCompiler.EncodedSystem

/-! Count the actual finite fibres of the test tiles, instead of their boxes. -/
namespace TranslationTiling.FiniteCompiler.MassSize

variable [SeedFrame]
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

abbrev Datum := ZMod (D T) × (∀ i : Channel T, K E i × P E i)
def mass : ℕ := D T * ∏ i : Channel T, E.r i * (E.a i*E.b i)
def datum (g : Ambient E) : Datum E :=
  (g.2.1,fun i => (targetBeta E g i,(g.2.2 i).2))

theorem datum_card : Fintype.card (Datum E)=mass E := by
  simp [Datum,mass,K,P,Fintype.card_prod,Fintype.card_pi]

theorem eq_of_q0_datum {v w : Ambient E} (hq : q0 E v=q0 E w)
    (hd : datum E v=datum E w) : v=w := by
  refine Prod.ext (congrArg (fun b : Base E => b.1) hq)
    (Prod.ext (congrArg (fun d : Datum E => d.1) hd) ?_)
  funext i
  have hb := congrArg (fun d : Datum E => (d.2 i).1) hd
  have hc := congrArg (fun d : Datum E => (d.2 i).2) hd
  dsimp only [datum] at hb hc
  refine Prod.ext ?_ hc
  rw [←shear_targetBeta E v i,←shear_targetBeta E w i]
  rw [hq,show v.1.1=w.1.1 from congrArg (fun b : Base E => b.1.1) hq,hb]

theorem graphTile_card_le (F : Finset (Ambient E)) (h : Plane)
    (d : Useful E → Low E) (hf : ∀ g∈F, q0 E g=(h,d (usefulProjection E g))) :
    F.card≤mass E := by
  rw [←datum_card E]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective (fun g : F => datum E g) (by
    intro v w he
    apply Subtype.ext
    apply eq_of_q0_datum E _ he
    rw [hf v v.property,hf w w.property]
    congr 1
    exact congrArg d (congrArg (fun d : Datum E => fun i => (d.2 i).2) he))

def otherMass (i : Channel T) : ℕ :=
  ∏ j : {j : Channel T // j≠i}, E.r j * (E.a j*E.b j)

abbrev OtherDatum (i : Channel T) := ∀ j : {j : Channel T // j≠i}, K E j × P E j

theorem other_card (i : Channel T) : Fintype.card (OtherDatum E i)=otherMass E i := by
  simp [OtherDatum,otherMass,K,P,Fintype.card_prod,Fintype.card_pi]

theorem other_prod (i : Channel T) :
    (E.r i*(E.a i*E.b i))*otherMass E i=∏ j : Channel T, E.r j*(E.a j*E.b j) := by
  have hh := Fintype.prod_subtype_mul_prod_subtype
    (fun j : Channel T => j=i) (fun j => E.r j*(E.a j*E.b j))
  have hval (j : {j : Channel T // j=i}) : (j : Channel T)=i := j.property
  simpa [otherMass,hval] using hh

def otherDatum (i : Channel T) (g : Ambient E) : OtherDatum E i :=
  fun j => (targetBeta E g j,(g.2.2 j).2)

theorem batch_injective (i : Channel T) (h : Plane) (e : P E i) (free : Bool)
    {v w : ↥(activationBatch E i h e free)}
    (hz : (v:Ambient E).2.1=(w:Ambient E).2.1)
    (ho : otherDatum E i v=otherDatum E i w) : v=w := by
  obtain ⟨vh,vk,vc,vl,vz⟩ := (mem_activationBatch E i h e free v).mp v.property
  obtain ⟨wh,wk,wc,wl,wz⟩ := (mem_activationBatch E i h e free w).mp w.property
  apply Subtype.ext
  refine Prod.ext (vh.trans wh.symm) (Prod.ext hz ?_)
  funext j
  by_cases hj : j=i
  · subst j; exact Prod.ext (vk.trans wk.symm) (vc.trans wc.symm)
  · have hb := congrArg (fun d : OtherDatum E i => (d ⟨j,hj⟩).1) ho
    have hc := congrArg (fun d : OtherDatum E i => (d ⟨j,hj⟩).2) ho
    dsimp only [otherDatum] at hb hc
    refine Prod.ext ?_ hc
    rw [←shear_targetBeta E v j,←shear_targetBeta E w j]
    change shear E j _ (low E j _) _ = shear E j _ (low E j _) _
    rw [vl j hj,wl j hj,show (v:Ambient E).1.1=(w:Ambient E).1.1 from
      congrArg Prod.fst (vh.trans wh.symm),hb]

theorem batch_card_true (i : Channel T) (h : Plane) (e : P E i) :
    (activationBatch E i h e true).card≤D T*otherMass E i := by
  have hh := Fintype.card_le_of_injective
    (fun g : ↥(activationBatch E i h e true) => ((g:Ambient E).2.1,otherDatum E i g))
    (by
      intro v w he
      exact batch_injective E i h e true
        (congrArg (fun d : ZMod (D T) × OtherDatum E i => d.1) he)
        (congrArg (fun d : ZMod (D T) × OtherDatum E i => d.2) he))
  simpa only [Fintype.card_coe,Fintype.card_prod,ZMod.card,other_card] using hh

theorem batch_card_false (i : Channel T) (h : Plane) (e : P E i) :
    (activationBatch E i h e false).card≤otherMass E i := by
  have hh := Fintype.card_le_of_injective
    (fun g : ↥(activationBatch E i h e false) => otherDatum E i g) (by
      intro v w he
      apply batch_injective E i h e false _ he
      have hv := ((mem_activationBatch E i h e false v).mp v.property).2.2.2.2
      have hw := ((mem_activationBatch E i h e false w).mp w.property).2.2.2.2
      simp only [Bool.false_eq_true,false_or] at hv hw
      exact hv.trans hw.symm)
  simpa only [Fintype.card_coe,other_card] using hh

theorem activation_card (n : Column T) : (ordinaryActivationTile E n).card≤mass E := by
  unfold ordinaryActivationTile
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun j _ => batch_card_true E _ _ _)).trans
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,ActivationIndex,Fintype.card_prod,
    K,ZMod.card,card_shiftIndex (E.a_two_le _) (E.b_two_le _)]
  rw [mass,←other_prod E (.inl n)]
  ring_nf
  exact le_rfl

theorem seed_card (t : Fin 2) : (seedActivationTile E t).card≤mass E := by
  unfold seedActivationTile
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun j _ => batch_card_false E _ _ _)).trans
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,SeedActivationIndex,ActivationIndex,
    Fintype.card_prod,K,ZMod.card,Residues,card_shiftIndex (E.a_two_le _) (E.b_two_le _)]
  rw [mass,←other_prod E (.inr t)]
  dsimp [D]
  ring_nf
  exact le_rfl

theorem test_card (F : Finset (Ambient E)) (hF : F∈testTiles E) : F.card≤mass E := by
  have hk : (kernelTile E).card≤mass E := graphTile_card_le E _ 0 (fun _ => 0)
    (by intro g hg; simpa using (mem_kernelTile E g).mp hg)
  have hc {t : ℕ} [NeZero t] (cy : ZMod t ↪ Channel T) (lab : ∀ j, Label T (cy j))
      (F : Finset (Ambient E)) (hf : F∈fixedCycleTiles E cy lab) : F.card≤mass E := by
    obtain rfl := Finset.mem_singleton.mp hf
    exact graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)
  rcases (mem_testTiles_iff E F).mp hF with rfl | hd | hw | hs | ⟨n,rfl⟩ | ⟨t,rfl⟩
  · exact hk
  · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hd
    rw [dependenceTile_card]; exact hk
  · obtain ⟨w,_,hf⟩ := Finset.mem_biUnion.mp hw; exact hc _ _ _ hf
  · obtain ⟨q,_,hf⟩ := Finset.mem_biUnion.mp hs; exact hc _ _ _ hf
  · exact activation_card E n
  · exact seed_card E t

end
end TranslationTiling.FiniteCompiler.MassSize
