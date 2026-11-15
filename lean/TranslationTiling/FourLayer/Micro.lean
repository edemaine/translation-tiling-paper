import TranslationTiling.FourLayer.LocalGeometry
import TranslationTiling.Proofs.KimPieceConnectivity

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m]

def MicroFiber (p q : Equiv.Perm (Fin m)) (i : Fin m) (r : Lattice 3) : Prop :=
  Rect (scales m) r ∧ color m p q (block r)=i ∧ ∀ j, r≠dent (scales m) j

def center (b : Lattice 3) : Lattice 3 := 3 • b+![1,1,1]

theorem corner_injective : Function.Injective (corner m) := by
  have hm := NeZero.pos m
  intro i j he
  by_contra hij
  have h := congrFun he i
  fin_cases i <;> fin_cases j <;> simp_all [corner,widths] <;> omega

theorem micro_box (b c : Lattice 3) (hb : InBox m b) (hc : c∈Kim.cube 3) :
    Rect (scales m) (3 • b+c) ∧ block (3 • b+c)=b := by
  constructor
  · intro i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    have hh : 0≤b i ∧ b i<(widths m i:ℤ) := by
      fin_cases i <;> simp [InBox,widths] at hb ⊢ <;> omega
    change 0≤3*b i+c i ∧ 3*b i+c i<(scales m i:ℤ)
    simp only [scales,Nat.cast_mul,Nat.cast_ofNat]
    omega
  · ext i
    have hi := (Kim.mem_cube_iff 3 _).mp hc i
    change (3*b i+c i)/3=b i
    omega

theorem dent_as_block (i : Fin 3) :
    dent (scales m) i=3 • corner m i+Kim.defectOffset i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [dent,gridMap,scales,widths,corner,Kim.defectOffset,Kim.bumpAt] <;> ring

private theorem lift_micro_path (p q : Equiv.Perm (Fin m)) (i : Fin m) (b : Lattice 3)
    (hb : Fiber m p q i b) {c d : Lattice 3}
    (h : FacePath (fun z => z∈Kim.cube 3 ∧ ∀ j, 3 • b+z≠dent (scales m) j) c d) :
    FacePath (MicroFiber m p q i) (3 • b+c) (3 • b+d) := by
  have mem (z) (hz : z∈Kim.cube 3 ∧ ∀ j, 3 • b+z≠dent (scales m) j) :
      MicroFiber m p q i (3 • b+z) := by
    have hh := micro_box m b z hb.1 hz.1
    exact ⟨hh.1,by rw [hh.2]; exact hb.2,hz.2⟩
  apply Relation.ReflTransGen.lift (fun z => 3 • b+z) _ c d h
  intro x y hxy
  exact ⟨mem x hxy.1,mem y hxy.2.1,Kim.adjacent_add_left _ hxy.2.2⟩

theorem block_path_center (p q : Equiv.Perm (Fin m)) (i : Fin m) (b c : Lattice 3)
    (hb : Fiber m p q i b) (hc : c∈Kim.cube 3)
    (hn : ∀ j, 3 • b+c≠dent (scales m) j) :
    FacePath (MicroFiber m p q i) (3 • b+c) (center b) := by
  apply lift_micro_path m p q i b hb
  by_cases hcorner : ∃ k, b=corner m k
  · obtain ⟨k,hk⟩ := hcorner
    have hne : c≠(![1,1,1] : Lattice 3)+Pi.single k 1 := by
      intro he
      apply hn k
      rw [hk,dent_as_block,he]
      congr 1
      ext j
      fin_cases k <;> fin_cases j <;> simp [Kim.defectOffset]
    apply FacePath.mono (Kim.punctured_block_path k c hc hne)
    intro z hz
    refine ⟨hz.1,fun j hj => ?_⟩
    have hh := congrArg block hj
    rw [(micro_box m b z hb.1 hz.1).2,dent_block] at hh
    have hkj : k=j := corner_injective m (hk.symm.trans hh)
    subst j
    apply hz.2
    rw [dent_as_block,hk] at hj
    have he : z=Kim.defectOffset k := add_left_cancel hj
    rw [he]
    ext j
    fin_cases k <;> fin_cases j <;> simp [Kim.defectOffset]
  · apply FacePath.box3 _ (0 : Lattice 3) (fun _ => 2) c ![1,1,1]
    · intro j
      change 0≤c j ∧ c j≤2
      have hh := (Kim.mem_cube_iff 3 _).mp hc j
      omega
    · intro j; fin_cases j <;> simp
    · intro z hz
      have hzc : z∈Kim.cube 3 := (Kim.mem_cube_iff 3 _).mpr (fun j => by have hh := hz j; change 0≤z j ∧ z j≤2 at hh; omega)
      refine ⟨hzc,fun j hj => ?_⟩
      have hh := congrArg block hj
      rw [(micro_box m b z hb.1 hzc).2,dent_block] at hh
      exact hcorner ⟨j,hh⟩

theorem micro_path_center (p q : Equiv.Perm (Fin m)) (i : Fin m) (r : Lattice 3)
    (hr : MicroFiber m p q i r) : FacePath (MicroFiber m p q i) r (center (block r)) := by
  let c : Lattice 3 := fun j => r j%3
  have hc : c∈Kim.cube 3 := (Kim.mem_cube_iff 3 _).mpr (fun j =>
    ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩)
  have he : 3 • block r+c=r := by
    ext j
    exact Int.mul_ediv_add_emod (r j) 3
  have h := block_path_center m p q i (block r) c ⟨block_mem m hr.1,hr.2.1⟩ hc
    (fun j => by simpa only [he] using hr.2.2 j)
  simpa only [he] using h

theorem center_mem (p q : Equiv.Perm (Fin m)) (i : Fin m) (b : Lattice 3)
    (hb : Fiber m p q i b) : MicroFiber m p q i (center b) := by
  have hc : (![1,1,1] : Lattice 3)∈Kim.cube 3 := by decide
  have hh := micro_box m b _ hb.1 hc
  refine ⟨hh.1,by simpa only [center,hh.2] using hb.2,fun j hj => ?_⟩
  have h := congrFun hj j
  fin_cases j <;> simp [center,dent,gridMap,scales,widths,Kim.bumpAt] at h <;> omega

theorem centers_edge (p q : Equiv.Perm (Fin m)) (i : Fin m) {b d : Lattice 3}
    (hb : Fiber m p q i b) (hd : Fiber m p q i d) (k : Fin 3) (he : d=b+Pi.single k 1) :
    FacePath (MicroFiber m p q i) (center b) (center d) := by
  let c2 := Function.update (![1,1,1] : Lattice 3) k 2
  let c0 := Function.update (![1,1,1] : Lattice 3) k 0
  have h2 : c2∈Kim.cube 3 := by fin_cases k <;> decide
  have h0 : c0∈Kim.cube 3 := by fin_cases k <;> decide
  have hn2 (j : Fin 3) : 3 • b+c2≠dent (scales m) j := by
    intro h
    have hh := congrArg block h
    rw [(micro_box m b c2 hb.1 h2).2,dent_block] at hh
    by_cases hj : j=k
    · subst j
      have hdk : 0≤d k ∧ d k<(widths m k:ℤ) := by
        have hbox := hd.1
        fin_cases k <;> simp [InBox,widths] at hbox ⊢ <;> omega
      have hek := congrFun he k
      have hbk := congrFun hh k
      simp [corner] at hbk
      simp at hek
      omega
    · have hcoord := congrFun h k
      have hne : k.val≠j.val := fun h => hj (Fin.ext h).symm
      simp [c2,dent,gridMap,Pi.single_apply,Kim.bumpAt,hne,Ne.symm hj] at hcoord
      omega
  have hn0 (j : Fin 3) : 3 • d+c0≠dent (scales m) j := by
    intro h
    have hh := congrFun h k
    by_cases hj : k=j
    · subst j
      simp [c0,dent,gridMap,Kim.bumpAt,scales] at hh
      omega
    · have hne : k.val≠j.val := fun h => hj (Fin.ext h)
      simp [c0,dent,gridMap,Pi.single_apply,Kim.bumpAt,hne,hj] at hh
      omega
  have hm2 : MicroFiber m p q i (3 • b+c2) := by
    have hh := micro_box m b c2 hb.1 h2
    exact ⟨hh.1,by rw [hh.2]; exact hb.2,hn2⟩
  have hm0 : MicroFiber m p q i (3 • d+c0) := by
    have hh := micro_box m d c0 hd.1 h0
    exact ⟨hh.1,by rw [hh.2]; exact hd.2,hn0⟩
  have hstep : FaceAdjacent (3 • b+c2) (3 • d+c0) := by
    refine ⟨k,Or.inl ?_⟩
    rw [he]
    ext j
    by_cases hj : j=k <;> simp [c2,c0,Pi.single_apply,hj,Pi.smul_apply,nsmul_eq_mul] <;> ring
  exact ((FacePath.reverse (block_path_center m p q i b c2 hb h2 hn2)).trans
    (FacePath.step hm2 hm0 hstep)).trans (block_path_center m p q i d c0 hd h0 hn0)

theorem centers_path (p q : Equiv.Perm (Fin m)) (i : Fin m) {b d : Lattice 3}
    (h : FacePath (Fiber m p q i) b d) :
    FacePath (MicroFiber m p q i) (center b) (center d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d h hcd ih =>
    obtain ⟨k,hk | hk⟩ := hcd.2.2
    · exact ih.trans (centers_edge m p q i hcd.1 hcd.2.1 k hk)
    · exact ih.trans (FacePath.reverse (centers_edge m p q i hcd.2.1 hcd.1 k hk))

theorem micro_connected (p q : Equiv.Perm (Fin m)) (i : Fin m) {r t : Lattice 3}
    (hr : MicroFiber m p q i r) (ht : MicroFiber m p q i t) :
    FacePath (MicroFiber m p q i) r t :=
  ((micro_path_center m p q i r hr).trans (centers_path m p q i
    (fiber_connected m p q i ⟨block_mem m hr.1,hr.2.1⟩ ⟨block_mem m ht.1,ht.2.1⟩))).trans
    (FacePath.reverse (micro_path_center m p q i t ht))

end
end TranslationTiling.FourLayer
