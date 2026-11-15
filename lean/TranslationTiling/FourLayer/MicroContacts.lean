import TranslationTiling.FourLayer.Micro

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable (m : ℕ) [NeZero m]

private theorem safe_z {r : Lattice 3} (h1 : r 2≠1) (h11 : r 2≠11) :
    ∀ j, r≠dent (scales m) j := by
  intro j he
  have h := congrFun he 2
  fin_cases j <;> simp [dent,gridMap,scales,widths,Kim.bumpAt] at h <;> omega

private theorem micro_mem (p q : Equiv.Perm (Fin m)) (i : Fin m) (b c : Lattice 3)
    (hb : Fiber m p q i b) (hc : c∈Kim.cube 3) (hn : ∀ j, 3 • b+c≠dent (scales m) j) :
    MicroFiber m p q i (3 • b+c) := by
  have hh := micro_box m b c hb.1 hc
  exact ⟨hh.1,by rw [hh.2]; exact hb.2,hn⟩

theorem internal_micro_contact (p q : Equiv.Perm (Fin m)) (i j : Fin m) :
    ∃ r t, MicroFiber m p q i r ∧ MicroFiber m p q j t ∧ t=r+Pi.single 2 1 := by
  have hi := i.isLt
  have hj := j.isLt
  let b : Lattice 3 := ![(j.val:ℤ),(i.val:ℤ),0]
  let d : Lattice 3 := ![(j.val:ℤ),(i.val:ℤ),1]
  let c2 : Lattice 3 := ![1,1,2]
  let c0 : Lattice 3 := ![1,1,0]
  have hb : Fiber m p q i b := by
    constructor
    · simp [b,InBox]; omega
    · simp [b,color]
  have hd : Fiber m p q j d := by
    constructor
    · simp [d,InBox]; omega
    · simp [d,color]
  refine ⟨3 • b+c2,3 • d+c0,?_,?_,?_⟩
  · exact micro_mem m p q i b c2 hb (by decide) (safe_z m (by simp [b,c2]) (by simp [b,c2]))
  · exact micro_mem m p q j d c0 hd (by decide) (safe_z m (by simp [d,c0]) (by simp [d,c0]))
  · ext k; fin_cases k <;> simp [b,d,c2,c0]

theorem x_micro_contact (p q : Equiv.Perm (Fin m)) (j : Fin m) :
    ∃ r t, MicroFiber m p q (p j) r ∧ MicroFiber m p q j t ∧
      r+Pi.single 0 1=gridMap (scales m) (Pi.single 0 1)+t := by
  have hj := j.isLt
  have hm := NeZero.pos m
  let b : Lattice 3 := ![2*(m:ℤ),(j.val:ℤ),2]
  let d : Lattice 3 := ![0,(j.val:ℤ),2]
  let c2 : Lattice 3 := ![2,1,1]
  let c0 : Lattice 3 := ![0,1,1]
  have hb : Fiber m p q (p j) b := by
    constructor
    · simp [b,InBox]; omega
    · simp [b,color,show ¬2*(m:ℤ)<m by omega]
  have hd : Fiber m p q j d := by
    constructor
    · simp [d,InBox]; omega
    · simp [d,color,NeZero.ne m]
  refine ⟨3 • b+c2,3 • d+c0,?_,?_,?_⟩
  · exact micro_mem m p q (p j) b c2 hb (by decide) (safe_z m (by simp [b,c2]) (by simp [b,c2]))
  · exact micro_mem m p q j d c0 hd (by decide) (safe_z m (by simp [d,c0]) (by simp [d,c0]))
  · ext k; fin_cases k <;> simp [b,d,c2,c0,scales,widths,gridMap] <;> ring

theorem y_micro_contact (p q : Equiv.Perm (Fin m)) (j : Fin m) :
    ∃ r t, MicroFiber m p q (q j) r ∧ MicroFiber m p q j t ∧
      r+Pi.single 1 1=gridMap (scales m) (Pi.single 1 1)+t := by
  have hj := j.isLt
  have hm := NeZero.pos m
  let b : Lattice 3 := ![(j.val:ℤ),2*(m:ℤ),3]
  let d : Lattice 3 := ![(j.val:ℤ),0,3]
  let c2 : Lattice 3 := ![1,2,1]
  let c0 : Lattice 3 := ![1,0,1]
  have hb : Fiber m p q (q j) b := by
    constructor
    · simp [b,InBox]; omega
    · simp [b,color,show ¬2*(m:ℤ)<m by omega]
  have hd : Fiber m p q j d := by
    constructor
    · simp [d,InBox]; omega
    · simp [d,color,NeZero.ne m]
  refine ⟨3 • b+c2,3 • d+c0,?_,?_,?_⟩
  · exact micro_mem m p q (q j) b c2 hb (by decide) (safe_z m (by simp [b,c2]) (by simp [b,c2]))
  · exact micro_mem m p q j d c0 hd (by decide) (safe_z m (by simp [d,c0]) (by simp [d,c0]))
  · ext k; fin_cases k <;> simp [b,d,c2,c0,scales,widths,gridMap] <;> ring

theorem z_micro_contact (p q : Equiv.Perm (Fin m)) (i j : Fin m) (hne : i≠j) :
    ∃ r t, MicroFiber m p q i r ∧ MicroFiber m p q j t ∧
      r+Pi.single 2 1=gridMap (scales m) (Pi.single 2 1)+t := by
  have hi := i.isLt
  have hj := j.isLt
  let b : Lattice 3 := ![(i.val:ℤ),(j.val:ℤ),3]
  let d : Lattice 3 := ![(i.val:ℤ),(j.val:ℤ),0]
  let c2 : Lattice 3 := ![1,1,2]
  let c0 : Lattice 3 := ![1,1,0]
  have hb : Fiber m p q i b := by
    constructor
    · simp [b,InBox]; omega
    · simp [b,color,show (j.val:ℤ)<m by exact_mod_cast hj]
  have hd : Fiber m p q j d := by
    constructor
    · simp [d,InBox]; omega
    · simp [d,color]
  have hn (k : Fin 3) : 3 • b+c2≠dent (scales m) k := by
    intro h
    have hz := congrFun h 2
    have hx := congrFun h 0
    have hy := congrFun h 1
    fin_cases k
    · simp [b,c2,dent,gridMap,scales,widths,Kim.bumpAt] at hz
    · simp [b,c2,dent,gridMap,scales,widths,Kim.bumpAt] at hz
    · simp [b,c2,dent,gridMap,scales,widths,Kim.bumpAt] at hx hy
      apply hne
      apply Fin.ext
      omega
  refine ⟨3 • b+c2,3 • d+c0,?_,?_,?_⟩
  · exact micro_mem m p q i b c2 hb (by decide) hn
  · exact micro_mem m p q j d c0 hd (by decide) (safe_z m (by simp [d,c0]) (by simp [d,c0]))
  · ext k; fin_cases k <;> simp [b,d,c2,c0,scales,widths,gridMap]

end
end TranslationTiling.FourLayer
