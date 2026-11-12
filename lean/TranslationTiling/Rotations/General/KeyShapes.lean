import TranslationTiling.Rotations.General.Parameters
import TranslationTiling.Rotations.General.Boxes

/-! Equal-volume keys with a one-voxel-wide, corner-mounted entrance neck.
Unlike the three-dimensional moment calculation, the recognition argument below
uses only coordinate extrema and the fact that a thick box cannot enter a thin neck. -/

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def keyLo : Lattice d := fun j => if j = 0 then neckLength d else 0

def keyHi (f : Face d) : Lattice d := fun j => keyLo j + (boxSide f j : ℤ) - 1

def KeyBox (f : Face d) : Set (Lattice d) := Box keyLo (keyHi f)

def Stem : Set (Lattice d) := {x | 1 ≤ x 0 ∧ x 0 < neckLength d ∧ ∀ j, j ≠ 0 → x j = 0}

def Key (f : Face d) : Set (Lattice d) := KeyBox f ∪ Stem

theorem key_bounds (f : Face d) (j : Fin d) : keyLo j ≤ keyHi f j := by
  have := boxSide_two_le f j
  dsimp [keyHi]
  omega

theorem keyBox_finite (f : Face d) : (KeyBox f).Finite := box_finite _ _

theorem keyBox_card (hd : 2 ≤ d) (f : Face d) : (KeyBox f).ncard = boxVolume d := by
  rw [KeyBox,box_ncard,← prod_boxSide hd f]
  apply Finset.prod_congr rfl
  intro j _
  simp [keyHi]

theorem keyBox_not_stem (f : Face d) {x : Lattice d} (hx : x ∈ KeyBox f) : x ∉ Stem := by
  intro hs
  have := (hx 0).1
  simp only [keyLo,ite_true] at this
  exact (not_le_of_gt hs.2.1) this

/-- A rectangle with at least two voxels in every direction cannot enter the thin stem. -/
theorem thick_box_in_keyBox (hd : 2 ≤ d) (f : Face d) {lo hi : Lattice d}
    (hw : ∀ j, lo j + 1 ≤ hi j) (hsub : Box lo hi ⊆ Key f) :
    Box lo hi ⊆ KeyBox f := by
  intro x hx
  rcases hsub hx with hc | hs
  · exact hc
  · exfalso
    let j : Fin d := ⟨1,by omega⟩
    have hj : j ≠ 0 := by intro h; have := congrArg Fin.val h; simp [j] at this
    let t : ℤ := if x j = hi j then x j - 1 else x j + 1
    let y : Lattice d := Function.update x j t
    have ht : lo j ≤ t ∧ t ≤ hi j := by
      have := hx j
      have := hw j
      dsimp [t]
      split_ifs <;> omega
    have hy : y ∈ Box lo hi := by
      intro i
      by_cases he : i = j
      · subst i; simpa [y] using ht
      · simpa [y,Function.update_of_ne he] using hx i
    have hy0 : y 0 = x 0 := by simp [y,Ne.symm hj]
    have hyt : y j ≠ 0 := by
      have hz := hs.2.2 j hj
      dsimp [y,t]
      simp only [Function.update_self]
      split_ifs <;> omega
    rcases hsub hy with hc | hs'
    · have := (hc 0).1
      simp only [keyLo,ite_true,hy0] at this
      exact (not_le_of_gt hs.2.1) this
    · exact hyt (hs'.2.2 j hj)

/-- Any isometry between complete keys sends the thick rectangular parts to each other. -/
theorem keyBox_image (hd : 2 ≤ d) (f g : Face d) (m : Motion d)
    (he : m.apply '' Key f = Key g) : m.apply '' KeyBox f = KeyBox g := by
  have hw (j : Fin d) : m.boxLo keyLo (keyHi f) j + 1 ≤ m.boxHi keyLo (keyHi f) j := by
    have := boxSide_two_le f (m.orientation.axes j)
    dsimp [Motion.boxLo,Motion.boxHi,keyHi]
    split_ifs <;> omega
  have sub : m.apply '' KeyBox f ⊆ KeyBox g := by
    rw [KeyBox,m.image_box]
    apply thick_box_in_keyBox hd g hw
    rw [← m.image_box]
    intro y hy
    rw [← he]
    exact Set.image_mono (Set.subset_union_left) hy
  apply Set.eq_of_subset_of_ncard_le sub _ (keyBox_finite g)
  rw [Set.ncard_image_of_injective _ m.injective,keyBox_card hd f,keyBox_card hd g]

/-- The uniquely shortest side identifies the face label under all grid isometries. -/
theorem key_label (hd : 2 ≤ d) (f g : Face d) (m : Motion d)
    (he : m.apply '' Key f = Key g) : f = g := by
  have hb := keyBox_image hd f g m he
  have hw (i : Fin d) : boxSide g i = boxSide f (m.orientation.axes i) := by
    have h := m.box_width (key_bounds f) (key_bounds g) hb i
    dsimp [keyHi] at h
    omega
  exact (boxSide_label hd g f m.orientation.axes hw).symm

/-- A complete key has no nontrivial signed-permutation symmetry. This also
rules out mapping one face's key to another face's key. -/
theorem key_rigid (hd : 2 ≤ d) (f g : Face d) (m : Motion d)
    (he : m.apply '' Key f = Key g) :
    f = g ∧ m.orientation = Orientation.ident ∧ m.offset = 0 := by
  have hfg := key_label hd f g m he
  subst g
  have hb := keyBox_image hd f f m he
  have ha (i : Fin d) : m.orientation.axes i = i := by
    apply boxSide_injective f
    have h := m.box_width (key_bounds f) (key_bounds f) hb i
    dsimp [keyHi] at h
    omega
  have hl : m.boxLo keyLo (keyHi f) = keyLo := by
    apply (box_bounds_eq _ (key_bounds f) (by simpa only [KeyBox,m.image_box] using hb)).1
    intro j
    have hj := boxSide_two_le f (m.orientation.axes j)
    dsimp [Motion.boxLo,Motion.boxHi,keyHi]
    split_ifs <;> omega
  let p : Lattice d := fun j => if j = 0 then 1 else 0
  have hp : p ∈ Stem := by
    refine ⟨?_,?_,?_⟩
    · simp [p]
    · simp only [p,ite_true]
      unfold neckLength
      omega
    · intro j hj; simp [p,hj]
  have hmp : m.apply p ∈ Stem := by
    have hmk : m.apply p ∈ Key f := by
      rw [← he]
      exact Set.mem_image_of_mem _ (Or.inr hp)
    rcases hmk with hc | hs
    · rw [← hb] at hc
      obtain ⟨y,hy,heq⟩ := hc
      have hyp := m.injective heq
      exact False.elim (keyBox_not_stem f (hyp ▸ hy) hp)
    · exact hs
  have hf (i : Fin d) : m.orientation.flip i = false := by
    by_contra hn
    have ht : m.orientation.flip i = true := by cases h : m.orientation.flip i <;> simp_all
    have hli := congrFun hl i
    simp only [Motion.boxLo,ha,ht,ite_true] at hli
    have hsi := boxSide_two_le f i
    by_cases hi : i = 0
    · subst i
      have hn := hmp.2.1
      simp only [Motion.apply,Pi.add_apply,Orientation.linear_apply,ha,Orientation.sign,
        ht,ite_true,p] at hn
      simp only [ite_true,keyHi,keyLo] at hli
      unfold neckLength at *
      omega
    · have hn := hmp.2.2 i hi
      simp only [Motion.apply,Pi.add_apply,Orientation.linear_apply,ha,Orientation.sign,
        ht,ite_true,p,ite_eq_right hi,mul_zero,add_zero] at hn
      simp only [keyHi,keyLo,ite_eq_right hi] at hli
      omega
  refine ⟨rfl,?_,?_⟩
  · apply Orientation.ext
    · exact Equiv.ext ha
    · exact funext hf
  · ext i
    have hli := congrFun hl i
    simp only [Motion.boxLo,ha,hf,ite_false] at hli
    simpa using hli

end TranslationTiling.Rotations.General
