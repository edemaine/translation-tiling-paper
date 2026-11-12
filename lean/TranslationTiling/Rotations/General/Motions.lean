import TranslationTiling.Rotations.Chambers
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.DeriveFintype

namespace TranslationTiling.Rotations.General

/-- Signed coordinate permutations in arbitrary dimension, including reflections. -/
@[ext] structure Orientation (d : ℕ) where
  axes : Equiv.Perm (Fin d)
  flip : Fin d → Bool
  deriving DecidableEq, Fintype

variable {d : ℕ}

def Orientation.sign (r : Orientation d) (i : Fin d) : ℤ := if r.flip i then -1 else 1

theorem Orientation.sign_sq (r : Orientation d) (i : Fin d) : r.sign i * r.sign i = 1 := by
  unfold sign; split_ifs <;> norm_num

def Orientation.linear (r : Orientation d) : Lattice d ≃+ Lattice d where
  toFun x i := r.sign i * x (r.axes i)
  invFun y j := r.sign (r.axes.symm j) * y (r.axes.symm j)
  left_inv x := by
    ext i
    simp only [Equiv.apply_symm_apply, ← mul_assoc, sign_sq, one_mul]
  right_inv y := by
    ext i
    simp only [Equiv.symm_apply_apply, ← mul_assoc, sign_sq, one_mul]
  map_add' x y := by ext i; exact mul_add _ _ _

@[simp] theorem Orientation.linear_apply (r : Orientation d) (x : Lattice d) (i : Fin d) :
    r.linear x i = r.sign i * x (r.axes i) := rfl

def Orientation.ident : Orientation d := ⟨Equiv.refl _, fun _ => false⟩

@[simp] theorem Orientation.ident_apply (x : Lattice d) : Orientation.ident.linear x = x := by
  ext i; simp [ident, linear, sign]

theorem Orientation.map_unit (r : Orientation d) (i : Fin d) :
    r.linear (Pi.single i 1) = r.sign (r.axes.symm i) • Pi.single (r.axes.symm i) 1 := by
  ext j
  by_cases h : j = r.axes.symm i
  · subst j; simp
  · have he : r.axes j ≠ i := by intro he; exact h ((r.axes.eq_symm_apply).mpr he)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne he]

theorem Orientation.adjacent (r : Orientation d) {x y : Lattice d}
    (h : FaceAdjacent x y) : FaceAdjacent (r.linear x) (r.linear y) := by
  have forward {a b : Lattice d} {i : Fin d} (he : b = a + Pi.single i 1) :
      FaceAdjacent (r.linear a) (r.linear b) := by
    rw [he, map_add, r.map_unit]
    refine ⟨r.axes.symm i, ?_⟩
    unfold Orientation.sign
    split_ifs
    · right
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · left
      simp
  obtain ⟨i, he | he⟩ := h
  · exact forward he
  · exact FacePath.adjacent_symm (forward he)

structure Motion (d : ℕ) where
  orientation : Orientation d
  offset : Lattice d
  deriving DecidableEq

def Motion.apply (m : Motion d) (x : Lattice d) : Lattice d := m.offset + m.orientation.linear x

def Motion.equiv (m : Motion d) : Lattice d ≃ Lattice d where
  toFun := m.apply
  invFun y := m.orientation.linear.symm (y - m.offset)
  left_inv x := by simp [Motion.apply]
  right_inv y := by simp [Motion.apply]

theorem Motion.injective (m : Motion d) : Function.Injective m.apply := m.equiv.injective

theorem Motion.adjacent (m : Motion d) {x y : Lattice d}
    (h : FaceAdjacent x y) : FaceAdjacent (m.apply x) (m.apply y) := by
  obtain ⟨i, he | he⟩ := m.orientation.adjacent h
  · exact ⟨i, Or.inl (by simp only [Motion.apply, he]; abel)⟩
  · exact ⟨i, Or.inr (by simp only [Motion.apply, he]; abel)⟩

theorem Motion.connected (m : Motion d) {S : Set (Lattice d)} (h : Connected S) :
    Connected (m.apply '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact Relation.ReflTransGen.lift m.apply
    (fun a b hab => ⟨Set.mem_image_of_mem _ hab.1,
      Set.mem_image_of_mem _ hab.2.1, m.adjacent hab.2.2⟩) x y (h x hx y hy)

def Orientation.inverse (r : Orientation d) : Orientation d :=
  ⟨r.axes.symm, fun i => r.flip (r.axes.symm i)⟩

@[simp] theorem Orientation.inverse_linear (r : Orientation d) :
    r.inverse.linear = r.linear.symm := by
  ext x i
  rfl

def Orientation.comp (r s : Orientation d) : Orientation d :=
  ⟨r.axes.trans s.axes, fun i => xor (r.flip i) (s.flip (r.axes i))⟩

@[simp] theorem Orientation.comp_linear (r s : Orientation d) (x : Lattice d) :
    (r.comp s).linear x = r.linear (s.linear x) := by
  ext i
  simp only [linear_apply, comp, Equiv.trans_apply, sign]
  have sign_xor (a b : Bool) : (if xor a b then (-1 : ℤ) else 1) =
      (if a then -1 else 1) * (if b then -1 else 1) := by
    cases a <;> cases b <;> decide
  rw [sign_xor]
  ring

def Motion.inverse (m : Motion d) : Motion d :=
  ⟨m.orientation.inverse, -m.orientation.linear.symm m.offset⟩

theorem Motion.inverse_apply (m : Motion d) (x : Lattice d) :
    m.inverse.apply x = m.orientation.linear.symm (x - m.offset) := by
  simp [inverse, Motion.apply, map_sub]
  abel

@[simp] theorem Motion.apply_inverse_apply (m : Motion d) (x : Lattice d) :
    m.apply (m.inverse.apply x) = x := by
  rw [Motion.inverse_apply]
  change m.offset + m.orientation.linear (m.orientation.linear.symm (x - m.offset)) = x
  rw [AddEquiv.apply_symm_apply]
  abel

@[simp] theorem Motion.inverse_apply_apply (m : Motion d) (x : Lattice d) :
    m.inverse.apply (m.apply x) = x := by
  rw [Motion.inverse_apply]
  simp [Motion.apply]

def Motion.comp (m n : Motion d) : Motion d :=
  ⟨m.orientation.comp n.orientation, m.offset + m.orientation.linear n.offset⟩

@[simp] theorem Motion.comp_apply (m n : Motion d) (x : Lattice d) :
    (m.comp n).apply x = m.apply (n.apply x) := by
  simp [comp, Motion.apply, map_add, add_assoc]

theorem Motion.preimage_eq (m : Motion d) (K : Set (Lattice d)) :
    m.apply ⁻¹' K = m.inverse.apply '' K := by
  ext x
  constructor
  · intro hx
    exact ⟨m.apply x, hx, m.inverse_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem Motion.pullback_component (m : Motion d) {S K : Set (Lattice d)} {v : Lattice d}
    (c : CutComponent (m.apply '' S) v K) :
    CutComponent S (m.inverse.apply v) (m.apply ⁻¹' K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := c.nonempty
    exact ⟨m.inverse.apply x, by simpa using hx⟩
  · intro x hx
    obtain ⟨y, hy, he⟩ := c.subset hx
    exact m.injective he ▸ hy
  · simpa using c.avoids
  · rw [m.preimage_eq]
    exact m.inverse.connected c.connected
  · intro x hx y hy hyv hxy
    apply c.closed _ hx _ (Set.mem_image_of_mem _ hy) ?_ (m.adjacent hxy)
    intro he
    apply hyv
    exact m.injective (by simpa using he)

end TranslationTiling.Rotations.General
