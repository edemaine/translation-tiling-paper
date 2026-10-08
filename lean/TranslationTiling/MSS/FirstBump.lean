import TranslationTiling.MSS.ComponentIsolation
import Mathlib.Tactic.Abel

/-! The first detached frame forces a translate in the first coordinate. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

def firstBumpCenter : Lattice 3 := scale • Pi.single 0 1 + marker 1

theorem first_bump_center_not_mem (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5) :
    firstBumpCenter ∉ component Q j := by
  have hp : firstBumpCenter 0 = 213 := by norm_num [firstBumpCenter, marker]
  intro hv
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv | hv
    · have hb := (mem_box_iff 100 _).mp (Finset.mem_sdiff.mp hv).1 0
      rw [hp] at hb
      norm_num at hb
    · obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      by_cases hi : i = 0
      · subst i
        have hu0 : u = 0 := by
          have he' : firstBumpCenter + u = firstBumpCenter := he
          exact add_left_cancel (he'.trans (add_zero _).symm)
        rw [hu0] at hu
        obtain ⟨_, k, hk⟩ := (mem_frame_iff 1 (by omega) _).mp hu
        simp only [Pi.zero_apply, Nat.cast_one] at hk
        omega
      · have h0 := congrFun he 0
        have hb := ((mem_frame_iff (i.val + 1) (by omega) _).mp hu).1 0
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi),
          smul_eq_mul, mul_zero, zero_add, marker, hp] at h0
        push_cast at h0
        have hi3 := i.isLt
        omega
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    have h0 := congrFun he 0
    have hb := ((mem_frame_iff j hj _).mp hu).1 0
    simp only [Pi.add_apply, Pi.smul_apply, kernelStep,
      if_neg (by decide : (0 : Fin 3) ≠ 2), smul_eq_mul, mul_zero, zero_add,
      marker, hp] at h0
    push_cast at h0
    omega

theorem adjacent_sub_mem_frame_one {p z : Lattice 3} (h : FaceAdjacent p z) :
    z - p ∈ frame 1 := by
  obtain ⟨i, h | h⟩ := h
  · have he : z - p = Pi.single i 1 := by rw [h]; abel
    rw [he]
    apply (mem_frame_iff 1 (by omega) _).mpr
    refine ⟨?_, i, Or.inr (by simp)⟩
    intro k
    by_cases hk : k = i
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  · have he : z - p = -Pi.single i 1 := by rw [h]; abel
    rw [he]
    apply (mem_frame_iff 1 (by omega) _).mpr
    refine ⟨?_, i, Or.inl (by simp)⟩
    intro k
    by_cases hk : k = i
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]

theorem first_bump_neighbor_mem (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    {z : Lattice 3} (hz : FaceAdjacent firstBumpCenter z) : z ∈ component Q j := by
  have h := common_bump_mem_component Q j hj hj5 0 (adjacent_sub_mem_frame_one hz)
  simpa only [Fin.val_zero, zero_add, firstBumpCenter, add_sub_cancel] using h

abbrev Placement (Q : ℕ) (C₁ C₂ : Set (Lattice 3)) :=
  Sum (C₁ × ↥(component Q 4)) (C₂ × ↥(component Q 5))

namespace Placement

def center {Q C₁ C₂} : Placement Q C₁ C₂ → Lattice 3
  | .inl z => z.1.val
  | .inr z => z.1.val

def vertex {Q C₁ C₂} : Placement Q C₁ C₂ → Lattice 3
  | .inl z => z.2.val
  | .inr z => z.2.val

def radius {Q C₁ C₂} : Placement Q C₁ C₂ → ℕ
  | .inl _ => 4
  | .inr _ => 5

def position {Q C₁ C₂} (a : Placement Q C₁ C₂) : Lattice 3 := a.center + a.vertex

theorem radius_pos {Q C₁ C₂} (a : Placement Q C₁ C₂) : 0 < a.radius := by
  cases a <;> simp only [radius] <;> omega

theorem radius_le {Q C₁ C₂} (a : Placement Q C₁ C₂) : a.radius ≤ 5 := by
  cases a <;> simp only [radius] <;> omega

theorem vertex_mem {Q C₁ C₂} (a : Placement Q C₁ C₂) :
    a.vertex ∈ component Q a.radius := by
  cases a with
  | inl z => exact z.2.property
  | inr z => exact z.2.property

theorem center_mem {Q C₁ C₂} (a : Placement Q C₁ C₂) : a.center ∈ C₁ ∪ C₂ := by
  cases a with
  | inl z => exact Or.inl z.1.property
  | inr z => exact Or.inr z.1.property

def withVertex {Q C₁ C₂} (a : Placement Q C₁ C₂) (v : Lattice 3)
    (hv : v ∈ component Q a.radius) : Placement Q C₁ C₂ := match a with
  | .inl z => .inl (z.1, ⟨v, hv⟩)
  | .inr z => .inr (z.1, ⟨v, hv⟩)

@[simp] theorem center_withVertex {Q C₁ C₂} (a : Placement Q C₁ C₂) (v) (hv) :
    (a.withVertex v hv).center = a.center := by cases a <;> rfl

@[simp] theorem radius_withVertex {Q C₁ C₂} (a : Placement Q C₁ C₂) (v) (hv) :
    (a.withVertex v hv).radius = a.radius := by cases a <;> rfl

@[simp] theorem vertex_withVertex {Q C₁ C₂} (a : Placement Q C₁ C₂) (v) (hv) :
    (a.withVertex v hv).vertex = v := by cases a <;> rfl

end Placement

theorem mixed_placement_bijective {Q C₁ C₂} (h : MixedTiling Q C₁ C₂) :
    Function.Bijective (Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂)) := by
  have he : Placement.position (Q := Q) (C₁ := C₁) (C₂ := C₂) =
      Sum.elim (fun z : C₁ × ↥(component Q 4) => z.1.val + z.2.val)
        (fun z : C₂ × ↥(component Q 5) => z.1.val + z.2.val) := by
    funext a; cases a <;> rfl
  rwa [he]

theorem mixed_first_forward {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) : c + scale • Pi.single 0 1 ∈ C₁ ∪ C₂ := by
  have hb := mixed_placement_bijective h
  obtain ⟨a, ha⟩ : ∃ a : Placement Q C₁ C₂, a.center = c := by
    rcases hc with hc | hc
    · exact ⟨.inl (⟨c, hc⟩, ⟨0, zero_mem_component Q 4 (by omega)⟩), rfl⟩
    · exact ⟨.inr (⟨c, hc⟩, ⟨0, zero_mem_component Q 5 (by omega)⟩), rfl⟩
  obtain ⟨b, hbpos⟩ := hb.2 (c + firstBumpCenter)
  have hiso : ∀ w ∈ component Q b.radius, ¬ FaceAdjacent b.vertex w := by
    intro w hw hadj
    let b' := b.withVertex w hw
    let z := b.center + w - c
    have hzadj : FaceAdjacent firstBumpCenter z := by
      have hh := adjacent_add b.center hadj
      have hh' := adjacent_add (-c) hh
      have hep : -c + (b.center + b.vertex) = firstBumpCenter := by
        rw [← Placement.position, hbpos]; abel
      have hez : -c + (b.center + w) = z := by dsimp [z]; abel
      rwa [hep, hez] at hh'
    have hz := first_bump_neighbor_mem Q a.radius a.radius_pos a.radius_le hzadj
    let a' := a.withVertex z hz
    have hepos : a'.position = b'.position := by
      simp only [Placement.position, Placement.center_withVertex,
        Placement.vertex_withVertex, a', b', ha]
      dsimp [z]; abel
    have he := hb.1 hepos
    have hec : a.center = b.center := by
      simpa only [a', b', Placement.center_withVertex] using congrArg Placement.center he
    have her : a.radius = b.radius := by
      simpa only [a', b', Placement.radius_withVertex] using congrArg Placement.radius he
    have hp : b.vertex = firstBumpCenter := by
      have he' := hbpos
      rw [Placement.position, ← hec, ha] at he'
      exact add_left_cancel he'
    have hm := b.vertex_mem
    rw [← her, hp] at hm
    exact first_bump_center_not_mem Q a.radius a.radius_pos a.radius_le hm
  have hv := component_isolated_point Q b.radius b.radius_pos b.radius_le b.vertex
    b.vertex_mem hiso
  have hec : b.center = c + scale • Pi.single 0 1 := by
    have hh := hbpos
    rw [Placement.position, hv, firstBumpCenter, ← add_assoc] at hh
    exact add_right_cancel hh
  rw [← hec]
  exact b.center_mem

end
end TranslationTiling.MSS
