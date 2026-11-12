import TranslationTiling.Rotations.BodyPaths

namespace TranslationTiling.Rotations.SixKeys

theorem update_ne {x v : Point} {i j : Fin 3} {t : ℤ}
    (hji : j ≠ i) (hx : x j ≠ v j) : Function.update x i t ≠ v := by
  intro he
  have hh := congrFun he j
  simp only [Function.update_of_ne hji] at hh
  exact hx hh

def Plane (i : Fin 3) (c : ℤ) : Set Point := {x | InCube x ∧ x i = c}

/-- A square grid of side 40 stays connected after one vertex deletion. -/
theorem plane_punctured (i : Fin 3) (c : ℤ) (hc : 0 ≤ c ∧ c ≤ 39) (v : Point) :
    Connected (Plane i c \ {v}) := by
  let j : Fin 3 := if i = 0 then 1 else 0
  let k : Fin 3 := if i = 2 then 1 else 2
  have hji : j ≠ i := by fin_cases i <;> decide
  have hki : k ≠ i := by fin_cases i <;> decide
  have hjk : j ≠ k := by fin_cases i <;> decide
  have cover (a : Fin 3) : a = i ∨ a = j ∨ a = k := by
    fin_cases i <;> fin_cases a <;> decide
  let cj : ℤ := if v j = 0 then 39 else 0
  let ck : ℤ := if v k = 0 then 39 else 0
  have hcj : 0 ≤ cj ∧ cj ≤ 39 ∧ cj ≠ v j := by dsimp [cj]; split_ifs <;> omega
  have hck : 0 ≤ ck ∧ ck ≤ 39 ∧ ck ≠ v k := by dsimp [ck]; split_ifs <;> omega
  let q : Point := fun a => if a = i then c else if a = j then cj else ck
  let P := fun z => z ∈ Plane i c ∧ z ≠ v
  have move (z : Point) (hz : z ∈ Plane i c) (a : Fin 3) (hai : a ≠ i)
      (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 39) (b : Fin 3) (hba : b ≠ a)
      (hzb : z b ≠ v b) : FacePath P z (Function.update z a t) := by
    apply FacePath.axis
    intro s hs hu
    have hbounds := hz.1 a
    have hst : 0 ≤ s ∧ s ≤ 39 := by
      rcases le_total (z a) t with hh | hh
      · rw [min_eq_left hh] at hs; rw [max_eq_right hh] at hu; omega
      · rw [min_eq_right hh] at hs; rw [max_eq_left hh] at hu; omega
    exact ⟨⟨inCube_update hz.1 a s hst, by simpa [Ne.symm hai] using hz.2⟩,
      update_ne hba hzb⟩
  have endJK (z : Point) (hz : z ∈ Plane i c) :
      Function.update (Function.update z j cj) k ck = q := by
    ext a
    rcases cover a with rfl | rfl | rfl <;>
      simp [q, hji, hki, Ne.symm hji, Ne.symm hki, hjk, Ne.symm hjk, hz.2]
  have endKJ (z : Point) (hz : z ∈ Plane i c) :
      Function.update (Function.update z k ck) j cj = q := by
    ext a
    rcases cover a with rfl | rfl | rfl <;>
      simp [q, hji, hki, Ne.symm hji, Ne.symm hki, hjk, Ne.symm hjk, hz.2]
  have path (z : Point) (hz : z ∈ Plane i c) (hzv : z ≠ v) : FacePath P z q := by
    by_cases hj : z j ≠ v j
    · have p₁ := move z hz k hki ck ⟨hck.1, hck.2.1⟩ j hjk hj
      have hz' : Function.update z k ck ∈ Plane i c :=
        ⟨inCube_update hz.1 k ck ⟨hck.1, hck.2.1⟩, by simpa [Ne.symm hki] using hz.2⟩
      have p₂ := move _ hz' j hji cj ⟨hcj.1, hcj.2.1⟩ k (Ne.symm hjk) (by simp [hck.2.2])
      rw [endKJ z hz] at p₂
      exact p₁.trans p₂
    · have hother : z i ≠ v i ∨ z k ≠ v k := by
        by_contra! hh
        apply hzv
        ext a
        rcases cover a with rfl | rfl | rfl <;> tauto
      have p₁ : FacePath P z (Function.update z j cj) := by
        rcases hother with hi | hk
        · exact move z hz j hji cj ⟨hcj.1, hcj.2.1⟩ i (Ne.symm hji) hi
        · exact move z hz j hji cj ⟨hcj.1, hcj.2.1⟩ k (Ne.symm hjk) hk
      have hz' : Function.update z j cj ∈ Plane i c :=
        ⟨inCube_update hz.1 j cj ⟨hcj.1, hcj.2.1⟩, by simpa [Ne.symm hji] using hz.2⟩
      have p₂ := move _ hz' k hki ck ⟨hck.1, hck.2.1⟩ j hjk (by simp [hcj.2.2])
      rw [endJK z hz] at p₂
      exact p₁.trans p₂
  intro x hx y hy
  exact (path x hx.1 hx.2).trans (path y hy.1 hy.2).reverse

end TranslationTiling.Rotations.SixKeys
