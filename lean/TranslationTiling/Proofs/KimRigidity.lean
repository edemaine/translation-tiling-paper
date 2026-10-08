import TranslationTiling.Proofs.KimDentForcing
import TranslationTiling.Proofs.KimCosetCoverage
import TranslationTiling.Proofs.KimShellConnectivity
import Mathlib.Tactic.Linarith

/-! Kim's shell coset rigidity, including arbitrary nonperiodic complements. -/

namespace TranslationTiling.Kim

noncomputable section
open scoped Classical

theorem shell_coordinate_upper (l : ℕ) {v : Lattice 3} (hv : v ∈ shell l)
    (i : Fin 3) : v i ≤ (l : ℤ) * (scale (boundary l).length : ℤ) := by
  obtain ⟨j, hj, q, hq, he⟩ := (mem_shell_iff _ _).mp hv
  have hb := (mem_cube_iff l _).mp
    (List.mem_filter.mp (List.getElem_mem (l := boundary l) hj)).1 i
  have hs : (1 : ℤ) ≤ scale (boundary l).length := by
    have := scale_pos (boundary l).length; omega
  have hprod : (scale (boundary l).length : ℤ) * (boundary l)[j] i ≤
      (scale (boundary l).length : ℤ) * ((l : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hqbound : q i ≤ scale (boundary l).length := by
    rcases mem_piece_cases hq with hq | hq
    · have hh := (mem_cube_iff _ _).mp (rawPiece_mem_cube hq.1) i; omega
    · have hh := bump_coordinate q hq.2 i; omega
  have he' := congrFun he i
  change v i = (scale (boundary l).length : ℤ) * (boundary l)[j] i + q i at he'
  nlinarith

theorem positive_steps_iterate {A : Set (Lattice 3)} (s : ℕ)
    (hstep : ∀ a ∈ A, ∀ i : Fin 3, a + (s : ℤ) • Pi.single i 1 ∈ A)
    {a : Lattice 3} (ha : a ∈ A) (i : Fin 3) (n : ℕ) :
    a + ((s : ℤ) * (n : ℤ)) • Pi.single i 1 ∈ A := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hh := hstep _ ih i
    convert hh using 1
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem coset_of_positive_steps (l : ℕ) (hl : 0 < l) (A : Set (Lattice 3))
    (hA : ExactTiling A {v | v ∈ shell l})
    (hstep : ∀ a ∈ A, ∀ i : Fin 3,
      a + (scale (boundary l).length : ℤ) • Pi.single i 1 ∈ A) :
    ∃ t, A = gridCoset (scale (boundary l).length) t := by
  let s := scale (boundary l).length
  let upper : ℤ := (l : ℤ) * s
  obtain ⟨⟨t, f₀⟩, _⟩ := hA.2 0
  have hfund := exactTiling_coset l hl t.val
  have hpos : 0 < (s : ℤ) := by have := scale_pos (boundary l).length; dsimp [s]; omega
  have subset : A ⊆ gridCoset s t.val := by
    intro a ha
    let n : Fin 3 → ℕ := fun i => (max (t.val i + upper - (a i + f₀.val i)) 0).toNat
    let a₁ := a + ((s : ℤ) * (n 0 : ℤ)) • Pi.single 0 1
    let a₂ := a₁ + ((s : ℤ) * (n 1 : ℤ)) • Pi.single 1 1
    let a₃ := a₂ + ((s : ℤ) * (n 2 : ℤ)) • Pi.single 2 1
    have ha₁ : a₁ ∈ A := positive_steps_iterate s hstep ha 0 (n 0)
    have ha₂ : a₂ ∈ A := positive_steps_iterate s hstep ha₁ 1 (n 1)
    have ha₃ : a₃ ∈ A := positive_steps_iterate s hstep ha₂ 2 (n 2)
    have eq₃ (i : Fin 3) : a₃ i = a i + (s : ℤ) * (n i : ℤ) := by
      fin_cases i <;> simp [a₃, a₂, a₁, Pi.single_apply]
    have above (i : Fin 3) : t.val i + upper ≤ a₃ i + f₀.val i := by
      have hn : 0 ≤ (n i : ℤ) ∧ t.val i + upper - (a i + f₀.val i) ≤ (n i : ℤ) := by
        dsimp [n]; omega
      have hmul : (n i : ℤ) ≤ (s : ℤ) * (n i : ℤ) := by nlinarith
      rw [eq₃]
      omega
    obtain ⟨⟨b, f⟩, he⟩ := hfund.2 (a₃ + f₀.val)
    have hbA : b.val ∈ A := by
      obtain ⟨z, hz⟩ := b.property
      have hznonneg (i : Fin 3) : 0 ≤ z i := by
        have hf : f.val i ≤ upper := shell_coordinate_upper l f.property i
        have hei := congrFun he i
        change b.val i + f.val i = a₃ i + f₀.val i at hei
        have hzi := congrFun hz i
        change b.val i = t.val i + (s : ℤ) * z i at hzi
        have hb := above i
        nlinarith
      have h0 := positive_steps_iterate s hstep t.property 0 (z 0).toNat
      have h1 := positive_steps_iterate s hstep h0 1 (z 1).toNat
      have h2 := positive_steps_iterate s hstep h1 2 (z 2).toNat
      have hnat (i : Fin 3) : ((z i).toNat : ℤ) = z i := by have := hznonneg i; omega
      have he' : t.val + ((s : ℤ) * ((z 0).toNat : ℤ)) • Pi.single 0 1 +
          ((s : ℤ) * ((z 1).toNat : ℤ)) • Pi.single 1 1 +
          ((s : ℤ) * ((z 2).toNat : ℤ)) • Pi.single 2 1 = b.val := by
        rw [hz]
        ext i
        fin_cases i
        · change t.val 0 + (s : ℤ) * ((z 0).toNat : ℤ) * 1 +
            (s : ℤ) * ((z 1).toNat : ℤ) * 0 + (s : ℤ) * ((z 2).toNat : ℤ) * 0 =
              t.val 0 + (s : ℤ) * z 0
          rw [hnat 0]; ring
        · change t.val 1 + (s : ℤ) * ((z 0).toNat : ℤ) * 0 +
            (s : ℤ) * ((z 1).toNat : ℤ) * 1 + (s : ℤ) * ((z 2).toNat : ℤ) * 0 =
              t.val 1 + (s : ℤ) * z 1
          rw [hnat 1]; ring
        · change t.val 2 + (s : ℤ) * ((z 0).toNat : ℤ) * 0 +
            (s : ℤ) * ((z 1).toNat : ℤ) * 0 + (s : ℤ) * ((z 2).toNat : ℤ) * 1 =
              t.val 2 + (s : ℤ) * z 2
          rw [hnat 2]; ring
      exact he' ▸ h2
    have hsame : b.val = a₃ := by
      have he' := hA.1 (a₁ := (⟨b.val, hbA⟩, f)) (a₂ := (⟨a₃, ha₃⟩, f₀)) he
      exact congrArg (fun p => p.1.val) he'
    have ha₃grid : a₃ ∈ gridCoset s t.val := hsame ▸ b.property
    obtain ⟨z, hz⟩ := ha₃grid
    refine ⟨fun i => z i - (n i : ℤ), ?_⟩
    ext i
    have hzi := congrFun hz i
    change a₃ i = t.val i + (s : ℤ) * z i at hzi
    change a i = t.val i + (s : ℤ) * (z i - (n i : ℤ))
    rw [eq₃] at hzi
    nlinarith
  refine ⟨t.val, Set.Subset.antisymm subset ?_⟩
  intro b hb
  obtain ⟨⟨a, f⟩, he⟩ := hA.2 (b + f₀.val)
  have hs := hfund.1 (a₁ := (⟨a.val, subset a.property⟩, f)) (a₂ := (⟨b, hb⟩, f₀)) he
  have haeq : a.val = b := congrArg (fun p => p.1.val) hs
  exact haeq ▸ a.property

/-- Every arbitrary tiling complement of the explicit shell is a full grid coset. -/
theorem cosetRigidity : CosetRigidity := by
  intro l hl A hA
  exact coset_of_positive_steps l (by omega) A hA (fun _ ha i => shell_forward_step l (by omega) hA ha i)

/-- All fields of Kim's geometric shell input, with no mathematical hypothesis. -/
theorem rigidity : Rigidity := rigidity_of_cosets cosetRigidity

end
end TranslationTiling.Kim
