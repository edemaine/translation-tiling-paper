import TranslationTiling.Rotations.KeyParameters
import TranslationTiling.Rotations.Moments

namespace TranslationTiling.Rotations.SixKeys

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def secondMoment (i : Face) (j : Fin 3) : ℤ :=
  ![![38882480, 256838400, 916056960],
    ![38882480, 404127360, 584263680],
    ![142396800, 68672240, 916056960],
    ![326376960, 68672240, 404127360],
    ![142396800, 584263680, 106673840],
    ![256838400, 326376960, 106673840]] i j

def thirdMoment (i : Face) (j : Fin 3) : ℤ :=
  ![![-9169130880, 2517016320, 10787212800],
    ![9169130880, 4245696000, 6469182720],
    ![1257984000, -11942461440, 10787212800],
    ![3321077760, 11942461440, 4245696000],
    ![1257984000, 6469182720, -15072220800],
    ![2517016320, 3321077760, 15072220800]] i j

def firstMoment (i : Face) (j : Fin 3) : ℤ :=
  ![![2170, 5628, 6888],
    ![12026, 6352, 6712],
    ![5268, 2350, 6888],
    ![6172, 11846, 6352],
    ![5268, 6348, 2530],
    ![5992, 6172, 11666]] i j

theorem sum_chamberVoxel : ∀ (i : Face) (j : Fin 3),
    (∑ x : Fin 364, chamberVoxel i x j) = firstMoment i j := by decide

theorem moment_chamber (i : Face) (j : Fin 3) (k : ℕ) :
    moment (chamber i) j k = ∑ x : Fin 364,
      ((364 : ℤ) * chamberVoxel i x j - firstMoment i j) ^ k := by
  unfold moment
  rw [chamber_card, chamber_eq_image]
  rw [Finset.sum_image (fun x _ y _ he => chamberVoxel_injective i he),
    Finset.sum_image (fun x _ y _ he => chamberVoxel_injective i he), sum_chamberVoxel]
  norm_num

theorem chamber_second : ∀ (i : Face) (j : Fin 3),
    moment (chamber i) j 2 = secondMoment i j := by
  intro i j
  rw [moment_chamber]
  fin_cases i <;> fin_cases j <;> decide

theorem chamber_third : ∀ (i : Face) (j : Fin 3),
    moment (chamber i) j 3 = thirdMoment i j := by
  intro i j
  rw [moment_chamber]
  fin_cases i <;> fin_cases j <;> decide

theorem signature_axes : ∀ (i j : Face) (a b c : Fin 3),
    secondMoment j 0 = secondMoment i a →
    secondMoment j 1 = secondMoment i b →
    secondMoment j 2 = secondMoment i c →
      i = j ∧ a = 0 ∧ b = 1 ∧ c = 2 := by decide

theorem thirdMoment_ne_zero : ∀ (i : Face) (j : Fin 3), thirdMoment i j ≠ 0 := by decide

theorem signature_rigid : ∀ (i j : Face) (r : Orientation),
    (∀ a, secondMoment j a = secondMoment i (r.axes a) ∧
      thirdMoment j a = r.sign a * thirdMoment i (r.axes a)) →
      i = j ∧ r = Orientation.ident := by
  intro i j r h
  obtain ⟨hij, h0, h1, h2⟩ := signature_axes i j (r.axes 0) (r.axes 1) (r.axes 2)
    (h 0).1 (h 1).1 (h 2).1
  subst j
  have hp : r.axes = Equiv.refl _ := by
    apply Equiv.ext
    intro a
    fin_cases a
    · simpa using h0
    · simpa using h1
    · simpa using h2
  have hf : r.flip = fun _ => false := by
    funext a
    have hh := (h a).2
    have hn := thirdMoment_ne_zero i a
    simp only [hp, Equiv.refl_apply] at hh
    cases he : r.flip a
    · rfl
    · simp [Orientation.sign, he] at hh
      omega
  refine ⟨rfl, ?_⟩
  cases r
  cases hp
  cases hf
  rfl

end TranslationTiling.Rotations.SixKeys
