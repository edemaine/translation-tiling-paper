import TranslationTiling.Rails.Compiler
import TranslationTiling.FiniteCompiler.Effective.MassGeometry

namespace TranslationTiling.Rails
noncomputable section
set_option maxHeartbeats 1000000

theorem geometry_bound {P w H M J : ℕ} (hP : 256≤P)
    (hH : H≤P^200) (hM : M≤P^(21*w+31)*3^(2*w+2))
    (hJ : J≤P^(12*w+23)*3^(2*w+2)) :
    (2^24*J)*(549072*8003^4)*H^2*M≤P^(33*w+466)*3^(4*w+4) := by
  have hk : 2^24*549072*8003^4≤P^12 :=
    (by norm_num : 2^24*549072*8003^4≤256^12).trans (Nat.pow_le_pow_left hP 12)
  calc
    _ = (2^24*549072*8003^4)*H^2*M*J := by ring
    _ ≤ P^12*(P^200)^2*(P^(21*w+31)*3^(2*w+2))*(P^(12*w+23)*3^(2*w+2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 2)) hM) hJ
    _ = _ := by
      simp only [mul_pow,←pow_mul]
      ring_nf

theorem compact_geometry_bound {P w H M J : ℕ} (hP : 256≤P)
    (hH : H≤P^25) (hM : M≤P^(21*w+31)*3^(2*w+2))
    (hJ : J≤P^(12*w+23)*3^(2*w+2)) :
    (2^24*J)*(549072*8003^4)*H^2*M≤P^(33*w+116)*3^(4*w+4) := by
  have hk : 2^24*549072*8003^4≤P^12 :=
    (by norm_num : 2^24*549072*8003^4≤256^12).trans (Nat.pow_le_pow_left hP 12)
  calc
    _ = (2^24*549072*8003^4)*H^2*M*J := by ring
    _ ≤ P^12*(P^25)^2*(P^(21*w+31)*3^(2*w+2))*(P^(12*w+23)*3^(2*w+2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 2)) hM) hJ
    _ = _ := by
      simp only [mul_pow,←pow_mul]
      ring_nf

theorem absorb_three {P w : ℕ} (hP : 256≤P) :
    P^(33*w+466)*3^(4*w+4)≤P^(34*w+467) := by
  have hthree : 3^(4*w+4)≤P^(w+1) := by
    calc
      _ = (3^4)^(w+1) := by rw [←pow_mul]; congr 1
      _ ≤ _ := Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ ≤ P^(33*w+466)*P^(w+1) := Nat.mul_le_mul_left _ hthree
    _ = _ := by rw [←pow_add]; congr 1; ring

end
end TranslationTiling.Rails
