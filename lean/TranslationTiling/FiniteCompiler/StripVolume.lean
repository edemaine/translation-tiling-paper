import TranslationTiling.FiniteCompiler.StripSupport

namespace TranslationTiling.Compiler.StripLift
open Rails Rails.Strips
open scoped Classical
noncomputable section
set_option maxHeartbeats 1300000

def shellCap (H U : ℕ) : ℕ :=
  let a := countCap H
  let B := railHeight U
  216*(4*a+7*(B+2)+1)*(4*a+1)

def volumeCap (H R J L : ℕ) : ℕ := Size.mssPieceCap*(J*L)*shellCap H (R*L)

theorem volume (d : CyclicTileData) (hQ : 0<d.1) (H R J q L : ℕ) (hq : q≤L)
    (hm : (cyclicTileSet d.1 d.2).card≤J*q) :
    (assemble (integerTile d) H (R*q)).length≤volumeCap H R J L := by
  have hr := (Size.integerTile_cubeCount_sharp d hQ).trans (Nat.mul_le_mul_left _ hm)
  have hlen := SlotAssembly.length_le _ (valid H) (integerTile d) (railHeight (R*q))
    (countCap H) (length_le H)
  have he : (integerTile d).dedup.length=Size.cubeCount (integerTile d) := by rw [←List.card_toFinset]; rfl
  rw [he] at hlen
  apply hlen.trans
  unfold volumeCap
  refine Nat.mul_le_mul (hr.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq))) ?_
  dsimp only [shellCap,railHeight]
  gcongr

theorem shellCap_coarse (H U : ℕ) (hH : 175≤H) :
    shellCap H U≤(549072*8003^4)*H^2*max (H^2) U := by
  let A := 4000*H+2003
  let B := max (A^2) (4000*max (H^2) U+2003)
  have ha : countCap H≤10*A^2 := by
    unfold countCap
    dsimp [A]
    nlinarith
  have hB : 1≤B := by dsimp [B]; omega
  have hB' : A^2≤B := le_max_left _ _
  have hU : railHeight U≤B := by unfold railHeight; dsimp [B]; omega
  have hx : 4*countCap H+7*(railHeight U+2)+1≤62*B := by omega
  have hy : 4*countCap H+1≤41*A^2 := by dsimp [A] at *; nlinarith
  have hA : A≤8003*H := by dsimp [A]; omega
  have hB'' : B≤8003^2*max (H^2) U := by
    dsimp [B]
    apply max_le
    · have hh : A^2≤(8003*H)^2 := Nat.pow_le_pow_left hA _
      have hh' := Nat.mul_le_mul_left (8003^2) (le_max_left (H^2) U)
      simpa [mul_pow] using hh.trans (by simpa [mul_pow] using hh')
    · have hh : 1≤max (H^2) U := (by nlinarith : 1≤H^2).trans (le_max_left _ _)
      omega
  calc
    _ ≤ 216*(62*B)*(41*A^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hx) hy
    _ = 549072*A^2*B := by ring
    _ ≤ _ := by
      have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 549072 (Nat.pow_le_pow_left hA 2)) hB''
      convert hh using 1 <;> ring

theorem volumeCap_coarse (H R J L : ℕ) (hH : 175≤H) :
    volumeCap H R J L≤
      (2^24*(J*L))*(549072*8003^4)*H^2*max (H^2) (R*L) := by
  unfold volumeCap
  calc
    _ ≤ (2^24*(J*L))*((549072*8003^4)*H^2*max (H^2) (R*L)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) (shellCap_coarse _ _ hH)
    _ = _ := by ring

end
end TranslationTiling.Compiler.StripLift

namespace TranslationTiling.FiniteCompiler
open scoped BigOperators
noncomputable section
variable [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T)

theorem inputOrder_eq_div : inputOrder E = E.cyclicOrder / MassSize.mass E := by
  have hmass : 0 < MassSize.mass E := by
    unfold MassSize.mass D
    exact Nat.mul_pos (pow_pos (NeZero.pos _) _) (Finset.prod_pos fun i _ =>
      Nat.mul_pos (E.r_pos i) (Nat.mul_pos (E.a_pos i) (E.b_pos i)))
  have he : E.cyclicOrder = inputOrder E * MassSize.mass E := by
    simp only [inputOrder,MassSize.mass,D,EncodingParameters.cyclicOrder,EncodingParameters.blockModulus]
    rw [mul_left_comm,←Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [he,Nat.mul_div_cancel _ hmass]

end
end TranslationTiling.FiniteCompiler
