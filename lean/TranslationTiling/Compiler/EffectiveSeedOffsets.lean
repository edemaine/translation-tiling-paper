import TranslationTiling.Compiler.EffectiveActivationOffsets

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

abbrev SeedNumbers := ActivationNumbers × (ℕ × ℕ × ℕ × ℕ)

/-- Seed offsets additionally prescribe the two planar residues and the
other seed's first useful coordinate. -/
def numericalSeedFirst (z : SeedNumbers) : ℤ :=
  let a := z.1.1.1
  let b := z.1.1.2.1
  let r := z.1.1.2.2
  let k := z.1.2.1
  let α := z.1.2.2.1
  let ξ := z.1.2.2.2.1
  let d := z.1.2.2.2.2
  let W := z.2.1
  let other := z.2.2.1
  let x := z.2.2.2.1
  let y := z.2.2.2.2
  let M := (r * a * b * W) * other
  let ρa := differenceResidue a (numericalRank α ξ d) α
  let ρb := differenceResidue b (numericalRank ξ α d) ξ
  (residueSearch M [(r, k), (a, ρa), (b, ρb), (W, x), (other, 0)] : ℤ) +
    (M : ℤ) * (Nat.pair (numericalActivationCode z.1.2) (Nat.pair x y) : ℤ)

theorem numericalSeedFirst_primrec : Primrec numericalSeedFirst := by
  have hAdata : Primrec (fun z : SeedNumbers =>
      (z.1.1.1, numericalRank z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2, z.1.2.2.1)) := by
    have hp : Primrec (fun z : SeedNumbers =>
        (z.1.2.2.1, z.1.2.2.2.1, z.1.2.2.2.2)) := by fun_prop
    have h := numericalRank_primrec.comp hp
    exact pairValue (by fun_prop) (h.pair (by fun_prop))
  have hBdata : Primrec (fun z : SeedNumbers =>
      (z.1.1.2.1, numericalRank z.1.2.2.2.1 z.1.2.2.1 z.1.2.2.2.2, z.1.2.2.2.1)) := by
    have hp : Primrec (fun z : SeedNumbers =>
        (z.1.2.2.2.1, z.1.2.2.1, z.1.2.2.2.2)) := by fun_prop
    have h := numericalRank_primrec.comp hp
    exact pairValue (by fun_prop) (h.pair (by fun_prop))
  have hA := differenceResidue_primrec.comp hAdata
  have hB := differenceResidue_primrec.comp hBdata
  have hM : Primrec (fun z : SeedNumbers =>
      (z.1.1.2.2 * z.1.1.1 * z.1.1.2.1 * z.2.1) * z.2.2.1) :=
    natMul (natMul (natMul (natMul (by fun_prop) (by fun_prop)) (by fun_prop))
      (by fun_prop)) (by fun_prop)
  have hcs : Primrec (fun z : SeedNumbers =>
      [(z.1.1.2.2, z.1.2.1), (z.1.1.1,
        differenceResidue z.1.1.1 (numericalRank z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2) z.1.2.2.1),
       (z.1.1.2.1,
        differenceResidue z.1.1.2.1 (numericalRank z.1.2.2.2.1 z.1.2.2.1 z.1.2.2.2.2) z.1.2.2.2.1),
       (z.2.1, z.2.2.2.1), (z.2.2.1, 0)]) :=
    consList (pairValue (by fun_prop) (by fun_prop))
      (consList (pairValue (by fun_prop) hA)
        (consList (pairValue (by fun_prop) hB) (by fun_prop)))
  have hs := residueSearch_primrec.comp (hM.pair hcs)
  have hcode : Primrec (fun z : SeedNumbers =>
      Nat.pair (numericalActivationCode z.1.2) (Nat.pair z.2.2.2.1 z.2.2.2.2)) := by
    unfold numericalActivationCode
    fun_prop
  exact intPlus (intCast hs) (intTimes (intCast hM) (intCast hcode))

noncomputable def nativeSeedNumbers {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) : SeedNumbers :=
  (nativeActivationNumbers E (.inr t) j.1,
    (residueModulus, E.a (.inr (otherSeed t)), j.2.1.val, j.2.2.val))

private theorem seedCongruences_iff {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) (n : ℕ) :
    Congruences [(E.r (.inr t), j.1.1.val),
      (E.a (.inr t), (rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2).val),
      (E.b (.inr t), (rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2).val),
      (residueModulus, j.2.1.val), (E.a (.inr (otherSeed t)), 0)] n ↔
      seedCRT E t (n : ZMod (seedModulus E t)) =
        ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
          rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0) := by
  have he : seedCRT E t (n : ZMod (seedModulus E t)) =
      (((((n : K E (.inr t)), (n : ZMod (E.a (.inr t)))),
        (n : ZMod (E.b (.inr t)))), (n : ZMod residueModulus)),
          (n : ZMod (E.a (.inr (otherSeed t))))) := by
    rw [map_natCast]
    rfl
  rw [he]
  simp only [Congruences, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true, Prod.mk.injEq,
    ← (ZMod.val_injective (E.r (.inr t))).eq_iff,
    ← (ZMod.val_injective (E.a (.inr t))).eq_iff,
    ← (ZMod.val_injective (E.b (.inr t))).eq_iff,
    ← (ZMod.val_injective residueModulus).eq_iff,
    ← (ZMod.val_injective (E.a (.inr (otherSeed t)))).eq_iff,
    ZMod.val_natCast, ZMod.val_zero, Nat.zero_mod,
    Nat.mod_eq_of_lt (ZMod.val_lt j.1.1), Nat.mod_eq_of_lt (ZMod.val_lt j.2.1),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2)),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2))]
  tauto

theorem numericalSeedFirst_eq {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) :
    numericalSeedFirst (nativeSeedNumbers E t j) = seedFirst E t j := by
  let i : Channel T := .inr t
  have hA : differenceResidue (E.a i)
      (numericalRank j.1.2.1.1.val j.1.2.1.2.val j.1.2.2.val) j.1.2.1.1.val =
        (rhoA (E.a_two_le i) (E.b_two_le i) j.1.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hB : differenceResidue (E.b i)
      (numericalRank j.1.2.1.2.val j.1.2.1.1.val j.1.2.2.val) j.1.2.1.2.val =
        (rhoB (E.a_two_le i) (E.b_two_le i) j.1.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hs := residueSearch_of_equiv (seedCRT E t).toEquiv
    ((((j.1.1, rhoA (E.a_two_le i) (E.b_two_le i) j.1.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.1.2), j.2.1), 0)
    [(E.r i, j.1.1.val), (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.1.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.1.2).val),
      (residueModulus, j.2.1.val), (E.a (.inr (otherSeed t)), 0)]
    (seedCongruences_iff E t j)
  unfold numericalSeedFirst nativeSeedNumbers nativeActivationNumbers seedFirst separatedResidueLift
  dsimp only
  dsimp only [i, seedModulus, activationModulus] at hs
  rw [hA, hB, hs]
  rfl

end TranslationTiling.Compiler.Effective
