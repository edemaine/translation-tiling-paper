import TranslationTiling.Compiler.EffectiveResidues
import TranslationTiling.Compiler.ActivationOffsets

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

abbrev ActivationNumbers := (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)

def numericalActivationCode (j : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  Nat.pair j.1 (Nat.pair j.2.1 (Nat.pair j.2.2.1 j.2.2.2))

def numericalActivationFirst (z : ActivationNumbers) : ℤ :=
  let a := z.1.1
  let b := z.1.2.1
  let r := z.1.2.2
  let k := z.2.1
  let α := z.2.2.1
  let ξ := z.2.2.2.1
  let d := z.2.2.2.2
  let M := r * a * b
  let ρa := differenceResidue a (numericalRank α ξ d) α
  let ρb := differenceResidue b (numericalRank ξ α d) ξ
  (residueSearch M [(r, k), (a, ρa), (b, ρb)] : ℤ) +
    (M : ℤ) * (numericalActivationCode z.2 : ℤ)

theorem numericalRank_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => numericalRank z.1 z.2.1 z.2.2) := by
  unfold numericalRank
  fun_prop

@[fun_prop] theorem numericalRankRule {α : Type*} [Primcodable α] {a b d : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hd : Primrec d) :
    Primrec (fun z => numericalRank (a z) (b z) (d z)) :=
  numericalRank_primrec.comp (ha.pair (hb.pair hd))

@[fun_prop] theorem differenceResidueRule {α : Type*} [Primcodable α] {a b d : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hd : Primrec d) :
    Primrec (fun z => differenceResidue (a z) (b z) (d z)) :=
  differenceResidue_primrec.comp (ha.pair (hb.pair hd))

@[fun_prop] theorem residueSearchRule {α : Type*} [Primcodable α]
    {M : α → ℕ} {cs : α → CongruenceList} (hM : Primrec M) (hcs : Primrec cs) :
    Primrec (fun z => residueSearch (M z) (cs z)) :=
  residueSearch_primrec.comp (hM.pair hcs)

@[fun_prop] theorem numberPairRule {α : Type*} [Primcodable α] {a b : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun z => Nat.pair (a z) (b z)) :=
  Primrec.encode.comp (ha.pair hb)

theorem numericalActivationFirst_primrec : Primrec numericalActivationFirst := by
  have hM : Primrec (fun z : ActivationNumbers => z.1.2.2 * z.1.1 * z.1.2.1) := by fun_prop
  have hαd : Primrec (fun z : ActivationNumbers =>
      (z.2.2.1, z.2.2.2.1, z.2.2.2.2)) := by fun_prop
  have hξd : Primrec (fun z : ActivationNumbers =>
      (z.2.2.2.1, z.2.2.1, z.2.2.2.2)) := by fun_prop
  have hα := numericalRank_primrec.comp hαd
  have hξ := numericalRank_primrec.comp hξd
  have hAd := (Primrec.fst.comp Primrec.fst).pair
    (hα.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hBd := (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    (hξ.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hA := differenceResidue_primrec.comp hAd
  have hB := differenceResidue_primrec.comp hBd
  have hcs := consList
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd))
    (consList ((Primrec.fst.comp Primrec.fst).pair hA)
      (consList ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair hB) (Primrec.const [])))
  have hsearch := residueSearch_primrec.comp (hM.pair hcs)
  have hcode : Primrec (fun z : ActivationNumbers => numericalActivationCode z.2) := by
    unfold numericalActivationCode
    fun_prop
  have hresult := intPlus (intCast hsearch) (intTimes (intCast hM) (intCast hcode))
  exact hresult

noncomputable def nativeActivationNumbers {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) : ActivationNumbers :=
  ((E.a i, E.b i, E.r i), (j.1.val, j.2.1.1.val, j.2.1.2.val, j.2.2.val))

private theorem activationCongruences_iff {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) (n : ℕ) :
    Congruences [(E.r i, j.1.val),
      (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val)] n ↔
      activationCRT E i (n : ZMod (activationModulus E i)) =
        ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
          rhoB (E.a_two_le i) (E.b_two_le i) j.2) := by
  have he : activationCRT E i (n : ZMod (activationModulus E i)) =
      (((n : K E i), (n : ZMod (E.a i))), (n : ZMod (E.b i))) := by
    rw [map_natCast]
    rfl
  rw [he]
  simp only [Congruences, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, and_true,
    Prod.mk.injEq, ← (ZMod.val_injective (E.r i)).eq_iff,
    ← (ZMod.val_injective (E.a i)).eq_iff, ← (ZMod.val_injective (E.b i)).eq_iff,
    ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt j.1),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoA (E.a_two_le i) (E.b_two_le i) j.2)),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoB (E.a_two_le i) (E.b_two_le i) j.2))]
  exact and_assoc.symm

theorem numericalActivationFirst_eq {T : LeanWang.TileSet} (E : EncodingParameters T)
    (n : Column T) (j : ActivationIndex E (.inl n)) :
    numericalActivationFirst (nativeActivationNumbers E (.inl n) j) = ordinaryFirst E n j := by
  let i : Channel T := .inl n
  have hA : differenceResidue (E.a i)
      (numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val) j.2.1.1.val =
        (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hB : differenceResidue (E.b i)
      (numericalRank j.2.1.2.val j.2.1.1.val j.2.2.val) j.2.1.2.val =
        (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hs := residueSearch_of_equiv (activationCRT E i).toEquiv
    ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.2)
    [(E.r i, j.1.val), (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val)]
    (activationCongruences_iff E i j)
  unfold numericalActivationFirst nativeActivationNumbers ordinaryFirst separatedResidueLift
  dsimp only
  dsimp only [i, activationModulus] at hs
  rw [hA, hB, hs]
  rfl

end TranslationTiling.Compiler.Effective
