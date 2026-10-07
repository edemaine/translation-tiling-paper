import TranslationTiling.Compiler.EffectiveSeedOffsets

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

abbrev ActivationCode := ℕ × ℕ × ℕ × ℕ

def activationIndices (a b r : ℕ) : List ActivationCode :=
  (List.range r).flatMap fun k => (List.range a).flatMap fun α =>
    (List.range b).flatMap fun ξ =>
      (List.range (numericalMultiplicity α ξ)).map fun d => (k, α, ξ, d)

theorem numericalMultiplicity_primrec : Primrec (fun z : ℕ × ℕ =>
    numericalMultiplicity z.1 z.2) := by
  unfold numericalMultiplicity
  fun_prop

@[fun_prop] theorem numericalMultiplicityRule {α : Type*} [Primcodable α]
    {a b : α → ℕ} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun z => numericalMultiplicity (a z) (b z)) :=
  numericalMultiplicity_primrec.comp (ha.pair hb)

theorem activationIndices_primrec : Primrec (fun z : ℕ × ℕ × ℕ =>
    activationIndices z.1 z.2.1 z.2.2) := by
  unfold activationIndices
  fun_prop

theorem mem_activationIndices (a b r : ℕ) (j : ActivationCode) :
    j ∈ activationIndices a b r ↔ j.1 < r ∧ j.2.1 < a ∧ j.2.2.1 < b ∧
      j.2.2.2 < numericalMultiplicity j.2.1 j.2.2.1 := by
  rcases j with ⟨k, α, ξ, d⟩
  simp only [activationIndices, List.mem_flatMap, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk, α', ha, ξ', hb, d', hd, rfl, rfl, rfl, rfl⟩
    exact ⟨hk, ha, hb, hd⟩
  · rintro ⟨hk, ha, hb, hd⟩
    exact ⟨k, hk, α, ha, ξ, hb, d, hd, rfl, rfl, rfl, rfl⟩

noncomputable def rawActivationIndex {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) : ActivationCode :=
  (j.1.val, j.2.1.1.val, j.2.1.2.val, j.2.2.val)

theorem rawActivationIndex_mem {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) :
    rawActivationIndex E i j ∈ activationIndices (E.a i) (E.b i) (E.r i) := by
  apply (mem_activationIndices _ _ _ _).mpr
  refine ⟨ZMod.val_lt j.1, ZMod.val_lt j.2.1.1, ZMod.val_lt j.2.1.2, ?_⟩
  simpa only [rawActivationIndex, shiftMultiplicity_numerical (E.a_two_le i) (E.b_two_le i)]
    using j.2.2.isLt

theorem activationIndices_native {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (code : ActivationCode) :
    code ∈ activationIndices (E.a i) (E.b i) (E.r i) ↔
      ∃ j : ActivationIndex E i, rawActivationIndex E i j = code := by
  constructor
  · intro hc
    obtain ⟨hk, hα, hξ, hd⟩ := (mem_activationIndices _ _ _ _).mp hc
    let e : P E i := ((code.2.1 : ℕ), (code.2.2.1 : ℕ))
    have he₁ : e.1.val = code.2.1 := by
      change (code.2.1 : ZMod (E.a i)).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hα]
    have he₂ : e.2.val = code.2.2.1 := by
      change (code.2.2.1 : ZMod (E.b i)).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hξ]
    have he : code.2.2.2 < shiftMultiplicity (E.a i) (E.b i) e := by
      rw [shiftMultiplicity_numerical (E.a_two_le i) (E.b_two_le i), he₁, he₂]
      exact hd
    refine ⟨((code.1 : ℕ), ⟨e, ⟨code.2.2.2, he⟩⟩), ?_⟩
    change ((code.1 : ZMod (E.r i)).val, e.1.val, e.2.val, code.2.2.2) = code
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk, he₁, he₂]
  · rintro ⟨j, rfl⟩
    exact rawActivationIndex_mem E i j

abbrev SeedCode := ActivationCode × (ℕ × ℕ)

def seedIndices (a b r W : ℕ) : List SeedCode :=
  (activationIndices a b r).flatMap fun j =>
    (List.range W).flatMap fun x => (List.range W).map fun y => (j, x, y)

theorem seedIndices_primrec : Primrec (fun z : (ℕ × ℕ × ℕ) × ℕ =>
    seedIndices z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hi : Primrec (fun z : (ℕ × ℕ × ℕ) × ℕ =>
      activationIndices z.1.1 z.1.2.1 z.1.2.2) := activationIndices_primrec.comp Primrec.fst
  unfold seedIndices
  fun_prop

noncomputable def rawSeedIndex {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) : SeedCode :=
  (rawActivationIndex E (.inr t) j.1, j.2.1.val, j.2.2.val)

theorem seedIndices_native {T : LeanWang.TileSet} (E : EncodingParameters T)
    (t : Fin 2) (code : SeedCode) :
    code ∈ seedIndices (E.a (.inr t)) (E.b (.inr t)) (E.r (.inr t)) residueModulus ↔
      ∃ j : SeedActivationIndex E t, rawSeedIndex E t j = code := by
  simp only [seedIndices, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨c, hc, x, hx, y, hy, rfl⟩
    obtain ⟨j, rfl⟩ := (activationIndices_native E (.inr t) c).mp hc
    refine ⟨(j, ((x : ℕ), (y : ℕ))), ?_⟩
    change (rawActivationIndex E (.inr t) j,
      (x : ZMod residueModulus).val, (y : ZMod residueModulus).val) =
        (rawActivationIndex E (.inr t) j, x, y)
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  · rintro ⟨j, rfl⟩
    exact ⟨rawActivationIndex E (.inr t) j.1, rawActivationIndex_mem E (.inr t) j.1,
      j.2.1.val, ZMod.val_lt j.2.1, j.2.2.val, ZMod.val_lt j.2.2, rfl⟩

end TranslationTiling.Compiler.Effective
