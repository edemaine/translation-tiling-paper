import TranslationTiling.FiniteCompiler.PackedProfiles
import TranslationTiling.FiniteCompiler.GuardedRefinement

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall
open scoped Classical
noncomputable section

def Profile.origin (p : Profile) (j : Fin p.width) : Fin 20 :=
  if hj : j.val < 18 then ⟨j.val, by omega⟩
  else if j.val < 18+p.radices.length then 18 else 19

def Profile.Fibre (p : Profile) (i : Fin 20) := {j : Fin p.width // p.origin j = i}

instance (p : Profile) (i : Fin 20) : Fintype (p.Fibre i) :=
  inferInstanceAs (Fintype {j : Fin p.width // p.origin j = i})

theorem Profile.arithmetic_unique (p : Profile) (i : Fin 20) (hi : i.val < 18)
    (j k : p.Fibre i) : j = k := by
  have eqVal (u : p.Fibre i) : u.val.val = i.val := by
    have he := u.property
    unfold Profile.origin at he
    split_ifs at he
    · exact congrArg Fin.val he
    · have : (18 : ℕ) = i.val := congrArg Fin.val he
      omega
    · have : (19 : ℕ) = i.val := congrArg Fin.val he
      omega
  exact Subtype.ext (Fin.ext ((eqVal j).trans (eqVal k).symm))

structure Layout (p : Profile) : Prop where
  cover : Function.Surjective p.origin
  positive : ∀ j : Fin p.width, 0 < p.arity j.val
  capacity : ∀ i : Fin 20,
    (∏ j : p.Fibre i, p.arity j.val.val) = PairSmall.arity p.radices.prod i
  slope : ∀ j : Fin p.width, PairSmall.slope (p.origin j) = p.slope j.val

variable {T : LeanWang.TileSet} (p : Profile) (h : Layout p)
  (code : Code T p.radices.prod)

local instance : AlphabetFamily (system code) := GuardedCompiler.alphabet code

def letterCode (i : Column (system code)) :
    Letter (system code) i ≃ ((j : p.Fibre i) → Fin (p.arity j.val.val)) :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact h.capacity i)).symm

private theorem unrestricted_wang (t : Fin 2) (i : Column (system code))
    (hi : 18 ≤ i.val) (v : Letter (system code) i) :
    LetterSeedSet (system code) t i v := by
  have he : i.val = 18 ∨ i.val = 19 := by
    have hi' : i.val < 20 := i.isLt
    omega
  rcases he with he | he
  · have he' : i = 18 := Fin.ext he
    subst i
    trivial
  · have he' : i = 19 := Fin.ext he
    subst i
    trivial

private def oneDigit (j : Fin p.width) (v : Fin (p.arity j.val))
    (k : p.Fibre (p.origin j)) : Fin (p.arity k.val.val) :=
  if e : j = k.val then e ▸ v else ⟨0,h.positive k.val⟩

private theorem oneDigit_eq (j : Fin p.width) (hi : (p.origin j).val < 18)
    (v : Letter (system code) (p.origin j)) :
    oneDigit p h j (letterCode p h code (p.origin j) v ⟨j,rfl⟩) =
      letterCode p h code (p.origin j) v := by
  funext k
  rw [p.arithmetic_unique _ hi k ⟨j,rfl⟩]
  simp [oneDigit]

def refinement : ColumnRefinement (system code) where
  width := p.width
  width_pos := by unfold Profile.width; omega
  origin := p.origin
  origin_surjective := h.cover
  radix j := p.arity j.val
  code := letterCode p h code
  seed t j v := if (p.origin j).val < 18 then
    LetterSeedSet (system code) t (p.origin j) ((letterCode p h code (p.origin j)).symm (oneDigit p h j v))
    else True
  seed_iff t i v := by
    by_cases hi : i.val < 18
    · have hseed (j : p.Fibre i) :
          (if (p.origin j.val).val < 18 then
            LetterSeedSet (system code) t (p.origin j.val)
              ((letterCode p h code (p.origin j.val)).symm
                (oneDigit p h j.val (letterCode p h code i v j)))
            else True) ↔ LetterSeedSet (system code) t i v := by
        obtain ⟨j,hj⟩ := j
        subst i
        rw [ite_eq_left hi, oneDigit_eq p h code j hi v, Equiv.symm_apply_apply]
      constructor
      · intro hs j
        exact (hseed j).mpr hs
      · intro hs
        obtain ⟨j,hj⟩ := h.cover i
        exact (hseed ⟨j,hj⟩).mp (hs ⟨j,hj⟩)
    · refine iff_of_true (unrestricted_wang p code t i (by omega) v) ?_
      intro j
      rw [ite_eq_right (by simpa only [j.property] using hi)]
      trivial

end
end TranslationTiling.FiniteCompiler.Packed
