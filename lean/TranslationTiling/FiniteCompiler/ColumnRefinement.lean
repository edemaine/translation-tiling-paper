import TranslationTiling.FiniteCompiler.PartialTests

namespace TranslationTiling.FiniteCompiler

open scoped Classical
noncomputable section

variable (T : System) [AlphabetFamily T]

/-- Replace a column by the digits of an equivalent alphabet, all with its original slope. -/
structure ColumnRefinement where
  width : ℕ
  width_pos : 0 < width
  origin : Fin width → Column T
  origin_surjective : Function.Surjective origin
  radix : Fin width → ℕ
  code : ∀ i : Column T, Letter T i ≃ ((j : {j // origin j = i}) → Fin (radix j.val))
  seed : Fin 2 → (j : Fin width) → Fin (radix j) → Prop
  seed_iff : ∀ t i (v : Letter T i),
    LetterSeedSet T t i v ↔ ∀ j : {j // origin j = i}, seed t j.val (code i v j)

variable {T}

namespace ColumnRefinement

variable (S : ColumnRefinement T)

abbrev system : System where
  width := S.width
  width_pos := S.width_pos
  alphabet := 0
  slope j := T.slope (S.origin j)
  allowed := ∅
  seed _ _ := True

def packWord (w : Word T) (i : Fin S.width) : Fin (S.radix i) :=
  S.code (S.origin i) (w (S.origin i)) ⟨i,rfl⟩

def unpackWord (w : (i : Fin S.width) → Fin (S.radix i)) : Word T :=
  fun i => (S.code i).symm (fun j => w j.val)

theorem unpack_pack (w : Word T) : S.unpackWord (S.packWord w) = w := by
  funext i
  apply (S.code i).injective
  rw [unpackWord, Equiv.apply_symm_apply]
  funext j
  obtain ⟨j,hj⟩ := j
  subst i
  rfl

@[instance_reducible] def family : AlphabetFamily S.system where
  size := S.radix
  allowed w := Allowed T (S.unpackWord w)
  seed := S.seed

attribute [local instance] family

def packArray (W : WordArray T) : WordArray S.system :=
  fun i m => S.packWord (fun j => W j m) i

def unpackArray (W : WordArray S.system) : WordArray T :=
  fun i m => S.unpackWord (fun j => W j m) i

theorem unpack_line (W : WordArray S.system) (x : Plane) :
    S.unpackWord (fun i => W i (lineValue S.system i x)) =
      fun i => S.unpackArray W i (lineValue T i x) := by
  funext i
  apply (S.code i).injective
  simp only [unpackWord, unpackArray, Equiv.apply_symm_apply]
  funext j
  obtain ⟨j,hj⟩ := j
  subst i
  rfl

theorem pack_line (W : WordArray T) (x : Plane) :
    (fun i => S.packArray W i (lineValue S.system i x)) =
      S.packWord (fun i => W i (lineValue T i x)) := rfl

theorem pack_lineRule {W : WordArray T} (h : LineRule T W) :
    LineRule S.system (S.packArray W) := by
  intro x
  change Allowed T (S.unpackWord (fun i => S.packArray W i (lineValue S.system i x)))
  rw [S.pack_line, S.unpack_pack]
  exact h x

private theorem code_unpack (w : Word S.system) (i : Column T) :
    S.code i (S.unpackWord w i) = fun j : {j // S.origin j = i} => w j.val := Equiv.apply_symm_apply _ _

theorem pack_seed {t : Fin 2} {w : Word T}
    (h : ∀ i, LetterSeedSet T t i (w i)) (j : Column S.system) :
    LetterSeedSet S.system t j (S.packWord w j) :=
  (S.seed_iff t (S.origin j) _).mp (h _) ⟨j,rfl⟩

theorem unpack_seed {t : Fin 2} {w : Word S.system}
    (h : ∀ j, LetterSeedSet S.system t j (w j)) (i : Column T) :
    LetterSeedSet T t i (S.unpackWord w i) := by
  apply (S.seed_iff t i _).mpr
  rw [S.code_unpack]
  exact fun j => h j.val

/-- Specifying one original letter specifies all of its digits. -/
def expand (p : PartialTest T) : PartialTest S.system where
  columns := Finset.univ.filter fun j => S.origin j ∈ p.columns
  label j := S.code (S.origin j.val) (p.label ⟨S.origin j.val,
    (Finset.mem_filter.mp j.property).2⟩) ⟨j.val,rfl⟩

theorem expand_nonempty {p : PartialTest T} (h : p.columns.Nonempty) :
    (S.expand p).columns.Nonempty := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,rfl⟩ := S.origin_surjective i
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

theorem expand_matches (p : PartialTest T) (w : Word S.system) :
    (S.expand p).Matches w ↔ p.Matches (S.unpackWord w) := by
  constructor
  · intro h i
    apply (S.code i.val).injective
    rw [S.code_unpack]
    funext j
    obtain ⟨j,hj⟩ := j
    obtain ⟨i,hi⟩ := i
    dsimp only at hj
    subst i
    exact h ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  · intro h j
    have hi : S.origin j.val ∈ p.columns := (Finset.mem_filter.mp j.property).2
    have he := congrArg (S.code (S.origin j.val)) (h ⟨S.origin j.val,hi⟩)
    rw [S.code_unpack] at he
    exact congrFun he ⟨j.val,rfl⟩

end ColumnRefinement
end
end TranslationTiling.FiniteCompiler
