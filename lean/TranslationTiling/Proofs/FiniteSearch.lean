import TranslationTiling.Proofs.Compactness
import LeanWang.Kari.SignedPrimrec
import Mathlib.Data.List.Sublists

namespace TranslationTiling

open LeanWang.Kari.SignedPrimrec

theorem lattice_sub_primrec (d : ℕ) :
    Primrec₂ ((· - ·) : Lattice d → Lattice d → Lattice d) := by
  have h : ∀ i : Fin d, Primrec fun p : Lattice d × Lattice d => p.1 i - p.2 i := by
    intro i
    exact intAdd.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
      (intNeg.comp (Primrec.fin_app.comp Primrec.snd (Primrec.const i)))
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap

/-- The finitely many translation variables appearing in the equations on `X`. -/
def localSupport {d : ℕ} (F : Tile d) (X : List (Lattice d)) : List (Lattice d) :=
  X.flatMap fun x => F.map fun f => x - f

/-- Check exact coverage on a finite target list by a finite translation list. -/
def LocalCover {d : ℕ} (F X B : List (Lattice d)) : Prop :=
  ∀ x ∈ X, ∃ f ∈ F, x - f ∈ B ∧ ∀ g ∈ F, x - g ∈ B → g = f

instance {d : ℕ} (F X B : List (Lattice d)) : Decidable (LocalCover F X B) := by
  unfold LocalCover
  infer_instance

/-- Exhaustive search through the subsets of the support of the local equations. -/
def finiteTest {d : ℕ} (F : Tile d) (X : List (Lattice d)) : Prop :=
  ∃ B ∈ (localSupport F X).sublists', LocalCover F X B

instance {d : ℕ} (F : Tile d) (X : List (Lattice d)) : Decidable (finiteTest F X) := by
  unfold finiteTest
  infer_instance

theorem finiteTest_iff {d : ℕ} (F : Tile d) (X : List (Lattice d)) :
    finiteTest F X ↔ LocallyTileable F X := by
  classical
  constructor
  · rintro ⟨B, _, hb⟩
    refine ⟨fun a => decide (a ∈ B), ?_⟩
    simpa [LocalCover] using hb
  · rintro ⟨b, hb⟩
    let B := (localSupport F X).filter fun a => b a
    refine ⟨B, List.mem_sublists'.mpr List.filter_sublist, ?_⟩
    have hmem (x f : Lattice d) (hx : x ∈ X) (hf : f ∈ F) :
        x - f ∈ localSupport F X := by
      simp only [localSupport, List.mem_flatMap, List.mem_map]
      exact ⟨x, hx, f, hf, rfl⟩
    intro x hx
    obtain ⟨f, hf, hbf, hu⟩ := hb x hx
    refine ⟨f, hf, ?_, ?_⟩
    · simp [B, hmem x f hx hf, hbf]
    · intro g hg hbg
      exact hu g hg (List.mem_filter.mp hbg).2

theorem mem_primrec {α : Type*} [Primcodable α] :
    PrimrecRel fun (a : α) (xs : List α) => a ∈ xs := by
  exact ((Primrec.eq : PrimrecRel fun a b : α => a = b).exists_mem_list.comp
    Primrec.snd Primrec.fst).of_eq (by simp)

theorem sublists_primrec {α : Type*} [Primcodable α] :
    Primrec (List.sublists' : List α → List (List α)) := by
  have hmap : Primrec fun p : α × List (List α) => p.2.map (List.cons p.1) :=
    Primrec.list_map Primrec.snd
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hstep : Primrec₂ fun (_ : List α) (p : α × List (List α)) =>
      p.2 ++ p.2.map (List.cons p.1) :=
    (Primrec.list_append.comp Primrec.snd hmap).comp₂ Primrec₂.right
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([[]] : List (List α))) hstep).of_eq
    (by intro xs; simp only [List.sublists'_eq_sublists'Aux, List.sublists'Aux_eq_map]; rfl)

private theorem localSupport_primrec (d : ℕ) :
    Primrec₂ (@localSupport d) := by
  exact Primrec.list_flatMap Primrec.snd
    (Primrec.list_map (Primrec.fst.comp Primrec.fst)
      ((lattice_sub_primrec d).comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd))

private theorem localCover_primrec (d : ℕ) :
    PrimrecPred fun p : Tile d × (Tile d × Tile d) => LocalCover p.1 p.2.1 p.2.2 := by
  -- Parameter order: (tile, targets, translations); outer binders are x, f, g.
  let C := Tile d × (Tile d × Tile d)
  have hinner : PrimrecRel fun (g : Lattice d) (p : (C × Lattice d) × Lattice d) =>
      p.1.2 - g ∈ p.1.1.2.2 → g = p.2 := by
    exact ((mem_primrec.comp
      ((lattice_sub_primrec d).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))).not.or
      (Primrec.eq.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).of_eq
        (by simp [imp_iff_not_or])
  have hall : PrimrecRel fun (f : Lattice d) (p : C × Lattice d) =>
      ∀ g ∈ p.1.1, p.2 - g ∈ p.1.2.2 → g = f := by
    exact (PrimrecRel.forall_mem_list hinner).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair Primrec.snd Primrec.fst)
  have hhit : PrimrecRel fun (f : Lattice d) (p : C × Lattice d) =>
      p.2 - f ∈ p.1.2.2 :=
    mem_primrec.comp
      ((lattice_sub_primrec d).comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hex : PrimrecRel fun (x : Lattice d) (p : C) =>
      ∃ f ∈ p.1, x - f ∈ p.2.2 ∧ ∀ g ∈ p.1, x - g ∈ p.2.2 → g = f := by
    exact (PrimrecRel.exists_mem_list (R := fun (f : Lattice d) (p : C × Lattice d) =>
      p.2 - f ∈ p.1.2.2 ∧ ∀ g ∈ p.1.1, p.2 - g ∈ p.1.2.2 → g = f)
      (hhit.and hall)).comp
      (Primrec.fst.comp Primrec.snd) (Primrec.pair Primrec.snd Primrec.fst)
  exact (PrimrecRel.forall_mem_list hex).comp (Primrec.fst.comp Primrec.snd) Primrec.id

/-- The local satisfiability test is primitive recursive, including its exhaustive search. -/
theorem finiteTest_primrec (d : ℕ) :
    PrimrecPred fun p : Tile d × Tile d => finiteTest p.1 p.2 := by
  have hrel : PrimrecRel fun (B : Tile d) (p : Tile d × Tile d) =>
      LocalCover p.1 p.2 B :=
    (localCover_primrec d).comp (Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  exact (PrimrecRel.exists_mem_list hrel).comp
    (sublists_primrec.comp (localSupport_primrec d)) Primrec.id

/-- All finite target lists are directly enumerated by their natural-number encodings. -/
def decodeTargets (d : ℕ) (n : ℕ) : Tile d :=
  (Encodable.decode (α := Tile d) n).getD []

theorem decodeTargets_primrec (d : ℕ) : Primrec (decodeTargets d) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem decodeTargets_computable (d : ℕ) : Computable (decodeTargets d) :=
  (decodeTargets_primrec d).to_comp

/-- Non-tilability is witnessed by one unsatisfiable finite list of target equations. -/
theorem not_tiles_iff_obstruction {d : ℕ} (F : Tile d) :
    ¬ Tiles F ↔ ∃ n, ¬ finiteTest F (decodeTargets d n) := by
  rw [tiles_iff_locallyTileable]
  simp only [not_forall]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨Encodable.encode X, ?_⟩
    simpa [decodeTargets, finiteTest_iff] using hX
  · rintro ⟨n, hn⟩
    exact ⟨decodeTargets d n, by simpa [finiteTest_iff] using hn⟩

/-- Co-r.e. membership in every fixed lattice dimension. -/
theorem tiles_coRE (d : ℕ) : LeanWang.CoREPred (@Tiles d) := by
  have htest : ComputablePred fun p : Tile d × ℕ =>
      ¬ finiteTest p.1 (decodeTargets d p.2) :=
    ((finiteTest_primrec d).comp
      (Primrec.pair Primrec.fst ((decodeTargets_primrec d).comp Primrec.snd))).not.computablePred
  exact (LeanWang.REPred.exists_nat htest).of_eq fun F =>
    (not_tiles_iff_obstruction F).symm

end TranslationTiling
