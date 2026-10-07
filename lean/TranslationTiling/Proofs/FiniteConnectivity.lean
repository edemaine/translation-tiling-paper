import TranslationTiling.Connectivity
import TranslationTiling.Proofs.FiniteSearch

namespace TranslationTiling

instance {d : ℕ} (x y : Lattice d) : Decidable (FaceAdjacent x y) := by
  unfold FaceAdjacent
  infer_instance

/-- Every nonempty proper part of the tile has an edge to its complement. -/
def finiteConnectedTest {d : ℕ} (F : Tile d) : Prop :=
  ∀ C ∈ F.sublists', C = [] ∨ (∀ y ∈ F, y ∈ C) ∨
    ∃ a ∈ C, ∃ b ∈ F, b ∉ C ∧ FaceAdjacent a b

instance {d : ℕ} (F : Tile d) : Decidable (finiteConnectedTest F) := by
  unfold finiteConnectedTest
  infer_instance

/-- The finite cut test agrees with paths inside the tile, including the empty tile. -/
theorem finiteConnectedTest_iff {d : ℕ} (F : Tile d) :
    finiteConnectedTest F ↔ FaceConnected F := by
  classical
  constructor
  · intro h x hx y hy
    let R := fun a b : Lattice d => a ∈ F ∧ b ∈ F ∧ FaceAdjacent a b
    let C := F.filter fun a => decide (Relation.ReflTransGen R x a)
    have hmemC (a : Lattice d) : a ∈ C ↔ a ∈ F ∧ Relation.ReflTransGen R x a := by
      simp [C]
    have hxC : x ∈ C := (hmemC x).mpr ⟨hx, Relation.ReflTransGen.refl⟩
    have hC : C ∈ F.sublists' := List.mem_sublists'.mpr List.filter_sublist
    rcases h C hC with hempty | hall | ⟨a, ha, b, hb, hbC, hab⟩
    · simp [hempty] at hxC
    · exact ((hmemC y).mp (hall y hy)).2
    · obtain ⟨haF, hxa⟩ := (hmemC a).mp ha
      exact False.elim (hbC ((hmemC b).mpr ⟨hb, hxa.tail ⟨haF, hb, hab⟩⟩))
  · intro h C hC
    by_cases hempty : C = []
    · exact Or.inl hempty
    by_cases hall : ∀ y ∈ F, y ∈ C
    · exact Or.inr (Or.inl hall)
    refine Or.inr (Or.inr ?_)
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil C hempty
    obtain ⟨y, hyF, hyC⟩ : ∃ y ∈ F, y ∉ C := by
      simpa only [not_forall, exists_prop] using hall
    have hxF : x ∈ F := (List.mem_sublists'.mp hC).subset hx
    by_contra hcross
    have hstay (z : Lattice d)
        (hpath : Relation.ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ FaceAdjacent a b) x z) :
        z ∈ C := by
      induction hpath with
      | refl => exact hx
      | @tail a b hxa hab ih =>
        by_contra hbC
        exact hcross ⟨a, ih, b, hab.2.1, hbC, hab.2.2⟩
    exact hyC (hstay y (h x hxF y hyF))

private theorem lattice_add_primrec (d : ℕ) :
    Primrec₂ ((· + ·) : Lattice d → Lattice d → Lattice d) := by
  have h : ∀ i : Fin d, Primrec fun z : Lattice d × Lattice d => z.1 i + z.2 i := by
    intro i
    exact LeanWang.Kari.SignedPrimrec.intAdd.comp
      (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
      (Primrec.fin_app.comp Primrec.snd (Primrec.const i))
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap

theorem faceAdjacent_primrec (d : ℕ) : PrimrecRel (@FaceAdjacent d) := by
  let E : List (Lattice d) := List.ofFn fun i : Fin d => Pi.single i 1
  have he : PrimrecRel fun (v : Lattice d) (z : Lattice d × Lattice d) =>
      z.2 = z.1 + v ∨ z.1 = z.2 + v :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
      ((lattice_add_primrec d).comp (Primrec.fst.comp Primrec.snd) Primrec.fst)).or
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      ((lattice_add_primrec d).comp (Primrec.snd.comp Primrec.snd) Primrec.fst))
  exact ((he.exists_mem_list).comp (Primrec.const E) Primrec.id).of_eq
    (by intro z; simp [E, FaceAdjacent, List.mem_ofFn])

/-- The exhaustive finite cut search is primitive recursive in the tile encoding. -/
theorem finiteConnectedTest_primrec (d : ℕ) : PrimrecPred (@finiteConnectedTest d) := by
  let P := Tile d × Tile d
  have hinner : PrimrecRel fun (b : Lattice d) (z : P × Lattice d) =>
      b ∉ z.1.1 ∧ FaceAdjacent z.2 b :=
    ((mem_primrec.comp Primrec.fst
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).not).and
    ((faceAdjacent_primrec d).comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have hcrossA : PrimrecRel fun (a : Lattice d) (z : P) =>
      ∃ b ∈ z.2, b ∉ z.1 ∧ FaceAdjacent a b :=
    (hinner.exists_mem_list).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.pair Primrec.snd Primrec.fst)
  have hcross : PrimrecPred fun z : P =>
      ∃ a ∈ z.1, ∃ b ∈ z.2, b ∉ z.1 ∧ FaceAdjacent a b :=
    hcrossA.exists_mem_list.comp Primrec.fst Primrec.id
  have hall : PrimrecPred fun z : P => ∀ y ∈ z.2, y ∈ z.1 :=
    mem_primrec.forall_mem_list.comp Primrec.snd Primrec.fst
  have hpart : PrimrecRel fun (C F : Tile d) =>
      C = [] ∨ (∀ y ∈ F, y ∈ C) ∨ ∃ a ∈ C, ∃ b ∈ F, b ∉ C ∧ FaceAdjacent a b :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [])).or (hall.or hcross)
  exact hpart.forall_mem_list.comp sublists_primrec Primrec.id

theorem faceConnected_computable (d : ℕ) : ComputablePred (@FaceConnected d) :=
  (finiteConnectedTest_primrec d).computablePred.of_eq fun F => finiteConnectedTest_iff F

/-- Both failures, disconnection and a finite tiling obstruction, are searchable. -/
theorem connectedTiles_coRE (d : ℕ) : LeanWang.CoREPred (@ConnectedTiles d) := by
  have hbad : ComputablePred fun z : Tile d × ℕ =>
      ¬ finiteConnectedTest z.1 ∨ ¬ finiteTest z.1 (decodeTargets d z.2) :=
    (((finiteConnectedTest_primrec d).comp Primrec.fst).not.or
      (((finiteTest_primrec d).comp
        (Primrec.pair Primrec.fst ((decodeTargets_primrec d).comp Primrec.snd))).not)).computablePred
  have hRE : REPred fun F : Tile d =>
      ∃ n, ¬ finiteConnectedTest F ∨ ¬ finiteTest F (decodeTargets d n) :=
    LeanWang.REPred.exists_nat hbad
  exact hRE.of_eq fun F => by
    constructor
    · rintro ⟨n, hconn | hn⟩ hF
      · exact hconn ((finiteConnectedTest_iff F).mpr hF.1)
      · exact ((not_tiles_iff_obstruction F).mpr ⟨n, hn⟩) hF.2
    · intro hF
      by_cases hconn : FaceConnected F
      · have hnot : ¬ Tiles F := fun ht => hF ⟨hconn, ht⟩
        obtain ⟨n, hn⟩ := (not_tiles_iff_obstruction F).mp hnot
        exact ⟨n, Or.inr hn⟩
      · exact ⟨0, Or.inl (fun ht => hconn ((finiteConnectedTest_iff F).mp ht))⟩

end TranslationTiling
