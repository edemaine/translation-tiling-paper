import TranslationTiling.Proofs.PeriodicGrid
import TranslationTiling.Proofs.Decidability
import TranslationTiling.Proofs.IntegerResidues
import Mathlib.Data.List.OfFn

namespace TranslationTiling

/-- Canonical representatives in the coordinate torus. -/
def residuePoint {d : ℕ} (m : ℕ) (x : Lattice d) : Lattice d := fun i => x i % (m : ℤ)

private def pointOfList (d : ℕ) (xs : List ℕ) : Lattice d := fun i => (xs.getD i.val 0 : ℤ)

/-- Enumerate the fundamental coordinate box by finite words of length `d`. -/
def residueBox (d m : ℕ) : Tile d :=
  (LeanWang.words (List.range m) d).map (pointOfList d)

private theorem mem_natWords_iff {alphabet : List ℕ} {d : ℕ} {xs : List ℕ} :
    xs ∈ LeanWang.words alphabet d ↔ xs.length = d ∧ ∀ n ∈ xs, n ∈ alphabet := by
  induction d generalizing xs with
  | zero => cases xs <;> simp [LeanWang.words]
  | succ d ih => cases xs <;> simp [LeanWang.words, ih, and_left_comm, and_assoc, and_comm]

theorem residuePoint_mem_box {d : ℕ} (m : ℕ) (hm : 0 < m) (x : Lattice d) :
    residuePoint m x ∈ residueBox d m := by
  let xs := List.ofFn fun i : Fin d => (x i % (m : ℤ)).toNat
  have hxs : xs ∈ LeanWang.words (List.range m) d := by
    rw [mem_natWords_iff]
    refine ⟨List.length_ofFn, ?_⟩
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    rw [List.mem_range]
    have hpos : (0 : ℤ) < m := Int.natCast_pos.mpr hm
    have hnonneg := Int.emod_nonneg (x i) (ne_of_gt hpos)
    have hlt := Int.emod_lt_of_pos (x i) hpos
    omega
  refine List.mem_map.mpr ⟨xs, hxs, ?_⟩
  funext i
  simp only [pointOfList, xs, residuePoint]
  simp only [List.getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
  exact Int.toNat_of_nonneg (Int.emod_nonneg (x i) (Int.natCast_ne_zero.mpr hm.ne'))

theorem residuePoint_sub {d : ℕ} (m : ℕ) (x f : Lattice d) :
    residuePoint m (residuePoint m x - f) = residuePoint m (x - f) := by
  funext i
  simp only [residuePoint, Pi.sub_apply, Int.sub_emod, Int.emod_emod]

theorem residuePoint_mem_iff {d : ℕ} {A : Set (Lattice d)} (m : ℕ)
    (hperiod : ∀ v : Lattice d, Period A (m • v)) (x : Lattice d) :
    residuePoint m x ∈ A ↔ x ∈ A := by
  have he : residuePoint m x + m • (fun i => x i / (m : ℤ)) = x := by
    funext i
    simp only [residuePoint, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, mul_comm (m : ℤ)]
    exact Int.emod_add_ediv_mul (x i) (m : ℤ)
  simpa only [he] using (hperiod (fun i => x i / (m : ℤ)) (residuePoint m x)).symm

/-- Finite exact coverage on a torus. Entries outside the box are harmless. -/
def PeriodicCertificate {d : ℕ} (F : Tile d) (m : ℕ) (B : Tile d) : Prop :=
  0 < m ∧ ∀ x ∈ residueBox d m,
    ∃ f ∈ F, residuePoint m (x - f) ∈ B ∧
      ∀ g ∈ F, residuePoint m (x - g) ∈ B → g = f

instance {d : ℕ} (F : Tile d) (m : ℕ) (B : Tile d) : Decidable (PeriodicCertificate F m B) := by
  unfold PeriodicCertificate
  infer_instance

theorem periodicCertificate_tiles {d : ℕ} {F : Tile d} {m : ℕ} {B : Tile d}
    (h : PeriodicCertificate F m B) : Tiles F := by
  refine ⟨{a | residuePoint m a ∈ B}, (exactTiling_iff _ _).mpr ?_⟩
  intro x
  obtain ⟨f, hf, hb, hu⟩ := h.2 (residuePoint m x) (residuePoint_mem_box m h.1 x)
  rw [residuePoint_sub] at hb
  refine ⟨⟨f, hf⟩, hb, ?_⟩
  intro g hg
  apply Subtype.ext
  apply hu g.val g.property
  rwa [residuePoint_sub]

theorem periodicCertificate_of_grid {d : ℕ} {F : Tile d} {A : Set (Lattice d)}
    (ha : ExactTiling A {f | f ∈ F}) (m : ℕ) (hm : 0 < m)
    (hp : ∀ v : Lattice d, Period A (m • v)) : ∃ B, PeriodicCertificate F m B := by
  classical
  let B := (residueBox d m).filter fun a => decide (a ∈ A)
  have hB (x : Lattice d) : residuePoint m x ∈ B ↔ x ∈ A := by
    simp only [B, List.mem_filter, decide_eq_true_eq,
      residuePoint_mem_box m hm x, true_and, residuePoint_mem_iff m hp x]
  refine ⟨B, hm, ?_⟩
  intro x _
  obtain ⟨f, hf, hu⟩ := (exactTiling_iff _ _).mp ha x
  refine ⟨f.val, f.property, (hB _).mpr hf, ?_⟩
  intro g hg hb
  exact congrArg Subtype.val (hu ⟨g, hg⟩ ((hB _).mp hb))

theorem planar_tiles_iff_periodicCertificate (hp : PlanarPeriodicity) (F : Tile 2) :
    Tiles F ↔ ∃ m B, PeriodicCertificate F m B := by
  constructor
  · intro hF
    obtain ⟨A, ha, m, hm, hperiod⟩ := planar_grid_of_periodicity hp hF
    obtain ⟨B, hB⟩ := periodicCertificate_of_grid ha m hm hperiod
    exact ⟨m, B, hB⟩
  · rintro ⟨m, B, hB⟩
    exact periodicCertificate_tiles hB

theorem residuePoint_primrec (d : ℕ) : Primrec₂ (@residuePoint d) := by
  have h : ∀ i : Fin d, Primrec fun z : ℕ × Lattice d => z.2 i % (z.1 : ℤ) := by
    intro i
    exact int_emod_nat_primrec.comp
      (Primrec.fin_app.comp Primrec.snd (Primrec.const i)) Primrec.fst
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap

private theorem pointOfList_primrec (d : ℕ) : Primrec (pointOfList d) := by
  have h : ∀ i : Fin d, Primrec fun xs : List ℕ => (xs.getD i.val 0 : ℤ) := by
    intro i
    exact LeanWang.Kari.SignedPrimrec.intOfNat.comp
      ((Primrec.list_getD 0).comp Primrec.id (Primrec.const i.val))
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap

private theorem natWords_primrec (d : ℕ) :
    Primrec fun m : ℕ => LeanWang.words (List.range m) d := by
  induction d with
  | zero => exact Primrec.const [[]]
  | succ d ih =>
    exact Primrec.list_flatMap ih
      (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))

theorem residueBox_primrec (d : ℕ) : Primrec (residueBox d) :=
  Primrec.list_map (natWords_primrec d) ((pointOfList_primrec d).comp Primrec.snd)

/-- The verifier is primitive recursive in the tile, modulus, and finite complement. -/
theorem periodicCertificate_primrec (d : ℕ) :
    PrimrecPred fun z : Tile d × (ℕ × Tile d) => PeriodicCertificate z.1 z.2.1 z.2.2 := by
  let C := Tile d × (ℕ × Tile d)
  have hinner : PrimrecRel fun (g : Lattice d) (z : (C × Lattice d) × Lattice d) =>
      residuePoint z.1.1.2.1 (z.1.2 - g) ∈ z.1.1.2.2 → g = z.2 := by
    exact ((mem_primrec.comp
      ((residuePoint_primrec d).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
        ((lattice_sub_primrec d).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))).not.or
      (Primrec.eq.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).of_eq
      (by simp [imp_iff_not_or])
  have hall : PrimrecRel fun (f : Lattice d) (z : C × Lattice d) =>
      ∀ g ∈ z.1.1, residuePoint z.1.2.1 (z.2 - g) ∈ z.1.2.2 → g = f :=
    hinner.forall_mem_list.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair Primrec.snd Primrec.fst)
  have hhit : PrimrecRel fun (f : Lattice d) (z : C × Lattice d) =>
      residuePoint z.1.2.1 (z.2 - f) ∈ z.1.2.2 :=
    mem_primrec.comp
      ((residuePoint_primrec d).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        ((lattice_sub_primrec d).comp (Primrec.snd.comp Primrec.snd) Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hex : PrimrecRel fun (x : Lattice d) (z : C) =>
      ∃ f ∈ z.1, residuePoint z.2.1 (x - f) ∈ z.2.2 ∧
        ∀ g ∈ z.1, residuePoint z.2.1 (x - g) ∈ z.2.2 → g = f :=
    (PrimrecRel.exists_mem_list (R := fun (f : Lattice d) (z : C × Lattice d) =>
      residuePoint z.1.2.1 (z.2 - f) ∈ z.1.2.2 ∧
        ∀ g ∈ z.1.1, residuePoint z.1.2.1 (z.2 - g) ∈ z.1.2.2 → g = f)
      (hhit.and hall)).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.snd Primrec.fst)
  have hcover : PrimrecPred fun z : C => ∀ x ∈ residueBox d z.2.1,
      ∃ f ∈ z.1, residuePoint z.2.1 (x - f) ∈ z.2.2 ∧
        ∀ g ∈ z.1, residuePoint z.2.1 (x - g) ∈ z.2.2 → g = f :=
    hex.forall_mem_list.comp ((residueBox_primrec d).comp (Primrec.fst.comp Primrec.snd)) Primrec.id
  exact (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)).and hcover

/-- One natural number encodes both the torus size and its finite complement. -/
def encodedPeriodicCertificate {d : ℕ} (F : Tile d) (n : ℕ) : Prop :=
  PeriodicCertificate F n.unpair.1 (decodeTargets d n.unpair.2)

theorem encodedPeriodicCertificate_computable (d : ℕ) :
    ComputablePred fun z : Tile d × ℕ => encodedPeriodicCertificate z.1 z.2 :=
  ((periodicCertificate_primrec d).comp (Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      ((decodeTargets_primrec d).comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))).computablePred

theorem planar_tiles_iff_encodedPeriodicCertificate (hp : PlanarPeriodicity) (F : Tile 2) :
    Tiles F ↔ ∃ n, encodedPeriodicCertificate F n := by
  rw [planar_tiles_iff_periodicCertificate hp F]
  constructor
  · rintro ⟨m, B, hB⟩
    refine ⟨Nat.pair m (Encodable.encode B), ?_⟩
    simpa [encodedPeriodicCertificate, decodeTargets] using hB
  · rintro ⟨n, hn⟩
    exact ⟨n.unpair.1, decodeTargets 2 n.unpair.2, hn⟩

/-- Finite torus certificates and finite obstructions give planar decidability. -/
theorem planar_decidable (hp : PlanarPeriodicity) : ComputablePred (@Tiles 2) :=
  decidability_of_certificates encodedPeriodicCertificate
    (encodedPeriodicCertificate_computable 2) (planar_tiles_iff_encodedPeriodicCertificate hp)

end TranslationTiling
