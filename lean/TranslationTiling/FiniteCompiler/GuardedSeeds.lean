import TranslationTiling.FiniteCompiler.PairSmallSystem

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open PairSmall
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

local instance : SeedFrame := compactSeedFrame

def seedDigit (r : ℕ) (t : Fin 2) (z : ZMod r) : Prop :=
  if t=0 then z.val≤(r-1)/2 else (r-1)/2<z.val

instance (r : ℕ) (t : Fin 2) (z : ZMod r) : Decidable (seedDigit r t z) := by
  unfold seedDigit
  infer_instance

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)

def alphabet : AlphabetFamily (system code) :=
  {family code with seed := fun t n j =>
    match roleEquiv.symm n with
    | .inl _ => ∃ u : (ZMod 5)ˣ, seedDigit 5 t u.val ∧ (pEquiv u).val=j.val
    | .inr (.inl _) => ∃ u : (ZMod 7)ˣ, seedDigit 7 t u.val ∧ (qEquiv u).val=j.val
    | .inr (.inr _) => True}

local instance guardedAlphabet : AlphabetFamily (system code) := alphabet code

theorem seed_p (t : Fin 2) (W : WordArray (system code)) (n : Sudoku.PairBoard.PColumn)
    (x : Plane) :
    LetterSeedSet (system code) t (atP n)
      (W (atP n) (lineValue (system code) (atP n) x)) ↔
    seedDigit 5 t (readP code W n (lineValue (system code) (atP n) x)).val := by
  unfold LetterSeedSet guardedAlphabet alphabet AlphabetFamily.seed
  dsimp only []
  simp only [atP,Equiv.symm_apply_apply]
  change (∃ u : (ZMod 5)ˣ, seedDigit 5 t u.val ∧
      (pEquiv u).val=(W (atP n) (lineValue (system code) (atP n) x)).val) ↔ _
  let u := readP code W n (lineValue (system code) (atP n) x)
  have he : (pEquiv u).val=(W (atP n) (lineValue (system code) (atP n) x)).val := by
    simp [u,readP]
  constructor
  · rintro ⟨z,hz,hj⟩
    have : z=u := pEquiv.injective (Fin.ext (hj.trans he.symm))
    simpa only [this,u,atP] using hz
  · exact fun h => ⟨u,h,he⟩

theorem seed_q (t : Fin 2) (W : WordArray (system code)) (n : Sudoku.PairBoard.QColumn)
    (x : Plane) :
    LetterSeedSet (system code) t (atQ n)
      (W (atQ n) (lineValue (system code) (atQ n) x)) ↔
    seedDigit 7 t (readQ code W n (lineValue (system code) (atQ n) x)).val := by
  unfold LetterSeedSet guardedAlphabet alphabet AlphabetFamily.seed
  dsimp only []
  simp only [atQ,Equiv.symm_apply_apply]
  change (∃ u : (ZMod 7)ˣ, seedDigit 7 t u.val ∧
      (qEquiv u).val=(W (atQ n) (lineValue (system code) (atQ n) x)).val) ↔ _
  let u := readQ code W n (lineValue (system code) (atQ n) x)
  have he : (qEquiv u).val=(W (atQ n) (lineValue (system code) (atQ n) x)).val := by
    simp [u,readQ]
  constructor
  · rintro ⟨z,hz,hj⟩
    have : z=u := qEquiv.injective (Fin.ext (hj.trans he.symm))
    simpa only [this,u,atQ] using hz
  · exact fun h => ⟨u,h,he⟩

theorem nonconstant_of_seeds (W : WordArray (system code))
    (h : ∀ t : Fin 2, ∃ x : Plane, ∀ n,
      LetterSeedSet (system code) t n (W n (lineValue (system code) n x))) :
    Sudoku.PairBoard.Nonconstant (board code W) := by
  obtain ⟨x,hx⟩ := h 0
  obtain ⟨y,hy⟩ := h 1
  constructor
  · intro n
    refine ⟨lineValue (system code) (atP n) x,lineValue (system code) (atP n) y,?_⟩
    have h0 := (seed_p code 0 W n x).mp (hx _)
    have h1 := (seed_p code 1 W n y).mp (hy _)
    intro he
    change readP code W n _=readP code W n _ at he
    rw [he] at h0
    simp [seedDigit] at h0 h1
    omega
  · intro n
    refine ⟨lineValue (system code) (atQ n) x,lineValue (system code) (atQ n) y,?_⟩
    have h0 := (seed_q code 0 W n x).mp (hx _)
    have h1 := (seed_q code 1 W n y).mp (hy _)
    intro he
    change readQ code W n _=readQ code W n _ at he
    rw [he] at h0
    simp [seedDigit] at h0 h1
    omega

private theorem digit_in_region {r : ℕ} (hp : r.Prime) (hdiv : r∣35)
    (x : Plane) (s : System) (y n : ℕ) (hy : (y:ZMod r)≠0)
    (he : SharedSeed.residue s x=(0,(y:ZMod residueModulus))) :
    (Sudoku.lastDigit r hp (x.2+(n:ℤ)*x.1)).val=(y:ZMod r) := by
  have hm : r∣residueModulus := by
    rw [residueModulus_value]
    exact hdiv
  let f : ZMod residueModulus →+* ZMod r := ZMod.castHom hm _
  have hx : (x.1 : ZMod r)=0 := by
    have h := congrArg (fun uv : Residues s => f uv.1) he
    simpa only [SharedSeed.residue,map_intCast,map_zero] using h
  have hy' : (x.2 : ZMod r)=(y:ZMod r) := by
    have h := congrArg (fun uv : Residues s => f uv.2) he
    simpa only [SharedSeed.residue,map_intCast,map_natCast] using h
  have hval : ((x.2+(n:ℤ)*x.1:ℤ):ZMod r)=(y:ZMod r) := by simp [hx,hy']
  have hnd : ¬(r:ℤ)∣x.2+(n:ℤ)*x.1 :=
    fun hd => hy (hval.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd))
  exact (Sudoku.lastDigit_eq_of_not_dvd r hp hnd).trans hval

private theorem compact_seed_regions (t : Fin 2) (s : System) (x : Plane)
    (hx : SharedSeed.residue s x ∈ seedActiveRegion s t) (n : ℕ) :
    seedDigit 5 t (Sudoku.lastDigit 5 (by decide) (x.2+(n:ℤ)*x.1)).val ∧
    seedDigit 7 t (Sudoku.lastDigit 7 (by decide) (x.2+(n:ℤ)*x.1)).val := by
  fin_cases t
  · obtain ⟨v,hv⟩ : SharedSeed.residue s x∈SharedSeed.firstRegion s := by
      simpa [seedActiveRegion] using hx
    have he : SharedSeed.residue s x=(0,((SharedSeed.firstHeight v:ℕ):ZMod residueModulus)) := hv.symm
    have h5 : ∀ v : ZMod 3, let z := (SharedSeed.firstHeight v:ZMod 5); z≠0 ∧ seedDigit 5 0 z := by decide +kernel
    have h7 : ∀ v : ZMod 3, let z := (SharedSeed.firstHeight v:ZMod 7); z≠0 ∧ seedDigit 7 0 z := by decide +kernel
    rw [digit_in_region (by decide) (by decide) x s _ n (h5 v).1 he,
      digit_in_region (by decide) (by decide) x s _ n (h7 v).1 he]
    exact ⟨(h5 v).2,(h7 v).2⟩
  · obtain ⟨v,hv⟩ : SharedSeed.residue s x∈SharedSeed.secondRegion s := by
      simpa [seedActiveRegion] using hx
    have he : SharedSeed.residue s x=(0,((SharedSeed.secondHeight v:ℕ):ZMod residueModulus)) := hv.symm
    have h5 : ∀ v : Fin 2 × ZMod 2, let z := (SharedSeed.secondHeight v:ZMod 5); z≠0 ∧ seedDigit 5 1 z := by decide +kernel
    have h7 : ∀ v : Fin 2 × ZMod 2, let z := (SharedSeed.secondHeight v:ZMod 7); z≠0 ∧ seedDigit 7 1 z := by decide +kernel
    rw [digit_in_region (by decide) (by decide) x s _ n (h5 v).1 he,
      digit_in_region (by decide) (by decide) x s _ n (h7 v).1 he]
    exact ⟨(h5 v).2,(h7 v).2⟩

theorem exists_solution_of_wang (E : EncodingParameters (system code))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let U := Sudoku.canonical τ (τ (0,0))
  let W := encodeArray code U
  refine ⟨CommonModel.commonGraph E W, CommonModel.common_solution E W
    (encodeArray_lineRule code U (Sudoku.canonical_lineRule τ hτ (τ (0,0)))) ?_⟩
  intro t n x hx
  obtain ⟨r,rfl⟩ := roleEquiv.surjective n
  rcases r with j | j | j
  · have hd := (compact_seed_regions t (system code) x hx (Sudoku.NineArithmetic.position 5 j)).1
    let m := lineValue (system code) (atP j) x
    have hr := readP_encoded code W (fun i => U i m) j m
      (by simp [W,encodeArray,encodeWord,atP])
    apply (seed_p code t W j x).mpr
    change seedDigit 5 t (readP code W j m).val
    rw [hr]
    simpa [U,Sudoku.canonical,m,lineValue,system,slope,atP,add_comm] using hd
  · have hd := (compact_seed_regions t (system code) x hx (Sudoku.NineArithmetic.position 7 j)).2
    let m := lineValue (system code) (atQ j) x
    have hr := readQ_encoded code W (fun i => U i m) j m
      (by simp [W,encodeArray,encodeWord,atQ])
    apply (seed_q code t W j x).mpr
    change seedDigit 7 t (readQ code W j m).val
    rw [hr]
    simpa [U,Sudoku.canonical,m,lineValue,system,slope,atQ,add_comm] using hd
  · unfold LetterSeedSet guardedAlphabet alphabet AlphabetFamily.seed
    dsimp only []
    simp only [Equiv.symm_apply_apply]

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
