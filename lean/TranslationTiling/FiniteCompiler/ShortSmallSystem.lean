import TranslationTiling.SudokuArithmetic.ShortBoardSoundness
import TranslationTiling.FiniteCompiler.Soundness
import TranslationTiling.FiniteCompiler.CommonSolution
import TranslationTiling.Compiler.Completeness

namespace TranslationTiling.FiniteCompiler.ShortSmall
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Roles := Sudoku.ShortBoard.PColumn ⊕ (Sudoku.ShortBoard.QColumn ⊕ Sudoku.ShortBoard.TileColumn)

def roleEquiv : Roles ≃ Fin 24 :=
  ((Equiv.refl (Fin 10)).sumCongr finSumFinEquiv).trans finSumFinEquiv

def atP (n : Sudoku.ShortBoard.PColumn) : Fin 24 := roleEquiv (.inl n)
def atQ (n : Sudoku.ShortBoard.QColumn) : Fin 24 := roleEquiv (.inr (.inl n))
def atC (n : Sudoku.ShortBoard.TileColumn) : Fin 24 := roleEquiv (.inr (.inr n))

def arity (d : ℕ) (n : Fin 24) : ℕ :=
  match roleEquiv.symm n with
  | .inl _ => 4
  | .inr (.inl _) => 6
  | .inr (.inr _) => d

def slope (n : Fin 24) : ℤ :=
  match roleEquiv.symm n with
  | .inl j => Sudoku.ShortArithmetic.position 5 j
  | .inr (.inl j) => Sudoku.ShortArithmetic.position 7 j
  | .inr (.inr j) => Sudoku.ShortBoard.position j

def pEquiv : (ZMod 5)ˣ ≃ Fin 4 :=
  (Fintype.equivFin _).trans (finCongr (by decide))
def qEquiv : (ZMod 7)ˣ ≃ Fin 6 :=
  (Fintype.equivFin _).trans (finCongr (by decide))

structure Code (T : LeanWang.TileSet) (d : ℕ) where
  encode : LeanWang.TileIn T → Fin d
  decode : Fin d → LeanWang.TileIn T
  inverse : Function.LeftInverse decode encode

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)

def encodeWord (w : Sudoku.Column → Sudoku.Symbol T) (n : Fin 24) : Fin (arity d n) :=
  ⟨match roleEquiv.symm n with
    | .inl j => (pEquiv (w (Sudoku.ShortBoard.originalP j)).1).val
    | .inr (.inl j) => (qEquiv (w (Sudoku.ShortBoard.originalQ j)).2.1).val
    | .inr (.inr j) => (code.encode (w (Sudoku.ShortBoard.originalC j)).2.2).val,
    by unfold arity; split <;> exact Fin.isLt _⟩

abbrev system (_code : Code T d) : System where
  width := 24
  width_pos := by decide
  alphabet := 0
  slope := slope
  allowed := ∅
  seed _ _ := True

@[instance_reducible] def family : AlphabetFamily (system code) where
  size := arity d
  allowed v := ∃ w, Sudoku.Allowed T w ∧ ∀ n, v n=encodeWord code w n
  seed t n j :=
    match roleEquiv.symm n with
    | .inl _ => ∃ u : (ZMod 5)ˣ, u.val=t.val+1 ∧ (pEquiv u).val=j.val
    | .inr (.inl _) => ∃ u : (ZMod 7)ˣ, u.val=t.val+1 ∧ (qEquiv u).val=j.val
    | .inr (.inr _) => True

local instance : AlphabetFamily (system code) := family code

@[simp] theorem arity_p (n : Sudoku.ShortBoard.PColumn) : arity d (atP n)=4 := by
  simp [arity,atP]
@[simp] theorem arity_q (n : Sudoku.ShortBoard.QColumn) : arity d (atQ n)=6 := by
  simp [arity,atQ]
@[simp] theorem arity_c (n : Sudoku.ShortBoard.TileColumn) : arity d (atC n)=d := by
  simp [arity,atC]

def readP (W : WordArray (system code)) (n : Sudoku.ShortBoard.PColumn) (m : ℤ) : (ZMod 5)ˣ :=
  pEquiv.symm ⟨(W (atP n) m).val,by have h : (W (atP n) m).val < arity d (atP n) := (W (atP n) m).isLt; simpa using h⟩
def readQ (W : WordArray (system code)) (n : Sudoku.ShortBoard.QColumn) (m : ℤ) : (ZMod 7)ˣ :=
  qEquiv.symm ⟨(W (atQ n) m).val,by have h : (W (atQ n) m).val < arity d (atQ n) := (W (atQ n) m).isLt; simpa using h⟩
def readC (W : WordArray (system code)) (n : Sudoku.ShortBoard.TileColumn) (m : ℤ) : LeanWang.TileIn T :=
  code.decode ⟨(W (atC n) m).val,by have h : (W (atC n) m).val < arity d (atC n) := (W (atC n) m).isLt; simpa using h⟩

def board (W : WordArray (system code)) : Sudoku.ShortBoard.Board T :=
  ⟨readP code W,readQ code W,readC code W⟩

theorem readP_encoded (W : WordArray (system code)) (w : Sudoku.Column → Sudoku.Symbol T)
    (n : Sudoku.ShortBoard.PColumn) (m : ℤ)
    (h : W (atP n) m=encodeWord code w (atP n)) :
    readP code W n m=(w (Sudoku.ShortBoard.originalP n)).1 := by
  apply pEquiv.injective
  apply Fin.ext
  simpa [readP,encodeWord,atP] using congrArg Fin.val h

theorem readQ_encoded (W : WordArray (system code)) (w : Sudoku.Column → Sudoku.Symbol T)
    (n : Sudoku.ShortBoard.QColumn) (m : ℤ)
    (h : W (atQ n) m=encodeWord code w (atQ n)) :
    readQ code W n m=(w (Sudoku.ShortBoard.originalQ n)).2.1 := by
  apply qEquiv.injective
  apply Fin.ext
  simpa [readQ,encodeWord,atQ] using congrArg Fin.val h

theorem readC_encoded (W : WordArray (system code)) (w : Sudoku.Column → Sudoku.Symbol T)
    (n : Sudoku.ShortBoard.TileColumn) (m : ℤ)
    (h : W (atC n) m=encodeWord code w (atC n)) :
    readC code W n m=(w (Sudoku.ShortBoard.originalC n)).2.2 := by
  have hh : (⟨(W (atC n) m).val,by have h : (W (atC n) m).val < arity d (atC n) := (W (atC n) m).isLt; simpa using h⟩ : Fin d)=code.encode (w (Sudoku.ShortBoard.originalC n)).2.2 := by
    apply Fin.ext
    simpa [encodeWord,atC] using congrArg Fin.val h
  dsimp [readC]
  rw [hh]
  exact code.inverse _

theorem board_lineRule (W : WordArray (system code)) (hw : LineRule (system code) W) :
    Sudoku.ShortBoard.LineRule (board code W) := by
  intro a b
  obtain ⟨w,hw',he⟩ := hw (a,b)
  have hr := Sudoku.ShortBoard.restrict_lineRule
    (W:=fun n _ => w n) (fun _ _ => hw') a b
  convert hr using 1
  · funext n
    apply readP_encoded
    simpa [lineValue,system,slope,atP,mul_comm,add_comm] using he (atP n)
  · funext n
    apply readQ_encoded
    simpa [lineValue,system,slope,atQ,mul_comm,add_comm] using he (atQ n)
  · funext n
    apply readC_encoded
    simpa [lineValue,system,slope,atC,mul_comm,add_comm] using he (atC n)

theorem board_nonconstant (W : WordArray (system code))
    (hs : ∀ t : Fin 2, ∃ x : Plane, ∀ n,
      LetterSeedSet (system code) t n (W n (lineValue (system code) n x))) :
    Sudoku.ShortBoard.Nonconstant (board code W) := by
  obtain ⟨x0,h0⟩ := hs 0
  obtain ⟨x1,h1⟩ := hs 1
  constructor
  · intro n
    refine ⟨lineValue (system code) (atP n) x0,lineValue (system code) (atP n) x1,?_⟩
    intro he
    have he' := congrArg (fun a : (ZMod 5)ˣ => a.val) he
    have ha := h0 (atP n)
    have hb := h1 (atP n)
    unfold LetterSeedSet at ha hb
    unfold instAlphabetFamilySystem at ha hb
    unfold family at ha hb
    unfold AlphabetFamily.seed at ha hb
    dsimp only [] at ha hb
    simp only [atP,Equiv.symm_apply_apply] at ha hb
    with_unfolding_all change (∃ u : (ZMod 5)ˣ, u.val=(0:Fin 2).val+1 ∧ (pEquiv u).val=_) at ha
    with_unfolding_all change (∃ u : (ZMod 5)ˣ, u.val=(1:Fin 2).val+1 ∧ (pEquiv u).val=_) at hb
    obtain ⟨u0,hu0,hc0⟩ := ha
    obtain ⟨u1,hu1,hc1⟩ := hb
    have hr0 : readP code W n (lineValue (system code) (atP n) x0)=u0 := by
      apply pEquiv.injective
      apply Fin.ext
      simpa [readP,atP] using hc0.symm
    have hr1 : readP code W n (lineValue (system code) (atP n) x1)=u1 := by
      apply pEquiv.injective
      apply Fin.ext
      simpa [readP,atP] using hc1.symm
    change (readP code W n _).val=(readP code W n _).val at he'
    have ha : (readP code W n (lineValue (system code) (atP n) x0)).val=1 := by rw [hr0]; exact hu0
    have hb : (readP code W n (lineValue (system code) (atP n) x1)).val=2 := by rw [hr1]; exact hu1
    rw [ha,hb] at he'
    exact (by decide : (1:ZMod 5)≠2) he'
  · intro n
    refine ⟨lineValue (system code) (atQ n) x0,lineValue (system code) (atQ n) x1,?_⟩
    intro he
    have he' := congrArg (fun a : (ZMod 7)ˣ => a.val) he
    have ha := h0 (atQ n)
    have hb := h1 (atQ n)
    unfold LetterSeedSet at ha hb
    unfold instAlphabetFamilySystem at ha hb
    unfold family at ha hb
    unfold AlphabetFamily.seed at ha hb
    dsimp only [] at ha hb
    simp only [atQ,Equiv.symm_apply_apply] at ha hb
    with_unfolding_all change (∃ u : (ZMod 7)ˣ, u.val=(0:Fin 2).val+1 ∧ (qEquiv u).val=_) at ha
    with_unfolding_all change (∃ u : (ZMod 7)ˣ, u.val=(1:Fin 2).val+1 ∧ (qEquiv u).val=_) at hb
    obtain ⟨u0,hu0,hc0⟩ := ha
    obtain ⟨u1,hu1,hc1⟩ := hb
    have hr0 : readQ code W n (lineValue (system code) (atQ n) x0)=u0 := by
      apply qEquiv.injective
      apply Fin.ext
      simpa [readQ,atQ] using hc0.symm
    have hr1 : readQ code W n (lineValue (system code) (atQ n) x1)=u1 := by
      apply qEquiv.injective
      apply Fin.ext
      simpa [readQ,atQ] using hc1.symm
    change (readQ code W n _).val=(readQ code W n _).val at he'
    have ha : (readQ code W n (lineValue (system code) (atQ n) x0)).val=1 := by rw [hr0]; exact hu0
    have hb : (readQ code W n (lineValue (system code) (atQ n) x1)).val=2 := by rw [hr1]; exact hu1
    rw [ha,hb] at he'
    exact (by decide : (1:ZMod 7)≠2) he'

theorem wang_of_solves (E : EncodingParameters (system code))
    {A : Set (Ambient E)} (hA : Solves E A) : LeanWang.TilesPlane T := by
  obtain ⟨W,hw,hs⟩ := array_of_solves E hA
  exact Sudoku.ShortBoard.soundness T (board code W)
    (board_lineRule code W hw) (board_nonconstant code W hs)

def encodeArray (U : Sudoku.Array T) : WordArray (system code) :=
  fun n m => encodeWord code (fun j => U j m) n

theorem encodeArray_lineRule (U : Sudoku.Array T) (hU : Sudoku.LineRule U) :
    LineRule (system code) (encodeArray code U) := by
  intro x
  refine ⟨fun j => U j (Compiler.lineValue j x),?_,?_⟩
  · simpa [Compiler.lineValue,mul_comm,add_comm] using hU x.1 x.2
  · intro n
    obtain ⟨r,rfl⟩ := roleEquiv.surjective n
    cases r with
    | inl j =>
      apply Fin.ext
      simp [encodeArray,encodeWord,lineValue,system,slope,Compiler.lineValue,Sudoku.ShortBoard.originalP,Sudoku.ShortBoard.originalQ,Sudoku.ShortBoard.originalC]
    | inr r =>
      cases r with
      | inl j =>
        apply Fin.ext
        simp [encodeArray,encodeWord,lineValue,system,slope,Compiler.lineValue,Sudoku.ShortBoard.originalP,Sudoku.ShortBoard.originalQ,Sudoku.ShortBoard.originalC]
      | inr j =>
        apply Fin.ext
        simp [encodeArray,encodeWord,lineValue,system,slope,Compiler.lineValue,Sudoku.ShortBoard.originalP,Sudoku.ShortBoard.originalQ,Sudoku.ShortBoard.originalC]

theorem exists_solution_of_wang (E : EncodingParameters (system code))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let U := Sudoku.canonical τ (τ (0,0))
  let W := encodeArray code U
  refine ⟨CommonModel.commonGraph E W, CommonModel.common_solution E W
    (encodeArray_lineRule code U (Sudoku.canonical_lineRule τ hτ (τ (0,0)))) ?_⟩
  intro t n x hx
  have hx' : Compiler.SharedSeed.residue T x∈Compiler.seedActiveRegion T t := by
    exact hx
  obtain ⟨r,rfl⟩ := roleEquiv.surjective n
  cases r with
  | inl j =>
    have ht := (Compiler.canonical_seed_regions τ t
      (Sudoku.ShortBoard.originalP j) x hx').1
    unfold LetterSeedSet instAlphabetFamilySystem family AlphabetFamily.seed
    dsimp only []
    simp only [Equiv.symm_apply_apply]
    with_unfolding_all change ∃ u : (ZMod 5)ˣ, u.val=t.val+1 ∧ (pEquiv u).val=_
    refine ⟨(U (Sudoku.ShortBoard.originalP j)
      (Compiler.lineValue (Sudoku.ShortBoard.originalP j) x)).1,?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using ht
    · simp [W,U,encodeArray,encodeWord,lineValue,system,slope,Compiler.lineValue,Sudoku.ShortBoard.originalP,Sudoku.ShortBoard.originalQ,Sudoku.ShortBoard.originalC]
  | inr r =>
    cases r with
    | inl j =>
      have ht := (Compiler.canonical_seed_regions τ t (Sudoku.ShortBoard.originalQ j) x hx').2
      unfold LetterSeedSet instAlphabetFamilySystem family AlphabetFamily.seed
      dsimp only []
      simp only [Equiv.symm_apply_apply]
      with_unfolding_all change ∃ u : (ZMod 7)ˣ, u.val=t.val+1 ∧ (qEquiv u).val=_
      refine ⟨(U (Sudoku.ShortBoard.originalQ j) (Compiler.lineValue (Sudoku.ShortBoard.originalQ j) x)).2.1,?_,?_⟩
      · simpa only [Nat.cast_add,Nat.cast_one] using ht
      · simp [W,U,encodeArray,encodeWord,lineValue,system,slope,Compiler.lineValue,Sudoku.ShortBoard.originalP,Sudoku.ShortBoard.originalQ,Sudoku.ShortBoard.originalC]
    | inr j =>
      unfold LetterSeedSet instAlphabetFamilySystem family AlphabetFamily.seed
      dsimp only []
      simp only [Equiv.symm_apply_apply]


theorem finite_system_iff_wang (E : EncodingParameters (system code)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A :=
  ⟨exists_solution_of_wang code E,fun ⟨_,hA⟩ => wang_of_solves code E hA⟩

end
end TranslationTiling.FiniteCompiler.ShortSmall
