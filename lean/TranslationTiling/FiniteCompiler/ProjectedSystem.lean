import TranslationTiling.FiniteCompiler.ProjectedCycles
import TranslationTiling.FiniteCompiler.PairSmallSystem
import TranslationTiling.SudokuArithmetic.ProjectedBoard

namespace TranslationTiling.FiniteCompiler.PairSmall
noncomputable section
open Sudoku.PairBoard (Selected ProjectedAllowed)
open Sudoku.NineArithmetic (baseSample atColumn)

def horizontalIndices : Fin 9 → Fin 20 := ![0,1,4,7,9,10,13,18,19]
def verticalIndices : Fin 9 → Fin 20 := ![0,1,4,9,10,13,16,18,19]
theorem horizontal_injective : Function.Injective horizontalIndices := by decide +kernel
theorem vertical_injective : Function.Injective verticalIndices := by decide +kernel

def projections (S : System) (h : S.width=20) : Projections S where
  p := ⟨fun n => (finCongr h).symm (atP n),fun _ _ he =>
    Sum.inl.inj (roleEquiv.injective ((finCongr h).symm.injective he))⟩
  q := ⟨fun n => (finCongr h).symm (atQ n),fun _ _ he =>
    Sum.inl.inj (Sum.inr.inj (roleEquiv.injective ((finCongr h).symm.injective he)))⟩
  horizontal := ⟨fun n => (finCongr h).symm (horizontalIndices n),fun _ _ he =>
    horizontal_injective ((finCongr h).symm.injective he)⟩
  vertical := ⟨fun n => (finCongr h).symm (verticalIndices n),fun _ _ he =>
    vertical_injective ((finCongr h).symm.injective he)⟩

def sideIndices (side : Bool) : Fin 9 → Fin 20 := if side then horizontalIndices else verticalIndices

theorem side_p (side : Bool) (n : Fin 9) (hn : Selected 5 side n) :
    ∃ i, sideIndices side i=atP n := by
  rcases hn with ⟨i,rfl⟩ | ⟨rfl,rfl⟩
  · cases side <;> fin_cases i <;> decide +kernel
  · exact ⟨3,by decide +kernel⟩

theorem side_q (side : Bool) (n : Fin 9) (hn : Selected 7 (!side) n) :
    ∃ i, sideIndices side i=atQ n := by
  rcases hn with ⟨i,rfl⟩ | ⟨h,rfl⟩
  · cases side <;> fin_cases i <;> decide +kernel
  · cases side
    · exact ⟨6,by decide +kernel⟩
    · contradiction

theorem side_c (side : Bool) (n : Fin 2) : ∃ i, sideIndices side i=atC n := by
  cases side <;> fin_cases n <;> decide +kernel

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance projectedSystemFamily : AlphabetFamily (system code) := family code

abbrev boardProjections := projections (system code) rfl

private theorem extension_rule (W : WordArray (system code)) (f : Fin 9 ↪ Column (system code))
    (hf : ProjectedLine f W) (a b : ℤ) :
    ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i, W (f i) (lineValue (system code) (f i) (a,b))=encodeWord code w (f i) := by
  obtain ⟨_,⟨w,hw,he⟩,hm⟩ := hf (a,b)
  exact ⟨w,hw,fun i => (hm i).symm.trans (he (f i))⟩

private theorem board_p (W : WordArray (system code))
    (h : ProjectedLine (boardProjections code).p W) :
    Sudoku.NineArithmetic.ArithmeticLineRule 5 (board code W).p := by
  intro a b
  obtain ⟨w,hw,he⟩ := extension_rule code W _ h a b
  have hr := Sudoku.PairBoard.arithmetic_p
    (Sudoku.PairBoard.restrict_lineRule (W:=fun n _ => w n) (fun _ _ => hw)) a b
  obtain ⟨a',b',hab,hp⟩ := hr
  refine ⟨a',b',hab,fun n u hu hs => ?_⟩
  have hh := readP_encoded code W w n (a*Sudoku.NineArithmetic.position 5 n+b) (by
    have hEn := he n
    change W (atP n) (lineValue (system code) (atP n) (a,b))=encodeWord code w (atP n) at hEn
    simpa [lineValue,system,slope,atP,mul_comm,add_comm] using hEn)
  change (readP code W n _).val=_
  rw [hh]
  exact hp n u hu hs

private theorem board_q (W : WordArray (system code))
    (h : ProjectedLine (boardProjections code).q W) :
    Sudoku.NineArithmetic.ArithmeticLineRule 7 (board code W).q := by
  intro a b
  obtain ⟨w,hw,he⟩ := extension_rule code W _ h a b
  have hr := Sudoku.PairBoard.arithmetic_q
    (Sudoku.PairBoard.restrict_lineRule (W:=fun n _ => w n) (fun _ _ => hw)) a b
  obtain ⟨a',b',hab,hq⟩ := hr
  refine ⟨a',b',hab,fun n u hu hs => ?_⟩
  have hh := readQ_encoded code W w n (a*Sudoku.NineArithmetic.position 7 n+b) (by
    have hEn := he n
    change W (atQ n) (lineValue (system code) (atQ n) (a,b))=encodeWord code w (atQ n) at hEn
    simpa [lineValue,system,slope,atQ,mul_comm,add_comm] using hEn)
  change (readQ code W n _).val=_
  rw [hh]
  exact hq n u hu hs

private theorem board_side (W : WordArray (system code)) (side : Bool)
    (hp : ProjectedLine (boardProjections code).horizontal W)
    (hq : ProjectedLine (boardProjections code).vertical W) (a b : ℤ) :
    ProjectedAllowed T side
      (fun n => (board code W).p n (a*Sudoku.NineArithmetic.position 5 n+b))
      (fun n => (board code W).q n (a*Sudoku.NineArithmetic.position 7 n+b))
      (fun n => (board code W).tile n (a*Sudoku.PairBoard.position n+b)) := by
  have hext : ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i, W (sideIndices side i) (lineValue (system code) (sideIndices side i) (a,b))=
        encodeWord code w (sideIndices side i) := by
    cases side
    · exact extension_rule code W _ hq a b
    · exact extension_rule code W _ hp a b
  obtain ⟨w,hw,he⟩ := hext
  have hr := Sudoku.PairBoard.restrict_lineRule (W:=fun n _ => w n) (fun _ _ => hw) a b
  obtain ⟨aa,bb,hap,haq,σ,hσ,htP,htQ,htC⟩ := hr
  refine ⟨aa,bb,hap,haq,σ,hσ,?_,?_,?_⟩
  · intro n hn u hu hs
    obtain ⟨i,hi⟩ := side_p side n hn
    have hh := he i
    rw [hi] at hh
    have heq := readP_encoded code W w n (a*Sudoku.NineArithmetic.position 5 n+b) (by
      simpa [lineValue,system,slope,atP,mul_comm,add_comm] using hh)
    change (readP code W n _).val=_
    rw [heq]
    exact htP n u hu hs
  · intro n hn u hu hs
    obtain ⟨i,hi⟩ := side_q side n hn
    have hh := he i
    rw [hi] at hh
    have heq := readQ_encoded code W w n (a*Sudoku.NineArithmetic.position 7 n+b) (by
      simpa [lineValue,system,slope,atQ,mul_comm,add_comm] using hh)
    change (readQ code W n _).val=_
    rw [heq]
    exact htQ n u hu hs
  · intro n u v hu hv h1 h2
    obtain ⟨i,hi⟩ := side_c side n
    have hh := he i
    rw [hi] at hh
    have heq := readC_encoded code W w n (a*Sudoku.PairBoard.position n+b) (by
      simpa [lineValue,system,slope,atC,mul_comm,add_comm] using hh)
    change readC code W n _=_
    rw [heq]
    exact htC n u v hu hv h1 h2

theorem projected_iff_wang (E : EncodingParameters (system code)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), ProjectedSolves E (boardProjections code) A := by
  constructor
  · intro h
    obtain ⟨A,hA⟩ := exists_solution_of_wang code E h
    exact ⟨A,projected_of_solves E _ hA⟩
  · rintro ⟨A,hA⟩
    obtain ⟨W,hp,hq,hh,hv,hs⟩ := projected_array E _ hA
    exact Sudoku.PairBoard.projected_soundness T (board code W) (fun side => board_side code W side hh hv)
      (board_p code W hp) (board_q code W hq) (board_nonconstant code W hs)

end
end TranslationTiling.FiniteCompiler.PairSmall
