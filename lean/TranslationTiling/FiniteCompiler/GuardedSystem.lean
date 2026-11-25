import TranslationTiling.SudokuArithmetic.PartialWordCertificate5
import TranslationTiling.SudokuArithmetic.PartialWordCertificate7
import TranslationTiling.FiniteCompiler.GuardedPatterns

namespace TranslationTiling.FiniteCompiler.GuardedCompiler
open PairSmall
open Sudoku.PairBoard (Guard QueryMatch GuardedRule)
open Sudoku.PartialWord (codes5 codes7 cover5 cover7)
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

local instance : SeedFrame := compactSeedFrame
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance : AlphabetFamily (system code) := alphabet code

def patterns : List (PartialTest (system code)) :=
  (codes5.map (testP code) ++ codes7.map (testQ code)) ++
    ((Finset.univ : Finset (QueryIndex d)).filter (badQuery code)).toList.map (queryPattern code)

private theorem codes5_nonempty :
    codes5.all (fun m => !(Sudoku.PartialWord.decode 5 m).isEmpty)=true := by decide +kernel
private theorem codes7_nonempty :
    codes7.all (fun m => !(Sudoku.PartialWord.decode 7 m).isEmpty)=true := by decide +kernel

private theorem decode_nonempty {r : ℕ} {L : List ℕ}
    (h : L.all (fun m => !(Sudoku.PartialWord.decode r m).isEmpty)=true)
    {m : ℕ} (hm : m∈L) : Sudoku.PartialWord.decode r m≠[] := by
  have he := List.all_eq_true.mp h m hm
  intro h0
  simp [h0] at he

/-- Every forbidden pattern contains an arithmetic letter. Thus the
Wang part of the pattern may be omitted when the Wang alphabet is a singleton. -/
theorem patterns_has_arithmetic (p : PartialTest (system code)) (hp : p ∈ patterns code) :
    ∃ i : Column (system code), i.val < 18 ∧ i ∈ p.columns := by
  simp only [patterns,List.mem_append,List.mem_map] at hp
  rcases hp with (⟨m,hm,rfl⟩ | ⟨m,hm,rfl⟩) | ⟨i,_,rfl⟩
  · exact pattern_has_arithmetic code _ _ _ (Or.inl (digits_nonempty 5 m
      (decode_nonempty codes5_nonempty hm)))
  · exact pattern_has_arithmetic code _ _ _ (Or.inr (digits_nonempty 7 m
      (decode_nonempty codes7_nonempty hm)))
  · exact query_has_arithmetic code i

private theorem arithmetic_P (w : Word (system code)) (hw : Allowed (system code) w) :
    Sudoku.PartialWord.IsArithmetic 5 (wordP code w) := by
  have hl := board_lineRule code (fun n _ => w n) (fun _ => hw)
  exact Sudoku.PairBoard.arithmetic_p hl 0 0

private theorem arithmetic_Q (w : Word (system code)) (hw : Allowed (system code) w) :
    Sudoku.PartialWord.IsArithmetic 7 (wordQ code w) := by
  have hl := board_lineRule code (fun n _ => w n) (fun _ => hw)
  exact Sudoku.PairBoard.arithmetic_q hl 0 0

private theorem guard_of_allowed (w : Word (system code)) (hw : Allowed (system code) w) :
    ∀ i : QueryIndex d, Guard 5 i.1 i.2.1 (wordP code w) →
      Guard 7 i.1 i.2.2.1 (wordQ code w) →
      QueryMatch i.1 (code.decode (wordC code w 0)) (code.decode (wordC code w 1)) := by
  have hl := board_lineRule code (fun n _ => w n) (fun _ => hw)
  have hproj : Sudoku.PairBoard.ProjectedLineRule (board code (fun n _ => w n)) := by
    intro side a b
    obtain ⟨u,v,hu,hv,σ,hσ,hp,hq,hc⟩ := hl a b
    exact ⟨u,v,hu,hv,σ,hσ,fun n _ => hp n,fun n _ => hq n,hc⟩
  have hg := Sudoku.PairBoard.guarded_of_projected hproj
  intro i ha hb
  exact hg _ _ _ 0 0 ha hb

theorem patterns_sound (p : PartialTest (system code)) (hp : p∈patterns code)
    (w : Word (system code)) (hw : Allowed (system code) w) : ¬ p.Matches w := by
  intro h
  simp only [patterns,List.mem_append,List.mem_map,Finset.mem_toList,Finset.mem_filter,
    Finset.mem_univ,true_and] at hp
  rcases hp with (⟨m,hm,rfl⟩|⟨m,hm,rfl⟩)|⟨i,hi,rfl⟩
  · exact Sudoku.PartialWord.avoids_of_safe (by decide) Sudoku.PartialWord.cover5_safe _
      (arithmetic_P code w hw) _ (List.mem_map.mpr ⟨m,hm,rfl⟩) ((testP_matches code m w).mp h)
  · exact Sudoku.PartialWord.avoids_of_safe (by decide) Sudoku.PartialWord.cover7_safe _
      (arithmetic_Q code w hw) _ (List.mem_map.mpr ⟨m,hm,rfl⟩) ((testQ_matches code m w).mp h)
  · obtain ⟨ha,hb,hc,hd⟩ := (query_matches code i w).mp h
    exact hi (by simpa only [hc,hd] using guard_of_allowed code w hw i ha hb)

theorem patterns_complete (W : WordArray (system code))
    (h : ∀ x p, p∈patterns code → p.columns.Nonempty →
      ¬p.Matches (fun n => W n (lineValue (system code) n x))) :
    Sudoku.NineArithmetic.ArithmeticLineRule 5 (board code W).p ∧
    Sudoku.NineArithmetic.ArithmeticLineRule 7 (board code W).q ∧ GuardedRule (board code W) := by
  have hp (x : Plane) (i : Fin 9) : wordP code (fun n => W n (lineValue (system code) n x)) i=
      (board code W).p i (x.1*Sudoku.NineArithmetic.position 5 i+x.2) := by
    simp [wordP,board,readP,lineValue,system,slope,atP,mul_comm,add_comm]
  have hq (x : Plane) (i : Fin 9) : wordQ code (fun n => W n (lineValue (system code) n x)) i=
      (board code W).q i (x.1*Sudoku.NineArithmetic.position 7 i+x.2) := by
    simp [wordQ,board,readQ,lineValue,system,slope,atQ,mul_comm,add_comm]
  have hpf (x : Plane) : wordP code (fun n => W n (lineValue (system code) n x))=
      (fun i => (board code W).p i (x.1*Sudoku.NineArithmetic.position 5 i+x.2)) :=
    funext (hp x)
  have hqf (x : Plane) : wordQ code (fun n => W n (lineValue (system code) n x))=
      (fun i => (board code W).q i (x.1*Sudoku.NineArithmetic.position 7 i+x.2)) :=
    funext (hq x)
  refine ⟨?_,?_,?_⟩
  · intro a b
    let w : Word (system code) := fun n => W n (lineValue (system code) n (a,b))
    have hav : ∀ p∈cover5, ¬ Sudoku.PartialWord.Matches
        (Sudoku.PartialWord.values 5 (wordP code w)) p := by
      intro p hp' hm
      obtain ⟨m,hm',rfl⟩ := List.mem_map.mp hp'
      exact h (a,b) _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨m,hm',rfl⟩)))))
        (pattern_nonempty code _ _ _ (Or.inl (digits_nonempty 5 m (decode_nonempty codes5_nonempty hm'))))
        ((testP_matches code m w).mpr hm)
    simpa only [w,hpf,Sudoku.PartialWord.IsArithmetic] using Sudoku.PartialWord.arithmetic_of_covers (by decide)
      Sudoku.PartialWord.partial5.unsat (wordP code w) hav
  · intro a b
    let w : Word (system code) := fun n => W n (lineValue (system code) n (a,b))
    have hav : ∀ p∈cover7, ¬ Sudoku.PartialWord.Matches
        (Sudoku.PartialWord.values 7 (wordQ code w)) p := by
      intro p hp' hm
      obtain ⟨m,hm',rfl⟩ := List.mem_map.mp hp'
      exact h (a,b) _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨m,hm',rfl⟩)))))
        (pattern_nonempty code _ _ _ (Or.inr (Or.inl (digits_nonempty 7 m (decode_nonempty codes7_nonempty hm')))))
        ((testQ_matches code m w).mpr hm)
    simpa only [w,hqf,Sudoku.PartialWord.IsArithmetic] using Sudoku.PartialWord.arithmetic_of_covers (by decide)
      Sudoku.PartialWord.partial7.unsat (wordQ code w) hav
  · intro j c c' a b hp' hq'
    let w : Word (system code) := fun n => W n (lineValue (system code) n (a,b))
    let i : QueryIndex d := (j,c,c',wordC code w 0,wordC code w 1)
    by_contra hn
    have hi : badQuery code i := by
      unfold badQuery
      simpa [i,w,wordC,board,readC,lineValue,system,slope,atC,Sudoku.PairBoard.position,
        mul_comm,add_comm] using hn
    have hmem : queryPattern code i∈patterns code := List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩),rfl⟩))
    exact h (a,b) _ hmem (query_nonempty code i)
      ((query_matches code i w).mpr ⟨by simpa [i,w,hpf] using hp',by simpa [i,w,hqf] using hq',rfl,rfl⟩)

variable (E : EncodingParameters (system code))

theorem deck_equiv : LeanWang.TilesPlane T ↔
    ∃ A : Set (Ambient E), ∀ F∈partialDeck E (patterns code), Tiles F A := by
  constructor
  · intro h
    obtain ⟨A,hA⟩ := exists_solution_of_wang code E h
    exact ⟨A,tiles_partialDeck_of_solves E _ hA (patterns_sound code)⟩
  · rintro ⟨A,hA⟩
    obtain ⟨W,hs,hr⟩ := partialDeck_array E _ hA
    obtain ⟨hp,hq,hg⟩ := patterns_complete code W hr
    exact Sudoku.PairBoard.guarded_soundness T _ hg hp hq (nonconstant_of_seeds code W hs)

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
