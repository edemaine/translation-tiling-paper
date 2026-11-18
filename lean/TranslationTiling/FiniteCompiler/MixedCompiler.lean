import TranslationTiling.FiniteCompiler.MixedGeometry
import TranslationTiling.FiniteCompiler.MixedProfile2
import TranslationTiling.FiniteCompiler.MixedProfile4
import TranslationTiling.FiniteCompiler.MixedProfile5
import TranslationTiling.Compiler.FiniteNormalizedInput

namespace TranslationTiling.FiniteCompiler.MixedCompiler
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000
namespace Profiles
open MixedParameters

def count (k : Fin 3) : ℕ := if k=0 then 2 else if k=1 then 4 else 5
def profile (k : Fin 3) : Profile := if k=0 then profile2 else if k=1 then profile4 else profile5
def horizontal (k : Fin 3) : ℕ := if k=0 then horizontal2 else if k=1 then horizontal4 else horizontal5
def exponent (k : Fin 3) : ℕ := if k=0 then exponent2 else if k=1 then exponent4 else exponent5

theorem count_pos (k : Fin 3) : 0<count k := by unfold count; split_ifs <;> omega
theorem count_cap (k : Fin 3) : 24*count k≤216 := by unfold count; split_ifs <;> norm_num

theorem valid (k : Fin 3) : Valid (profile k) := by
  fin_cases k
  · exact profile2_valid
  · exact profile4_valid
  · exact profile5_valid

theorem capacity (k : Fin 3) : 24*count k≤∏ b : Fin 3, (profile k).radices b := by
  fin_cases k <;> decide +kernel

theorem support (k : Fin 3) : SupportValid (profile k) (horizontal k) := by
  fin_cases k
  · exact support2
  · exact support4
  · exact support5

theorem wordCount (k : Fin 3) : 10000≤(profile k).wordCount ∧ 256^2≤3*(profile k).wordCount ∧
    Nat.log 2 (6*(profile k).wordCount)+1≤192 := by
  fin_cases k
  · exact wordCount2
  · exact wordCount4
  · exact wordCount5

theorem volume (k : Fin 3) :
    (horizontal k)^2≤(2^15*(3*(profile k).wordCount)^2)*(profile k).order ∧
    (2^24*549072*8003^4)*(horizontal k)^2*(profile k).order*(profile k).mass*
      (2^15*(3*(profile k).wordCount)^2)^2≤2^exponent k := by
  fin_cases k
  · exact volume2
  · exact volume4
  · exact volume5
end Profiles

open MixedAlphabetSystem

def code (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Code T := by
  have hc : Fintype.card (Sudoku.Symbol T)≤24*T.length := by
    let f : Sudoku.Symbol T → Fin (24*T.length) := fun s =>
      ⟨Effective.jointIndex T s,Effective.jointIndex_lt T s⟩
    simpa using Fintype.card_le_of_injective f (fun s u h =>
      Effective.jointIndex_injective T (congrArg Fin.val h))
  have hp : 24*T.length≤Fintype.card ((b : Fin 3) → Fin ((Profiles.profile k).radices b)) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin,hlen]
    exact Profiles.capacity k
  let f : Sudoku.Symbol T ↪ ((b : Fin 3) → Fin ((Profiles.profile k).radices b)) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc.trans hp))
  exact ⟨(Profiles.profile k).radices,f,f.injective⟩

local instance codeFamily (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    AlphabetFamily (system (code k T hlen)) := family (code k T hlen)

theorem code_size (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (n : Column (system (code k T hlen))) :
    AlphabetFamily.size (T:=system (code k T hlen)) n=(Profiles.profile k).arity n.val := by
  have hn : n.val<48 := n.isLt
  change (Profiles.profile k).radices (finProdFinEquiv.symm n : Sudoku.Column × Fin 3).2=_
  rw [MixedParameters.Profile.arity,if_pos hn]
  rfl

def parameters (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Parameters (code k T hlen) :=
  MixedParameters.encoding (Profiles.profile k) (Profiles.valid k) rfl (code_size k T hlen)

theorem parameters_prime (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (i : @PrimeTag (system (code k T hlen)) (family (code k T hlen))) :
    (parameters k T hlen).primeAt i≤65536 :=
  ((Profiles.valid k).2.2.1 _ (MixedParameters.at_mem _ (Profiles.valid k) rfl
    (code_size k T hlen) (MixedParameters.tagIndex_lt _ (Profiles.valid k) rfl (code_size k T hlen) i))).2.2.2

theorem cap_bound (W s : ℕ) (hs : s≤3*W) (hW : 256^2≤3*W)
    (hlog : Nat.log 2 (6*W)+1≤192) :
    freshCap (max s (256^2)) (256^4)≤2^15*(3*W)^2 := by
  let X := max s (256^2)
  have hX : X≤3*W := max_le hs hW
  have hL : Stacking.differenceLog X≤192 := by
    have hh := Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.mul_le_mul_left 2 hX)) 1
    exact hh.trans (by simpa only [show 2*(3*W)=6*W by ring] using hlog)
  have hLo : 1≤Stacking.differenceLog X := by unfold Stacking.differenceLog; omega
  have hP : 256^4≤X^2 := by
    calc
      256^4 = (256^2)^2 := by norm_num
      _ ≤ X^2 := Nat.pow_le_pow_left (le_max_right _ _) 2
  have hcap : freshCap X (256^4)≤132*X^2*Stacking.differenceLog X := by
    unfold freshCap Stacking.logPartitionThreshold
    have hh : X^2≤X^2*Stacking.differenceLog X := Nat.le_mul_of_pos_right _ hLo
    nlinarith
  calc
    _ ≤ 132*X^2*192 := hcap.trans (Nat.mul_le_mul_left _ hL)
    _ ≤ 2^15*X^2 := by omega
    _ ≤ 2^15*(3*W)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 2)

def tile (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Tile 3 :=
  compiled (code k T hlen) (parameters k T hlen) (Profiles.horizontal k)

theorem tile_facts (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    tile k T hlen≠[] ∧ FaceConnected (tile k T hlen) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (tile k T hlen)) ∧
    (tile k T hlen).length≤2^Profiles.exponent k := by
  let C := code k T hlen
  let E := parameters k T hlen
  let H := Profiles.horizontal k
  let p := Profiles.profile k
  have hsupport : CompactSupport.Bound E H :=
    MixedParameters.encoding_support p (Profiles.valid k) rfl (code_size k T hlen)
      (Profiles.support k) (slope_bound C)
  have hH : 1≤H := (by decide : 1≤175).trans (Profiles.support k).1
  obtain ⟨hn,hc,hi,hb⟩ := compiled_facts C E H hH hsupport (parameters_prime k T hlen)
  refine ⟨hn,hc,hi,?_⟩
  have hwords : @Fintype.card (Word (system C)) _=p.wordCount :=
    MixedParameters.word_card p (Profiles.valid k) rfl (code_size k T hlen)
  have hs : (numericalFamily C E).length≤3*p.wordCount := by
    rw [numericalFamily_length]
    exact testTiles_card C E _ hwords (Profiles.wordCount k).1
      (by rw [hlen]; exact Profiles.count_cap k)
  have hell := cap_bound p.wordCount (numericalFamily C E).length hs
    (Profiles.wordCount k).2.1 (Profiles.wordCount k).2.2
  have ho : E.cyclicOrder=p.order := MixedParameters.encoding_order p (Profiles.valid k) rfl (code_size k T hlen)
  have hm : MassSize.mass E=p.mass := MixedParameters.encoding_mass p (Profiles.valid k) rfl (code_size k T hlen)
  rw [ho,hm] at hb
  have hv := Profiles.volume k
  have hM : max (H^2) (p.order*freshCap (max (numericalFamily C E).length (256^2)) (256^4))≤
      p.order*(2^15*(3*p.wordCount)^2) := by
    apply max_le
    · simpa only [Nat.mul_comm] using hv.1
    · exact Nat.mul_le_mul_left _ hell
  apply hb.trans
  apply le_trans _ hv.2
  calc
    _ ≤ (2^24*(p.mass*(2^15*(3*p.wordCount)^2)))*(549072*8003^4)*H^2*
        (p.order*(2^15*(3*p.wordCount)^2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hell)))) hM
    _ = _ := by ring

/-- The finite table is the specified mixed-alphabet construction on normalized inputs. -/
def finiteTile (k : Fin 3) (i : Fin (Compiler.Size.inputs (Profiles.count k)).length) : Tile 3 :=
  tile k (Compiler.Size.decodeInput (Profiles.count k) i) (Compiler.Size.decodeInput_length _ i)

def compile (k : Fin 3) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Compiler.Size.inputIndex (Profiles.count k) (Profiles.count_pos k) T)

theorem compile_computable (k : Fin 3) : Computable (compile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).to_comp.comp
    (Compiler.Size.inputIndex_primrec _ (Profiles.count_pos k)).to_comp

theorem compile_facts (k : Fin 3) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    compile k T≠[] ∧ FaceConnected (compile k T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compile k T)) ∧
    (compile k T).length≤2^Profiles.exponent k := by
  have hlen' : (Compiler.Size.normalize T).length=Profiles.count k := by simpa using hlen
  have hf := tile_facts k (Compiler.Size.normalize T) hlen'
  have he : compile k T=tile k (Compiler.Size.normalize T) hlen' := by
    unfold compile finiteTile
    congr 1
    exact Compiler.Size.decodeInput_index _ (Profiles.count_pos k) T hlen
  rw [he]
  exact ⟨hf.1,hf.2.1,(Compiler.Size.normalize_tilesPlane T).symm.trans hf.2.2.1,hf.2.2.2⟩

end
end TranslationTiling.FiniteCompiler.MixedCompiler
