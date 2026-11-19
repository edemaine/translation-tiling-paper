import TranslationTiling.FiniteCompiler.NineSmallGeometry
import TranslationTiling.FiniteCompiler.NineProfile4
import TranslationTiling.FiniteCompiler.NineProfile5
import TranslationTiling.FiniteCompiler.NineProfile6
import TranslationTiling.FiniteCompiler.NineProfile10
import TranslationTiling.FiniteCompiler.NineProfile20
import TranslationTiling.FiniteCompiler.NineProfile30
import TranslationTiling.Compiler.FiniteNormalizedInput

namespace TranslationTiling.FiniteCompiler.NineSmallCompiler
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000
namespace Profiles
open NineParameters

def count (k : Fin 27) : ℕ := 4+k.val
def profile (k : Fin 27) : Profile :=
  if k=0 then profile4 else if k=1 then profile5 else if k=2 then profile6 else if k.val<7 then profile10 else if k.val<17 then profile20 else profile30
def horizontal (k : Fin 27) : ℕ :=
  if k=0 then horizontal4 else if k=1 then horizontal5 else if k=2 then horizontal6 else if k.val<7 then horizontal10 else if k.val<17 then horizontal20 else horizontal30
def exponent (k : Fin 27) : ℕ :=
  if k=0 then exponent4 else if k=1 then exponent5 else if k=2 then exponent6 else if k.val<7 then exponent10 else if k.val<17 then exponent20 else exponent30

theorem count_pos (k : Fin 27) : 0<count k := by unfold count; omega
theorem capacity (k : Fin 27) : count k≤(profile k).alphabet := by fin_cases k <;> decide +kernel
theorem arity_cap (k : Fin 27) : (profile k).alphabet≤30 := by fin_cases k <;> decide +kernel

theorem valid (k : Fin 27) : Valid (profile k) := by
  fin_cases k
  · exact profile4_valid
  · exact profile5_valid
  · exact profile6_valid
  all_goals first | exact profile10_valid | exact profile20_valid | exact profile30_valid

theorem support (k : Fin 27) : SupportValid (profile k) (horizontal k) := by
  fin_cases k
  · exact support4
  · exact support5
  · exact support6
  all_goals first | exact support10 | exact support20 | exact support30

theorem wordCount (k : Fin 27) : 10000≤(profile k).wordCount ∧ 256^2≤3*(profile k).wordCount ∧
    Nat.log 2 (6*(profile k).wordCount)+1≤192 := by
  fin_cases k
  · exact wordCount4
  · exact wordCount5
  · exact wordCount6
  all_goals first | exact wordCount10 | exact wordCount20 | exact wordCount30

theorem volume (k : Fin 27) :
    (horizontal k)^2≤(2^15*(3*(profile k).wordCount)^2)*(profile k).order ∧
    (2^24*549072*8003^4)*(horizontal k)^2*(profile k).order*(profile k).mass*
      (2^15*(3*(profile k).wordCount)^2)^2≤2^exponent k := by
  fin_cases k
  · exact volume4
  · exact volume5
  · exact volume6
  all_goals first | exact volume10 | exact volume20 | exact volume30
end Profiles

open NineSmall

def code (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    Code T (Profiles.profile k).alphabet := by
  have hn : T≠[] := by
    intro h
    have hp := Profiles.count_pos k
    have hz : T.length=0 := by rw [h]; rfl
    omega
  have hex : ∃ t, t∈T := by cases T with
    | nil => exact (hn rfl).elim
    | cons t ts => exact ⟨t,by simp⟩
  letI : Nonempty (LeanWang.TileIn T) := ⟨⟨hex.choose,hex.choose_spec⟩⟩
  have hcap : T.length≤(Profiles.profile k).alphabet := by rw [hlen]; exact Profiles.capacity k
  let f : LeanWang.TileIn T → Fin (Profiles.profile k).alphabet :=
    fun t => ⟨T.idxOf t.val,(List.idxOf_lt_length_of_mem t.property).trans_le hcap⟩
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    exact (List.idxOf_inj t.property).mp (congrArg Fin.val h)
  exact ⟨f,Function.invFun f,Function.leftInverse_invFun hf⟩

local instance codeFamily (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    AlphabetFamily (system (code k T hlen)) := family (code k T hlen)

theorem code_size (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (n : Column (system (code k T hlen))) :
    AlphabetFamily.size (T:=system (code k T hlen)) n=(Profiles.profile k).arity n.val := by
  fin_cases n <;> rfl

def parameters (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    @EncodingParameters (system (code k T hlen)) (family (code k T hlen)) :=
  NineParameters.encoding (Profiles.profile k) (Profiles.valid k) rfl (code_size k T hlen)

theorem parameters_prime (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (i : @PrimeTag (system (code k T hlen)) (family (code k T hlen))) :
    (parameters k T hlen).primeAt i≤65536 :=
  ((Profiles.valid k).2.2.1 _ (NineParameters.at_mem _ (Profiles.valid k) rfl
    (code_size k T hlen) (NineParameters.tagIndex_lt _ (Profiles.valid k) rfl (code_size k T hlen) i))).2.2.2

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

def tile (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Tile 3 :=
  compiled (code k T hlen) (parameters k T hlen) (Profiles.horizontal k)

theorem tile_facts (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    tile k T hlen≠[] ∧ FaceConnected (tile k T hlen) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (tile k T hlen)) ∧
    (tile k T hlen).length≤2^Profiles.exponent k := by
  let C := code k T hlen
  let E := parameters k T hlen
  let H := Profiles.horizontal k
  let p := Profiles.profile k
  have hsupport : CompactSupport.Bound E H :=
    NineParameters.encoding_support p (Profiles.valid k) rfl (code_size k T hlen)
      (Profiles.support k) (slope_bound C)
  have hH : 1≤H := (by decide : 1≤175).trans (Profiles.support k).1
  obtain ⟨hn,hc,hi,hb⟩ := compiled_facts C E H hH hsupport (parameters_prime k T hlen)
  refine ⟨hn,hc,hi,?_⟩
  have hwords : @Fintype.card (Word (system C)) _=p.wordCount :=
    NineParameters.word_card p (Profiles.valid k) rfl (code_size k T hlen)
  have hs : (numericalFamily C E).length≤3*p.wordCount := by
    rw [numericalFamily_length]
    exact testTiles_card C E (Profiles.arity_cap k) _ hwords
      ((by norm_num : 2000≤10000).trans (Profiles.wordCount k).1)
  have hell := cap_bound p.wordCount (numericalFamily C E).length hs
    (Profiles.wordCount k).2.1 (Profiles.wordCount k).2.2
  have ho : E.cyclicOrder=p.order := NineParameters.encoding_order p (Profiles.valid k) rfl (code_size k T hlen)
  have hm : MassSize.mass E=p.mass := NineParameters.encoding_mass p (Profiles.valid k) rfl (code_size k T hlen)
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
def finiteTile (k : Fin 27) (i : Fin (Compiler.Size.inputs (Profiles.count k)).length) : Tile 3 :=
  tile k (Compiler.Size.decodeInput (Profiles.count k) i) (Compiler.Size.decodeInput_length _ i)

def compile (k : Fin 27) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Compiler.Size.inputIndex (Profiles.count k) (Profiles.count_pos k) T)

theorem compile_computable (k : Fin 27) : Computable (compile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).to_comp.comp
    (Compiler.Size.inputIndex_primrec _ (Profiles.count_pos k)).to_comp

theorem compile_facts (k : Fin 27) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
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
end TranslationTiling.FiniteCompiler.NineSmallCompiler
