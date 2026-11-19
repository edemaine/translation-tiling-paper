import TranslationTiling.FiniteCompiler.ProjectedGeometry
import TranslationTiling.Compiler.FiniteNormalizedInput
import TranslationTiling.FiniteCompiler.ProjectedProfile6
import TranslationTiling.FiniteCompiler.ProjectedProfile7
import TranslationTiling.FiniteCompiler.ProjectedProfile10
import TranslationTiling.FiniteCompiler.ProjectedProfile20
import TranslationTiling.FiniteCompiler.ProjectedProfile30
import TranslationTiling.FiniteCompiler.ProjectedProfile40
import TranslationTiling.FiniteCompiler.ProjectedProfile44

namespace TranslationTiling.FiniteCompiler.ProjectedCompiler
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000
open PairSmall
namespace Profiles
open ProjectedParameters

structure CheckedProfile where
  profile : Profile
  horizontal : ℕ
  exponent : ℕ
  valid : Valid profile
  support : SupportValid profile horizontal
  volume : horizontal^2≤(freshCap (testLimit profile.alphabet) (256^4))*profile.order ∧
    (2^24*549072*8003^4)*horizontal^2*profile.order*profile.mass*(freshCap (testLimit profile.alphabet) (256^4))^2≤2^exponent

def checked6 : CheckedProfile := ⟨profile6,horizontal6,exponent6,profile6_valid,support6,volume6⟩
def checked7 : CheckedProfile := ⟨profile7,horizontal7,exponent7,profile7_valid,support7,volume7⟩
def checked10 : CheckedProfile := ⟨profile10,horizontal10,exponent10,profile10_valid,support10,volume10⟩
def checked20 : CheckedProfile := ⟨profile20,horizontal20,exponent20,profile20_valid,support20,volume20⟩
def checked30 : CheckedProfile := ⟨profile30,horizontal30,exponent30,profile30_valid,support30,volume30⟩
def checked40 : CheckedProfile := ⟨profile40,horizontal40,exponent40,profile40_valid,support40,volume40⟩
def checked44 : CheckedProfile := ⟨profile44,horizontal44,exponent44,profile44_valid,support44,volume44⟩

def count (k : Fin 39) : ℕ := 6+k.val

def checked (k : Fin 39) : CheckedProfile :=
  if k.val<1 then checked6 else if k.val<2 then checked7
  else if k.val<5 then checked10 else if k.val<15 then checked20
  else if k.val<25 then checked30 else if k.val<35 then checked40 else checked44

def profile (k : Fin 39) : Profile := (checked k).profile
def horizontal (k : Fin 39) : ℕ := (checked k).horizontal
def exponent (k : Fin 39) : ℕ := (checked k).exponent

theorem count_pos (k : Fin 39) : 0<count k := by unfold count; omega
theorem capacity (k : Fin 39) : count k≤(profile k).alphabet := by fin_cases k <;> decide +kernel
theorem alphabet_ge (k : Fin 39) : 6≤(profile k).alphabet := by fin_cases k <;> decide +kernel
theorem testLimit_ge (k : Fin 39) : 256^2≤testLimit (profile k).alphabet := by fin_cases k <;> decide +kernel
theorem valid (k : Fin 39) : Valid (profile k) := (checked k).valid
theorem support (k : Fin 39) : SupportValid (profile k) (horizontal k) := (checked k).support
theorem volume (k : Fin 39) :
    (horizontal k)^2≤(freshCap (testLimit (profile k).alphabet) (256^4))*(profile k).order ∧
    (2^24*549072*8003^4)*(horizontal k)^2*(profile k).order*(profile k).mass*
      (freshCap (testLimit (profile k).alphabet) (256^4))^2≤2^exponent k := (checked k).volume
end Profiles

open PairSmall

def code (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
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

local instance codeFamily (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    AlphabetFamily (system (code k T hlen)) := family (code k T hlen)

theorem code_size (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (n : Column (system (code k T hlen))) :
    AlphabetFamily.size (T:=system (code k T hlen)) n=(Profiles.profile k).arity n.val := by
  fin_cases n <;> rfl

def parameters (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    @EncodingParameters (system (code k T hlen)) (family (code k T hlen)) :=
  ProjectedParameters.encoding (Profiles.profile k) (Profiles.valid k) rfl (code_size k T hlen)

theorem parameters_prime (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (i : @PrimeTag (system (code k T hlen)) (family (code k T hlen))) :
    (parameters k T hlen).primeAt i≤65536 :=
  ((Profiles.valid k).2.2.1 _ (ProjectedParameters.at_mem _ (Profiles.valid k) rfl
    (code_size k T hlen) (ProjectedParameters.tagIndex_lt _ (Profiles.valid k) rfl (code_size k T hlen) i))).2.2.2

theorem freshCap_mono {x y P : ℕ} (h : x≤y) : freshCap x P≤freshCap y P := by
  have hl := Nat.add_le_add_right
    (Nat.log_mono_right (b:=2) (Nat.mul_le_mul_left 2 h)) 1
  unfold freshCap Stacking.logPartitionThreshold Stacking.differenceLog
  gcongr

def tile (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Tile 3 :=
  projectedCompiled (code k T hlen) (parameters k T hlen) (Profiles.horizontal k)

theorem tile_facts (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    tile k T hlen≠[] ∧ FaceConnected (tile k T hlen) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (tile k T hlen)) ∧
    (tile k T hlen).length≤2^Profiles.exponent k := by
  let C := code k T hlen
  let E := parameters k T hlen
  let H := Profiles.horizontal k
  let p := Profiles.profile k
  have hsupport : CompactSupport.Bound E H :=
    ProjectedParameters.encoding_support p (Profiles.valid k) rfl (code_size k T hlen)
      (Profiles.support k) (slope_bound C)
  have hH : 1≤H := (by decide : 1≤175).trans (Profiles.support k).1
  obtain ⟨hn,hc,hi,hb⟩ := projectedCompiled_facts C E H hH hsupport (parameters_prime k T hlen)
  refine ⟨hn,hc,hi,?_⟩
  let L := freshCap (testLimit p.alphabet) (256^4)
  have hs : (projectedFamily C E).length≤testLimit p.alphabet := by
    rw [projectedFamily_length]
    have h := projected_card C E (Profiles.alphabet_ge k)
    exact Nat.le_of_lt h
  have hell : freshCap (max (projectedFamily C E).length (256^2)) (256^4)≤L :=
    freshCap_mono (max_le hs (Profiles.testLimit_ge k))
  have ho : E.cyclicOrder=p.order := ProjectedParameters.encoding_order p (Profiles.valid k) rfl (code_size k T hlen)
  have hm : MassSize.mass E=p.mass := ProjectedParameters.encoding_mass p (Profiles.valid k) rfl (code_size k T hlen)
  rw [ho,hm] at hb
  have hv := Profiles.volume k
  have hM : max (H^2) (p.order*freshCap (max (projectedFamily C E).length (256^2)) (256^4))≤
      p.order*L := by
    apply max_le
    · simpa only [Nat.mul_comm] using hv.1
    · exact Nat.mul_le_mul_left _ hell
  apply hb.trans
  apply le_trans _ hv.2
  calc
    _ ≤ (2^24*(p.mass*L))*(549072*8003^4)*H^2*
        (p.order*L) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hell)))) hM
    _ = _ := by ring

/-- The finite table is the specified mixed-alphabet construction on normalized inputs. -/
def finiteTile (k : Fin 39) (i : Fin (Compiler.Size.inputs (Profiles.count k)).length) : Tile 3 :=
  tile k (Compiler.Size.decodeInput (Profiles.count k) i) (Compiler.Size.decodeInput_length _ i)

def compile (k : Fin 39) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Compiler.Size.inputIndex (Profiles.count k) (Profiles.count_pos k) T)

theorem compile_computable (k : Fin 39) : Computable (compile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).to_comp.comp
    (Compiler.Size.inputIndex_primrec _ (Profiles.count_pos k)).to_comp

theorem compile_facts (k : Fin 39) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
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
end TranslationTiling.FiniteCompiler.ProjectedCompiler
