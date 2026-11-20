import TranslationTiling.FiniteCompiler.GuardedStrip
import TranslationTiling.Compiler.FiniteNormalizedInput
import TranslationTiling.FiniteCompiler.ProjectedProfile6
import TranslationTiling.FiniteCompiler.ProjectedProfile7
import TranslationTiling.FiniteCompiler.ProjectedProfile10
import TranslationTiling.FiniteCompiler.ProjectedProfile20
import TranslationTiling.FiniteCompiler.ProjectedProfile30
import TranslationTiling.FiniteCompiler.ProjectedProfile40
import TranslationTiling.FiniteCompiler.ProjectedProfile44
import TranslationTiling.FiniteCompiler.ProjectedProfile48

namespace TranslationTiling.FiniteCompiler.ProjectedCompiler
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
local instance : SeedFrame := compactSeedFrame
open GuardedCompiler Compiler.StripLift
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000
open PairSmall
namespace Profiles
open ProjectedParameters

def ordinaryRadius (p : Profile) (n : ℕ) : ℕ :=
  2*(p.rAt n*p.entry n*p.entry (22+n))

def seedRadius (p : Profile) (t : ℕ) : ℕ :=
  2*(3-t)*(p.rAt (20+t)*(p.entry (20+t)*p.entry (42+t))^2)*35^3

def stripRadius (p : Profile) (s : ℕ) : ℕ :=
  (((List.finRange 20).map fun n =>
      if (PairSmall.slope n).natAbs=s then ordinaryRadius p n.val else 0).foldl max
    (if s=0 then max 35 (max (seedRadius p 0) (seedRadius p 1)) else 0))

structure CheckedProfile where
  profile : Profile
  exponent : ℕ
  valid : Valid profile
  base : 35≤stripRadius profile 0
  ordinary : ∀ n : Fin 20, ordinaryRadius profile n.val≤stripRadius profile (PairSmall.slope n).natAbs
  seed : ∀ t : Fin 2, seedRadius profile t.val≤stripRadius profile 0
  volume : reservedVolumeCap 35 (stripRadius profile) (profile.order / profile.mass)
    profile.mass (reservedCap (testLimit profile.alphabet) 65536)≤2^exponent

def checked6 : CheckedProfile := ⟨profile6,2307,profile6_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked7 : CheckedProfile := ⟨profile7,2389,profile7_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked10 : CheckedProfile := ⟨profile10,2487,profile10_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked20 : CheckedProfile := ⟨profile20,2988,profile20_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked30 : CheckedProfile := ⟨profile30,3489,profile30_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked40 : CheckedProfile := ⟨profile40,3999,profile40_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked44 : CheckedProfile := ⟨profile44,4206,profile44_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
def checked48 : CheckedProfile := ⟨profile48,4679,profile48_valid,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

def count (k : Fin 43) : ℕ := 6+k.val

def checked (k : Fin 43) : CheckedProfile :=
  if k.val<1 then checked6 else if k.val<2 then checked7
  else if k.val<5 then checked10 else if k.val<15 then checked20
  else if k.val<25 then checked30 else if k.val<35 then checked40 else if k.val<39 then checked44 else checked48

def profile (k : Fin 43) : Profile := (checked k).profile
def exponent (k : Fin 43) : ℕ := (checked k).exponent

theorem count_pos (k : Fin 43) : 0<count k := by unfold count; omega
theorem capacity (k : Fin 43) : count k≤(profile k).alphabet := by fin_cases k <;> decide +kernel
theorem alphabet_ge (k : Fin 43) : 6≤(profile k).alphabet := by fin_cases k <;> decide +kernel
theorem valid (k : Fin 43) : Valid (profile k) := (checked k).valid
theorem volume (k : Fin 43) :
    reservedVolumeCap 35 (stripRadius (profile k)) ((profile k).order / (profile k).mass)
      (profile k).mass (reservedCap (testLimit (profile k).alphabet) 65536)≤2^exponent k :=
  (checked k).volume

end Profiles

open PairSmall

def code (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
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

local instance codeFamily (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    AlphabetFamily (system (code k T hlen)) := GuardedCompiler.alphabet (code k T hlen)

theorem code_size (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (n : Column (system (code k T hlen))) :
    AlphabetFamily.size (T:=system (code k T hlen)) n=(Profiles.profile k).arity n.val := by
  fin_cases n <;> rfl

def parameters (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    @EncodingParameters compactSeedFrame (system (code k T hlen)) (GuardedCompiler.alphabet (code k T hlen)) :=
  ProjectedParameters.encoding (Profiles.profile k) (Profiles.valid k) rfl (code_size k T hlen)

theorem parameters_prime (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k)
    (i : @PrimeTag (system (code k T hlen)) (GuardedCompiler.alphabet (code k T hlen))) :
    (parameters k T hlen).primeAt i≤65536 :=
  ((Profiles.valid k).2.2.1 _ (ProjectedParameters.at_mem _ (Profiles.valid k) rfl
    (code_size k T hlen) (ProjectedParameters.tagIndex_lt _ (Profiles.valid k) rfl (code_size k T hlen) i))).2.2.2

private theorem tile_witness (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    ∃ U : Tile 3, U≠[] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧ U.length≤2^Profiles.exponent k := by
  let C := code k T hlen
  let E := parameters k T hlen
  let p := Profiles.profile k
  let H := Profiles.stripRadius p
  have hs : StripBounds C E H := by
    refine ⟨(Profiles.checked k).base,?_,?_⟩
    · intro n
      have hr := ProjectedParameters.encoding_r p (Profiles.valid k) rfl (code_size k T hlen) (.inl n)
      change 2*(E.r (.inl n)*E.a (.inl n)*E.b (.inl n))≤_
      change E.r (.inl n)=p.rAt n.val at hr
      rw [hr]
      exact (Profiles.checked k).ordinary n
    · intro t
      have h := (Profiles.checked k).seed t
      have hr := ProjectedParameters.encoding_r p (Profiles.valid k) rfl (code_size k T hlen) (.inr t)
      have ho : (otherSeed t).val+2=3-t.val := by dsimp [otherSeed]; have := t.isLt; omega
      rw [E.seed_a,ho]
      unfold CompactSupport.B
      change E.r (.inr t)=p.rAt (20+t.val) at hr
      rw [hr]
      have hd : residueModulus=35 := by norm_num [residueModulus_value,compactSeedFrame]
      rw [hd]
      change 2*(3-t.val)*(p.rAt (20+t.val)*(p.entry (20+t.val)*p.entry (22+(20+t.val)))^2)*35^3≤_
      rw [show 22+(20+t.val)=42+t.val by omega]
      exact h
  have hlarge : 65536+3≤2*(testLimit p.alphabet)^2 := by
    have hs : 2313≤testLimit p.alphabet := by unfold testLimit; omega
    exact (by decide : 65536+3≤2*2313^2).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _))
  obtain ⟨U,hne,hc,hi,hb⟩ :=
    exists_strip_tile C E H hs (parameters_prime k T hlen) (Profiles.alphabet_ge k) hlarge
  have ho : E.cyclicOrder=p.order := ProjectedParameters.encoding_order p (Profiles.valid k) rfl (code_size k T hlen)
  have hm : MassSize.mass E=p.mass := ProjectedParameters.encoding_mass p (Profiles.valid k) rfl (code_size k T hlen)
  rw [inputOrder_eq_div E,ho,hm] at hb
  exact ⟨U,hne,hc,hi,hb.trans (Profiles.volume k)⟩

def tile (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) : Tile 3 :=
  (tile_witness k T hlen).choose

theorem tile_facts (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
    tile k T hlen≠[] ∧ FaceConnected (tile k T hlen) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (tile k T hlen)) ∧
    (tile k T hlen).length≤2^Profiles.exponent k := (tile_witness k T hlen).choose_spec

/-- The finite table is the specified mixed-alphabet construction on normalized inputs. -/
def finiteTile (k : Fin 43) (i : Fin (Compiler.Size.inputs (Profiles.count k)).length) : Tile 3 :=
  tile k (Compiler.Size.decodeInput (Profiles.count k) i) (Compiler.Size.decodeInput_length _ i)

def compile (k : Fin 43) (T : LeanWang.TileSet) : Tile 3 :=
  finiteTile k (Compiler.Size.inputIndex (Profiles.count k) (Profiles.count_pos k) T)

theorem compile_computable (k : Fin 43) : Computable (compile k) :=
  (Compiler.Effective.finFunction_primrec (finiteTile k)).to_comp.comp
    (Compiler.Size.inputIndex_primrec _ (Profiles.count_pos k)).to_comp

theorem compile_facts (k : Fin 43) (T : LeanWang.TileSet) (hlen : T.length=Profiles.count k) :
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
