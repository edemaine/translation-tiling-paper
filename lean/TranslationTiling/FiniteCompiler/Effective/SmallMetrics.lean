import TranslationTiling.FiniteCompiler.Effective.Arithmetic
import TranslationTiling.FiniteCompiler.CompactSupport

namespace TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem prod_range (w : ℕ) (f : ℕ→ℕ) :
    ((List.range w).map f).prod=∏ i : Fin w, f i.val := by
  have he : (List.range w).map f=List.ofFn (fun i : Fin w => f i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp
  rw [he,Fin.prod_ofFn]

private theorem prod_channels (T : System) (f : ℕ→ℕ) :
    (∏ c : Channel T, f (SmallProfiles.channelIndex c))=((List.range (T.width+2)).map f).prod := by
  rw [prod_range,Fin.prod_univ_add,Fintype.prod_sum_type]
  rfl

theorem parameters_small_order (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3) :
    (parameters T).cyclicOrder=(SmallProfiles.profile i).order T.width := by
  unfold EncodingParameters.cyclicOrder EncodingParameters.blockModulus
  simp_rw [parameters_small_r T i hw hB,EncodingParameters.a,EncodingParameters.b,
    parameters_small_prime T i hw hB]
  simp only [SmallProfiles.tagIndex]
  rw [prod_channels T (fun c => (SmallProfiles.profile i).rAt T.width c ^2*
    (SmallProfiles.profile i).entry c*(SmallProfiles.profile i).entry (T.width+2+c))]
  unfold SmallProfiles.Profile.order
  have hd : residueModulus^2=30625 := by
    norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  change residueModulus^2*_ = 30625*_
  rw [hd]

theorem parameters_small_mass (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3) :
    MassSize.mass (parameters T)=(SmallProfiles.profile i).mass T.width := by
  unfold MassSize.mass
  simp_rw [parameters_small_r T i hw hB,EncodingParameters.a,EncodingParameters.b,
    parameters_small_prime T i hw hB]
  simp only [SmallProfiles.tagIndex]
  simp_rw [←Nat.mul_assoc]
  rw [prod_channels T (fun c => (SmallProfiles.profile i).rAt T.width c*
    (SmallProfiles.profile i).entry c*(SmallProfiles.profile i).entry (T.width+2+c))]
  unfold SmallProfiles.Profile.mass
  have hd : residueModulus^2=30625 := by
    norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  change residueModulus^2*_ = 30625*_
  rw [hd]

theorem parameters_small_support (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3)
    (hS : ∀ n, (T.slope n).natAbs≤16) :
    CompactSupport.Bound (parameters T) (SmallProfiles.horizontal i) := by
  have hv := SmallProfiles.support i
  have hmod : residueModulus=175 := by
    norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  have hm : residueModulus≤SmallProfiles.horizontal i := by rw [hmod]; exact hv.1
  refine ⟨hm,fun n => (hS n).trans ((by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 16≤residueModulus).trans hm),?_,?_⟩
  · intro n
    unfold CompactSupport.A
    rw [parameters_small_r T i hw hB]
    unfold EncodingParameters.a EncodingParameters.b
    rw [parameters_small_prime T i hw hB,parameters_small_prime T i hw hB]
    simp only [SmallProfiles.tagIndex,SmallProfiles.channelIndex]
    have hn : n.val<SmallProfiles.width i := by simpa only [hw] using n.isLt
    simpa only [←hw] using hv.2.1 n.val (List.mem_range.mpr hn)
  · intro t
    have ho : (otherSeed t).val+2=3-t.val := by
      dsimp [otherSeed]
      have ht := t.isLt
      omega
    unfold CompactSupport.A
    rw [(parameters T).seed_a,ho,parameters_small_r T i hw hB]
    unfold EncodingParameters.a EncodingParameters.b
    rw [parameters_small_prime T i hw hB,parameters_small_prime T i hw hB]
    simp only [SmallProfiles.tagIndex,SmallProfiles.channelIndex]
    rw [hmod,show T.width+2+(T.width+t.val)=2*T.width+2+t.val by omega,hw]
    exact hv.2.2 t.val (List.mem_range.mpr t.isLt)

end
end TranslationTiling.FiniteCompiler.Effective
