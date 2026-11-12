import TranslationTiling.FiniteCompiler.Effective.WordLists

namespace TranslationTiling.FiniteCompiler.Effective

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem encodedWord_match (T : LeanWang.TileSet) (w : Compiler.Word T)
    (v : Word (bitSystem T)) :
    encodedWord T (Compiler.Effective.rawWord w) = wordList v ↔
      ∀ i b, v (BitSystem.flat i b) = BitSystem.symbolBit (bitCode T) (w i) b := by
  rw [encodedWord_eq,wordList,List.ofFn_inj]
  constructor
  · intro h i b
    apply Fin.ext
    have hi := congrFun h (BitSystem.flat i b)
    simpa only [BitSystem.flat,Equiv.symm_apply_apply] using hi.symm
  · intro h
    funext k
    have hk : BitSystem.flat (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = k :=
      finProdFinEquiv.apply_symm_apply k
    simpa only [hk] using congrArg Fin.val (h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).symm

theorem bitPayload_correct (T : LeanWang.TileSet) : PayloadCorrect (bitSystem T) (bitPayload T) := by
  constructor
  · intro n
    have hn : n.val < ((bitPayload T).1).length := by
      simpa only [bitPayload,List.length_map,List.length_range,bitSystem,BitSystem.system] using n.isLt
    rw [List.getD_eq_getElem _ _ hn]
    simp only [bitPayload,List.getElem_map,List.getElem_range,bitSystem,BitSystem.system]
    rfl
  constructor
  · intro v
    change wordList v ∈ (goodRawWords T).map (encodedWord T) ↔ _
    simp only [List.mem_map,mem_goodRawWords]
    constructor
    · rintro ⟨w,⟨v',rfl,hv'⟩,he⟩
      exact ⟨v',hv',(encodedWord_match T v' v).mp he⟩
    · rintro ⟨v',hv',he⟩
      exact ⟨Compiler.Effective.rawWord v',⟨v',rfl,hv'⟩,(encodedWord_match T v' v).mpr he⟩
  · intro t j
    fin_cases t <;>
      simp only [bitPayload,ite_true,ite_false,reduceCtorEq,seedAlphabet,List.mem_map,
        Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
    all_goals
      constructor
      · rintro ⟨j',hj',he⟩
        have hj : j' = j := Fin.ext he
        subst j'
        exact hj'
      · intro hj
        exact ⟨j,hj,rfl⟩

end TranslationTiling.FiniteCompiler.Effective
