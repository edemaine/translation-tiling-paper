import TranslationTiling.FiniteCompiler.Effective.RawChecks
import TranslationTiling.FiniteCompiler.Effective.Specifications
import TranslationTiling.FiniteCompiler.Effective.RawActivation
import TranslationTiling.FiniteCompiler.EncodedSystem

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

def decodedFamily {T : System} (E : EncodingParameters T) (Fs : List CyclicTile) :
    Finset (Finset (Ambient E)) := (Fs.map fun xs => xs.toFinset.image (decodeNumericalPoint E)).toFinset

@[simp] theorem mem_decodedFamily {T : System} (E : EncodingParameters T)
    (Fs : List CyclicTile) (F : Finset (Ambient E)) :
    F ∈ decodedFamily E Fs ↔ ∃ xs ∈ Fs, xs.toFinset.image (decodeNumericalPoint E) = F := by
  simp only [decodedFamily,List.mem_toFinset,List.mem_map]

@[simp] theorem decodedFamily_append {T : System} (E : EncodingParameters T)
    (Fs Gs : List CyclicTile) : decodedFamily E (Fs ++ Gs) = decodedFamily E Fs ∪ decodedFamily E Gs := by
  simp only [decodedFamily,List.map_append,List.toFinset_append]

@[simp] theorem decodedFamily_cons {T : System} (E : EncodingParameters T)
    (F : CyclicTile) (Fs : List CyclicTile) : decodedFamily E (F :: Fs) =
    insert (F.toFinset.image (decodeNumericalPoint E)) (decodedFamily E Fs) := by
  simp only [decodedFamily,List.map_cons,List.toFinset_cons]

theorem lowFromKeys_nil {T : System} (E : EncodingParameters T) : lowFromKeys E [] = 0 := by
  funext i
  simp [lowFromKeys]

theorem lowFromKeys_singleton {T : System} (E : EncodingParameters T) (j : Channel T) :
    lowFromKeys E [channelKey j] = (lowGenerator E j).2 := by
  funext i
  by_cases hi : i = j
  · subst i; simp [lowFromKeys,lowGenerator]
  · have hk : channelKey i ≠ channelKey j := fun he => hi (channelKey_injective T he)
    simp [lowFromKeys,lowGenerator,hi,hk]

theorem lowDependence_correct (T : System) :
    decodedFamily (parameters T) (lowDependenceFamily (parameterData T)) =
      Finset.univ.image (fun d : Σ i : Channel T, {j : Channel T // j ≠ i} =>
        dependenceTile (parameters T) (Sum.inl d)) := by
  ext F
  simp only [mem_decodedFamily,lowDependenceFamily,List.mem_flatMap,List.mem_map,
    List.mem_filter,decide_eq_true_eq,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨i,hi,j,⟨hj,hji⟩,rfl⟩,rfl⟩
    obtain ⟨i,rfl⟩ := (mem_channelKeys T i).mp hi
    obtain ⟨j,rfl⟩ := (mem_channelKeys T j).mp hj
    have hne : j ≠ i := fun he => hji (congrArg channelKey he)
    refine ⟨⟨i,⟨j,hne⟩⟩,?_⟩
    rw [rawInvariance_correct,lowFromKeys_singleton]
    rfl
  · rintro ⟨⟨i,⟨j,hji⟩⟩,rfl⟩
    refine ⟨_,⟨channelKey i,(mem_channelKeys T _).mpr ⟨i,rfl⟩,channelKey j,
      ⟨(mem_channelKeys T _).mpr ⟨j,rfl⟩,fun he => hji (channelKey_injective T he)⟩,rfl⟩,?_⟩
    rw [rawInvariance_correct,lowFromKeys_singleton]
    rfl

theorem lineDependence_correct (T : System) (p : Payload) (hp : PayloadCorrect T p) :
    decodedFamily (parameters T) (lineDependenceFamily (parameterData T,p)) =
      Finset.univ.image (fun n : Column T => dependenceTile (parameters T) (.inr (.inl n))) := by
  have he (n : Column T) :
      (rawInvariance (parameterData T) (denseChannelKey T.width n.val)
        (1,-p.1.getD n.val 0) []).toFinset.image (decodeNumericalPoint (parameters T)) =
        dependenceTile (parameters T) (.inr (.inl n)) := by
    have hd := denseChannelKey_eq T (Sum.inl n)
    change denseChannelKey T.width n.val = _ at hd
    rw [hd,rawInvariance_correct,lowFromKeys_nil,hp.1 n]
    rfl
  ext F
  simp only [mem_decodedFamily,lineDependenceFamily,List.mem_map,List.mem_range,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨n,hn,rfl⟩,rfl⟩
    exact ⟨⟨n,hn⟩,(he ⟨n,hn⟩).symm⟩
  · rintro ⟨n,rfl⟩
    exact ⟨_,⟨n.val,n.isLt,rfl⟩,he n⟩

theorem seedDependence_correct (T : System) :
    decodedFamily (parameters T) (seedDependenceFamily (parameterData T)) =
      Finset.univ.image (fun d : Fin 2 × Bool => dependenceTile (parameters T) (.inr (.inr d))) := by
  have he (t : Fin 2) (b : Bool) :
      (rawInvariance (parameterData T) (Nat.pair 1 t.val)
        (if b then (0,(Sudoku.Width : ℤ)) else ((Sudoku.Width : ℤ),0)) []).toFinset.image
          (decodeNumericalPoint (parameters T)) = dependenceTile (parameters T) (.inr (.inr (t,b))) := by
    change (rawInvariance (parameterData T) (channelKey (T := T) (.inr t)) _ []).toFinset.image _ = _
    rw [rawInvariance_correct,lowFromKeys_nil]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,dependenceTile,
      dependenceChannel,dependenceShift,seedStep,residueModulus_eq]
  ext F
  simp only [mem_decodedFamily,seedDependenceFamily,List.mem_flatMap,List.mem_range,
    List.mem_cons,List.not_mem_nil,or_false,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨t,ht,hxs⟩,rfl⟩
    rcases hxs with rfl | rfl
    · exact ⟨(⟨t,ht⟩,false),(he ⟨t,ht⟩ false).symm⟩
    · exact ⟨(⟨t,ht⟩,true),(he ⟨t,ht⟩ true).symm⟩
  · rintro ⟨⟨t,b⟩,rfl⟩
    cases b
    · exact ⟨_,⟨t.val,t.isLt,Or.inl rfl⟩,he t false⟩
    · exact ⟨_,⟨t.val,t.isLt,Or.inr rfl⟩,he t true⟩

theorem rawDependence_correct (T : System) (p : Payload) (hp : PayloadCorrect T p) :
    decodedFamily (parameters T) (rawDependenceFamily (parameterData T,p)) = dependenceTiles (parameters T) := by
  rw [rawDependenceFamily,decodedFamily_append,decodedFamily_append,
    lowDependence_correct,lineDependence_correct T p hp,seedDependence_correct]
  ext F
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,dependenceTiles]
  constructor
  · rintro (h | h)
    · rcases h with ⟨d,rfl⟩ | ⟨n,rfl⟩
      · exact ⟨.inl d,rfl⟩
      · exact ⟨.inr (.inl n),rfl⟩
    · obtain ⟨d,rfl⟩ := h
      exact ⟨.inr (.inr d),rfl⟩
  · rintro ⟨d,rfl⟩
    rcases d with d | d
    · exact Or.inl (Or.inl ⟨d,rfl⟩)
    · rcases d with n | d
      · exact Or.inl (Or.inr ⟨n,rfl⟩)
      · exact Or.inr ⟨d,rfl⟩

theorem rawWordFamily_correct (T : System) (p : Payload) (hp : PayloadCorrect T p) :
    decodedFamily (parameters T) (rawWordFamily (parameterData T,p)) = wordConstraintTiles (parameters T) := by
  have hg (w : Word T) := specifiedGadgets_correct _ _ _ (rawWordSpec_matches T w)
  ext F
  simp only [decodedFamily,rawWordFamily,List.mem_toFinset,List.mem_map,List.mem_flatMap,
    mem_numericalBadWords T p hp,wordConstraintTiles,Finset.mem_biUnion,
    Finset.mem_filter,Finset.mem_univ,true_and,mem_allowedWords]
  constructor
  · rintro ⟨xs,⟨w,⟨W,rfl,hW⟩,hxs⟩,hF⟩
    refine ⟨W,hW,?_⟩
    rw [← hg W]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs,hxs,hF⟩)
  · rintro ⟨W,hW,hF⟩
    rw [← hg W] at hF
    obtain ⟨xs,hxs,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact ⟨xs,⟨wordList W,⟨W,rfl,hW⟩,hxs⟩,he⟩

theorem mem_badSeedArguments (T : System) (p : Payload) (hp : PayloadCorrect T p) (q : ℕ × ℕ × ℕ) :
    q ∈ badSeedArguments (parameterData T,p) ↔
      ∃ z : Fin 2 × Column T × Symbol T,
        (z.1.val,z.2.1.val,z.2.2.val) = q ∧ ¬ SeedSet T z.1 z.2.2 := by
  have hs (t : Fin 2) (j : Symbol T) : j.val ∈ rawSeedAlphabet p t.val ↔ SeedSet T t j := by
    rw [← hp.2.2 t j]
    rfl
  simp only [badSeedArguments,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range,
    decide_eq_true_eq,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨t,ht,n,hn,j,hj,he⟩,hb⟩
    rcases he with ⟨rfl,rfl,rfl⟩
    exact ⟨(⟨t,ht⟩,⟨n,hn⟩,⟨j,hj⟩),rfl,fun h => hb ((hs ⟨t,ht⟩ ⟨j,hj⟩).mpr h)⟩
  · rintro ⟨⟨t,n,j⟩,he,hb⟩
    rcases he with ⟨rfl,rfl,rfl⟩
    exact ⟨⟨t.val,t.isLt,n.val,n.isLt,j.val,j.isLt,rfl⟩,
      fun h => hb ((hs t j).mp h)⟩

theorem rawSeedConstraint_correct (T : System) (p : Payload) (hp : PayloadCorrect T p) :
    decodedFamily (parameters T) (rawSeedConstraintFamily (parameterData T,p)) =
      seedConstraintTiles (parameters T) := by
  have hg (t : Fin 2) (n : Column T) (j : Symbol T) :=
    specifiedGadgets_correct _ _ _ (rawSeedSpec_matches T t n j)
  ext F
  simp only [decodedFamily,rawSeedConstraintFamily,List.mem_toFinset,List.mem_map,List.mem_flatMap,
    mem_badSeedArguments T p hp,seedConstraintTiles,Finset.mem_biUnion,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨q,⟨⟨t,n,j⟩,rfl,hq⟩,hxs⟩,hF⟩
    refine ⟨(t,n,j),hq,?_⟩
    rw [← hg t n j]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs,hxs,hF⟩)
  · rintro ⟨⟨t,n,j⟩,hq,hF⟩
    rw [← hg t n j] at hF
    obtain ⟨xs,hxs,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact ⟨xs,⟨(t.val,n.val,j.val),⟨(t,n,j),rfl,hq⟩,hxs⟩,he⟩

theorem rawOrdinaryFamily_correct (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hnonneg : ∀ n, 0 ≤ T.slope n) :
    decodedFamily (parameters T) (rawOrdinaryFamily (parameterData T,p)) =
      Finset.univ.image (ordinaryActivationTile (parameters T)) := by
  have he (n : Column T) :
      (ordinaryCodes (rawEnvironment (parameterData T) (denseChannelKey T.width n.val))
        (p.1.getD n.val 0).toNat).toFinset.image (decodeNumericalPoint (parameters T)) =
        ordinaryActivationTile (parameters T) n := by
    have hd := denseChannelKey_eq T (Sum.inl n)
    change denseChannelKey T.width n.val = _ at hd
    rw [hd,hp.1 n]
    exact rawOrdinaryTile_correct T n _ (Int.toNat_of_nonneg (hnonneg n)).symm
  ext F
  simp only [mem_decodedFamily,rawOrdinaryFamily,List.mem_map,List.mem_range,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨n,hn,rfl⟩,rfl⟩
    exact ⟨⟨n,hn⟩,(he ⟨n,hn⟩).symm⟩
  · rintro ⟨n,rfl⟩
    exact ⟨_,⟨n.val,n.isLt,rfl⟩,he n⟩

theorem rawSeedFamily_correct (T : System) :
    decodedFamily (parameters T) (rawSeedFamily (parameterData T)) =
      Finset.univ.image (seedActivationTile (parameters T)) := by
  ext F
  simp only [mem_decodedFamily,rawSeedFamily,List.mem_map,List.mem_range,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨xs,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨⟨t,ht⟩,(rawSeedTile_correct T ⟨t,ht⟩).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨_,⟨t.val,t.isLt,rfl⟩,rawSeedTile_correct T t⟩

theorem rawFamily_correct (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hnonneg : ∀ n, 0 ≤ T.slope n) :
    decodedFamily (parameters T) (rawFamily (parameterData T,p)) = testTiles (parameters T) := by
  rw [rawFamily,decodedFamily_cons,decodedFamily_append,decodedFamily_append,
    decodedFamily_append,decodedFamily_append,rawKernel_correct,rawDependence_correct T p hp,
    rawWordFamily_correct T p hp,rawSeedConstraint_correct T p hp,
    rawOrdinaryFamily_correct T p hp hnonneg,rawSeedFamily_correct]
  ext F
  simp only [Finset.mem_insert,Finset.mem_union,mem_testTiles_iff,Finset.mem_image,Finset.mem_univ,true_and]
  tauto

end
end TranslationTiling.FiniteCompiler.Effective
