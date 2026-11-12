theorem real_tiling_coRE_complete (d : ℕ) (hd : 3 ≤ d)
  (motions : Set (Motion d))
  (hm : motions ∈ ({allMotions, translations, translationsAndRotations,
                    translationsAndReflections} : Set _)) :
  LeanWang.CoREComplete fun P : Prototile d => Connected P ∧ RealTiles P motions := ...
