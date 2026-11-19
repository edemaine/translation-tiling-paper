import TranslationTiling.Compiler.FiveTileCoverCertificate

namespace TranslationTiling.Compiler.FiveTile.CoverCases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def coverInputs31 : List CoverInput :=
  [.rectangular 0 1 0 4,
   .rectangular 0 1 1 4,
   .rectangular 0 1 2 4,
   .rectangular 0 1 3 4,
   .rectangular 0 1 4 0,
   .rectangular 0 1 4 1,
   .rectangular 0 1 4 2,
   .rectangular 0 1 4 3,
   .rectangular 0 2 0 4,
   .rectangular 0 2 1 4,
   .rectangular 0 2 2 4,
   .rectangular 0 2 3 4,
   .rectangular 0 2 4 0,
   .rectangular 0 2 4 1,
   .rectangular 0 2 4 2,
   .rectangular 0 2 4 3,
   .rectangular 0 3 0 4,
   .rectangular 0 3 1 4,
   .rectangular 0 3 2 4,
   .rectangular 0 3 3 4,
   .rectangular 0 3 4 0,
   .rectangular 0 3 4 1,
   .rectangular 0 3 4 2,
   .rectangular 0 3 4 3,
   .rectangular 0 4 0 4,
   .rectangular 0 4 1 4,
   .rectangular 0 4 2 4,
   .rectangular 0 4 3 4,
   .rectangular 0 4 4 0,
   .rectangular 0 4 4 1,
   .rectangular 0 4 4 2,
   .rectangular 0 4 4 3,
   .rowbit 0,
   .rowbit 1,
   .rowbit 2,
   .rowbit 3,
   .rowbit 4,
   .exclude ⟨31,9,0⟩,
   .exclude ⟨1023,52,0⟩,
   .exclude ⟨31775,52,6⟩,
   .exclude ⟨32767,182,0⟩,
   .exclude ⟨1015839,52,8⟩,
   .exclude ⟨1016831,182,2⟩,
   .exclude ⟨1047583,182,12⟩,
   .exclude ⟨1048575,435,0⟩,
   .exclude ⟨32505887,52,9⟩,
   .exclude ⟨32506879,182,3⟩,
   .exclude ⟨32537631,182,13⟩,
   .exclude ⟨32538623,435,1⟩,
   .exclude ⟨33521695,182,16⟩,
   .exclude ⟨33522687,435,4⟩,
   .exclude ⟨33553439,435,18⟩,
   .exclude ⟨33554431,675,0⟩]

theorem coverInputs31_valid : (coverInputs31.all CoverInput.valid)=true := by decide +kernel

def coverFormula31 : Sat.Fmla := coverInputs31.map (CoverInput.clause 31)

five_cover_certificate 31
  (include_str "Certificates/FiveTiles/cover31.cnf")
  (include_str "Certificates/FiveTiles/cover31.lrat")

def checkedCover31 : CheckedCover := ⟨31,fun cs hcs => plane_of_cover_inputs cs hcs 31 coverInputs31 coverInputs31_valid cover31_unsat⟩

end TranslationTiling.Compiler.FiveTile.CoverCases
