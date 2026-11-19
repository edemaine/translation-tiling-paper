import TranslationTiling.Compiler.FiveTileCertificate

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs32 : List Input :=
  [.choice 1 5,
   .horizontal 1 5 0 0,
   .horizontal 1 5 1 0,
   .horizontal 1 5 2 0,
   .horizontal 1 5 3 0,
   .horizontal 1 5 4 0,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs32_valid : (inputs32.all (Input.valid 138 5 6))=true := by decide +kernel

def formula32 : Sat.Fmla := inputs32.map (Input.clause 5)

five_tile_certificate 32
  (include_str "Certificates/FiveTiles/32.cnf")
  (include_str "Certificates/FiveTiles/32.lrat")

def checked32 : CheckedCase := ⟨138, plane_of_inputs inputs32 inputs32_valid case32_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs33 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 3,
   .horizontal 2 5 1 4,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs33_valid : (inputs33.all (Input.valid 139 5 6))=true := by decide +kernel

def formula33 : Sat.Fmla := inputs33.map (Input.clause 5)

five_tile_certificate 33
  (include_str "Certificates/FiveTiles/33.cnf")
  (include_str "Certificates/FiveTiles/33.lrat")

def checked33 : CheckedCase := ⟨139, plane_of_inputs inputs33 inputs33_valid case33_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs34 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs34_valid : (inputs34.all (Input.valid 152 5 6))=true := by decide +kernel

def formula34 : Sat.Fmla := inputs34.map (Input.clause 5)

five_tile_certificate 34
  (include_str "Certificates/FiveTiles/34.cnf")
  (include_str "Certificates/FiveTiles/34.lrat")

def checked34 : CheckedCase := ⟨152, plane_of_inputs inputs34 inputs34_valid case34_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs35 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs35_valid : (inputs35.all (Input.valid 153 5 6))=true := by decide +kernel

def formula35 : Sat.Fmla := inputs35.map (Input.clause 5)

five_tile_certificate 35
  (include_str "Certificates/FiveTiles/35.cnf")
  (include_str "Certificates/FiveTiles/35.lrat")

def checked35 : CheckedCase := ⟨153, plane_of_inputs inputs35 inputs35_valid case35_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs36 : List Input :=
  [.choice 1 5,
   .horizontal 1 5 0 0,
   .horizontal 1 5 1 0,
   .horizontal 1 5 2 0,
   .horizontal 1 5 3 0,
   .horizontal 1 5 4 0,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs36_valid : (inputs36.all (Input.valid 154 5 6))=true := by decide +kernel

def formula36 : Sat.Fmla := inputs36.map (Input.clause 5)

five_tile_certificate 36
  (include_str "Certificates/FiveTiles/36.cnf")
  (include_str "Certificates/FiveTiles/36.lrat")

def checked36 : CheckedCase := ⟨154, plane_of_inputs inputs36 inputs36_valid case36_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs37 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 3,
   .horizontal 2 5 1 4,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs37_valid : (inputs37.all (Input.valid 155 5 6))=true := by decide +kernel

def formula37 : Sat.Fmla := inputs37.map (Input.clause 5)

five_tile_certificate 37
  (include_str "Certificates/FiveTiles/37.cnf")
  (include_str "Certificates/FiveTiles/37.lrat")

def checked37 : CheckedCase := ⟨155, plane_of_inputs inputs37 inputs37_valid case37_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs38 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs38_valid : (inputs38.all (Input.valid 165 5 6))=true := by decide +kernel

def formula38 : Sat.Fmla := inputs38.map (Input.clause 5)

five_tile_certificate 38
  (include_str "Certificates/FiveTiles/38.cnf")
  (include_str "Certificates/FiveTiles/38.lrat")

def checked38 : CheckedCase := ⟨165, plane_of_inputs inputs38 inputs38_valid case38_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs39 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 4,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 4,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs39_valid : (inputs39.all (Input.valid 170 5 6))=true := by decide +kernel

def formula39 : Sat.Fmla := inputs39.map (Input.clause 5)

five_tile_certificate 39
  (include_str "Certificates/FiveTiles/39.cnf")
  (include_str "Certificates/FiveTiles/39.lrat")

def checked39 : CheckedCase := ⟨170, plane_of_inputs inputs39 inputs39_valid case39_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs40 : List Input :=
  [.choice 1 5,
   .horizontal 1 5 0 1,
   .horizontal 1 5 1 1,
   .horizontal 1 5 2 1,
   .horizontal 1 5 3 1,
   .horizontal 1 5 4 1,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs40_valid : (inputs40.all (Input.valid 184 5 6))=true := by decide +kernel

def formula40 : Sat.Fmla := inputs40.map (Input.clause 5)

five_tile_certificate 40
  (include_str "Certificates/FiveTiles/40.cnf")
  (include_str "Certificates/FiveTiles/40.lrat")

def checked40 : CheckedCase := ⟨184, plane_of_inputs inputs40 inputs40_valid case40_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs41 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs41_valid : (inputs41.all (Input.valid 186 5 6))=true := by decide +kernel

def formula41 : Sat.Fmla := inputs41.map (Input.clause 5)

five_tile_certificate 41
  (include_str "Certificates/FiveTiles/41.cnf")
  (include_str "Certificates/FiveTiles/41.lrat")

def checked41 : CheckedCase := ⟨186, plane_of_inputs inputs41 inputs41_valid case41_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs42 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 1 4,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 0 1,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 2,
   .horizontal 2 5 0 4,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 2,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 2,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs42_valid : (inputs42.all (Input.valid 201 5 6))=true := by decide +kernel

def formula42 : Sat.Fmla := inputs42.map (Input.clause 5)

five_tile_certificate 42
  (include_str "Certificates/FiveTiles/42.cnf")
  (include_str "Certificates/FiveTiles/42.lrat")

def checked42 : CheckedCase := ⟨201, plane_of_inputs inputs42 inputs42_valid case42_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs43 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 2,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 0 2,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs43_valid : (inputs43.all (Input.valid 216 5 6))=true := by decide +kernel

def formula43 : Sat.Fmla := inputs43.map (Input.clause 5)

five_tile_certificate 43
  (include_str "Certificates/FiveTiles/43.cnf")
  (include_str "Certificates/FiveTiles/43.lrat")

def checked43 : CheckedCase := ⟨216, plane_of_inputs inputs43 inputs43_valid case43_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs44 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 1 4,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 0 1,
   .vertical 2 4 0 1,
   .horizontal 2 4 1 0,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 2,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 2,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs44_valid : (inputs44.all (Input.valid 217 5 6))=true := by decide +kernel

def formula44 : Sat.Fmla := inputs44.map (Input.clause 5)

five_tile_certificate 44
  (include_str "Certificates/FiveTiles/44.cnf")
  (include_str "Certificates/FiveTiles/44.lrat")

def checked44 : CheckedCase := ⟨217, plane_of_inputs inputs44 inputs44_valid case44_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs45 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .choice 2 4,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 3,
   .horizontal 2 5 0 4,
   .horizontal 2 5 1 3,
   .horizontal 2 5 1 4,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs45_valid : (inputs45.all (Input.valid 231 5 6))=true := by decide +kernel

def formula45 : Sat.Fmla := inputs45.map (Input.clause 5)

five_tile_certificate 45
  (include_str "Certificates/FiveTiles/45.cnf")
  (include_str "Certificates/FiveTiles/45.lrat")

def checked45 : CheckedCase := ⟨231, plane_of_inputs inputs45 inputs45_valid case45_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs46 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 2,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs46_valid : (inputs46.all (Input.valid 248 5 6))=true := by decide +kernel

def formula46 : Sat.Fmla := inputs46.map (Input.clause 5)

five_tile_certificate 46
  (include_str "Certificates/FiveTiles/46.cnf")
  (include_str "Certificates/FiveTiles/46.lrat")

def checked46 : CheckedCase := ⟨248, plane_of_inputs inputs46 inputs46_valid case46_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs47 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs47_valid : (inputs47.all (Input.valid 396 5 6))=true := by decide +kernel

def formula47 : Sat.Fmla := inputs47.map (Input.clause 5)

five_tile_certificate 47
  (include_str "Certificates/FiveTiles/47.cnf")
  (include_str "Certificates/FiveTiles/47.lrat")

def checked47 : CheckedCase := ⟨396, plane_of_inputs inputs47 inputs47_valid case47_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs48 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs48_valid : (inputs48.all (Input.valid 429 5 6))=true := by decide +kernel

def formula48 : Sat.Fmla := inputs48.map (Input.clause 5)

five_tile_certificate 48
  (include_str "Certificates/FiveTiles/48.cnf")
  (include_str "Certificates/FiveTiles/48.lrat")

def checked48 : CheckedCase := ⟨429, plane_of_inputs inputs48 inputs48_valid case48_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs49 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 2 0,
   .horizontal 2 3 2 1,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 0,
   .horizontal 2 3 3 1,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 0,
   .horizontal 2 3 4 1,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .choice 2 4,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 2 3,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 3,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .horizontal 2 5 4 3,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs49_valid : (inputs49.all (Input.valid 495 5 6))=true := by decide +kernel

def formula49 : Sat.Fmla := inputs49.map (Input.clause 5)

five_tile_certificate 49
  (include_str "Certificates/FiveTiles/49.cnf")
  (include_str "Certificates/FiveTiles/49.lrat")

def checked49 : CheckedCase := ⟨495, plane_of_inputs inputs49 inputs49_valid case49_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs50 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs50_valid : (inputs50.all (Input.valid 924 5 6))=true := by decide +kernel

def formula50 : Sat.Fmla := inputs50.map (Input.clause 5)

five_tile_certificate 50
  (include_str "Certificates/FiveTiles/50.cnf")
  (include_str "Certificates/FiveTiles/50.lrat")

def checked50 : CheckedCase := ⟨924, plane_of_inputs inputs50 inputs50_valid case50_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs51 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 1,
   .horizontal 2 4 1 1,
   .horizontal 2 4 2 1,
   .horizontal 2 4 3 1,
   .horizontal 2 4 4 1,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs51_valid : (inputs51.all (Input.valid 957 5 6))=true := by decide +kernel

def formula51 : Sat.Fmla := inputs51.map (Input.clause 5)

five_tile_certificate 51
  (include_str "Certificates/FiveTiles/51.cnf")
  (include_str "Certificates/FiveTiles/51.lrat")

def checked51 : CheckedCase := ⟨957, plane_of_inputs inputs51 inputs51_valid case51_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs52 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 2 0,
   .horizontal 2 3 2 1,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 0,
   .horizontal 2 3 3 1,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 0,
   .horizontal 2 3 4 1,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 1 0,
   .horizontal 3 3 4 0,
   .horizontal 3 3 4 1,
   .horizontal 3 3 4 2,
   .horizontal 3 3 4 3,
   .horizontal 3 3 4 4,
   .choice 4 3,
   .choice 2 4,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 1 1,
   .choice 2 5,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 2 0,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs52_valid : (inputs52.all (Input.valid 1023 5 6))=true := by decide +kernel

def formula52 : Sat.Fmla := inputs52.map (Input.clause 5)

five_tile_certificate 52
  (include_str "Certificates/FiveTiles/52.cnf")
  (include_str "Certificates/FiveTiles/52.lrat")

def checked52 : CheckedCase := ⟨1023, plane_of_inputs inputs52 inputs52_valid case52_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs53 : List Input :=
  [.choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 1 1,
   .horizontal 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 0 2,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 2,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 0 1,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs53_valid : (inputs53.all (Input.valid 1057 5 6))=true := by decide +kernel

def formula53 : Sat.Fmla := inputs53.map (Input.clause 5)

five_tile_certificate 53
  (include_str "Certificates/FiveTiles/53.cnf")
  (include_str "Certificates/FiveTiles/53.lrat")

def checked53 : CheckedCase := ⟨1057, plane_of_inputs inputs53 inputs53_valid case53_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs54 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 2,
   .horizontal 2 4 1 2,
   .horizontal 2 4 2 2,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .horizontal 3 4 0 0,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 2,
   .horizontal 3 4 0 3,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .horizontal 3 4 1 1,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .vertical 4 4 0 1,
   .vertical 4 4 1 0,
   .vertical 4 4 1 1,
   .choice 1 5,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 2,
   .horizontal 2 5 1 2,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 0 0,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs54_valid : (inputs54.all (Input.valid 1058 5 6))=true := by decide +kernel

def formula54 : Sat.Fmla := inputs54.map (Input.clause 5)

five_tile_certificate 54
  (include_str "Certificates/FiveTiles/54.cnf")
  (include_str "Certificates/FiveTiles/54.lrat")

def checked54 : CheckedCase := ⟨1058, plane_of_inputs inputs54 inputs54_valid case54_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs55 : List Input :=
  [.rectangular 0 1 0 2,
   .rectangular 0 1 2 1,
   .rectangular 0 2 0 1,
   .rectangular 2 0 1 0,
   .rectangular 2 1 1 0,
   .choice 1 3,
   .vertical 1 3 0 2,
   .horizontal 1 3 0 3,
   .horizontal 1 3 0 4,
   .horizontal 1 3 1 2,
   .horizontal 1 3 1 3,
   .horizontal 1 3 1 4,
   .horizontal 1 3 2 2,
   .horizontal 1 3 2 3,
   .horizontal 1 3 2 4,
   .horizontal 1 3 3 2,
   .horizontal 1 3 3 3,
   .horizontal 1 3 3 4,
   .horizontal 1 3 4 2,
   .horizontal 1 3 4 3,
   .horizontal 1 3 4 4,
   .choice 2 3,
   .horizontal 2 3 0 0,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 0 2,
   .horizontal 2 3 0 3,
   .horizontal 2 3 0 4,
   .vertical 2 3 1 0,
   .horizontal 2 3 1 1,
   .vertical 2 3 1 1,
   .horizontal 2 3 1 2,
   .vertical 2 3 1 2,
   .horizontal 2 3 1 3,
   .horizontal 2 3 1 4,
   .vertical 2 3 2 0,
   .horizontal 2 3 2 1,
   .vertical 2 3 2 1,
   .horizontal 2 3 2 2,
   .vertical 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 1,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 1,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .horizontal 3 3 0 0,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 0 2,
   .horizontal 3 3 0 3,
   .horizontal 3 3 0 4,
   .vertical 3 3 1 0,
   .horizontal 3 3 1 1,
   .vertical 3 3 1 1,
   .horizontal 3 3 1 2,
   .vertical 3 3 1 2,
   .horizontal 3 3 1 3,
   .horizontal 3 3 1 4,
   .vertical 3 3 2 0,
   .horizontal 3 3 2 1,
   .vertical 3 3 2 1,
   .horizontal 3 3 2 2,
   .vertical 3 3 2 2,
   .horizontal 3 3 2 3,
   .horizontal 3 3 2 4,
   .horizontal 3 3 3 4,
   .horizontal 3 3 4 4,
   .choice 4 3,
   .vertical 4 3 0 1,
   .vertical 4 3 0 2,
   .vertical 4 3 1 0,
   .vertical 4 3 1 1,
   .vertical 4 3 1 2,
   .vertical 4 3 2 0,
   .vertical 4 3 2 1,
   .vertical 4 3 2 2,
   .choice 1 4,
   .horizontal 1 4 0 0,
   .vertical 1 4 0 0,
   .vertical 1 4 1 0,
   .horizontal 1 4 1 1,
   .horizontal 1 4 2 1,
   .horizontal 1 4 3 0,
   .horizontal 1 4 3 1,
   .horizontal 1 4 4 0,
   .horizontal 1 4 4 1,
   .choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 2,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .vertical 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .vertical 2 4 2 0,
   .horizontal 2 4 2 1,
   .vertical 2 4 2 1,
   .horizontal 2 4 2 2,
   .vertical 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .horizontal 3 4 0 0,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 0 2,
   .horizontal 3 4 0 3,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .horizontal 3 4 1 1,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .vertical 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .vertical 3 4 2 0,
   .horizontal 3 4 2 1,
   .vertical 3 4 2 1,
   .horizontal 3 4 2 2,
   .vertical 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .vertical 4 4 0 1,
   .vertical 4 4 0 2,
   .vertical 4 4 1 0,
   .vertical 4 4 1 2,
   .vertical 4 4 2 0,
   .vertical 4 4 2 1,
   .vertical 4 4 2 2,
   .choice 1 5,
   .horizontal 1 5 1 1,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 1,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 1,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 1,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 2,
   .horizontal 2 5 2 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 0 0,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩,
   .exclude 1028 1028 ⟨2,2,60⟩,
   .exclude 1028 4097 ⟨2,1,10⟩,
   .exclude 1062 2177 ⟨2,2,27⟩]

theorem inputs55_valid : (inputs55.all (Input.valid 1062 5 6))=true := by decide +kernel

def formula55 : Sat.Fmla := inputs55.map (Input.clause 5)

five_tile_certificate 55
  (include_str "Certificates/FiveTiles/55.cnf")
  (include_str "Certificates/FiveTiles/55.lrat")

def checked55 : CheckedCase := ⟨1062, plane_of_inputs inputs55 inputs55_valid case55_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs56 : List Input :=
  [.choice 1 5,
   .horizontal 1 5 0 1,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 1,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 1,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 1,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 1,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 0 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs56_valid : (inputs56.all (Input.valid 1064 5 6))=true := by decide +kernel

def formula56 : Sat.Fmla := inputs56.map (Input.clause 5)

five_tile_certificate 56
  (include_str "Certificates/FiveTiles/56.cnf")
  (include_str "Certificates/FiveTiles/56.lrat")

def checked56 : CheckedCase := ⟨1064, plane_of_inputs inputs56 inputs56_valid case56_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs57 : List Input :=
  [.choice 1 4,
   .horizontal 1 4 0 2,
   .horizontal 1 4 1 2,
   .horizontal 1 4 2 2,
   .horizontal 1 4 3 2,
   .horizontal 1 4 4 2,
   .choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 2,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 1 5,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 2,
   .horizontal 2 5 0 4,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 2,
   .horizontal 2 5 1 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .horizontal 2 5 4 4,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs57_valid : (inputs57.all (Input.valid 1066 5 6))=true := by decide +kernel

def formula57 : Sat.Fmla := inputs57.map (Input.clause 5)

five_tile_certificate 57
  (include_str "Certificates/FiveTiles/57.cnf")
  (include_str "Certificates/FiveTiles/57.lrat")

def checked57 : CheckedCase := ⟨1066, plane_of_inputs inputs57 inputs57_valid case57_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs58 : List Input :=
  [.rectangular 0 1 0 2,
   .rectangular 0 1 1 0,
   .rectangular 0 2 0 1,
   .rectangular 0 2 1 2,
   .rectangular 1 0 0 2,
   .rectangular 2 0 0 1,
   .choice 1 3,
   .horizontal 1 3 0 0,
   .vertical 1 3 0 0,
   .vertical 1 3 0 1,
   .vertical 1 3 0 2,
   .horizontal 1 3 0 4,
   .vertical 1 3 1 0,
   .horizontal 1 3 1 1,
   .vertical 1 3 1 1,
   .horizontal 1 3 1 2,
   .vertical 1 3 1 2,
   .horizontal 1 3 1 4,
   .vertical 1 3 2 0,
   .horizontal 1 3 2 1,
   .vertical 1 3 2 1,
   .horizontal 1 3 2 2,
   .vertical 1 3 2 2,
   .horizontal 1 3 2 4,
   .horizontal 1 3 3 0,
   .horizontal 1 3 3 1,
   .horizontal 1 3 3 2,
   .horizontal 1 3 3 4,
   .horizontal 1 3 4 0,
   .horizontal 1 3 4 1,
   .horizontal 1 3 4 2,
   .horizontal 1 3 4 4,
   .choice 2 3,
   .horizontal 2 3 0 0,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 0 2,
   .horizontal 2 3 0 4,
   .vertical 2 3 1 0,
   .horizontal 2 3 1 1,
   .vertical 2 3 1 1,
   .horizontal 2 3 1 2,
   .vertical 2 3 1 2,
   .horizontal 2 3 1 4,
   .vertical 2 3 2 0,
   .horizontal 2 3 2 1,
   .vertical 2 3 2 1,
   .horizontal 2 3 2 2,
   .vertical 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 0,
   .horizontal 2 3 3 1,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 1,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .vertical 3 3 1 2,
   .horizontal 3 3 1 4,
   .vertical 3 3 2 1,
   .vertical 3 3 2 2,
   .horizontal 3 3 2 4,
   .horizontal 3 3 3 0,
   .horizontal 3 3 3 1,
   .horizontal 3 3 3 2,
   .horizontal 3 3 3 3,
   .horizontal 3 3 3 4,
   .horizontal 3 3 4 4,
   .choice 4 3,
   .vertical 4 3 2 0,
   .choice 0 4,
   .vertical 0 4 0 0,
   .vertical 0 4 0 2,
   .horizontal 0 4 0 4,
   .horizontal 0 4 1 1,
   .horizontal 0 4 1 4,
   .horizontal 0 4 2 1,
   .horizontal 0 4 2 4,
   .horizontal 0 4 3 1,
   .horizontal 0 4 3 4,
   .horizontal 0 4 4 1,
   .horizontal 0 4 4 4,
   .choice 1 4,
   .horizontal 1 4 0 0,
   .vertical 1 4 0 1,
   .vertical 1 4 0 2,
   .horizontal 1 4 0 4,
   .vertical 1 4 1 0,
   .horizontal 1 4 1 1,
   .vertical 1 4 1 1,
   .horizontal 1 4 1 2,
   .vertical 1 4 1 2,
   .horizontal 1 4 1 4,
   .vertical 1 4 2 0,
   .horizontal 1 4 2 1,
   .vertical 1 4 2 1,
   .horizontal 1 4 2 2,
   .vertical 1 4 2 2,
   .horizontal 1 4 2 3,
   .horizontal 1 4 2 4,
   .horizontal 1 4 3 0,
   .horizontal 1 4 3 1,
   .horizontal 1 4 3 2,
   .horizontal 1 4 3 3,
   .horizontal 1 4 3 4,
   .horizontal 1 4 4 0,
   .horizontal 1 4 4 1,
   .horizontal 1 4 4 2,
   .choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .vertical 2 4 0 2,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .vertical 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .vertical 2 4 2 0,
   .horizontal 2 4 2 1,
   .vertical 2 4 2 1,
   .horizontal 2 4 2 2,
   .vertical 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 0,
   .horizontal 3 4 1 1,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .vertical 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .vertical 3 4 2 0,
   .vertical 3 4 2 1,
   .vertical 3 4 2 2,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 0 5,
   .horizontal 0 5 0 4,
   .horizontal 0 5 1 1,
   .horizontal 0 5 1 2,
   .horizontal 0 5 1 4,
   .horizontal 0 5 2 2,
   .horizontal 0 5 2 4,
   .horizontal 0 5 3 1,
   .horizontal 0 5 3 2,
   .horizontal 0 5 3 4,
   .horizontal 0 5 4 1,
   .horizontal 0 5 4 2,
   .horizontal 0 5 4 4,
   .choice 1 5,
   .horizontal 1 5 0 0,
   .horizontal 1 5 0 4,
   .horizontal 1 5 1 1,
   .horizontal 1 5 1 2,
   .horizontal 1 5 1 3,
   .horizontal 1 5 1 4,
   .horizontal 1 5 2 1,
   .horizontal 1 5 2 2,
   .horizontal 1 5 2 3,
   .horizontal 1 5 2 4,
   .horizontal 1 5 3 0,
   .horizontal 1 5 3 1,
   .horizontal 1 5 3 2,
   .horizontal 1 5 3 3,
   .horizontal 1 5 3 4,
   .horizontal 1 5 4 1,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 4,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 2,
   .horizontal 2 5 1 4,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 2 4,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 3 4,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩,
   .exclude 1028 1028 ⟨2,2,60⟩,
   .exclude 1028 4097 ⟨2,1,10⟩,
   .exclude 1062 2177 ⟨2,2,27⟩]

theorem inputs58_valid : (inputs58.all (Input.valid 1070 5 6))=true := by decide +kernel

def formula58 : Sat.Fmla := inputs58.map (Input.clause 5)

five_tile_certificate 58
  (include_str "Certificates/FiveTiles/58.cnf")
  (include_str "Certificates/FiveTiles/58.lrat")

def checked58 : CheckedCase := ⟨1070, plane_of_inputs inputs58 inputs58_valid case58_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs59 : List Input :=
  [.choice 1 5,
   .horizontal 1 5 0 1,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 1,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 1,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 1,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 1,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 0 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5]

theorem inputs59_valid : (inputs59.all (Input.valid 1080 5 6))=true := by decide +kernel

def formula59 : Sat.Fmla := inputs59.map (Input.clause 5)

five_tile_certificate 59
  (include_str "Certificates/FiveTiles/59.cnf")
  (include_str "Certificates/FiveTiles/59.lrat")

def checked59 : CheckedCase := ⟨1080, plane_of_inputs inputs59 inputs59_valid case59_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs60 : List Input :=
  [.choice 1 4,
   .horizontal 1 4 0 2,
   .horizontal 1 4 1 2,
   .horizontal 1 4 2 2,
   .horizontal 1 4 3 2,
   .horizontal 1 4 4 2,
   .choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 2,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .choice 1 5,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 2,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs60_valid : (inputs60.all (Input.valid 1082 5 6))=true := by decide +kernel

def formula60 : Sat.Fmla := inputs60.map (Input.clause 5)

five_tile_certificate 60
  (include_str "Certificates/FiveTiles/60.cnf")
  (include_str "Certificates/FiveTiles/60.lrat")

def checked60 : CheckedCase := ⟨1082, plane_of_inputs inputs60 inputs60_valid case60_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs61 : List Input :=
  [.rectangular 0 1 0 1,
   .rectangular 0 1 0 2,
   .rectangular 0 1 1 0,
   .rectangular 0 2 0 1,
   .rectangular 0 2 1 2,
   .rectangular 0 2 2 0,
   .choice 1 3,
   .vertical 1 3 0 1,
   .vertical 1 3 0 2,
   .horizontal 1 3 1 1,
   .horizontal 1 3 2 1,
   .horizontal 1 3 3 1,
   .horizontal 1 3 4 1,
   .choice 2 3,
   .horizontal 2 3 0 0,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 0 2,
   .vertical 2 3 1 0,
   .horizontal 2 3 1 1,
   .vertical 2 3 1 1,
   .horizontal 2 3 1 2,
   .vertical 2 3 1 2,
   .vertical 2 3 2 0,
   .horizontal 2 3 2 1,
   .vertical 2 3 2 1,
   .horizontal 2 3 2 2,
   .vertical 2 3 2 2,
   .horizontal 2 3 3 0,
   .horizontal 2 3 3 1,
   .horizontal 2 3 3 2,
   .horizontal 2 3 4 0,
   .horizontal 2 3 4 1,
   .horizontal 2 3 4 2,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 0 2,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .vertical 3 3 1 2,
   .vertical 3 3 2 0,
   .vertical 3 3 2 1,
   .vertical 3 3 2 2,
   .horizontal 3 3 3 0,
   .horizontal 3 3 3 1,
   .horizontal 3 3 3 2,
   .horizontal 3 3 3 3,
   .horizontal 3 3 3 4,
   .horizontal 3 3 4 0,
   .horizontal 3 3 4 1,
   .horizontal 3 3 4 2,
   .horizontal 3 3 4 3,
   .horizontal 3 3 4 4,
   .choice 4 3,
   .choice 1 4,
   .horizontal 1 4 0 0,
   .vertical 1 4 0 0,
   .horizontal 1 4 1 1,
   .horizontal 1 4 2 1,
   .horizontal 1 4 3 0,
   .horizontal 1 4 3 1,
   .horizontal 1 4 4 0,
   .horizontal 1 4 4 1,
   .choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .vertical 2 4 0 2,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .vertical 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .vertical 2 4 2 0,
   .horizontal 2 4 2 1,
   .vertical 2 4 2 1,
   .horizontal 2 4 2 2,
   .vertical 2 4 2 2,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .vertical 3 4 0 0,
   .vertical 3 4 0 1,
   .vertical 3 4 0 2,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .vertical 3 4 1 2,
   .vertical 3 4 2 0,
   .horizontal 3 4 2 1,
   .vertical 3 4 2 1,
   .horizontal 3 4 2 2,
   .vertical 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 1,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 1,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .vertical 4 4 0 1,
   .choice 1 5,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 1,
   .horizontal 2 5 1 2,
   .horizontal 2 5 2 1,
   .horizontal 2 5 2 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩,
   .exclude 1028 1028 ⟨2,2,60⟩,
   .exclude 1028 4097 ⟨2,1,10⟩,
   .exclude 1062 2177 ⟨2,2,27⟩]

theorem inputs61_valid : (inputs61.all (Input.valid 1086 5 6))=true := by decide +kernel

def formula61 : Sat.Fmla := inputs61.map (Input.clause 5)

five_tile_certificate 61
  (include_str "Certificates/FiveTiles/61.cnf")
  (include_str "Certificates/FiveTiles/61.lrat")

def checked61 : CheckedCase := ⟨1086, plane_of_inputs inputs61 inputs61_valid case61_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs62 : List Input :=
  [.choice 2 3,
   .vertical 2 3 0 0,
   .vertical 2 3 0 1,
   .vertical 2 3 1 0,
   .vertical 2 3 1 1,
   .horizontal 2 3 2 2,
   .horizontal 2 3 2 3,
   .horizontal 2 3 2 4,
   .horizontal 2 3 3 2,
   .horizontal 2 3 3 3,
   .horizontal 2 3 3 4,
   .horizontal 2 3 4 2,
   .horizontal 2 3 4 3,
   .horizontal 2 3 4 4,
   .choice 3 3,
   .vertical 3 3 0 0,
   .vertical 3 3 0 1,
   .vertical 3 3 1 0,
   .vertical 3 3 1 1,
   .choice 1 4,
   .horizontal 1 4 0 2,
   .horizontal 1 4 0 3,
   .horizontal 1 4 0 4,
   .vertical 1 4 1 1,
   .horizontal 1 4 1 2,
   .horizontal 1 4 1 3,
   .horizontal 1 4 1 4,
   .horizontal 1 4 2 2,
   .horizontal 1 4 2 3,
   .horizontal 1 4 2 4,
   .horizontal 1 4 3 2,
   .horizontal 1 4 3 3,
   .horizontal 1 4 3 4,
   .horizontal 1 4 4 2,
   .horizontal 1 4 4 3,
   .horizontal 1 4 4 4,
   .choice 2 4,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 2,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .horizontal 3 4 0 1,
   .vertical 3 4 0 1,
   .horizontal 3 4 0 2,
   .horizontal 3 4 0 3,
   .horizontal 3 4 0 4,
   .horizontal 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .vertical 4 4 1 0,
   .vertical 4 4 1 1,
   .choice 1 5,
   .horizontal 1 5 0 1,
   .horizontal 1 5 2 1,
   .horizontal 1 5 3 1,
   .horizontal 1 5 4 1,
   .choice 2 5,
   .horizontal 2 5 0 1,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 2,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 1,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs62_valid : (inputs62.all (Input.valid 1089 5 6))=true := by decide +kernel

def formula62 : Sat.Fmla := inputs62.map (Input.clause 5)

five_tile_certificate 62
  (include_str "Certificates/FiveTiles/62.cnf")
  (include_str "Certificates/FiveTiles/62.lrat")

def checked62 : CheckedCase := ⟨1089, plane_of_inputs inputs62 inputs62_valid case62_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs63 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 2,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 3 2,
   .horizontal 2 4 4 2,
   .choice 3 4,
   .horizontal 3 4 0 0,
   .horizontal 3 4 0 2,
   .horizontal 3 4 0 3,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 0,
   .horizontal 3 4 3 2,
   .horizontal 3 4 3 3,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 0,
   .horizontal 3 4 4 2,
   .horizontal 3 4 4 3,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 1 1,
   .choice 0 5,
   .horizontal 0 5 0 2,
   .horizontal 0 5 1 2,
   .horizontal 0 5 2 2,
   .horizontal 0 5 3 2,
   .horizontal 0 5 4 2,
   .choice 1 5,
   .horizontal 1 5 0 0,
   .horizontal 1 5 0 2,
   .horizontal 1 5 1 0,
   .horizontal 1 5 1 2,
   .horizontal 1 5 2 2,
   .horizontal 1 5 3 0,
   .horizontal 1 5 3 2,
   .horizontal 1 5 4 0,
   .horizontal 1 5 4 2,
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 2,
   .horizontal 2 5 1 0,
   .horizontal 2 5 1 2,
   .horizontal 2 5 2 2,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 3 2,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .horizontal 2 5 4 2,
   .choice 3 5,
   .horizontal 3 5 0 0,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 2,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 2,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 0,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs63_valid : (inputs63.all (Input.valid 1090 5 6))=true := by decide +kernel

def formula63 : Sat.Fmla := inputs63.map (Input.clause 5)

five_tile_certificate 63
  (include_str "Certificates/FiveTiles/63.cnf")
  (include_str "Certificates/FiveTiles/63.lrat")

def checked63 : CheckedCase := ⟨1090, plane_of_inputs inputs63 inputs63_valid case63_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile

def caseBlock1 : List CheckedCase := [Cases.checked32, Cases.checked33, Cases.checked34, Cases.checked35, Cases.checked36, Cases.checked37, Cases.checked38, Cases.checked39, Cases.checked40, Cases.checked41, Cases.checked42, Cases.checked43, Cases.checked44, Cases.checked45, Cases.checked46, Cases.checked47, Cases.checked48, Cases.checked49, Cases.checked50, Cases.checked51, Cases.checked52, Cases.checked53, Cases.checked54, Cases.checked55, Cases.checked56, Cases.checked57, Cases.checked58, Cases.checked59, Cases.checked60, Cases.checked61, Cases.checked62, Cases.checked63]

end TranslationTiling.Compiler.FiveTile
