import TranslationTiling.Compiler.FiveTileCertificate

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs0 : List Input :=
  [.choice 3 5,
   .horizontal 3 5 0 0,
   .horizontal 3 5 0 1,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs0_valid : (inputs0.all (Input.valid 0 5 6))=true := by decide +kernel

def formula0 : Sat.Fmla := inputs0.map (Input.clause 5)

five_tile_certificate 0
  (include_str "Certificates/FiveTiles/0.cnf")
  (include_str "Certificates/FiveTiles/0.lrat")

def checked0 : CheckedCase := ⟨0, plane_of_inputs inputs0 inputs0_valid case0_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs1 : List Input :=
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
   .choice 3 5,
   .horizontal 3 5 0 1,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs1_valid : (inputs1.all (Input.valid 1 5 6))=true := by decide +kernel

def formula1 : Sat.Fmla := inputs1.map (Input.clause 5)

five_tile_certificate 1
  (include_str "Certificates/FiveTiles/1.cnf")
  (include_str "Certificates/FiveTiles/1.lrat")

def checked1 : CheckedCase := ⟨1, plane_of_inputs inputs1 inputs1_valid case1_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs2 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs2_valid : (inputs2.all (Input.valid 2 5 6))=true := by decide +kernel

def formula2 : Sat.Fmla := inputs2.map (Input.clause 5)

five_tile_certificate 2
  (include_str "Certificates/FiveTiles/2.cnf")
  (include_str "Certificates/FiveTiles/2.lrat")

def checked2 : CheckedCase := ⟨2, plane_of_inputs inputs2 inputs2_valid case2_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs3 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs3_valid : (inputs3.all (Input.valid 3 5 6))=true := by decide +kernel

def formula3 : Sat.Fmla := inputs3.map (Input.clause 5)

five_tile_certificate 3
  (include_str "Certificates/FiveTiles/3.cnf")
  (include_str "Certificates/FiveTiles/3.lrat")

def checked3 : CheckedCase := ⟨3, plane_of_inputs inputs3 inputs3_valid case3_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs4 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs4_valid : (inputs4.all (Input.valid 6 5 6))=true := by decide +kernel

def formula4 : Sat.Fmla := inputs4.map (Input.clause 5)

five_tile_certificate 4
  (include_str "Certificates/FiveTiles/4.cnf")
  (include_str "Certificates/FiveTiles/4.lrat")

def checked4 : CheckedCase := ⟨6, plane_of_inputs inputs4 inputs4_valid case4_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs5 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs5_valid : (inputs5.all (Input.valid 7 5 6))=true := by decide +kernel

def formula5 : Sat.Fmla := inputs5.map (Input.clause 5)

five_tile_certificate 5
  (include_str "Certificates/FiveTiles/5.cnf")
  (include_str "Certificates/FiveTiles/5.lrat")

def checked5 : CheckedCase := ⟨7, plane_of_inputs inputs5 inputs5_valid case5_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs6 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs6_valid : (inputs6.all (Input.valid 14 5 6))=true := by decide +kernel

def formula6 : Sat.Fmla := inputs6.map (Input.clause 5)

five_tile_certificate 6
  (include_str "Certificates/FiveTiles/6.cnf")
  (include_str "Certificates/FiveTiles/6.lrat")

def checked6 : CheckedCase := ⟨14, plane_of_inputs inputs6 inputs6_valid case6_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs7 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs7_valid : (inputs7.all (Input.valid 15 5 6))=true := by decide +kernel

def formula7 : Sat.Fmla := inputs7.map (Input.clause 5)

five_tile_certificate 7
  (include_str "Certificates/FiveTiles/7.cnf")
  (include_str "Certificates/FiveTiles/7.lrat")

def checked7 : CheckedCase := ⟨15, plane_of_inputs inputs7 inputs7_valid case7_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs8 : List Input :=
  [.choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs8_valid : (inputs8.all (Input.valid 30 5 6))=true := by decide +kernel

def formula8 : Sat.Fmla := inputs8.map (Input.clause 5)

five_tile_certificate 8
  (include_str "Certificates/FiveTiles/8.cnf")
  (include_str "Certificates/FiveTiles/8.lrat")

def checked8 : CheckedCase := ⟨30, plane_of_inputs inputs8 inputs8_valid case8_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs9 : List Input :=
  [.choice 2 4,
   .vertical 2 4 0 0,
   .horizontal 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
   .horizontal 2 4 2 1,
   .horizontal 2 4 2 2,
   .horizontal 2 4 2 3,
   .horizontal 2 4 2 4,
   .horizontal 2 4 3 1,
   .horizontal 2 4 3 2,
   .horizontal 2 4 3 3,
   .horizontal 2 4 3 4,
   .horizontal 2 4 4 1,
   .horizontal 2 4 4 2,
   .horizontal 2 4 4 3,
   .horizontal 2 4 4 4,
   .choice 3 4,
   .vertical 3 4 0 0,
   .choice 2 5,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 3 0,
   .horizontal 2 5 4 0,
   .choice 3 5,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs9_valid : (inputs9.all (Input.valid 31 5 6))=true := by decide +kernel

def formula9 : Sat.Fmla := inputs9.map (Input.clause 5)

five_tile_certificate 9
  (include_str "Certificates/FiveTiles/9.cnf")
  (include_str "Certificates/FiveTiles/9.lrat")

def checked9 : CheckedCase := ⟨31, plane_of_inputs inputs9 inputs9_valid case9_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs10 : List Input :=
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
   .horizontal 2 5 1 1,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 1,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs10_valid : (inputs10.all (Input.valid 33 5 6))=true := by decide +kernel

def formula10 : Sat.Fmla := inputs10.map (Input.clause 5)

five_tile_certificate 10
  (include_str "Certificates/FiveTiles/10.cnf")
  (include_str "Certificates/FiveTiles/10.lrat")

def checked10 : CheckedCase := ⟨33, plane_of_inputs inputs10 inputs10_valid case10_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs11 : List Input :=
  [.choice 3 4,
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
   .vertical 4 4 0 0,
   .vertical 4 4 0 1,
   .vertical 4 4 1 0,
   .vertical 4 4 1 1,
   .choice 3 5,
   .horizontal 3 5 0 0,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs11_valid : (inputs11.all (Input.valid 34 5 6))=true := by decide +kernel

def formula11 : Sat.Fmla := inputs11.map (Input.clause 5)

five_tile_certificate 11
  (include_str "Certificates/FiveTiles/11.cnf")
  (include_str "Certificates/FiveTiles/11.lrat")

def checked11 : CheckedCase := ⟨34, plane_of_inputs inputs11 inputs11_valid case11_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs12 : List Input :=
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
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs12_valid : (inputs12.all (Input.valid 36 5 6))=true := by decide +kernel

def formula12 : Sat.Fmla := inputs12.map (Input.clause 5)

five_tile_certificate 12
  (include_str "Certificates/FiveTiles/12.cnf")
  (include_str "Certificates/FiveTiles/12.lrat")

def checked12 : CheckedCase := ⟨36, plane_of_inputs inputs12 inputs12_valid case12_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs13 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 0 0,
   .vertical 2 4 0 1,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .horizontal 2 4 1 1,
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
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 3,
   .horizontal 2 5 0 4,
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
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 34 65 ⟨2,1,1⟩]

theorem inputs13_valid : (inputs13.all (Input.valid 38 5 6))=true := by decide +kernel

def formula13 : Sat.Fmla := inputs13.map (Input.clause 5)

five_tile_certificate 13
  (include_str "Certificates/FiveTiles/13.cnf")
  (include_str "Certificates/FiveTiles/13.lrat")

def checked13 : CheckedCase := ⟨38, plane_of_inputs inputs13 inputs13_valid case13_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs14 : List Input :=
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
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs14_valid : (inputs14.all (Input.valid 44 5 6))=true := by decide +kernel

def formula14 : Sat.Fmla := inputs14.map (Input.clause 5)

five_tile_certificate 14
  (include_str "Certificates/FiveTiles/14.cnf")
  (include_str "Certificates/FiveTiles/14.lrat")

def checked14 : CheckedCase := ⟨44, plane_of_inputs inputs14 inputs14_valid case14_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs15 : List Input :=
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

theorem inputs15_valid : (inputs15.all (Input.valid 46 5 6))=true := by decide +kernel

def formula15 : Sat.Fmla := inputs15.map (Input.clause 5)

five_tile_certificate 15
  (include_str "Certificates/FiveTiles/15.cnf")
  (include_str "Certificates/FiveTiles/15.lrat")

def checked15 : CheckedCase := ⟨46, plane_of_inputs inputs15 inputs15_valid case15_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs16 : List Input :=
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
   .horizontal 3 5 1 1,
   .horizontal 3 5 1 2,
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

theorem inputs16_valid : (inputs16.all (Input.valid 60 5 6))=true := by decide +kernel

def formula16 : Sat.Fmla := inputs16.map (Input.clause 5)

five_tile_certificate 16
  (include_str "Certificates/FiveTiles/16.cnf")
  (include_str "Certificates/FiveTiles/16.lrat")

def checked16 : CheckedCase := ⟨60, plane_of_inputs inputs16 inputs16_valid case16_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs17 : List Input :=
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

theorem inputs17_valid : (inputs17.all (Input.valid 62 5 6))=true := by decide +kernel

def formula17 : Sat.Fmla := inputs17.map (Input.clause 5)

five_tile_certificate 17
  (include_str "Certificates/FiveTiles/17.cnf")
  (include_str "Certificates/FiveTiles/17.lrat")

def checked17 : CheckedCase := ⟨62, plane_of_inputs inputs17 inputs17_valid case17_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs18 : List Input :=
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
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 2,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
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

theorem inputs18_valid : (inputs18.all (Input.valid 65 5 6))=true := by decide +kernel

def formula18 : Sat.Fmla := inputs18.map (Input.clause 5)

five_tile_certificate 18
  (include_str "Certificates/FiveTiles/18.cnf")
  (include_str "Certificates/FiveTiles/18.lrat")

def checked18 : CheckedCase := ⟨65, plane_of_inputs inputs18 inputs18_valid case18_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs19 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 3 0,
   .horizontal 2 4 4 0,
   .choice 3 4,
   .horizontal 3 4 0 3,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
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
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 2,
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
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs19_valid : (inputs19.all (Input.valid 68 5 6))=true := by decide +kernel

def formula19 : Sat.Fmla := inputs19.map (Input.clause 5)

five_tile_certificate 19
  (include_str "Certificates/FiveTiles/19.cnf")
  (include_str "Certificates/FiveTiles/19.lrat")

def checked19 : CheckedCase := ⟨68, plane_of_inputs inputs19 inputs19_valid case19_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs20 : List Input :=
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
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .horizontal 2 4 1 0,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
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
   .horizontal 3 4 1 0,
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 1,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
   .horizontal 3 4 2 4,
   .horizontal 3 4 3 4,
   .horizontal 3 4 4 4,
   .choice 4 4,
   .vertical 4 4 1 0,
   .vertical 4 4 1 1,
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
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 3,
   .horizontal 3 5 1 4,
   .horizontal 3 5 2 3,
   .horizontal 3 5 2 4,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 2,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs20_valid : (inputs20.all (Input.valid 69 5 6))=true := by decide +kernel

def formula20 : Sat.Fmla := inputs20.map (Input.clause 5)

five_tile_certificate 20
  (include_str "Certificates/FiveTiles/20.cnf")
  (include_str "Certificates/FiveTiles/20.lrat")

def checked20 : CheckedCase := ⟨69, plane_of_inputs inputs20 inputs20_valid case20_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs21 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 3 0,
   .horizontal 2 4 4 0,
   .choice 3 4,
   .horizontal 3 4 0 4,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
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
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 2,
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
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs21_valid : (inputs21.all (Input.valid 76 5 6))=true := by decide +kernel

def formula21 : Sat.Fmla := inputs21.map (Input.clause 5)

five_tile_certificate 21
  (include_str "Certificates/FiveTiles/21.cnf")
  (include_str "Certificates/FiveTiles/21.lrat")

def checked21 : CheckedCase := ⟨76, plane_of_inputs inputs21 inputs21_valid case21_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs22 : List Input :=
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
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
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

theorem inputs22_valid : (inputs22.all (Input.valid 77 5 6))=true := by decide +kernel

def formula22 : Sat.Fmla := inputs22.map (Input.clause 5)

five_tile_certificate 22
  (include_str "Certificates/FiveTiles/22.cnf")
  (include_str "Certificates/FiveTiles/22.lrat")

def checked22 : CheckedCase := ⟨77, plane_of_inputs inputs22 inputs22_valid case22_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs23 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 3 0,
   .horizontal 2 4 4 0,
   .choice 3 4,
   .vertical 3 4 1 1,
   .horizontal 3 4 2 0,
   .horizontal 3 4 2 2,
   .horizontal 3 4 2 3,
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
   .choice 2 5,
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 1 0,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 1 0,
   .horizontal 3 5 1 2,
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
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs23_valid : (inputs23.all (Input.valid 92 5 6))=true := by decide +kernel

def formula23 : Sat.Fmla := inputs23.map (Input.clause 5)

five_tile_certificate 23
  (include_str "Certificates/FiveTiles/23.cnf")
  (include_str "Certificates/FiveTiles/23.lrat")

def checked23 : CheckedCase := ⟨92, plane_of_inputs inputs23 inputs23_valid case23_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs24 : List Input :=
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
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
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

theorem inputs24_valid : (inputs24.all (Input.valid 93 5 6))=true := by decide +kernel

def formula24 : Sat.Fmla := inputs24.map (Input.clause 5)

five_tile_certificate 24
  (include_str "Certificates/FiveTiles/24.cnf")
  (include_str "Certificates/FiveTiles/24.lrat")

def checked24 : CheckedCase := ⟨93, plane_of_inputs inputs24 inputs24_valid case24_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs25 : List Input :=
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
   .horizontal 2 4 0 2,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 0,
   .vertical 2 4 1 1,
   .horizontal 2 4 1 2,
   .horizontal 2 4 1 3,
   .horizontal 2 4 1 4,
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
   .vertical 3 4 1 0,
   .vertical 3 4 1 1,
   .horizontal 3 4 1 2,
   .horizontal 3 4 1 3,
   .horizontal 3 4 1 4,
   .choice 4 4,
   .vertical 4 4 0 0,
   .vertical 4 4 0 1,
   .vertical 4 4 1 0,
   .vertical 4 4 1 1,
   .choice 2 5,
   .horizontal 2 5 2 0,
   .horizontal 2 5 2 1,
   .horizontal 2 5 3 0,
   .horizontal 2 5 3 1,
   .horizontal 2 5 4 0,
   .horizontal 2 5 4 1,
   .choice 3 5,
   .horizontal 3 5 0 2,
   .horizontal 3 5 0 3,
   .horizontal 3 5 0 4,
   .horizontal 3 5 1 2,
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
   .exclude 1 1 ⟨1,1,0⟩,
   .exclude 64 64 ⟨1,1,1⟩,
   .exclude 34 34 ⟨2,2,126⟩,
   .exclude 65 34 ⟨1,2,5⟩]

theorem inputs25_valid : (inputs25.all (Input.valid 99 5 6))=true := by decide +kernel

def formula25 : Sat.Fmla := inputs25.map (Input.clause 5)

five_tile_certificate 25
  (include_str "Certificates/FiveTiles/25.cnf")
  (include_str "Certificates/FiveTiles/25.lrat")

def checked25 : CheckedCase := ⟨99, plane_of_inputs inputs25 inputs25_valid case25_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs26 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 3,
   .horizontal 2 4 0 4,
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
   .horizontal 3 4 0 4,
   .vertical 3 4 1 1,
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
   .horizontal 2 5 0 0,
   .horizontal 2 5 0 1,
   .horizontal 2 5 0 3,
   .horizontal 2 5 0 4,
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
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs26_valid : (inputs26.all (Input.valid 100 5 6))=true := by decide +kernel

def formula26 : Sat.Fmla := inputs26.map (Input.clause 5)

five_tile_certificate 26
  (include_str "Certificates/FiveTiles/26.cnf")
  (include_str "Certificates/FiveTiles/26.lrat")

def checked26 : CheckedCase := ⟨100, plane_of_inputs inputs26 inputs26_valid case26_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs27 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .horizontal 2 4 0 1,
   .horizontal 2 4 0 4,
   .vertical 2 4 1 1,
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
   .horizontal 3 4 0 4,
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
   .horizontal 2 5 0 1,
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
   .choice 4 5,
   .exclude 64 64 ⟨1,1,1⟩]

theorem inputs27_valid : (inputs27.all (Input.valid 108 5 6))=true := by decide +kernel

def formula27 : Sat.Fmla := inputs27.map (Input.clause 5)

five_tile_certificate 27
  (include_str "Certificates/FiveTiles/27.cnf")
  (include_str "Certificates/FiveTiles/27.lrat")

def checked27 : CheckedCase := ⟨108, plane_of_inputs inputs27 inputs27_valid case27_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs28 : List Input :=
  [.choice 2 4,
   .horizontal 2 4 0 0,
   .horizontal 2 4 0 1,
   .vertical 2 4 1 1,
   .horizontal 2 4 2 0,
   .horizontal 2 4 2 1,
   .horizontal 2 4 3 0,
   .horizontal 2 4 3 1,
   .horizontal 2 4 4 0,
   .horizontal 2 4 4 1,
   .choice 3 4,
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

theorem inputs28_valid : (inputs28.all (Input.valid 124 5 6))=true := by decide +kernel

def formula28 : Sat.Fmla := inputs28.map (Input.clause 5)

five_tile_certificate 28
  (include_str "Certificates/FiveTiles/28.cnf")
  (include_str "Certificates/FiveTiles/28.lrat")

def checked28 : CheckedCase := ⟨124, plane_of_inputs inputs28 inputs28_valid case28_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs29 : List Input :=
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
   .choice 4 5]

theorem inputs29_valid : (inputs29.all (Input.valid 132 5 6))=true := by decide +kernel

def formula29 : Sat.Fmla := inputs29.map (Input.clause 5)

five_tile_certificate 29
  (include_str "Certificates/FiveTiles/29.cnf")
  (include_str "Certificates/FiveTiles/29.lrat")

def checked29 : CheckedCase := ⟨132, plane_of_inputs inputs29 inputs29_valid case29_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs30 : List Input :=
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

theorem inputs30_valid : (inputs30.all (Input.valid 136 5 6))=true := by decide +kernel

def formula30 : Sat.Fmla := inputs30.map (Input.clause 5)

five_tile_certificate 30
  (include_str "Certificates/FiveTiles/30.cnf")
  (include_str "Certificates/FiveTiles/30.lrat")

def checked30 : CheckedCase := ⟨136, plane_of_inputs inputs30 inputs30_valid case30_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile.Cases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def inputs31 : List Input :=
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
   .horizontal 2 5 0 4,
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
   .horizontal 3 5 3 0,
   .horizontal 3 5 3 1,
   .horizontal 3 5 3 2,
   .horizontal 3 5 3 3,
   .horizontal 3 5 3 4,
   .horizontal 3 5 4 1,
   .horizontal 3 5 4 3,
   .horizontal 3 5 4 4,
   .choice 4 5,
   .exclude 1 1 ⟨1,1,0⟩]

theorem inputs31_valid : (inputs31.all (Input.valid 137 5 6))=true := by decide +kernel

def formula31 : Sat.Fmla := inputs31.map (Input.clause 5)

five_tile_certificate 31
  (include_str "Certificates/FiveTiles/31.cnf")
  (include_str "Certificates/FiveTiles/31.lrat")

def checked31 : CheckedCase := ⟨137, plane_of_inputs inputs31 inputs31_valid case31_unsat (by decide) (by decide)⟩

end TranslationTiling.Compiler.FiveTile.Cases

namespace TranslationTiling.Compiler.FiveTile

def caseBlock0 : List CheckedCase := [Cases.checked0, Cases.checked1, Cases.checked2, Cases.checked3, Cases.checked4, Cases.checked5, Cases.checked6, Cases.checked7, Cases.checked8, Cases.checked9, Cases.checked10, Cases.checked11, Cases.checked12, Cases.checked13, Cases.checked14, Cases.checked15, Cases.checked16, Cases.checked17, Cases.checked18, Cases.checked19, Cases.checked20, Cases.checked21, Cases.checked22, Cases.checked23, Cases.checked24, Cases.checked25, Cases.checked26, Cases.checked27, Cases.checked28, Cases.checked29, Cases.checked30, Cases.checked31]

end TranslationTiling.Compiler.FiveTile
