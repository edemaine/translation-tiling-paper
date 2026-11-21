import TranslationTiling.FiniteCompiler.PackedCompiler

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.StripLift TranslationTiling.FiniteCompiler.Effective

set_option maxRecDepth 12000
set_option maxHeartbeats 9000000
set_option exponentiation.threshold 20000

def profile15 : Profile :=
  ⟨[3, 5],
   [(83, 107), (229, 127), (103, 101), (113, 167), (241, 179), (29, 223), (79, 191), (53, 227), (197, 131), (73, 17), (109, 47), (157, 23), (199, 11), (173, 19), (13, 37), (41, 67), (31, 89), (61, 43), (193, 137), (97, 71), (149, 181), (163, 59), (2, 1229), (3, 773)],
   [[(677, 3, 4), (463, 3, 2), (701, 2, 5), (487, 2, 3)],
    [(839, 2, 3), (941, 3, 2), (991, 1, 6), (1093, 2, 5)],
    [(307, 2, 1), (509, 2, 3), (719, 6, 1), (709, 1, 6)],
    [(673, 3, 2), (1061, 2, 5), (727, 2, 3), (953, 4, 3)],
    [(599, 1, 2), (661, 2, 1), (1439, 3, 4), (1019, 2, 3)],
    [(281, 2, 1), (571, 12, 1), (397, 6, 1), (881, 15, 2)],
    [(349, 2, 1), (461, 1, 2), (823, 8, 1), (619, 3, 2)],
    [(613, 3, 2), (439, 4, 1), (757, 10, 1), (863, 12, 1)],
    [(1049, 2, 5), (983, 1, 6), (787, 2, 3), (919, 4, 1)],
    [(311, 1, 14), (367, 2, 13), (379, 1, 18), (389, 3, 10), (277, 1, 12), (647, 7, 8)],
    [(733, 5, 4), (577, 4, 3), (359, 2, 3), (421, 3, 2), (547, 2, 7), (641, 2, 9)],
    [(521, 2, 9), (617, 1, 20), (563, 3, 4), (337, 2, 1), (751, 2, 19), (383, 2, 3)],
    [(331, 1, 12), (683, 1, 44), (419, 1, 20), (353, 1, 14), (541, 2, 13), (431, 2, 3)],
    [(401, 1, 12), (211, 1, 2), (593, 2, 13), (743, 1, 30), (631, 2, 15), (557, 3, 2)],
    [(139, 5, 2), (587, 11, 12), (263, 6, 5), (317, 13, 4), (293, 14, 3), (347, 21, 2)],
    [(257, 3, 2), (313, 6, 1), (443, 1, 6), (659, 3, 8), (283, 2, 3), (499, 4, 5)],
    [(569, 4, 5), (151, 2, 1), (457, 9, 2), (271, 3, 2), (643, 15, 2), (449, 3, 4)],
    [(233, 1, 4), (251, 2, 3), (269, 3, 2), (491, 1, 10), (373, 4, 3), (409, 6, 1)],
    [(467, 1, 2), (523, 2, 1), (853, 3, 2)],
    [(239, 1, 2), (433, 3, 2), (601, 4, 3), (653, 6, 1), (691, 2, 7)],
    [(1171, 3, 4), (479, 2, 1), (809, 3, 2)],
    [(607, 3, 2), (739, 2, 7), (503, 2, 3), (829, 4, 3), (857, 2, 9)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile15Primes0 :
    ∀ q ∈ ([83, 107, 229, 127, 103, 101, 113, 167, 241, 179, 29, 223, 79, 191, 53, 227, 197, 131, 73, 17, 109, 47, 157, 23, 199] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes1 :
    ∀ q ∈ ([11, 173, 19, 13, 37, 41, 67, 31, 89, 61, 43, 193, 137, 97, 71, 149, 181, 163, 59, 2, 1229, 3, 773, 677, 463] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes2 :
    ∀ q ∈ ([701, 487, 839, 941, 991, 1093, 307, 509, 719, 709, 673, 1061, 727, 953, 599, 661, 1439, 1019, 281, 571, 397, 881, 349, 461, 823] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes3 :
    ∀ q ∈ ([619, 613, 439, 757, 863, 1049, 983, 787, 919, 311, 367, 379, 389, 277, 647, 733, 577, 359, 421, 547, 641, 521, 617, 563, 337] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes4 :
    ∀ q ∈ ([751, 383, 331, 683, 419, 353, 541, 431, 401, 211, 593, 743, 631, 557, 139, 587, 263, 317, 293, 347, 257, 313, 443, 659, 283] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes5 :
    ∀ q ∈ ([499, 569, 151, 457, 271, 643, 449, 233, 251, 269, 491, 373, 409, 467, 523, 853, 239, 433, 601, 653, 691, 1171, 479, 809, 607] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile15Primes6 :
    ∀ q ∈ ([739, 503, 829, 857, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile15_valid : Valid profile15 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([83, 107, 229, 127, 103, 101, 113, 167, 241, 179, 29, 223, 79, 191, 53, 227, 197, 131, 73, 17, 109, 47, 157, 23, 199] ++ [11, 173, 19, 13, 37, 41, 67, 31, 89, 61, 43, 193, 137, 97, 71, 149, 181, 163, 59, 2, 1229, 3, 773, 677, 463] ++ [701, 487, 839, 941, 991, 1093, 307, 509, 719, 709, 673, 1061, 727, 953, 599, 661, 1439, 1019, 281, 571, 397, 881, 349, 461, 823] ++ [619, 613, 439, 757, 863, 1049, 983, 787, 919, 311, 367, 379, 389, 277, 647, 733, 577, 359, 421, 547, 641, 521, 617, 563, 337] ++ [751, 383, 331, 683, 419, 353, 541, 431, 401, 211, 593, 743, 631, 557, 139, 587, 263, 317, 293, 347, 257, 313, 443, 659, 283] ++ [499, 569, 151, 457, 271, 643, 449, 233, 251, 269, 491, 373, 409, 467, 523, 853, 239, 433, 601, 653, 691, 1171, 479, 809, 607] ++ [739, 503, 829, 857, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨profile15Primes0, profile15Primes1⟩, profile15Primes2⟩, profile15Primes3⟩, profile15Primes4⟩, profile15Primes5⟩, profile15Primes6⟩

theorem profile15_cap : profile15.cap ≤ 2^2438 := by
  have hr : profile15.inputOrder = 529929043366908780882054059643635339990099029609758601688882858087607480331865375507049568456583074252111947825995564804360920201809440988782547878828984606108478722273437680162293480279948473875759711064264581065383175071485624946686968158973224739717940865539622939092676247143910246594956711 := by decide +kernel
  have hj : profile15.mass = 18293588383630919816344252256927471837518589711339349612919611230143447938772579905822591020226172091435196546081995334758017097643192259479600162169483330610481283459762104058886424829181259319942566403331431479821758024378255474493251953194433191214199053980964680745370461960577144858562410818427496347952045703822281426385664699103405999648479632002270629653491729462970229949172075450 := by decide +kernel
  have hl : reservedCap profile15.testLimit 65536 = 244985235078 := by decide +kernel
  have h0 : profile15.radius 0 = 7485160058129869226 := by decide +kernel
  have h1 : profile15.radius 1 = 229644495296359587358 := by decide +kernel
  have h2 : profile15.radius 2 = 126694388038136438242 := by decide +kernel
  have h3 : profile15.radius 3 = 34134041983034578618 := by decide +kernel
  have h4 : profile15.radius 4 = 86135978016764291362 := by decide +kernel
  have h5 : profile15.radius 5 = 725841340504138 := by decide +kernel
  have h6 : profile15.radius 6 = 2473473664879754 := by decide +kernel
  have h7 : profile15.radius 7 = 665334554573402506 := by decide +kernel
  have h8 : profile15.radius 8 = 18219742631716016966 := by decide +kernel
  have h9 : profile15.radius 9 = 16951717829755553818 := by decide +kernel
  have h10 : profile15.radius 10 = 38493443839319114 := by decide +kernel
  have h11 : profile15.radius 11 = 0 := by decide +kernel
  have h12 : profile15.radius 12 = 0 := by decide +kernel
  have h13 : profile15.radius 13 = 0 := by decide +kernel
  have h14 : profile15.radius 14 = 6181926549649573454 := by decide +kernel
  have h15 : profile15.radius 15 = 0 := by decide +kernel
  have h16 : profile15.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile15.radius = 705221620321420449513294189 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile15.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

def checked15 : CheckedProfile :=
  ⟨profile15, 2438, profile15_valid,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, profile15_cap, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

def profile19683 : Profile :=
  ⟨[3, 3, 3, 3, 3, 3, 3, 3, 3],
   [(23, 461), (139, 269), (311, 79), (59, 271), (97, 103), (73, 449), (367, 61), (157, 149), (151, 239), (109, 43), (101, 89), (67, 31), (17, 277), (281, 13), (127, 19), (71, 29), (229, 37), (41, 11), (313, 257), (223, 137), (193, 241), (337, 263), (173, 317), (349, 113), (373, 467), (107, 179), (401, 181), (167, 251), (191, 439), (397, 83), (131, 443), (47, 211), (163, 383), (53, 353), (199, 389), (197, 233), (2, 1229), (3, 773)],
   [[(829, 16, 1), (991, 3, 2), (691, 10, 1), (1151, 30, 1)],
    [(547, 2, 1), (677, 1, 2), (1103, 6, 1), (1381, 8, 1)],
    [(859, 2, 3), (1249, 3, 4), (701, 2, 1), (1259, 1, 12)],
    [(601, 1, 2), (743, 8, 1), (719, 3, 2), (1049, 4, 3)],
    [(503, 2, 3), (509, 1, 4), (491, 4, 1), (1097, 6, 5)],
    [(1409, 7, 2), (887, 6, 1), (1033, 8, 1), (1117, 3, 2)],
    [(733, 1, 6), (1283, 2, 9), (1039, 2, 5), (1223, 3, 2)],
    [(1051, 1, 6), (1091, 6, 1), (463, 2, 1), (769, 3, 2)],
    [(541, 2, 1), (1447, 8, 1), (1019, 2, 3), (1321, 4, 3)],
    [(347, 2, 3), (479, 4, 1), (631, 5, 2), (433, 2, 5), (757, 3, 10), (499, 3, 4)],
    [(683, 5, 2), (457, 1, 4), (647, 2, 5), (659, 3, 4), (1277, 10, 3), (1063, 7, 4)],
    [(661, 2, 17), (557, 6, 5), (1031, 14, 3), (997, 1, 30), (521, 5, 6), (227, 2, 3)],
    [(571, 1, 2), (809, 15, 2), (617, 20, 1), (379, 6, 1), (911, 21, 2), (1193, 5, 4)],
    [(593, 1, 24), (359, 1, 6), (307, 1, 2), (947, 3, 8), (619, 1, 26), (853, 1, 44)],
    [(431, 1, 16), (653, 2, 21), (641, 4, 7), (907, 4, 21), (881, 2, 33), (577, 2, 17)],
    [(839, 11, 2), (941, 1, 30), (739, 10, 1), (419, 1, 12), (487, 4, 7), (613, 7, 4)],
    [(673, 1, 12), (953, 4, 1), (569, 2, 3), (643, 2, 5), (599, 1, 10), (761, 3, 2)],
    [(283, 1, 22), (293, 5, 8), (331, 7, 4), (409, 3, 26), (421, 10, 1), (523, 9, 14)],
    [(827, 1, 2), (883, 2, 1), (1453, 3, 2)],
    [(857, 2, 3), (1217, 3, 4), (1303, 4, 3)],
    [(1013, 4, 1), (1399, 6, 1), (1109, 2, 3)],
    [(863, 1, 2), (937, 2, 1), (2063, 3, 4)],
    [(1153, 3, 2), (1297, 2, 3), (1009, 4, 1)],
    [(811, 2, 1), (1499, 3, 4), (1489, 2, 7)],
    [(1213, 2, 1), (1307, 1, 2), (2053, 3, 2)],
    [(607, 4, 1), (823, 1, 4), (1181, 1, 6)],
    [(1487, 1, 6), (983, 2, 1), (2069, 2, 7)],
    [(919, 4, 1), (1087, 2, 3), (1171, 1, 4)],
    [(1451, 3, 2), (821, 2, 1), (1069, 1, 2)],
    [(877, 2, 1), (563, 1, 2), (1061, 1, 8)],
    [(1753, 10, 1), (967, 4, 1), (1279, 3, 2)],
    [(587, 8, 1), (727, 2, 3), (751, 7, 2)],
    [(929, 1, 2), (709, 2, 1), (1361, 6, 1)],
    [(1201, 16, 1), (1289, 11, 2), (971, 5, 2)],
    [(787, 2, 1), (1583, 6, 1), (977, 1, 2)],
    [(1129, 1, 4), (1021, 4, 1), (1093, 2, 3)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile19683Primes0 :
    ∀ q ∈ ([23, 461, 139, 269, 311, 79, 59, 271, 97, 103, 73, 449, 367, 61, 157, 149, 151, 239, 109, 43, 101, 89, 67, 31, 17] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes1 :
    ∀ q ∈ ([277, 281, 13, 127, 19, 71, 29, 229, 37, 41, 11, 313, 257, 223, 137, 193, 241, 337, 263, 173, 317, 349, 113, 373, 467] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes2 :
    ∀ q ∈ ([107, 179, 401, 181, 167, 251, 191, 439, 397, 83, 131, 443, 47, 211, 163, 383, 53, 353, 199, 389, 197, 233, 2, 1229, 3] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes3 :
    ∀ q ∈ ([773, 829, 991, 691, 1151, 547, 677, 1103, 1381, 859, 1249, 701, 1259, 601, 743, 719, 1049, 503, 509, 491, 1097, 1409, 887, 1033, 1117] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes4 :
    ∀ q ∈ ([733, 1283, 1039, 1223, 1051, 1091, 463, 769, 541, 1447, 1019, 1321, 347, 479, 631, 433, 757, 499, 683, 457, 647, 659, 1277, 1063, 661] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes5 :
    ∀ q ∈ ([557, 1031, 997, 521, 227, 571, 809, 617, 379, 911, 1193, 593, 359, 307, 947, 619, 853, 431, 653, 641, 907, 881, 577, 839, 941] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes6 :
    ∀ q ∈ ([739, 419, 487, 613, 673, 953, 569, 643, 599, 761, 283, 293, 331, 409, 421, 523, 827, 883, 1453, 857, 1217, 1303, 1013, 1399, 1109] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes7 :
    ∀ q ∈ ([863, 937, 2063, 1153, 1297, 1009, 811, 1499, 1489, 1213, 1307, 2053, 607, 823, 1181, 1487, 983, 2069, 919, 1087, 1171, 1451, 821, 1069, 877] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile19683Primes8 :
    ∀ q ∈ ([563, 1061, 1753, 967, 1279, 587, 727, 751, 929, 709, 1361, 1201, 1289, 971, 787, 1583, 977, 1129, 1021, 1093, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile19683_valid : Valid profile19683 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([23, 461, 139, 269, 311, 79, 59, 271, 97, 103, 73, 449, 367, 61, 157, 149, 151, 239, 109, 43, 101, 89, 67, 31, 17] ++ [277, 281, 13, 127, 19, 71, 29, 229, 37, 41, 11, 313, 257, 223, 137, 193, 241, 337, 263, 173, 317, 349, 113, 373, 467] ++ [107, 179, 401, 181, 167, 251, 191, 439, 397, 83, 131, 443, 47, 211, 163, 383, 53, 353, 199, 389, 197, 233, 2, 1229, 3] ++ [773, 829, 991, 691, 1151, 547, 677, 1103, 1381, 859, 1249, 701, 1259, 601, 743, 719, 1049, 503, 509, 491, 1097, 1409, 887, 1033, 1117] ++ [733, 1283, 1039, 1223, 1051, 1091, 463, 769, 541, 1447, 1019, 1321, 347, 479, 631, 433, 757, 499, 683, 457, 647, 659, 1277, 1063, 661] ++ [557, 1031, 997, 521, 227, 571, 809, 617, 379, 911, 1193, 593, 359, 307, 947, 619, 853, 431, 653, 641, 907, 881, 577, 839, 941] ++ [739, 419, 487, 613, 673, 953, 569, 643, 599, 761, 283, 293, 331, 409, 421, 523, 827, 883, 1453, 857, 1217, 1303, 1013, 1399, 1109] ++ [863, 937, 2063, 1153, 1297, 1009, 811, 1499, 1489, 1213, 1307, 2053, 607, 823, 1181, 1487, 983, 2069, 919, 1087, 1171, 1451, 821, 1069, 877] ++ [563, 1061, 1753, 967, 1279, 587, 727, 751, 929, 709, 1361, 1201, 1289, 971, 787, 1583, 977, 1129, 1021, 1093, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨profile19683Primes0, profile19683Primes1⟩, profile19683Primes2⟩, profile19683Primes3⟩, profile19683Primes4⟩, profile19683Primes5⟩, profile19683Primes6⟩, profile19683Primes7⟩, profile19683Primes8⟩

theorem profile19683_cap : profile19683.cap ≤ 2^3594 := by
  have hr : profile19683.inputOrder = 676647134505443952648742423232751870548710647490018757246612538850159230966163573779534028000228884769410043912002996258231644190996010817456387724157658126654812157437595692385706566941022361828063458197927046160454589649600746827699261415492969991149400791011728765299943783641403850729040107830864312106600845563552896784148259248443637331898828010346579117226855372078173215638120963021433245743047158819784478134576532627 := by decide +kernel
  have hj : profile19683.mass = 191029489345993639728399971874034864280755210624191655479524255174835342467988029369595162619169481217013753252780777281691548272048291146312598008827411573907955163747682125395849969721215804154660214810665330919623262574161076005363169977532827835383516781404927949085092473894396425093408141543652567127670042953900505183142577400917029678229337851399030423828549552739680694395858931752009218510399111063435138082352090274626272946092163316683165924159370477566986590896694651757366418928706048168553543925840289718005040045974346894378059031134820801004900496599339798593996912867408050 := by decide +kernel
  have hl : reservedCap profile19683.testLimit 65536 = 1120450803227331701374118 := by decide +kernel
  have h0 : profile19683.radius 0 = 160806506893263226118 := by decide +kernel
  have h1 : profile19683.radius 1 = 3247821383755861209314 := by decide +kernel
  have h2 : profile19683.radius 2 = 185926181919017892602 := by decide +kernel
  have h3 : profile19683.radius 3 = 1105672506472794145078 := by decide +kernel
  have h4 : profile19683.radius 4 = 238757401970476933466 := by decide +kernel
  have h5 : profile19683.radius 5 = 94533841068233302 := by decide +kernel
  have h6 : profile19683.radius 6 = 53505512777622842 := by decide +kernel
  have h7 : profile19683.radius 7 = 401416118456393315642 := by decide +kernel
  have h8 : profile19683.radius 8 = 300528610663170637222 := by decide +kernel
  have h9 : profile19683.radius 9 = 1812633012975838015562 := by decide +kernel
  have h10 : profile19683.radius 10 = 76058479965109394 := by decide +kernel
  have h11 : profile19683.radius 11 = 0 := by decide +kernel
  have h12 : profile19683.radius 12 = 0 := by decide +kernel
  have h13 : profile19683.radius 13 = 0 := by decide +kernel
  have h14 : profile19683.radius 14 = 2229439440717530866 := by decide +kernel
  have h15 : profile19683.radius 15 = 0 := by decide +kernel
  have h16 : profile19683.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile19683.radius = 14321442594502493445227213013 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile19683.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

def checked19683 : CheckedProfile :=
  ⟨profile19683, 3594, profile19683_valid,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, profile19683_cap, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

def profile10460353203 : Profile :=
  ⟨[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   [(43, 631), (47, 619), (53, 617), (59, 613), (61, 607), (67, 601), (71, 599), (73, 593), (79, 587), (11, 683), (13, 677), (17, 673), (19, 661), (23, 659), (29, 653), (31, 647), (37, 643), (41, 641), (83, 577), (89, 571), (97, 569), (101, 563), (103, 557), (107, 547), (109, 541), (113, 523), (127, 521), (131, 509), (137, 503), (139, 499), (149, 491), (151, 487), (157, 479), (163, 467), (167, 463), (173, 461), (179, 457), (181, 449), (191, 443), (193, 439), (197, 433), (199, 431), (211, 421), (223, 419), (227, 409), (229, 401), (233, 397), (239, 389), (241, 383), (251, 379), (257, 373), (263, 367), (269, 359), (271, 353), (277, 349), (281, 347), (283, 337), (293, 331), (307, 317), (311, 313), (2, 1229), (3, 773)],
   [[(1319, 16, 1), (1907, 15, 2), (1993, 17, 2), (1663, 24, 1)],
    [(1567, 7, 2), (1951, 2, 3), (1277, 14, 1), (1747, 24, 1)],
    [(2521, 1, 4), (2029, 15, 2), (1571, 18, 1), (2347, 21, 2)],
    [(1321, 12, 1), (2111, 15, 2), (1439, 14, 1), (2383, 30, 1)],
    [(1583, 16, 1), (2309, 8, 3), (2129, 15, 2), (2617, 23, 2)],
    [(2207, 15, 2), (2341, 17, 2), (2473, 10, 3), (2339, 8, 3)],
    [(2161, 22, 1), (1877, 18, 1), (883, 4, 1), (1553, 5, 2)],
    [(1259, 1, 2), (739, 2, 1), (1697, 7, 2), (2591, 3, 4)],
    [(1061, 6, 1), (1693, 14, 1), (2551, 10, 3), (2393, 8, 3)],
    [(1123, 40, 1), (1861, 45, 2), (991, 28, 1), (947, 24, 1), (1399, 3, 2), (727, 4, 1)],
    [(1249, 44, 1), (1301, 48, 1), (1327, 50, 1), (1223, 42, 1), (1367, 1, 2), (1171, 38, 1)],
    [(2543, 110, 1), (911, 14, 1), (877, 12, 1), (2213, 51, 2), (2417, 63, 2), (809, 8, 1)],
    [(1801, 60, 1), (1307, 34, 1), (1759, 23, 2), (1607, 15, 2), (1193, 28, 1), (1721, 21, 2)],
    [(1433, 5, 2), (2269, 70, 1), (1303, 28, 1), (751, 4, 1), (1847, 23, 2), (2039, 60, 1)],
    [(769, 4, 1), (1741, 15, 2), (1291, 22, 1), (1117, 16, 1), (2437, 39, 2), (1987, 46, 1)],
    [(1511, 7, 2), (1453, 26, 1), (709, 2, 1), (1019, 12, 1), (2131, 27, 2), (2441, 37, 2)],
    [(2003, 2, 3), (1619, 9, 2), (2137, 23, 2), (1753, 30, 1), (1013, 10, 1), (2447, 14, 3)],
    [(1543, 22, 1), (1487, 5, 2), (1789, 28, 1), (1297, 16, 1), (1051, 10, 1), (1871, 30, 1)],
    [(743, 2, 1), (1901, 9, 2), (1237, 1, 2)],
    [(1409, 3, 2), (2351, 20, 1), (2477, 15, 2)],
    [(1151, 6, 1), (1733, 12, 1), (2593, 15, 2)],
    [(967, 4, 1), (2237, 11, 2), (2381, 18, 1)],
    [(1381, 8, 1), (1999, 14, 1), (1217, 1, 2)],
    [(761, 2, 1), (1201, 1, 2), (1831, 12, 1)],
    [(2503, 18, 1), (2273, 1, 4), (2281, 11, 2)],
    [(2657, 5, 4), (2557, 18, 1), (1879, 12, 1)],
    [(1283, 6, 1), (1931, 7, 2), (2579, 8, 3)],
    [(2459, 11, 2), (1033, 4, 1), (2081, 12, 1)],
    [(1873, 10, 1), (2239, 9, 2), (1783, 2, 3)],
    [(1889, 10, 1), (2609, 8, 3), (2053, 4, 3)],
    [(2411, 3, 4), (2069, 4, 3), (1087, 4, 1)],
    [(1091, 4, 1), (1997, 10, 1), (2099, 1, 4)],
    [(2371, 9, 2), (1429, 3, 2), (2677, 14, 1)],
    [(1097, 1, 2), (1423, 3, 2), (2357, 3, 4)],
    [(1723, 2, 3), (1427, 3, 2), (2467, 12, 1)],
    [(1153, 4, 1), (1787, 5, 2), (2017, 1, 4)],
    [(1531, 6, 1), (1451, 3, 2), (1093, 1, 2)],
    [(811, 2, 1), (1709, 2, 3), (2621, 12, 1)],
    [(2857, 8, 3), (3109, 7, 4), (1459, 3, 2)],
    [(2089, 4, 3), (1597, 6, 1), (1949, 1, 4)],
    [(2087, 4, 3), (827, 2, 1), (1063, 1, 2)],
    [(829, 2, 1), (2819, 12, 1), (2719, 5, 4)],
    [(2531, 10, 1), (2741, 9, 2), (2953, 12, 1)],
    [(2399, 7, 2), (2203, 8, 1), (2791, 5, 4)],
    [(863, 2, 1), (1499, 3, 2), (2861, 9, 2)],
    [(1489, 3, 2), (859, 2, 1), (1031, 1, 2)],
    [(1657, 2, 3), (1493, 3, 2), (2287, 3, 4)],
    [(1823, 6, 1), (1973, 5, 2), (2423, 2, 5)],
    [(2539, 1, 6), (2113, 4, 3), (2311, 8, 1)],
    [(881, 2, 1), (1009, 1, 2), (2141, 4, 3)],
    [(887, 2, 1), (3407, 6, 5), (2777, 5, 4)],
    [(2153, 4, 3), (1627, 2, 3), (997, 1, 2)],
    [(2243, 3, 4), (2063, 5, 2), (2333, 2, 5)],
    [(1979, 6, 1), (977, 1, 2), (2389, 1, 6)],
    [(2083, 5, 2), (2011, 6, 1), (1601, 2, 3)],
    [(2297, 2, 5), (1669, 1, 4), (1471, 4, 1)],
    [(2251, 2, 5), (2143, 4, 3), (1523, 3, 2)],
    [(2713, 7, 2), (1579, 2, 3), (2789, 5, 4)],
    [(941, 1, 2), (2179, 4, 3), (2803, 5, 4)],
    [(1559, 3, 2), (937, 1, 2), (2801, 8, 1)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile10460353203Primes0 :
    ∀ q ∈ ([43, 631, 47, 619, 53, 617, 59, 613, 61, 607, 67, 601, 71, 599, 73, 593, 79, 587, 11, 683, 13, 677, 17, 673, 19] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes1 :
    ∀ q ∈ ([661, 23, 659, 29, 653, 31, 647, 37, 643, 41, 641, 83, 577, 89, 571, 97, 569, 101, 563, 103, 557, 107, 547, 109, 541] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes2 :
    ∀ q ∈ ([113, 523, 127, 521, 131, 509, 137, 503, 139, 499, 149, 491, 151, 487, 157, 479, 163, 467, 167, 463, 173, 461, 179, 457, 181] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes3 :
    ∀ q ∈ ([449, 191, 443, 193, 439, 197, 433, 199, 431, 211, 421, 223, 419, 227, 409, 229, 401, 233, 397, 239, 389, 241, 383, 251, 379] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes4 :
    ∀ q ∈ ([257, 373, 263, 367, 269, 359, 271, 353, 277, 349, 281, 347, 283, 337, 293, 331, 307, 317, 311, 313, 2, 1229, 3, 773, 1319] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes5 :
    ∀ q ∈ ([1907, 1993, 1663, 1567, 1951, 1277, 1747, 2521, 2029, 1571, 2347, 1321, 2111, 1439, 2383, 1583, 2309, 2129, 2617, 2207, 2341, 2473, 2339, 2161, 1877] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes6 :
    ∀ q ∈ ([883, 1553, 1259, 739, 1697, 2591, 1061, 1693, 2551, 2393, 1123, 1861, 991, 947, 1399, 727, 1249, 1301, 1327, 1223, 1367, 1171, 2543, 911, 877] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes7 :
    ∀ q ∈ ([2213, 2417, 809, 1801, 1307, 1759, 1607, 1193, 1721, 1433, 2269, 1303, 751, 1847, 2039, 769, 1741, 1291, 1117, 2437, 1987, 1511, 1453, 709, 1019] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes8 :
    ∀ q ∈ ([2131, 2441, 2003, 1619, 2137, 1753, 1013, 2447, 1543, 1487, 1789, 1297, 1051, 1871, 743, 1901, 1237, 1409, 2351, 2477, 1151, 1733, 2593, 967, 2237] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes9 :
    ∀ q ∈ ([2381, 1381, 1999, 1217, 761, 1201, 1831, 2503, 2273, 2281, 2657, 2557, 1879, 1283, 1931, 2579, 2459, 1033, 2081, 1873, 2239, 1783, 1889, 2609, 2053] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes10 :
    ∀ q ∈ ([2411, 2069, 1087, 1091, 1997, 2099, 2371, 1429, 2677, 1097, 1423, 2357, 1723, 1427, 2467, 1153, 1787, 2017, 1531, 1451, 1093, 811, 1709, 2621, 2857] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes11 :
    ∀ q ∈ ([3109, 1459, 2089, 1597, 1949, 2087, 827, 1063, 829, 2819, 2719, 2531, 2741, 2953, 2399, 2203, 2791, 863, 1499, 2861, 1489, 859, 1031, 1657, 1493] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes12 :
    ∀ q ∈ ([2287, 1823, 1973, 2423, 2539, 2113, 2311, 881, 1009, 2141, 887, 3407, 2777, 2153, 1627, 997, 2243, 2063, 2333, 1979, 977, 2389, 2083, 2011, 1601] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile10460353203Primes13 :
    ∀ q ∈ ([2297, 1669, 1471, 2251, 2143, 1523, 2713, 1579, 2789, 941, 2179, 2803, 1559, 937, 2801, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile10460353203_valid : Valid profile10460353203 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([43, 631, 47, 619, 53, 617, 59, 613, 61, 607, 67, 601, 71, 599, 73, 593, 79, 587, 11, 683, 13, 677, 17, 673, 19] ++ [661, 23, 659, 29, 653, 31, 647, 37, 643, 41, 641, 83, 577, 89, 571, 97, 569, 101, 563, 103, 557, 107, 547, 109, 541] ++ [113, 523, 127, 521, 131, 509, 137, 503, 139, 499, 149, 491, 151, 487, 157, 479, 163, 467, 167, 463, 173, 461, 179, 457, 181] ++ [449, 191, 443, 193, 439, 197, 433, 199, 431, 211, 421, 223, 419, 227, 409, 229, 401, 233, 397, 239, 389, 241, 383, 251, 379] ++ [257, 373, 263, 367, 269, 359, 271, 353, 277, 349, 281, 347, 283, 337, 293, 331, 307, 317, 311, 313, 2, 1229, 3, 773, 1319] ++ [1907, 1993, 1663, 1567, 1951, 1277, 1747, 2521, 2029, 1571, 2347, 1321, 2111, 1439, 2383, 1583, 2309, 2129, 2617, 2207, 2341, 2473, 2339, 2161, 1877] ++ [883, 1553, 1259, 739, 1697, 2591, 1061, 1693, 2551, 2393, 1123, 1861, 991, 947, 1399, 727, 1249, 1301, 1327, 1223, 1367, 1171, 2543, 911, 877] ++ [2213, 2417, 809, 1801, 1307, 1759, 1607, 1193, 1721, 1433, 2269, 1303, 751, 1847, 2039, 769, 1741, 1291, 1117, 2437, 1987, 1511, 1453, 709, 1019] ++ [2131, 2441, 2003, 1619, 2137, 1753, 1013, 2447, 1543, 1487, 1789, 1297, 1051, 1871, 743, 1901, 1237, 1409, 2351, 2477, 1151, 1733, 2593, 967, 2237] ++ [2381, 1381, 1999, 1217, 761, 1201, 1831, 2503, 2273, 2281, 2657, 2557, 1879, 1283, 1931, 2579, 2459, 1033, 2081, 1873, 2239, 1783, 1889, 2609, 2053] ++ [2411, 2069, 1087, 1091, 1997, 2099, 2371, 1429, 2677, 1097, 1423, 2357, 1723, 1427, 2467, 1153, 1787, 2017, 1531, 1451, 1093, 811, 1709, 2621, 2857] ++ [3109, 1459, 2089, 1597, 1949, 2087, 827, 1063, 829, 2819, 2719, 2531, 2741, 2953, 2399, 2203, 2791, 863, 1499, 2861, 1489, 859, 1031, 1657, 1493] ++ [2287, 1823, 1973, 2423, 2539, 2113, 2311, 881, 1009, 2141, 887, 3407, 2777, 2153, 1627, 997, 2243, 2063, 2333, 1979, 977, 2389, 2083, 2011, 1601] ++ [2297, 1669, 1471, 2251, 2143, 1523, 2713, 1579, 2789, 941, 2179, 2803, 1559, 937, 2801, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨profile10460353203Primes0, profile10460353203Primes1⟩, profile10460353203Primes2⟩, profile10460353203Primes3⟩, profile10460353203Primes4⟩, profile10460353203Primes5⟩, profile10460353203Primes6⟩, profile10460353203Primes7⟩, profile10460353203Primes8⟩, profile10460353203Primes9⟩, profile10460353203Primes10⟩, profile10460353203Primes11⟩, profile10460353203Primes12⟩, profile10460353203Primes13⟩

theorem profile10460353203_cap : profile10460353203.cap ≤ 2^5954 := by
  have hr : profile10460353203.inputOrder = 14483271100019247900990777367542792240445242544073052045925944741160077053893134895954060535683652815614161212440188592171766026954171847836562954782211783509807383767756921416262573411179928813617107772088182357158054801761927610799753387760681572979356112904096220744520145467509077807444535854505326135597939263372441518094102174319208946572662839558163025025208384362038248433473008402901051139129342863322398529100990417681270140323780810863121986612027790600796653446702418180442619288086732130025801524067754379738190954130411177832664404143811438567816678929771323117078646204284750558896502573147834086005438142412165723345155393661145639682309556204799460178067944525180926090156959829869236417 := by decide +kernel
  have hj : profile10460353203.mass = 19354693173730245314170399883379157129302989025573849110147920296450368591478450288186489812780157900436117217817166155757526289683665735413273543194700001176796037609404671426736895323578765885785315314507676221367624021649963029950562235794907692163000096282327836219901669044195873635638821872641520779098218673878709242388241375758590534070337132720198218530333764741747551970196722970086257121340285387625713580250318957520744613432297398573861851247802559908762842439717252474826301187506467098962168928032235582145323410696401678762463943594348428479201843688438845937003287399661269313470707695571976630084875361270542046274355988873021174645922677918559449085665009251383809620457251902225451576467985447339732073056534156545946888241013773307040581114241771206421703432606451501104063133729572994958788153141101013702521849044851342022989440090810874382802189051344618853556048718501761304249609470236528891501262667588326188954659838248528738359369049580176147540427032984269166504743950 := by decide +kernel
  have hl : reservedCap profile10460353203.testLimit 65536 = 183713935370948471662405571954659224146103805718 := by decide +kernel
  have h0 : profile10460353203.radius 0 = 29974039323728777440438 := by decide +kernel
  have h1 : profile10460353203.radius 1 = 74306112564268656400706 := by decide +kernel
  have h2 : profile10460353203.radius 2 = 201170779034895260426258 := by decide +kernel
  have h3 : profile10460353203.radius 3 = 343144772126642030982314 := by decide +kernel
  have h4 : profile10460353203.radius 4 = 363238945721296251590722 := by decide +kernel
  have h5 : profile10460353203.radius 5 = 2406785328390429926 := by decide +kernel
  have h6 : profile10460353203.radius 6 = 473114616657369374 := by decide +kernel
  have h7 : profile10460353203.radius 7 = 354078125509637901835178 := by decide +kernel
  have h8 : profile10460353203.radius 8 = 330976910041306873465742 := by decide +kernel
  have h9 : profile10460353203.radius 9 = 1432848731926367022788954 := by decide +kernel
  have h10 : profile10460353203.radius 10 = 1016999378301094294 := by decide +kernel
  have h11 : profile10460353203.radius 11 = 0 := by decide +kernel
  have h12 : profile10460353203.radius 12 = 0 := by decide +kernel
  have h13 : profile10460353203.radius 13 = 0 := by decide +kernel
  have h14 : profile10460353203.radius 14 = 550269696387788639709506 := by decide +kernel
  have h15 : profile10460353203.radius 15 = 0 := by decide +kernel
  have h16 : profile10460353203.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile10460353203.radius = 12078622613627905680657687901101 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile10460353203.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

def checked10460353203 : CheckedProfile :=
  ⟨profile10460353203, 5954, profile10460353203_valid,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, profile10460353203_cap, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end TranslationTiling.FiniteCompiler.Packed
