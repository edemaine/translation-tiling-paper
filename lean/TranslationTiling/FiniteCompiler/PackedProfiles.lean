import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.ReservedStripLift
import TranslationTiling.FiniteCompiler.DistinctPrimes
import Mathlib.Tactic.NormNum.Prime

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective

/-- A finite prime table for the guarded construction with mixed-radix Wang letters. -/
structure Profile where
  radices : List ℕ
  pairs : List (ℕ × ℕ)
  digits : List (List (ℕ × ℕ × ℕ))

def Profile.width (p : Profile) : ℕ := 18 + 2*p.radices.length

def Profile.arity (p : Profile) (i : ℕ) : ℕ :=
  if i < 9 then 4 else if i < 18 then 6
  else if i < p.width then p.radices.getD ((i-18) % p.radices.length) 0 else 1

def Profile.slope (p : Profile) (i : ℕ) : ℕ :=
  if i < 18 then ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ).getD i 0
  else if i < 18+p.radices.length then 0 else 2

def Profile.a (p : Profile) (i : ℕ) : ℕ := (p.pairs.getD i (0,0)).1
def Profile.b (p : Profile) (i : ℕ) : ℕ := (p.pairs.getD i (0,0)).2
def Profile.row (p : Profile) (i : ℕ) : List (ℕ × ℕ × ℕ) := p.digits.getD i []
def Profile.digit (p : Profile) (i j : ℕ) : ℕ × ℕ × ℕ := (p.row i).getD j (0,0,0)

def Profile.primes (p : Profile) : List ℕ :=
  p.pairs.flatMap (fun (a,b) => [a,b]) ++ p.digits.flatMap (fun row => row.map Prod.fst)

def Profile.r (p : Profile) (i : ℕ) : ℕ := ((p.row i).map Prod.fst).prod

def Profile.inputOrder (p : Profile) : ℕ := ((List.range (p.width+2)).map p.r).prod

def Profile.mass (p : Profile) : ℕ :=
  1225 * ((List.range (p.width+2)).map fun i => p.r i*(p.a i*p.b i)).prod

def Profile.radius (p : Profile) (s : ℕ) : ℕ :=
  (((List.range p.width).map fun i => if p.slope i = s then 2*p.r i*p.a i*p.b i else 0).foldl max
    (if s = 0 then max 35 (max
      (6*p.r p.width*(p.a p.width*p.b p.width)^2*35^3)
      (4*p.r (p.width+1)*(p.a (p.width+1)*p.b (p.width+1))^2*35^3))
    else 0))

def Profile.testLimit (p : Profile) : ℕ :=
  2313 + 72*p.radices.prod^2 + (p.width+2)^2 + 2*p.width + 8 +
    4*((List.range p.width).map p.arity).sum

def Profile.cap (p : Profile) : ℕ :=
  reservedVolumeCap 35 p.radius p.inputOrder p.mass (reservedCap p.testLimit 65536)

def Valid (p : Profile) : Prop :=
  p.pairs.length = p.width+2 ∧
  p.digits.length = p.width+2 ∧
  p.primes.Nodup ∧
  (∀ q ∈ p.primes, q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536) ∧
  (∀ i ∈ List.range (p.width+2), (p.row i).length = p.arity i ∧
    ∀ r ∈ p.row i, 0 < r.2.1 ∧ 0 < r.2.2 ∧ r.1 = r.2.1*p.a i+r.2.2*p.b i) ∧
  (∀ t ∈ List.range 2, p.a (p.width+t) = t+2 ∧
    (1225 < p.b (p.width+t) ∨
      t=1 ∧ p.b (p.width+t)%3=2 ∧ 1225<2*p.b (p.width+t)))

instance (p : Profile) : Decidable (Valid p) := by unfold Valid; infer_instance

set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 10000

def profile12 : Profile :=
  ⟨[3, 4],
   [(127, 83), (173, 73), (109, 167), (103, 257), (157, 263), (101, 79), (149, 113), (53, 223), (179, 137), (11, 29), (41, 97), (17, 211), (13, 71), (59, 37), (67, 47), (151, 19), (31, 107), (61, 23), (277, 233), (43, 139), (197, 163), (271, 89), (2, 1229), (3, 773)],
   [[(293, 1, 2), (503, 2, 3), (547, 3, 2), (337, 2, 1)],
    [(419, 2, 1), (857, 2, 7), (757, 1, 8), (911, 4, 3)],
    [(821, 6, 1), (661, 3, 2), (443, 1, 2), (719, 2, 3)],
    [(463, 2, 1), (617, 1, 2), (823, 3, 2), (977, 2, 3)],
    [(577, 2, 1), (683, 1, 2), (1103, 2, 3), (997, 3, 2)],
    [(281, 2, 1), (733, 1, 8), (461, 3, 2), (641, 4, 3)],
    [(601, 1, 4), (709, 4, 1), (827, 1, 6), (673, 3, 2)],
    [(499, 1, 2), (541, 6, 1), (859, 12, 1), (647, 8, 1)],
    [(727, 1, 4), (769, 2, 3), (853, 4, 1), (811, 3, 2)],
    [(193, 7, 4), (457, 2, 15), (131, 4, 3), (241, 14, 3), (353, 11, 8), (269, 6, 7)],
    [(317, 3, 2), (619, 8, 3), (593, 5, 4), (373, 2, 3), (563, 9, 2), (761, 2, 7)],
    [(439, 1, 2), (701, 4, 3), (347, 8, 1), (653, 26, 1), (313, 6, 1), (643, 13, 2)],
    [(607, 3, 8), (571, 33, 2), (433, 6, 5), (401, 9, 4), (331, 20, 1), (239, 2, 3)],
    [(421, 4, 5), (487, 7, 2), (739, 5, 12), (251, 3, 2), (229, 2, 3), (509, 8, 1)],
    [(349, 1, 6), (409, 4, 3), (181, 2, 1), (389, 3, 4), (677, 8, 3), (691, 4, 9)],
    [(359, 2, 3), (379, 1, 12), (587, 2, 15), (227, 1, 4), (491, 3, 2), (569, 1, 22)],
    [(659, 4, 5), (383, 2, 3), (307, 3, 2), (431, 7, 2), (479, 12, 1), (521, 3, 4)],
    [(191, 2, 3), (367, 3, 8), (283, 2, 7), (613, 1, 24), (467, 2, 15), (199, 1, 6)],
    [(743, 1, 2), (787, 2, 1), (1297, 3, 2)],
    [(397, 6, 1), (599, 1, 4), (311, 4, 1), (751, 11, 2)],
    [(557, 2, 1), (523, 1, 2), (883, 2, 3)],
    [(631, 2, 1), (449, 1, 2), (809, 2, 3), (983, 1, 8)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile12Primes0 : ∀ q ∈ ([127, 83, 173, 73, 109, 167, 103, 257, 157, 263, 101, 79, 149, 113, 53, 223, 179, 137, 11, 29, 41, 97, 17, 211, 13, 71, 59, 37, 67, 47, 151, 19] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile12Primes1 : ∀ q ∈ ([31, 107, 61, 23, 277, 233, 43, 139, 197, 163, 271, 89, 2, 1229, 3, 773, 293, 503, 547, 337, 419, 857, 757, 911, 821, 661, 443, 719, 463, 617, 823, 977] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile12Primes2 : ∀ q ∈ ([577, 683, 1103, 997, 281, 733, 461, 641, 601, 709, 827, 673, 499, 541, 859, 647, 727, 769, 853, 811, 193, 457, 131, 241, 353, 269, 317, 619, 593, 373, 563, 761] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile12Primes3 : ∀ q ∈ ([439, 701, 347, 653, 313, 643, 607, 571, 433, 401, 331, 239, 421, 487, 739, 251, 229, 509, 349, 409, 181, 389, 677, 691, 359, 379, 587, 227, 491, 569, 659, 383] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile12Primes4 : ∀ q ∈ ([307, 431, 479, 521, 191, 367, 283, 613, 467, 199, 743, 787, 1297, 397, 599, 311, 751, 557, 523, 883, 631, 449, 809, 983, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile12_valid : Valid profile12 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([127, 83, 173, 73, 109, 167, 103, 257, 157, 263, 101, 79, 149, 113, 53, 223, 179, 137, 11, 29, 41, 97, 17, 211, 13, 71, 59, 37, 67, 47, 151, 19] ++ [31, 107, 61, 23, 277, 233, 43, 139, 197, 163, 271, 89, 2, 1229, 3, 773, 293, 503, 547, 337, 419, 857, 757, 911, 821, 661, 443, 719, 463, 617, 823, 977] ++ [577, 683, 1103, 997, 281, 733, 461, 641, 601, 709, 827, 673, 499, 541, 859, 647, 727, 769, 853, 811, 193, 457, 131, 241, 353, 269, 317, 619, 593, 373, 563, 761] ++ [439, 701, 347, 653, 313, 643, 607, 571, 433, 401, 331, 239, 421, 487, 739, 251, 229, 509, 349, 409, 181, 389, 677, 691, 359, 379, 587, 227, 491, 569, 659, 383] ++ [307, 431, 479, 521, 191, 367, 283, 613, 467, 199, 743, 787, 1297, 397, 599, 311, 751, 557, 523, 883, 631, 449, 809, 983, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨profile12Primes0, profile12Primes1⟩, profile12Primes2⟩, profile12Primes3⟩, profile12Primes4⟩

theorem profile12_cap : profile12.cap ≤ 2^2392 := by
  have hr : profile12.inputOrder = 75858080942920977427789267848113073799714386557388642951215091041479765324468383777492343369392401072974302054626999379028007196637406640699844333040572599281843528556850201830331840105351252572184720284777294801818191279793623834262662606914109883398794649554303530174237997162917492963 := by decide +kernel
  have hj : profile12.mass = 6291860467726809751907001654182802398570339318028825374938161134501161347851873367814702049045985133920739371851608737677873701119342908731353665966632905278117291571838435411950349530384411383684886339271569298605204964404105063610002557471989411768496421243084055553478220588266544763660101259169389655582875228348634642705194241337378146775330158873149103297956936247430354200150 := by decide +kernel
  have hl : reservedCap profile12.testLimit 65536 = 113025506078 := by decide +kernel
  have h0 : profile12.radius 0 = 168697835914796386 := by decide +kernel
  have h1 : profile12.radius 1 = 147908139658340354434 := by decide +kernel
  have h2 : profile12.radius 2 = 100679691722652759434 := by decide +kernel
  have h3 : profile12.radius 3 = 8788498029902391814 := by decide +kernel
  have h4 : profile12.radius 4 = 19353798404135259178 := by decide +kernel
  have h5 : profile12.radius 5 = 971287300014134 := by decide +kernel
  have h6 : profile12.radius 6 = 7986122884736086 := by decide +kernel
  have h7 : profile12.radius 7 = 29610536995961131534 := by decide +kernel
  have h8 : profile12.radius 8 = 29063768085627880678 := by decide +kernel
  have h9 : profile12.radius 9 = 55290248020588348694 := by decide +kernel
  have h10 : profile12.radius 10 = 18968554199970134 := by decide +kernel
  have h11 : profile12.radius 11 = 0 := by decide +kernel
  have h12 : profile12.radius 12 = 0 := by decide +kernel
  have h13 : profile12.radius 13 = 0 := by decide +kernel
  have h14 : profile12.radius 14 = 3171056391305795074 := by decide +kernel
  have h15 : profile12.radius 15 = 0 := by decide +kernel
  have h16 : profile12.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile12.radius = 664362652028527853495879037 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile12.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

def profile36 : Profile :=
  ⟨[3, 3, 4],
   [(131, 127), (59, 193), (71, 293), (157, 61), (73, 137), (139, 67), (11, 281), (101, 47), (107, 233), (151, 29), (43, 31), (97, 83), (23, 199), (37, 197), (227, 13), (79, 19), (103, 17), (41, 113), (173, 109), (317, 179), (89, 251), (211, 149), (181, 229), (163, 53), (2, 1229), (3, 773)],
   [[(389, 2, 1), (643, 2, 3), (647, 3, 2), (1151, 2, 7)],
    [(547, 6, 1), (563, 3, 2), (1051, 8, 3), (311, 2, 1)],
    [(577, 4, 1), (941, 5, 2), (719, 6, 1), (1021, 2, 3)],
    [(401, 1, 4), (863, 2, 9), (619, 2, 5), (593, 3, 2)],
    [(283, 2, 1), (347, 1, 2), (977, 4, 5), (557, 2, 3)],
    [(541, 1, 6), (809, 1, 10), (757, 4, 3), (829, 5, 2)],
    [(683, 11, 2), (853, 52, 1), (727, 15, 2), (479, 18, 1)],
    [(491, 3, 4), (397, 3, 2), (733, 4, 7), (599, 5, 2)],
    [(661, 4, 1), (787, 3, 2), (1039, 1, 4), (1303, 10, 1)],
    [(331, 2, 1), (743, 3, 10), (383, 1, 8), (569, 3, 4), (499, 1, 12), (691, 4, 3)],
    [(191, 3, 2), (241, 2, 5), (167, 1, 4), (353, 1, 10), (601, 1, 18), (439, 3, 10)],
    [(263, 1, 2), (457, 3, 2), (277, 2, 1), (761, 1, 8), (443, 2, 3), (859, 8, 1)],
    [(421, 1, 2), (751, 24, 1), (659, 20, 1), (337, 6, 1), (521, 14, 1), (613, 18, 1)],
    [(271, 2, 1), (641, 12, 1), (419, 6, 1), (431, 1, 2), (653, 7, 2), (739, 4, 3)],
    [(409, 1, 14), (617, 1, 30), (487, 1, 20), (461, 1, 18), (701, 2, 19), (467, 2, 1)],
    [(449, 4, 7), (373, 4, 3), (433, 5, 2), (709, 2, 29), (367, 2, 11), (313, 3, 4)],
    [(239, 1, 8), (631, 2, 25), (257, 2, 3), (307, 1, 12), (463, 4, 3), (223, 2, 1)],
    [(677, 11, 2), (359, 6, 1), (349, 3, 2), (523, 10, 1), (503, 4, 3), (821, 9, 4)],
    [(827, 1, 6), (673, 2, 3), (1019, 4, 3)],
    [(1171, 2, 3), (1033, 1, 4), (1447, 4, 1)],
    [(607, 4, 1), (769, 3, 2), (947, 5, 2), (1093, 1, 4)],
    [(509, 1, 2), (571, 2, 1), (1291, 4, 3)],
    [(1049, 2, 3), (1097, 1, 4), (953, 4, 1)],
    [(811, 4, 3), (379, 2, 1), (269, 1, 2), (587, 1, 8)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile36Primes0 : ∀ q ∈ ([131, 127, 59, 193, 71, 293, 157, 61, 73, 137, 139, 67, 11, 281, 101, 47, 107, 233, 151, 29, 43, 31, 97, 83, 23, 199, 37, 197, 227, 13, 79, 19] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile36Primes1 : ∀ q ∈ ([103, 17, 41, 113, 173, 109, 317, 179, 89, 251, 211, 149, 181, 229, 163, 53, 2, 1229, 3, 773, 389, 643, 647, 1151, 547, 563, 1051, 311, 577, 941, 719, 1021] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile36Primes2 : ∀ q ∈ ([401, 863, 619, 593, 283, 347, 977, 557, 541, 809, 757, 829, 683, 853, 727, 479, 491, 397, 733, 599, 661, 787, 1039, 1303, 331, 743, 383, 569, 499, 691, 191, 241] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile36Primes3 : ∀ q ∈ ([167, 353, 601, 439, 263, 457, 277, 761, 443, 859, 421, 751, 659, 337, 521, 613, 271, 641, 419, 431, 653, 739, 409, 617, 487, 461, 701, 467, 449, 373, 433, 709] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile36Primes4 : ∀ q ∈ ([367, 313, 239, 631, 257, 307, 463, 223, 677, 359, 349, 523, 503, 821, 827, 673, 1019, 1171, 1033, 1447, 607, 769, 947, 1093, 509, 571, 1291, 1049, 1097, 953, 811, 379] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile36Primes5 : ∀ q ∈ ([269, 587, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile36_valid : Valid profile36 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([131, 127, 59, 193, 71, 293, 157, 61, 73, 137, 139, 67, 11, 281, 101, 47, 107, 233, 151, 29, 43, 31, 97, 83, 23, 199, 37, 197, 227, 13, 79, 19] ++ [103, 17, 41, 113, 173, 109, 317, 179, 89, 251, 211, 149, 181, 229, 163, 53, 2, 1229, 3, 773, 389, 643, 647, 1151, 547, 563, 1051, 311, 577, 941, 719, 1021] ++ [401, 863, 619, 593, 283, 347, 977, 557, 541, 809, 757, 829, 683, 853, 727, 479, 491, 397, 733, 599, 661, 787, 1039, 1303, 331, 743, 383, 569, 499, 691, 191, 241] ++ [167, 353, 601, 439, 263, 457, 277, 761, 443, 859, 421, 751, 659, 337, 521, 613, 271, 641, 419, 431, 653, 739, 409, 617, 487, 461, 701, 467, 449, 373, 433, 709] ++ [367, 313, 239, 631, 257, 307, 463, 223, 677, 359, 349, 523, 503, 821, 827, 673, 1019, 1171, 1033, 1447, 607, 769, 947, 1093, 509, 571, 1291, 1049, 1097, 953, 811, 379] ++ [269, 587, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨profile36Primes0, profile36Primes1⟩, profile36Primes2⟩, profile36Primes3⟩, profile36Primes4⟩, profile36Primes5⟩

theorem profile36_cap : profile36.cap ≤ 2^2573 := by
  have hr : profile36.inputOrder = 170961658372874278210244960929741787114404205646090487407544873349106342594683198628148485452465966430832058081954258438823064537714328890562239229638975695263557328765468544420555154668381743975525770014917261508809716190847499605536130229677721847166177287823134666449299751262674927432249117883361462915073 := by decide +kernel
  have hj : profile36.mass = 23272616154750428254284554047194689734313754921167200470117837206734652164917515783414155951470127639249580959284466865235151683322427800858646739128529569168929593863872361803099953600378372792805017336473797724857546147753584934084039725505762922654291095186774201352157274575697639534449805426604824693631858884072127441726826128365143936764546585911834981781985530786803381701292099977077869973872467132198450 := by decide +kernel
  have hl : reservedCap profile36.testLimit 65536 = 6746154761558 := by decide +kernel
  have h0 : profile36.radius 0 = 161849507332142644802 := by decide +kernel
  have h1 : profile36.radius 1 = 1908713405400388294 := by decide +kernel
  have h2 : profile36.radius 2 = 155243378931121485698 := by decide +kernel
  have h3 : profile36.radius 3 = 205279912641965473306 := by decide +kernel
  have h4 : profile36.radius 4 = 220685693108986454554 := by decide +kernel
  have h5 : profile36.radius 5 = 5115826360443082 := by decide +kernel
  have h6 : profile36.radius 6 = 1254205381359194 := by decide +kernel
  have h7 : profile36.radius 7 = 109464289452039029014 := by decide +kernel
  have h8 : profile36.radius 8 = 17730067706210032198 := by decide +kernel
  have h9 : profile36.radius 9 = 4302300636883839418 := by decide +kernel
  have h10 : profile36.radius 10 = 35116065424893578 := by decide +kernel
  have h11 : profile36.radius 11 = 0 := by decide +kernel
  have h12 : profile36.radius 12 = 0 := by decide +kernel
  have h13 : profile36.radius 13 = 0 := by decide +kernel
  have h14 : profile36.radius 14 = 169751519755643141438 := by decide +kernel
  have h15 : profile36.radius 15 = 0 := by decide +kernel
  have h16 : profile36.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile36.radius = 3171997273476572909007785349 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile36.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

def profile243 : Profile :=
  ⟨[3, 3, 3, 3, 3],
   [(31, 239), (29, 367), (97, 293), (71, 127), (61, 197), (151, 223), (263, 89), (227, 103), (179, 79), (23, 83), (109, 13), (113, 53), (41, 199), (47, 67), (37, 137), (163, 17), (73, 11), (193, 19), (157, 107), (229, 173), (311, 43), (257, 101), (251, 139), (131, 241), (191, 167), (331, 149), (277, 233), (59, 271), (2, 1229), (3, 773)],
   [[(509, 1, 2), (673, 14, 1), (757, 9, 2), (881, 13, 2)],
    [(599, 8, 1), (1063, 24, 1), (947, 20, 1), (541, 6, 1)],
    [(683, 1, 2), (487, 2, 1), (1069, 8, 1), (877, 3, 2)],
    [(269, 2, 1), (751, 7, 2), (467, 3, 2), (523, 2, 3)],
    [(563, 6, 1), (577, 3, 2), (929, 12, 1), (821, 7, 2)],
    [(827, 4, 1), (971, 2, 3), (1129, 6, 1), (1201, 5, 2)],
    [(619, 1, 4), (967, 3, 2), (1153, 1, 10), (1319, 4, 3)],
    [(433, 1, 2), (557, 2, 1), (887, 3, 2), (1051, 1, 8)],
    [(337, 1, 2), (853, 3, 4), (653, 1, 6), (911, 2, 7)],
    [(313, 10, 1), (461, 2, 5), (419, 11, 2), (373, 9, 2), (677, 15, 4), (857, 12, 7)],
    [(317, 1, 16), (353, 3, 2), (587, 3, 20), (379, 3, 4), (283, 2, 5), (499, 1, 30)],
    [(491, 2, 5), (823, 4, 7), (809, 2, 11), (643, 1, 10), (431, 1, 6), (1021, 2, 15)],
    [(521, 3, 2), (937, 18, 1), (281, 2, 1), (761, 4, 3), (439, 1, 2), (691, 12, 1)],
    [(839, 15, 2), (349, 6, 1), (409, 3, 4), (181, 1, 2), (463, 7, 2), (449, 1, 6)],
    [(359, 6, 1), (211, 2, 1), (659, 3, 4), (733, 5, 4), (607, 9, 2), (829, 15, 2)],
    [(727, 3, 14), (571, 1, 24), (547, 2, 13), (401, 1, 14), (941, 4, 17), (479, 2, 9)],
    [(739, 5, 34), (593, 3, 34), (647, 6, 19), (347, 4, 5), (457, 4, 15), (701, 9, 4)],
    [(307, 1, 6), (443, 2, 3), (383, 1, 10), (709, 2, 17), (617, 3, 2), (769, 3, 10)],
    [(1013, 1, 8), (421, 2, 1), (1049, 6, 1)],
    [(977, 2, 3), (631, 2, 1), (1033, 3, 2)],
    [(397, 1, 2), (1009, 2, 9), (569, 1, 6)],
    [(863, 1, 6), (661, 1, 4), (1019, 2, 5)],
    [(641, 2, 1), (1031, 3, 2), (919, 2, 3)],
    [(613, 1, 2), (503, 2, 1), (1289, 8, 1)],
    [(907, 3, 2), (859, 1, 4), (883, 2, 3)],
    [(811, 2, 1), (1109, 2, 3), (1291, 3, 2)],
    [(743, 1, 2), (787, 2, 1), (1297, 3, 2)],
    [(601, 1, 2), (719, 3, 2), (389, 2, 1)],
    [(1231, 1, 1)],
    [(797, 8, 1)]]⟩

private theorem profile243Primes0 : ∀ q ∈ ([31, 239, 29, 367, 97, 293, 71, 127, 61, 197, 151, 223, 263, 89, 227, 103, 179, 79, 23, 83, 109, 13, 113, 53, 41, 199, 47, 67, 37, 137, 163, 17] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile243Primes1 : ∀ q ∈ ([73, 11, 193, 19, 157, 107, 229, 173, 311, 43, 257, 101, 251, 139, 131, 241, 191, 167, 331, 149, 277, 233, 59, 271, 2, 1229, 3, 773, 509, 673, 757, 881] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile243Primes2 : ∀ q ∈ ([599, 1063, 947, 541, 683, 487, 1069, 877, 269, 751, 467, 523, 563, 577, 929, 821, 827, 971, 1129, 1201, 619, 967, 1153, 1319, 433, 557, 887, 1051, 337, 853, 653, 911] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile243Primes3 : ∀ q ∈ ([313, 461, 419, 373, 677, 857, 317, 353, 587, 379, 283, 499, 491, 823, 809, 643, 431, 1021, 521, 937, 281, 761, 439, 691, 839, 349, 409, 181, 463, 449, 359, 211] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile243Primes4 : ∀ q ∈ ([659, 733, 607, 829, 727, 571, 547, 401, 941, 479, 739, 593, 647, 347, 457, 701, 307, 443, 383, 709, 617, 769, 1013, 421, 1049, 977, 631, 1033, 397, 1009, 569, 863] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

private theorem profile243Primes5 : ∀ q ∈ ([661, 1019, 641, 1031, 919, 613, 503, 1289, 907, 859, 883, 811, 1109, 1291, 743, 787, 1297, 601, 719, 389, 1231, 797] : List ℕ),
    q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536 := by
  simp only [List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

theorem profile243_valid : Valid profile243 := by
  refine ⟨by decide +kernel, by decide +kernel,
    (distinctCheck_sound (seen := 0) (by decide +kernel)).1, ?_,
    by decide +kernel, by decide +kernel⟩
  change ∀ q ∈ ([31, 239, 29, 367, 97, 293, 71, 127, 61, 197, 151, 223, 263, 89, 227, 103, 179, 79, 23, 83, 109, 13, 113, 53, 41, 199, 47, 67, 37, 137, 163, 17] ++ [73, 11, 193, 19, 157, 107, 229, 173, 311, 43, 257, 101, 251, 139, 131, 241, 191, 167, 331, 149, 277, 233, 59, 271, 2, 1229, 3, 773, 509, 673, 757, 881] ++ [599, 1063, 947, 541, 683, 487, 1069, 877, 269, 751, 467, 523, 563, 577, 929, 821, 827, 971, 1129, 1201, 619, 967, 1153, 1319, 433, 557, 887, 1051, 337, 853, 653, 911] ++ [313, 461, 419, 373, 677, 857, 317, 353, 587, 379, 283, 499, 491, 823, 809, 643, 431, 1021, 521, 937, 281, 761, 439, 691, 839, 349, 409, 181, 463, 449, 359, 211] ++ [659, 733, 607, 829, 727, 571, 547, 401, 941, 479, 739, 593, 647, 347, 457, 701, 307, 443, 383, 709, 617, 769, 1013, 421, 1049, 977, 631, 1033, 397, 1009, 569, 863] ++ [661, 1019, 641, 1031, 919, 613, 503, 1289, 907, 859, 883, 811, 1109, 1291, 743, 787, 1297, 601, 719, 389, 1231, 797] : List ℕ), q.Prime ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≤ 65536
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨profile243Primes0, profile243Primes1⟩, profile243Primes2⟩, profile243Primes3⟩, profile243Primes4⟩, profile243Primes5⟩

theorem profile243_cap : profile243.cap ≤ 2^2876 := by
  have hr : profile243.inputOrder = 2497659737387961684848937432539291305067756811108920755337601161013535427259265160268358946440880411371029919106495898134566730219346297262573435021954056054337354492910443461042771276907148975616360093519127978157556382075618614193050018266220533974310910328803387531829686443790692802233110859707366015574036071350102934723673586185652396983 := by decide +kernel
  have hj : profile243.mass = 7849015182059394543871271002713466897272041461594774019424965072866171743674903302350462799441392408152148818737289320495961531446675126588835549850319590710628789002053235741704715164825533867418000740345840809850051471871854295773027622164257076413300311420911115825592005974697394268931396561346881863567760371252100718006045853834758425099655156026248652494548572342933082519497925232630173477938750750821169633894211150968855011457851671370593959596759488377350 := by decide +kernel
  have hl : reservedCap profile243.testLimit 65536 = 17383152414107078 := by decide +kernel
  have h0 : profile243.radius 0 = 49954375307673945782 := by decide +kernel
  have h1 : profile243.radius 1 = 9963182966306231194 := by decide +kernel
  have h2 : profile243.radius 2 = 1107970361020230123298 := by decide +kernel
  have h3 : profile243.radius 3 = 516746789733724351574 := by decide +kernel
  have h4 : profile243.radius 4 = 28380448800412967194 := by decide +kernel
  have h5 : profile243.radius 5 = 73328617109207378 := by decide +kernel
  have h6 : profile243.radius 6 = 42615439989752554 := by decide +kernel
  have h7 : profile243.radius 7 = 186664530209207396842 := by decide +kernel
  have h8 : profile243.radius 8 = 227454155874370711262 := by decide +kernel
  have h9 : profile243.radius 9 = 50618893348514394706 := by decide +kernel
  have h10 : profile243.radius 10 = 4836382134465766 := by decide +kernel
  have h11 : profile243.radius 11 = 0 := by decide +kernel
  have h12 : profile243.radius 12 = 0 := by decide +kernel
  have h13 : profile243.radius 13 = 0 := by decide +kernel
  have h14 : profile243.radius 14 = 128510768386145451154 := by decide +kernel
  have h15 : profile243.radius 15 = 0 := by decide +kernel
  have h16 : profile243.radius 16 = 0 := by decide +kernel
  have ha : Rails.Strips.countCapAt 35 profile243.radius = 4491393409621939086932531685 := by
    change (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).map fun i =>
      (2*Rails.Strips.radius (profile243.radius i)+1)*(2*Rails.Strips.widthAt 35 i+1)).sum = _
    norm_num [Rails.Strips.radius, Rails.Strips.widthAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  unfold Profile.cap Compiler.StripLift.reservedVolumeCap
  simp only [hr,hj,hl,ha]
  decide +kernel

end TranslationTiling.FiniteCompiler.Packed
