import TranslationTiling.FourLayer.Rectangle
import TranslationTiling.Compiler.EffectiveConnected
import TranslationTiling.Compiler.EffectiveChoices

namespace TranslationTiling.FourLayer
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev MatchingCertificate := List ℕ×List ℕ

def Required (X : Tile 3) : Prop :=
  ∀ i∈List.range X.length, ∀ j∈List.range X.length,
    i=j ∨ X.getD i 0≠X.getD j 0

def TableValid (n : ℕ) (p : List ℕ) : Prop :=
  p.length=n ∧ (∀ i∈List.range n, p.getD i 0<n) ∧
    ∀ i∈List.range n, ∀ j∈List.range n, i=j ∨ p.getD i 0≠p.getD j 0

def MatchValid (X : Tile 3) (p : List ℕ) (k : Fin 3) : Prop :=
  ∀ i∈List.range X.length, ∀ j∈List.range X.length,
    X.getD j 0≠X.getD i 0+Pi.single k 1 ∨ p.getD j 0=i

def MatchingValid (X : Tile 3) (c : MatchingCertificate) : Prop :=
  if Required X then TableValid X.length c.1 ∧ TableValid X.length c.2 ∧
    MatchValid X c.1 0 ∧ MatchValid X c.2 1 else c=([],[])

@[fun_prop] theorem required_primrec : PrimrecPred Required := by unfold Required; fun_prop
@[fun_prop] theorem tableValid_primrec :
    PrimrecPred (fun z : ℕ×List ℕ => TableValid z.1 z.2) := by unfold TableValid; fun_prop
@[fun_prop] theorem matchValid_primrec (k : Fin 3) :
    PrimrecPred (fun z : Tile 3×List ℕ => MatchValid z.1 z.2 k) := by
  unfold MatchValid
  fun_prop

@[fun_prop] theorem matchingValid_primrec :
    PrimrecPred (fun z : Tile 3×MatchingCertificate => MatchingValid z.1 z.2) := by
  have hr : PrimrecPred (fun z : Tile 3×MatchingCertificate => Required z.1) := required_primrec.comp Primrec.fst
  have h1 : PrimrecPred (fun z : Tile 3×MatchingCertificate => TableValid z.1.length z.2.1) :=
    tableValid_primrec.comp (show Primrec (fun z : Tile 3×MatchingCertificate => (z.1.length,z.2.1)) by fun_prop)
  have h2 : PrimrecPred (fun z : Tile 3×MatchingCertificate => TableValid z.1.length z.2.2) :=
    tableValid_primrec.comp (show Primrec (fun z : Tile 3×MatchingCertificate => (z.1.length,z.2.2)) by fun_prop)
  have hx : PrimrecPred (fun z : Tile 3×MatchingCertificate => MatchValid z.1 z.2.1 0) :=
    (matchValid_primrec 0).comp (show Primrec (fun z : Tile 3×MatchingCertificate => (z.1,z.2.1)) by fun_prop)
  have hy : PrimrecPred (fun z : Tile 3×MatchingCertificate => MatchValid z.1 z.2.2 1) :=
    (matchValid_primrec 1).comp (show Primrec (fun z : Tile 3×MatchingCertificate => (z.1,z.2.2)) by fun_prop)
  have he : PrimrecPred (fun z : Tile 3×MatchingCertificate => z.2=([],[])) := by fun_prop
  apply ((hr.and (h1.and (h2.and (hx.and hy)))).or (hr.not.and he)).of_eq
  intro z
  by_cases h : Required z.1 <;> simp [MatchingValid,h]

def slots (X : Tile 3) (i : Fin X.length) : Lattice 3 := X.getD i.val 0

theorem slots_injective (X : Tile 3) (h : Required X) : Function.Injective (slots X) := by
  intro i j he
  rcases h i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt) with hh | hh
  · exact Fin.ext hh
  · exact (hh he).elim

def permTable {n : ℕ} (p : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (p i).val

@[simp] theorem permTable_getD {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (permTable p).getD i.val 0=(p i).val := by
  simp [permTable,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt]

theorem permTable_valid {n : ℕ} (p : Equiv.Perm (Fin n)) : TableValid n (permTable p) := by
  refine ⟨by simp [permTable],?_,?_⟩
  · intro i hi
    have hh := permTable_getD p ⟨i,List.mem_range.mp hi⟩
    rw [hh]
    exact (p _).isLt
  · intro i hi j hj
    by_cases h : i=j
    · exact Or.inl h
    · right
      rw [permTable_getD p ⟨i,List.mem_range.mp hi⟩,permTable_getD p ⟨j,List.mem_range.mp hj⟩]
      intro he
      exact h (congrArg Fin.val (p.injective (Fin.ext he)))

theorem exists_matchingCertificate (X : Tile 3) : ∃ c, MatchingValid X c := by
  by_cases h : Required X
  · obtain ⟨p,hp⟩ := exists_matching (slots X) (slots_injective X h) 0
    obtain ⟨q,hq⟩ := exists_matching (slots X) (slots_injective X h) 1
    refine ⟨(permTable p,permTable q),?_⟩
    simp only [MatchingValid,if_pos h]
    refine ⟨permTable_valid p,permTable_valid q,?_,?_⟩
    · intro i hi j hj
      by_cases he : X.getD j 0=X.getD i 0+Pi.single 0 1
      · right
        have hh := hp ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩ he
        rw [permTable_getD p ⟨j,List.mem_range.mp hj⟩,hh]
      · exact Or.inl he
    · intro i hi j hj
      by_cases he : X.getD j 0=X.getD i 0+Pi.single 1 1
      · right
        have hh := hq ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩ he
        rw [permTable_getD q ⟨j,List.mem_range.mp hj⟩,hh]
      · exact Or.inl he
  · exact ⟨([],[]),by simp [MatchingValid,h]⟩

def decodeMatching (n : ℕ) : MatchingCertificate := (Encodable.decode n).getD ([],[])

@[fun_prop] theorem decodeMatching_primrec : Primrec decodeMatching := by
  exact Primrec.option_getD.comp Primrec.decode (Primrec.const ([],[]))

private theorem exists_matchingCode (X : Tile 3) : ∃ n, MatchingValid X (decodeMatching n) := by
  obtain ⟨c,hc⟩ := exists_matchingCertificate X
  exact ⟨Encodable.encode c,by simpa only [decodeMatching,Encodable.encodek,Option.getD_some] using hc⟩

def matchingCode (X : Tile 3) : ℕ :=
  leastWitness (fun X n => MatchingValid X (decodeMatching n)) exists_matchingCode X

def matching (X : Tile 3) : MatchingCertificate := decodeMatching (matchingCode X)

theorem matching_computable : Computable matching := by
  have h := leastWitness_computable (fun X n => MatchingValid X (decodeMatching n))
    ((matchingValid_primrec.comp (Primrec.fst.pair (decodeMatching_primrec.comp Primrec.snd))).computablePred)
    exists_matchingCode
  exact decodeMatching_primrec.to_comp.comp h

theorem matching_spec (X : Tile 3) (h : Required X) :
    TableValid X.length (matching X).1 ∧ TableValid X.length (matching X).2 ∧
      MatchValid X (matching X).1 0 ∧ MatchValid X (matching X).2 1 := by
  have hh : MatchingValid X (matching X) := by
    unfold matching matchingCode leastWitness
    exact @Nat.find_spec _ (Classical.decPred _) (exists_matchingCode X)
  simpa only [MatchingValid,if_pos h] using hh

def tablePermutation (n : ℕ) (p : List ℕ) (h : TableValid n p) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => ⟨p.getD i.val 0,h.2.1 i.val (List.mem_range.mpr i.isLt)⟩)
    (Finite.injective_iff_bijective.mp (by
      intro i j he
      have hh := congrArg Fin.val he
      rcases h.2.2 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt) with hij | hij
      · exact Fin.ext hij
      · exact (hij hh).elim))

@[simp] theorem tablePermutation_val (n : ℕ) (p : List ℕ) (h : TableValid n p) (i : Fin n) :
    (tablePermutation n p h i).val=p.getD i.val 0 := rfl

theorem tablePermutation_match (X : Tile 3) (p : List ℕ) (h : TableValid X.length p)
    (k : Fin 3) (hk : MatchValid X p k) (i j : Fin X.length)
    (he : slots X j=slots X i+Pi.single k 1) : tablePermutation X.length p h j=i := by
  apply Fin.ext
  rcases hk i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt) with hne | heq
  · exact (hne he).elim
  · exact heq

attribute [irreducible] matching matchingCode decodeMatching

end
end TranslationTiling.FourLayer
