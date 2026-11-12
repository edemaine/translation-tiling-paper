import TranslationTiling.EuclideanMembership.IntegerTests

/-! Computable constructors for the closed polynomial constraints. -/
namespace TranslationTiling.EuclideanMembership

open Compiler.Effective

def pConst (a : ℤ) : Polynomial := [(a,[])]
def pVar (i : ℕ) : Polynomial := [(1,[i])]
def pAdd (p q : Polynomial) : Polynomial := p++q
def pNeg (p : Polynomial) : Polynomial := p.map fun t => (-t.1,t.2)
def pSub (p q : Polynomial) : Polynomial := pAdd p (pNeg q)
def pMul (p q : Polynomial) : Polynomial :=
  p.flatMap fun s => q.map fun t => (s.1*t.1,s.2++t.2)
def pSum (ps : List Polynomial) : Polynomial := ps.flatten

def fTrue : Formula := [[]]
def fFalse : Formula := []
def fLe (p : Polynomial) : Formula := [[p]]
def fEq (p q : Polynomial) : Formula := [[pSub p q,pSub q p]]
def fOr (f g : Formula) : Formula := f++g
def fAnd (f g : Formula) : Formula := f.flatMap fun c => g.map fun e => c++e

def fAll (fs : List Formula) : Formula := fs.foldr fAnd fTrue

def renamePolynomial (r : ℕ → ℕ) (p : Polynomial) : Polynomial :=
  p.map fun t => (t.1,t.2.map r)

def renameFormula (r : ℕ → ℕ) (f : Formula) : Formula :=
  f.map fun c => c.map (renamePolynomial r)

@[simp] theorem evaluate_const (a : ℤ) (x : ℕ → ℝ) : evaluate (pConst a) x=a := by
  simp [evaluate,pConst,monomial]
@[simp] theorem evaluate_var (i : ℕ) (x : ℕ → ℝ) : evaluate (pVar i) x=x i := by
  simp [evaluate,pVar,monomial]
@[simp] theorem evaluate_add (p q : Polynomial) (x : ℕ → ℝ) :
    evaluate (pAdd p q) x=evaluate p x+evaluate q x := by simp [evaluate,pAdd]
@[simp] theorem evaluate_neg (p : Polynomial) (x : ℕ → ℝ) :
    evaluate (pNeg p) x= -evaluate p x := by
  induction p with
  | nil => simp [pNeg,evaluate]
  | cons t p ih =>
    change ((-t.1 : ℤ) : ℝ)*monomial t.2 x+evaluate (pNeg p) x =
      -((t.1 : ℝ)*monomial t.2 x+evaluate p x)
    rw [ih,Int.cast_neg]
    ring
@[simp] theorem evaluate_sub (p q : Polynomial) (x : ℕ → ℝ) :
    evaluate (pSub p q) x=evaluate p x-evaluate q x := by simp [pSub,sub_eq_add_neg]
@[simp] theorem evaluate_mul (p q : Polynomial) (x : ℕ → ℝ) :
    evaluate (pMul p q) x=evaluate p x*evaluate q x := by
  induction p generalizing q with
  | nil => simp [pMul,evaluate]
  | cons s p ih =>
    have hm : evaluate (q.map fun t => (s.1*t.1,s.2++t.2)) x=
        (s.1 : ℝ)*monomial s.2 x*evaluate q x := by
      induction q with
      | nil => simp [evaluate]
      | cons t q iq =>
        simp only [List.map_cons,evaluate,List.sum_cons,Int.cast_mul]
        change (s.1 : ℝ)*(t.1 : ℝ)*(monomial (s.2++t.2) x)+
          evaluate (q.map fun t => (s.1*t.1,s.2++t.2)) x = _
        rw [iq]
        simp only [monomial,List.map_append,List.prod_append,evaluate]
        ring
    change evaluate (q.map (fun t => (s.1*t.1,s.2++t.2))++pMul p q) x = _
    rw [show evaluate (q.map (fun t => (s.1*t.1,s.2++t.2))++pMul p q) x=
      evaluate (q.map (fun t => (s.1*t.1,s.2++t.2))) x+evaluate (pMul p q) x by simp [evaluate]]
    rw [hm,ih]
    simp only [evaluate,List.map_cons,List.sum_cons]
    ring

@[simp] theorem evaluate_sum (ps : List Polynomial) (x : ℕ → ℝ) :
    evaluate (pSum ps) x=(ps.map fun p => evaluate p x).sum := by
  induction ps with
  | nil => simp [pSum,evaluate]
  | cons p ps ih => simpa [pSum,evaluate] using congrArg (evaluate p x+·) ih

@[simp] theorem holds_true (x : ℕ → ℝ) : Holds fTrue 0 x := by simp [Holds,fTrue]
@[simp] theorem holds_false (x : ℕ → ℝ) : ¬ Holds fFalse 0 x := by simp [Holds,fFalse]
@[simp] theorem holds_le (p : Polynomial) (x : ℕ → ℝ) : Holds (fLe p) 0 x ↔ evaluate p x ≤ 0 := by
  simp [Holds,fLe]
@[simp] theorem holds_eq (p q : Polynomial) (x : ℕ → ℝ) :
    Holds (fEq p q) 0 x ↔ evaluate p x=evaluate q x := by
  have hh : Holds (fEq p q) 0 x ↔
      evaluate p x-evaluate q x ≤ 0 ∧ evaluate q x-evaluate p x ≤ 0 := by
    simp [Holds,fEq,evaluate_sub]
  rw [hh]
  constructor <;> intro h
  · exact le_antisymm (sub_nonpos.mp h.1) (sub_nonpos.mp h.2)
  · simp [h]

@[simp] theorem holds_or (f g : Formula) (x : ℕ → ℝ) :
    Holds (fOr f g) 0 x ↔ Holds f 0 x ∨ Holds g 0 x := by simp [Holds,fOr,or_and_right,exists_or]
@[simp] theorem holds_and (f g : Formula) (x : ℕ → ℝ) :
    Holds (fAnd f g) 0 x ↔ Holds f 0 x ∧ Holds g 0 x := by
  simp only [Holds,fAnd,List.mem_flatMap,List.mem_map,List.forall_mem_append]
  aesop
@[simp] theorem holds_all (fs : List Formula) (x : ℕ → ℝ) :
    Holds (fAll fs) 0 x ↔ ∀ f ∈ fs, Holds f 0 x := by
  induction fs with
  | nil => simp [fAll]
  | cons f fs ih =>
    change Holds (fAnd f (fAll fs)) 0 x ↔ _
    rw [holds_and,ih]
    simp

@[simp] theorem evaluate_rename (r : ℕ → ℕ) (p : Polynomial) (x : ℕ → ℝ) :
    evaluate (renamePolynomial r p) x=evaluate p (x ∘ r) := by
  simp [evaluate,renamePolynomial,monomial,List.map_map,Function.comp_def]
@[simp] theorem holds_rename (r : ℕ → ℕ) (f : Formula) (x : ℕ → ℝ) :
    Holds (renameFormula r f) 0 x ↔ Holds f 0 (x ∘ r) := by
  simp [Holds,renameFormula,evaluate_rename]

@[fun_prop] theorem pConst_primrec : Primrec pConst := by unfold pConst; fun_prop
@[fun_prop] theorem pVar_primrec : Primrec pVar := by unfold pVar; fun_prop
@[fun_prop] theorem pAdd_primrec : Primrec (fun q : Polynomial × Polynomial => pAdd q.1 q.2) := by
  unfold pAdd; fun_prop
@[fun_prop] theorem pNeg_primrec : Primrec pNeg := by unfold pNeg; fun_prop
@[fun_prop] theorem pMul_primrec : Primrec (fun q : Polynomial × Polynomial => pMul q.1 q.2) := by
  unfold pMul; fun_prop
@[fun_prop] theorem pSum_primrec : Primrec pSum := Primrec.list_flatten

def pProd (ps : List Polynomial) : Polynomial := ps.foldr pMul (pConst 1)
def fAny (fs : List Formula) : Formula := fs.flatten

@[simp] theorem evaluate_prod (ps : List Polynomial) (x : ℕ → ℝ) :
    evaluate (pProd ps) x=(ps.map fun p => evaluate p x).prod := by
  induction ps with
  | nil => simp [pProd]
  | cons p ps ih =>
    simpa only [pProd,List.foldr_cons,evaluate_mul,List.map_cons,List.prod_cons] using (congrArg (fun t => evaluate p x * t) ih)

@[simp] theorem holds_any (fs : List Formula) (x : ℕ → ℝ) :
    Holds (fAny fs) 0 x ↔ ∃ f ∈ fs, Holds f 0 x := by
  simp only [fAny,Holds,List.mem_flatten]
  aesop

@[fun_prop] theorem pSub_primrec : Primrec (fun q : Polynomial × Polynomial => pSub q.1 q.2) := by
  unfold pSub; fun_prop
@[fun_prop] theorem pProd_primrec : Primrec pProd := by
  change Primrec (fun ps : List Polynomial => ps.foldr (fun b c => pMul b c) (pConst 1))
  apply foldList (h := fun (_ : List Polynomial) (q : Polynomial × Polynomial) => pMul q.1 q.2) <;> fun_prop
@[fun_prop] theorem fLe_primrec : Primrec fLe := by unfold fLe; fun_prop
@[fun_prop] theorem fEq_primrec : Primrec (fun q : Polynomial × Polynomial => fEq q.1 q.2) := by
  unfold fEq; fun_prop
@[fun_prop] theorem fOr_primrec : Primrec (fun q : Formula × Formula => fOr q.1 q.2) := by
  unfold fOr; fun_prop
@[fun_prop] theorem fAnd_primrec : Primrec (fun q : Formula × Formula => fAnd q.1 q.2) := by
  unfold fAnd; fun_prop
@[fun_prop] theorem fAll_primrec : Primrec fAll := by
  change Primrec (fun fs : List Formula => fs.foldr (fun b c => fAnd b c) fTrue)
  apply foldList (h := fun (_ : List Formula) (q : Formula × Formula) => fAnd q.1 q.2) <;> fun_prop
@[fun_prop] theorem fAny_primrec : Primrec fAny := Primrec.list_flatten

end TranslationTiling.EuclideanMembership
