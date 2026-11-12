import TranslationTiling.EuclideanMembership.PolynomialBounds
import TranslationTiling.Compiler.EffectiveAlphabet

/-! Finite approximation tests use integers only. Each real variable is replaced
by a point of a finite rational grid; clearing denominators makes every atomic
test a signed integer comparison. -/
namespace TranslationTiling.EuclideanMembership

open Compiler.Effective

/-- A common denominator large enough for the error of the finite family. -/
def denominator (fs : List Formula) (k : ℕ) : ℕ :=
  (k+1)*(totalWeight fs+1)

def integerGrid (D : ℕ) : List ℤ :=
  (List.range (2*D+1)).map fun n : ℕ => (n : ℤ)-(D : ℤ)

def degree (p : Polynomial) : ℕ := p.foldr (fun t n => max t.2.length n) 0

def scaledMonomial (D N : ℕ) (z : List ℤ) (t : ℤ × List ℕ) : ℤ :=
  t.1 * (t.2.map (fun i => z.getD i 0)).prod * (D^(N-t.2.length) : ℕ)

def scaledEvaluate (D N : ℕ) (z : List ℤ) (p : Polynomial) : ℤ :=
  (p.map (scaledMonomial D N z)).sum

def integerHolds (f : Formula) (k D : ℕ) (z : List ℤ) : Prop :=
  ∃ c ∈ f, ∀ p ∈ c,
    scaledEvaluate D (degree p) z p * (k+1 : ℕ) ≤ (D^degree p : ℕ)

instance (f : Formula) (k D : ℕ) (z : List ℤ) : Decidable (integerHolds f k D z) := by
  unfold integerHolds
  infer_instance

/-- An explicit finite search over rational vectors; no real-number operation
or oracle occurs in this definition. -/
def finiteTest (fs : List Formula) (k : ℕ) : Prop :=
  ∃ z ∈ strings (integerGrid (denominator fs k)) (arity fs),
    ∀ f ∈ fs, integerHolds f k (denominator fs k) z

instance (fs : List Formula) (k : ℕ) : Decidable (finiteTest fs k) := by
  unfold finiteTest
  infer_instance

@[local fun_prop] theorem natPower {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a ^ g a) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg

@[local fun_prop] theorem intProduct {α : Type*} [Primcodable α] {f : α → List ℤ}
    (hf : Primrec f) : Primrec (fun a => (f a).prod) := by
  change Primrec (fun a => (f a).foldr (· * ·) 1)
  apply foldList (h := fun _ p => p.1*p.2) hf (Primrec.const 1)
  fun_prop

@[local fun_prop] theorem intSum {α : Type*} [Primcodable α] {f : α → List ℤ}
    (hf : Primrec f) : Primrec (fun a => (f a).sum) := by
  change Primrec (fun a => (f a).foldr (· + ·) 0)
  apply foldList (h := fun _ p => p.1+p.2) hf (Primrec.const 0)
  fun_prop

@[local fun_prop] theorem natSum {α : Type*} [Primcodable α] {f : α → List ℕ}
    (hf : Primrec f) : Primrec (fun a => (f a).sum) := by
  change Primrec (fun a => (f a).foldr (· + ·) 0)
  apply foldList (h := fun _ p => p.1+p.2) hf (Primrec.const 0)
  fun_prop

@[fun_prop] theorem weight_primrec : Primrec weight := by unfold weight; fun_prop

@[fun_prop] theorem polynomials_primrec : Primrec polynomials := by
  exact Primrec.list_flatten.comp Primrec.list_flatten

@[fun_prop] theorem variableIndices_primrec : Primrec variableIndices := by
  unfold variableIndices
  fun_prop

@[fun_prop] theorem arity_primrec : Primrec arity := by
  unfold arity
  apply foldList (h := fun _ p => max (p.1+1) p.2) (by fun_prop) (Primrec.const 0)
  fun_prop

@[fun_prop] theorem totalWeight_primrec : Primrec totalWeight := by
  unfold totalWeight
  fun_prop

@[fun_prop] theorem denominator_primrec : Primrec (fun q : List Formula × ℕ => denominator q.1 q.2) := by
  unfold denominator
  fun_prop

@[fun_prop] theorem integerGrid_primrec : Primrec integerGrid := by unfold integerGrid; fun_prop

@[fun_prop] theorem degree_primrec : Primrec degree := by
  unfold degree
  apply foldList (h := fun (_ : Polynomial) (p : (ℤ × List ℕ) × ℕ) => max p.1.2.length p.2) Primrec.id (Primrec.const 0)
  fun_prop

@[fun_prop] theorem scaledMonomial_primrec :
    Primrec (fun q : ℕ × ℕ × List ℤ × (ℤ × List ℕ) => scaledMonomial q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold scaledMonomial
  fun_prop

@[fun_prop] theorem scaledEvaluate_primrec :
    Primrec (fun q : ℕ × ℕ × List ℤ × Polynomial => scaledEvaluate q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold scaledEvaluate
  apply intSum
  apply mapList (g := fun (q : ℕ × ℕ × List ℤ × Polynomial) (t : ℤ × List ℕ) =>
    scaledMonomial q.1 q.2.1 q.2.2.1 t) (by fun_prop)
  exact scaledMonomial_primrec.comp (show Primrec (fun q :
    (ℕ × ℕ × List ℤ × Polynomial) × (ℤ × List ℕ) =>
      (q.1.1,q.1.2.1,q.1.2.2.1,q.2)) by fun_prop)

@[local fun_prop] theorem scaledEvaluate_rule {α : Type*} [Primcodable α]
    {f g : α → ℕ} {z : α → List ℤ} {p : α → Polynomial}
    (hf : Primrec f) (hg : Primrec g) (hz : Primrec z) (hp : Primrec p) :
    Primrec (fun a => scaledEvaluate (f a) (g a) (z a) (p a)) :=
  scaledEvaluate_primrec.comp (hf.pair (hg.pair (hz.pair hp)))

theorem integerHolds_primrec :
    PrimrecPred (fun q : Formula × ℕ × ℕ × List ℤ => integerHolds q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold integerHolds
  fun_prop

@[local fun_prop] theorem integerHolds_rule {α : Type*} [Primcodable α]
    {f : α → Formula} {k D : α → ℕ} {z : α → List ℤ}
    (hf : Primrec f) (hk : Primrec k) (hD : Primrec D) (hz : Primrec z) :
    PrimrecPred (fun a => integerHolds (f a) (k a) (D a) (z a)) :=
  integerHolds_primrec.comp (hf.pair (hk.pair (hD.pair hz)))

@[local fun_prop] theorem strings_rule {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => strings (f a) (g a)) := strings_primrec.comp (hf.pair hg)

@[local fun_prop] theorem denominator_rule {α : Type*} [Primcodable α]
    {f : α → List Formula} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => denominator (f a) (g a)) := denominator_primrec.comp (hf.pair hg)

theorem finiteTest_primrec : PrimrecPred (fun q : List Formula × ℕ => finiteTest q.1 q.2) := by
  unfold finiteTest
  fun_prop

end TranslationTiling.EuclideanMembership
