import TranslationTiling.Proofs.FiniteSearch
import TranslationTiling.Proofs.IntegerResidues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! Primitive-recursive closure rules for the compiler's finite arithmetic.
`fun_prop` assembles ordinary kernel-checked proofs from these rules. -/

namespace TranslationTiling.Compiler.Effective

open LeanWang.Kari.SignedPrimrec

attribute [fun_prop] Primrec PrimrecPred
attribute [fun_prop] Primrec.id Primrec.const Primrec.fst Primrec.snd Primrec.comp
attribute [fun_prop] Primrec.list_range Primrec.list_length Primrec.list_head?
attribute [fun_prop] Primrec.encode Primrec.decode
attribute [fun_prop] Primrec.option_some
attribute [fun_prop] Primrec.unpair

@[fun_prop] theorem natAdd {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a + g a) :=
  Primrec.nat_add.comp hf hg

@[fun_prop] theorem natMul {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a * g a) :=
  Primrec.nat_mul.comp hf hg

@[fun_prop] theorem natSub {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a - g a) :=
  Primrec.nat_sub.comp hf hg

@[fun_prop] theorem natMod {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a % g a) :=
  Primrec.nat_mod.comp hf hg

@[fun_prop] theorem natDiv {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a / g a) :=
  Primrec.nat_div.comp hf hg

@[fun_prop] theorem natMax {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => max (f a) (g a)) :=
  Primrec.nat_max.comp hf hg

@[fun_prop] theorem intCast {α : Type*} [Primcodable α] {f : α → ℕ}
    (hf : Primrec f) : Primrec (fun a => (f a : ℤ)) := intOfNat.comp hf

@[fun_prop] theorem intPlus {α : Type*} [Primcodable α] {f g : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a + g a) :=
  intAdd.comp hf hg

@[fun_prop] theorem intMinus {α : Type*} [Primcodable α] {f g : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a - g a) :=
  intAdd.comp hf (intNeg.comp hg)

@[fun_prop] theorem intTimes {α : Type*} [Primcodable α] {f g : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a * g a) :=
  intMul.comp hf hg

@[fun_prop] theorem intNegative {α : Type*} [Primcodable α] {f : α → ℤ}
    (hf : Primrec f) : Primrec (fun a => -f a) := intNeg.comp hf

@[fun_prop] theorem intModulo {α : Type*} [Primcodable α] {f : α → ℤ} {g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a % (g a : ℤ)) :=
  int_emod_nat_primrec.comp hf hg

theorem natAbs_primrec : Primrec Int.natAbs := by
  exact (intCasesOn Primrec.id Primrec.snd.to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (by intro z; cases z <;> rfl)

@[fun_prop] theorem intAbs {α : Type*} [Primcodable α] {f : α → ℤ}
    (hf : Primrec f) : Primrec (fun a => (f a).natAbs) := natAbs_primrec.comp hf

theorem toNat_primrec : Primrec Int.toNat := by
  exact (intCasesOn Primrec.id Primrec.snd.to₂
    (Primrec.const 0).to₂).of_eq (by intro z; cases z <;> rfl)

@[fun_prop] theorem intToNat {α : Type*} [Primcodable α] {f : α → ℤ}
    (hf : Primrec f) : Primrec (fun a => (f a).toNat) := toNat_primrec.comp hf

@[fun_prop] theorem mapList {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → β → γ}
    (hf : Primrec f) (hg : Primrec (fun p : α × β => g p.1 p.2)) :
    Primrec (fun a => (f a).map (g a)) := Primrec.list_map hf hg

@[fun_prop] theorem appendList {α β : Type*} [Primcodable α] [Primcodable β]
    {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a ++ g a) := Primrec.list_append.comp hf hg

@[fun_prop] theorem consList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a :: g a) := Primrec.list_cons.comp hf hg

@[fun_prop] theorem filterList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Prop} [DecidableRel p]
    (hf : Primrec f) (hp : PrimrecPred (fun z : α × β => p z.1 z.2)) :
    Primrec (fun a => (f a).filter fun b => decide (p a b)) := by
  apply (Primrec.listFilterMap (g := fun a b => if p a b then some b else none) hf
    (Primrec.ite hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq
  intro a
  simp only [← List.filterMap_eq_filter, Option.guard, decide_eq_true_eq]

@[fun_prop] theorem vector3 {α : Type*} [Primcodable α] {f g h : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => ![f a, g a, h a]) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro i
  fin_cases i <;> simp <;> assumption

@[fun_prop] theorem vector2 {α β : Type*} [Primcodable α] [Primcodable β] {f g : α → β}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => ![f a, g a]) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro i
  fin_cases i <;> simp <;> assumption

@[fun_prop] theorem flatMapList {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → β → List γ}
    (hf : Primrec f) (hg : Primrec (fun p : α × β => g p.1 p.2)) :
    Primrec (fun a => (f a).flatMap (g a)) := Primrec.list_flatMap hf hg

@[fun_prop] theorem foldList {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → γ} {h : α → β × γ → γ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec (fun p : α × (β × γ) => h p.1 p.2)) :
    Primrec (fun a => (f a).foldr (fun b c => h a (b, c)) (g a)) :=
  Primrec.list_foldr hf hg hh

@[fun_prop] theorem pairValue {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a, g a)) := hf.pair hg

@[fun_prop] theorem piValue {α β : Type*} [Primcodable α] [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} (hf : ∀ i, Primrec (fun a => f a i)) : Primrec f :=
  Primrec.fin_curry.mpr ((Primrec.fin_curry₁.mpr hf).swap)

theorem applyFin {α β : Type*} [Primcodable α] [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} {g : α → Fin n} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a (g a)) := Primrec.fin_app.comp hf hg

def indexed {β : Type*} {n : ℕ} (f : Fin n → β) (i : Fin n) : β := f i

@[fun_prop] theorem indexedValue {α β : Type*} [Primcodable α] [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} {g : α → Fin n} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => indexed (f a) (g a)) := Primrec.fin_app.comp hf hg

@[fun_prop] theorem finVal {α : Type*} [Primcodable α] {n : ℕ} {f : α → Fin n}
    (hf : Primrec f) : Primrec (fun a => (f a).val) := Primrec.fin_val.comp hf

@[fun_prop] theorem evalFin {β : Type*} [Primcodable β] {n : ℕ} (i : Fin n) :
    Primrec (fun f : Fin n → β => f i) := Primrec.fin_app.comp Primrec.id (Primrec.const i)

@[fun_prop] theorem getList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → ℕ} (d : β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).getD (g a) d) := (Primrec.list_getD d).comp hf hg

theorem zipIdx_primrec {β : Type*} [Primcodable β] (d : β) :
    Primrec (fun xs : List β => xs.zipIdx) := by
  have hp : Primrec (fun xs : List β =>
      (List.range xs.length).map fun i => (xs.getD i d, i)) := by fun_prop
  apply hp.of_eq
  intro xs
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.length_map, List.length_range] at hi
    simp [List.getD_eq_getElem?_getD, hi]

@[fun_prop] theorem intLE {α : Type*} [Primcodable α] {f g : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) : PrimrecPred (fun a => f a ≤ g a) := by
  apply (Primrec.eq.comp (toNat_primrec.comp (intMinus hf hg)) (Primrec.const 0)).of_eq
  intro a
  rw [Int.toNat_eq_zero]
  exact sub_nonpos

@[fun_prop] theorem intLT {α : Type*} [Primcodable α] {f g : α → ℤ}
    (hf : Primrec f) (hg : Primrec g) : PrimrecPred (fun a => f a < g a) :=
  (intLE (intPlus hf (Primrec.const 1)) hg).of_eq (fun a => Int.add_one_le_iff)

@[fun_prop] theorem memberList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun a => f a ∈ g a) := mem_primrec.comp hf hg

@[fun_prop] theorem equalValues {α β : Type*} [Primcodable α] [Primcodable β]
    {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun a => f a = g a) := Primrec.eq.comp hf hg

@[fun_prop] theorem natLE {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : PrimrecPred (fun a => f a ≤ g a) :=
  Primrec.nat_le.comp hf hg

@[fun_prop] theorem natLT {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : PrimrecPred (fun a => f a < g a) :=
  Primrec.nat_lt.comp hf hg

attribute [fun_prop] PrimrecPred.not PrimrecPred.and PrimrecPred.or

@[fun_prop] theorem decideValue {α : Type*} [Primcodable α] {p : α → Prop}
    [DecidablePred p] (hp : PrimrecPred p) : Primrec (fun a => decide (p a)) := hp.decide

@[fun_prop] theorem iteValue {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimrecPred p) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if p a then f a else g a) := Primrec.ite hp hf hg

@[fun_prop] theorem allList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Prop} (hf : Primrec f)
    (hp : PrimrecPred (fun z : α × β => p z.1 z.2)) :
    PrimrecPred (fun a => ∀ b ∈ f a, p a b) :=
  hp.primrecRel.swap.forall_mem_list.comp hf Primrec.id

@[fun_prop] theorem someList {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Prop} (hf : Primrec f)
    (hp : PrimrecPred (fun z : α × β => p z.1 z.2)) :
    PrimrecPred (fun a => ∃ b ∈ f a, p a b) :=
  hp.primrecRel.swap.exists_mem_list.comp hf Primrec.id

@[fun_prop] theorem allFin {α : Type*} [Primcodable α] {n : ℕ}
    {p : α → Fin n → Prop} (hp : PrimrecPred (fun z : α × Fin n => p z.1 z.2)) :
    PrimrecPred (fun a => ∀ i, p a i) := by
  apply (allList (Primrec.const (List.ofFn (id : Fin n → Fin n))) hp).of_eq
  intro a
  simp

end TranslationTiling.Compiler.Effective
