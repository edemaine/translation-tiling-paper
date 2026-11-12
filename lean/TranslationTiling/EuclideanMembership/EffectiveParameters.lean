import TranslationTiling.EuclideanMembership.SlotModel
import TranslationTiling.EuclideanMembership.Syntax

namespace TranslationTiling.EuclideanMembership
open Compiler.Effective
variable {d : ℕ}

@[fun_prop] theorem ofFnValue {α β : Type*} [Primcodable α] [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} (hf : ∀ i, Primrec (fun a => f a i)) :
    Primrec (fun a => List.ofFn (f a)) := Primrec.list_ofFn hf

@[fun_prop] theorem natPairValue {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => Nat.pair (f a) (g a)) :=
  Primrec₂.natPair.comp hf hg

@[fun_prop] theorem slotIndexValue {α : Type*} [Primcodable α]
    {z : α → Lattice d} {c : α → ℕ} (hz : Primrec z) (hc : Primrec c) :
    Primrec (fun a => slotIndex (z a) (c a)) := by
  unfold slotIndex
  exact Primrec.encode.comp ((Primrec.sumInr (α := ℕ) (β := Lattice d × ℕ)).comp (hz.pair hc))

@[fun_prop] theorem reciprocalIndexValue {α : Type*} [Primcodable α]
    {n : α → ℕ} (hn : Primrec n) : Primrec (fun a => reciprocalIndex d (n a)) := by
  unfold reciprocalIndex
  exact Primrec.encode.comp ((Primrec.sumInl (α := ℕ) (β := Lattice d × ℕ)).comp hn)

@[fun_prop] theorem natSumValue {α : Type*} [Primcodable α] {f : α → List ℕ}
    (hf : Primrec f) : Primrec (fun a => (f a).sum) :=
  (Primrec.list_foldr hf (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

@[fun_prop] theorem coordinateRadius_primrec : Primrec (@coordinateRadius d) := by
  unfold coordinateRadius
  fun_prop
@[fun_prop] theorem bodyRadius_primrec : Primrec (@bodyRadius d) := by unfold bodyRadius; fun_prop
@[fun_prop] theorem tileDiameter_primrec : Primrec (@tileDiameter d) := by unfold tileDiameter; fun_prop
@[fun_prop] theorem coordinateSum_primrec : Primrec (@coordinateSum d) := by unfold coordinateSum; fun_prop

@[fun_prop] theorem cellBoxValue {α : Type*} [Primcodable α]
    {b : α → ℕ} (hb : Primrec b) : Primrec (fun a => cellBox d (b a)) := by
  unfold cellBox
  apply mapList
  · exact strings_primrec.comp ((integerGrid_primrec.comp hb).pair (Primrec.const d))
  · apply piValue
    intro i
    fun_prop

@[fun_prop] theorem probeCellsValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {a : α → Probe d} (hp : Primrec p) (ha : Primrec a) :
    Primrec (fun t => probeCells (p t) (a t)) := by
  unfold probeCells probeRadius
  fun_prop

@[fun_prop] theorem anchorPoint_primrec : Primrec (@anchorPoint d) := by
  unfold anchorPoint
  fun_prop

@[fun_prop] theorem renameFormulaValue {α : Type*} [Primcodable α]
    {r : α → ℕ → ℕ} {f : α → Formula}
    (hr : Primrec (fun q : α × ℕ => r q.1 q.2)) (hf : Primrec f) :
    Primrec (fun a => renameFormula (r a) (f a)) := by
  unfold renameFormula renamePolynomial
  fun_prop

end TranslationTiling.EuclideanMembership
