import TranslationTiling.FiniteCompiler.Effective.GeometryPrimitives
import TranslationTiling.Compiler.EffectiveCycleFamily

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- One useful-coordinate point and one digit-subgroup displacement. -/
abbrev SparseChoice := ℕ × ℕ × ℕ

def pointTable (a b : ℕ) (z : SparseChoice) : List ℕ :=
  (List.range (a * b)).map fun k => if k / b = z.1 ∧ k % b = z.2.1 then z.2.2 else 0

@[fun_prop] theorem pointTable_primrec : Primrec (fun d : (ℕ × ℕ) × SparseChoice =>
    pointTable d.1.1 d.1.2 d.2) := by
  unfold pointTable
  fun_prop

theorem pointTable_apply {a b : ℕ} [NeZero a] [NeZero b]
    (z : SparseChoice) (e : ZMod a × ZMod b) :
    (pointTable a b z).getD (rectangularIndex b e.1.val e.2.val) 0 =
      if e.1.val = z.1 ∧ e.2.val = z.2.1 then z.2.2 else 0 := by
  have hi := rectangularIndex_lt e
  have hd : rectangularIndex b e.1.val e.2.val / b = e.1.val := by
    unfold rectangularIndex
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (NeZero.pos b),Nat.div_eq_of_lt (ZMod.val_lt e.2),Nat.zero_add]
  have hm : rectangularIndex b e.1.val e.2.val % b = e.2.val := by
    unfold rectangularIndex
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (ZMod.val_lt e.2)]
  simp only [pointTable,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,hd,hm]

def sparseAlphabet (c : CycleConfiguration) : List SparseChoice :=
  if c.2.2.2.2 then
    (List.range c.2.2.1).flatMap fun a => (List.range c.2.2.2.1).flatMap fun b =>
      (subgroupCodes c.1 c.2.1).map fun d => (a,b,d)
  else [(0,0,0)]

@[fun_prop] theorem sparseAlphabet_primrec : Primrec sparseAlphabet := by
  have hp : Primrec (fun c : CycleConfiguration => (c.1,c.2.1)) := by fun_prop
  have hs := subgroupCodes_primrec.comp hp
  have hm : Primrec (fun d : (CycleConfiguration × ℕ) × ℕ =>
      (subgroupCodes d.1.1.1 d.1.1.2.1).map fun z => (d.1.2,d.2,z)) := by
    have hp : Primrec (fun d : (CycleConfiguration × ℕ) × ℕ => d.1.1) := by fun_prop
    apply mapList (hs.comp hp)
    fun_prop
  have hb : Primrec (fun d : CycleConfiguration × ℕ =>
      (List.range d.1.2.2.2.1).flatMap fun b =>
        (subgroupCodes d.1.1 d.1.2.1).map fun z => (d.2,b,z)) := by
    exact flatMapList (by fun_prop) hm
  have ha : Primrec (fun c : CycleConfiguration =>
      (List.range c.2.2.1).flatMap fun a => (List.range c.2.2.2.1).flatMap fun b =>
        (subgroupCodes c.1 c.2.1).map fun z => (a,b,z)) :=
    flatMapList (by fun_prop) hb
  unfold sparseAlphabet
  fun_prop

def sparseRow (c : CycleConfiguration) (z : SparseChoice) : CycleRow :=
  if c.2.2.2.2 then (c.1,c.2.2.1,c.2.2.2.1,pointTable c.2.2.1 c.2.2.2.1 z)
  else (c.1,1,1,[0])

@[fun_prop] theorem sparseRow_primrec : Primrec (fun d : CycleConfiguration × SparseChoice =>
    sparseRow d.1 d.2) := by
  unfold sparseRow
  have hp : Primrec (fun d : CycleConfiguration × SparseChoice =>
      ((d.1.2.2.1,d.1.2.2.2.1),d.2)) := by fun_prop
  have ht := pointTable_primrec.comp hp
  fun_prop

def sparseRows (cs : List CycleConfiguration) (zs : List SparseChoice) : List CycleRow :=
  (List.range cs.length).map fun i => sparseRow (cs.getD i (0,[],0,0,false)) (zs.getD i (0,0,0))

theorem sparseRows_primrec : Primrec (fun d : List CycleConfiguration × List SparseChoice =>
    sparseRows d.1 d.2) := by
  unfold sparseRows
  have hp : Primrec (fun d : (List CycleConfiguration × List SparseChoice) × ℕ =>
      (d.1.1.getD d.2 (0,[],0,0,false),d.1.2.getD d.2 (0,0,0))) := by fun_prop
  have hr := sparseRow_primrec.comp hp
  fun_prop

def sparseGadgets (N : ℕ) (cs : List CycleConfiguration) : List (List NumericalPoint) :=
  (mixedProducts (cs.map sparseAlphabet)).map fun zs => cycleCodes N (sparseRows cs zs)

theorem sparseGadgets_primrec : Primrec (fun d : ℕ × List CycleConfiguration =>
    sparseGadgets d.1 d.2) := by
  unfold sparseGadgets
  have ha : Primrec (fun d : ℕ × List CycleConfiguration => mixedProducts (d.2.map sparseAlphabet)) := by
    apply mixedProducts_primrec.comp
    fun_prop
  have hp : Primrec (fun d : (ℕ × List CycleConfiguration) × List SparseChoice =>
      (d.1.2,d.2)) := by fun_prop
  have hg : Primrec (fun d : (ℕ × List CycleConfiguration) × List SparseChoice =>
      cycleCodes d.1.1 (sparseRows d.1.2 d.2)) :=
    cycleCodes_primrec.comp ((Primrec.fst.comp Primrec.fst).pair (sparseRows_primrec.comp hp))
  exact mapList ha hg

end TranslationTiling.FiniteCompiler.Effective
