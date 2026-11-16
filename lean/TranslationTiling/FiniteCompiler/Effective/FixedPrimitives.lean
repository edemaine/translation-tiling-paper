import TranslationTiling.FiniteCompiler.Effective.SparsePrimitives

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local fun_prop] cycleCodes_primrec

def triggerTable (a b u : ℕ) : List ℕ :=
  (List.range (a*b)).map fun k => if k=0 then 0 else u

@[fun_prop] theorem triggerTable_primrec : Primrec (fun d : ℕ×ℕ×ℕ =>
    triggerTable d.1 d.2.1 d.2.2) := by
  unfold triggerTable
  fun_prop

theorem triggerTable_apply {a b : ℕ} [NeZero a] [NeZero b]
    (u : ℕ) (e : ZMod a × ZMod b) :
    (triggerTable a b u).getD (rectangularIndex b e.1.val e.2.val) 0 =
      if e=0 then 0 else u := by
  have hi := rectangularIndex_lt e
  have hz : rectangularIndex b e.1.val e.2.val=0 ↔ e=0 := by
    simp only [rectangularIndex,Prod.ext_iff,Prod.fst_zero,Prod.snd_zero]
    constructor
    · intro h
      constructor <;> apply ZMod.val_injective <;> simp only [ZMod.val_zero]
      · have hb := NeZero.pos b; nlinarith
      · omega
    · rintro ⟨h1,h2⟩; simp [h1,h2]
  simp only [triggerTable,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some,hz]

def fixedRow (c : CycleConfiguration) (q : ℕ) : CycleRow :=
  if c.2.2.2.2 then
    (c.1,c.2.2.1,c.2.2.2.1,triggerTable c.2.2.1 c.2.2.2.1 (c.1/q))
  else (c.1,1,1,[0])

@[fun_prop] theorem fixedRow_primrec : Primrec (fun d : CycleConfiguration×ℕ =>
    fixedRow d.1 d.2) := by
  unfold fixedRow
  fun_prop

def fixedRows (cs : List CycleConfiguration) (qs : List ℕ) : List CycleRow :=
  (List.range cs.length).map fun i => fixedRow (cs.getD i (0,[],0,0,false)) (qs.getD i 0)

@[fun_prop] theorem fixedRows_primrec : Primrec (fun d : List CycleConfiguration×List ℕ =>
    fixedRows d.1 d.2) := by
  unfold fixedRows
  fun_prop

def fixedGadgets (N : ℕ) (cs : List CycleConfiguration) (qs : List ℕ) : List (List NumericalPoint) :=
  [cycleCodes N (fixedRows cs qs)]

@[fun_prop] theorem fixedGadgets_primrec : Primrec (fun d : ℕ×List CycleConfiguration×List ℕ =>
    fixedGadgets d.1 d.2.1 d.2.2) := by
  unfold fixedGadgets
  fun_prop

theorem fixedRows_ofFn {m : ℕ} (cs : Fin m → CycleConfiguration) (qs : List ℕ) :
    fixedRows (List.ofFn cs) qs = List.ofFn (fun s => fixedRow (cs s) (qs.getD s.val 0)) := by
  apply List.ext_getElem
  · simp only [fixedRows,List.length_map,List.length_range,List.length_ofFn]
  · intro k hk hk'
    have hkm : k<m := by simpa only [List.length_ofFn] using hk'
    simp only [fixedRows,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,dif_pos hkm,Option.getD_some,List.getElem_ofFn]

end
end TranslationTiling.FiniteCompiler.Effective
