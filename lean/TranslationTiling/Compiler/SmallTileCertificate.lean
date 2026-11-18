import TranslationTiling.Compiler.SingleInputBound
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fin.Tuple.Basic

/-! Certificates for periodic tilings with at most three Wang symbols. -/
namespace TranslationTiling.Compiler.SmallTile
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 200000

abbrev Letter := Fin 3
abbrev Matrix := Letter → Letter → Bool

def pack : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 1 else 0)+2*pack bs

def matrixCode (r : Matrix) : ℕ :=
  pack (List.ofFn fun i : Fin 9 => r ⟨i.val/3,by omega⟩ ⟨i.val%3,Nat.mod_lt _ (by decide)⟩)

def edge (mask : ℕ) (a b : Letter) : Bool := mask.testBit (3*a.val+b.val)

theorem matrixCode_edge : ∀ r : Matrix, ∀ a b, edge (matrixCode r) a b=r a b := by
  decide +kernel

def Rectangular (r : Matrix) : Prop :=
  ∀ a b c d, r a c=true → r b c=true → r a d=r b d

instance (r : Matrix) : Decidable (Rectangular r) := by unfold Rectangular; infer_instance

def digit (code i : ℕ) : Letter := ⟨code/3^i%3,Nat.mod_lt _ (by decide)⟩
def row (code : ℕ) (x : Fin 4) : Letter := digit code x.val

def rowCode (r : Fin 4 → Letter) : ℕ :=
  (r 0).val+3*(r 1).val+9*(r 2).val+27*(r 3).val

theorem rowCode_lt (r : Fin 4 → Letter) : rowCode r<81 := by
  have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt; have := (r 3).isLt
  unfold rowCode
  omega

theorem row_rowCode (r : Fin 4 → Letter) (x : Fin 4) : row (rowCode r) x=r x := by
  have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt; have := (r 3).isLt
  apply Fin.ext
  fin_cases x <;> simp only [row,digit,rowCode,Fin.val_zero,Fin.val_one,Fin.reduceFinMk] <;> norm_num <;> omega

def rowOK (H a : ℕ) : Bool :=
  (List.range 3).all fun x => edge H (digit a x) (digit a (x+1))

def vertical (V a b : ℕ) : Bool :=
  (List.range 4).all fun x => edge V (digit a x) (digit b x)

def rows (H : ℕ) : List ℕ := (List.range 81).filter (rowOK H)

def torusOK (H V k code : ℕ) : Bool :=
  (List.range k).all fun y => (List.range k).all fun x =>
    edge H (digit code (x+k*y)) (digit code ((x+1)%k+k*y)) &&
    edge V (digit code (x+k*y)) (digit code (x+k*((y+1)%k)))

inductive Certificate where
  | periodic (three : Bool) (code : Fin 19683)
  | obstruction (ranks : ℕ)
deriving DecidableEq

def Valid (H V : ℕ) : Certificate → Bool
  | .periodic b code => torusOK H V (if b then 3 else 2) code.val
  | .obstruction ranks => (rows H).all fun a => (rows H).all fun b =>
      !(vertical V a b) || decide ((digit ranks a).val < (digit ranks b).val)

def Patch (H V : ℕ) (a : Fin 4 → Fin 4 → Letter) : Prop :=
  (∀ y : Fin 4, ∀ x : Fin 3, edge H (a y ⟨x.val,by omega⟩) (a y ⟨x.val+1,by omega⟩)=true) ∧
  (∀ y : Fin 3, ∀ x : Fin 4, edge V (a ⟨y.val,by omega⟩ x) (a ⟨y.val+1,by omega⟩ x)=true)

theorem rowCode_mem {H V : ℕ} {a : Fin 4 → Fin 4 → Letter} (ha : Patch H V a) (y : Fin 4) :
    rowCode (a y)∈rows H := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (rowCode_lt _),?_⟩
  apply List.all_eq_true.mpr
  intro x hx
  have hx' : x<3 := List.mem_range.mp hx
  change edge H (row (rowCode (a y)) ⟨x,by omega⟩)
    (row (rowCode (a y)) ⟨x+1,by omega⟩)=true
  simp only [row_rowCode]
  exact ha.1 y ⟨x,hx'⟩

theorem rowCode_vertical {H V : ℕ} {a : Fin 4 → Fin 4 → Letter}
    (ha : Patch H V a) (y : Fin 3) :
    vertical V (rowCode (a ⟨y.val,by omega⟩)) (rowCode (a ⟨y.val+1,by omega⟩))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have hx' : x<4 := List.mem_range.mp hx
  change edge V (row (rowCode (a ⟨y.val,by omega⟩)) ⟨x,hx'⟩)
    (row (rowCode (a ⟨y.val+1,by omega⟩)) ⟨x,hx'⟩)=true
  simp only [row_rowCode]
  exact ha.2 y ⟨x,hx'⟩

theorem obstruction_false {H V ranks : ℕ} (hc : Valid H V (.obstruction ranks)=true)
    {a : Fin 4 → Fin 4 → Letter} (ha : Patch H V a) : False := by
  have hstep (y : Fin 3) :
      (digit ranks (rowCode (a ⟨y.val,by omega⟩))).val <
        (digit ranks (rowCode (a ⟨y.val+1,by omega⟩))).val := by
    have h := List.all_eq_true.mp (List.all_eq_true.mp hc _ (rowCode_mem ha ⟨y.val,by omega⟩))
      _ (rowCode_mem ha ⟨y.val+1,by omega⟩)
    simpa only [rowCode_vertical ha y,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h
  have h0 := hstep 0
  have h1 := hstep 1
  have h2 := hstep 2
  have hb := (digit ranks (rowCode (a 3))).isLt
  change _ < 3 at hb
  change (digit ranks (rowCode (a 0))).val < (digit ranks (rowCode (a 1))).val at h0
  change (digit ranks (rowCode (a 1))).val < (digit ranks (rowCode (a 2))).val at h1
  change (digit ranks (rowCode (a 2))).val < (digit ranks (rowCode (a 3))).val at h2
  omega

def Accepted (H V : ℕ) : Prop :=
  ∃ b : Bool, ∃ code : Fin 19683, torusOK H V (if b then 3 else 2) code.val=true
instance (H V : ℕ) : Decidable (Accepted H V) := by unfold Accepted; infer_instance

theorem accepted_of_certificate {H V : ℕ} {a : Fin 4 → Fin 4 → Letter}
    (ha : Patch H V a) {c : Certificate} (hc : Valid H V c=true) : Accepted H V := by
  cases c with
  | periodic b code => exact ⟨b,code,hc⟩
  | obstruction ranks => exact (obstruction_false hc ha).elim

end TranslationTiling.Compiler.SmallTile
