import TranslationTiling.EuclideanMembership.Probes
import TranslationTiling.EuclideanMembership.MatrixRestrictions

/-! Bounded real parameters for a countable collection of spatial slots.
Reciprocals of positive integers are additional variables constrained by
polynomial equations, keeping the constraint language integer-coefficient. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint RealMatrix)
noncomputable section
variable {d : ℕ}

abbrev Parameter (d : ℕ) := ℕ ⊕ (Lattice d × ℕ)

instance (priority := 2000) parameterEncodable (d : ℕ) : Encodable (Parameter d) :=
  (inferInstance : Primcodable (Parameter d)).toEncodable

def reciprocalIndex (d n : ℕ) : ℕ := Encodable.encode (Sum.inl n : Parameter d)
def slotIndex (z : Lattice d) (c : ℕ) : ℕ := Encodable.encode (Sum.inr (z,c) : Parameter d)

def presence (x : Assignment) (z : Lattice d) : ℝ := x (slotIndex z (Nat.pair 0 0))
def slotShift (x : Assignment) (z : Lattice d) (i : Fin d) : ℝ := x (slotIndex z (Nat.pair 1 i.val))
def slotRows (x : Assignment) (z : Lattice d) : RealMatrix d :=
  fun i j => x (slotIndex z (Nat.pair 2 (Nat.pair i.val j.val)))
def slotNormal (x : Assignment) (z : Lattice d) (i : Fin d) : ℝ :=
  x (slotIndex z (Nat.pair 3 i.val))
def reciprocalValue (x : Assignment) (n : ℕ) : ℝ := x (reciprocalIndex d n)

def ReciprocalCorrect (x : Assignment) : Prop :=
  ∀ n : ℕ, ((n : ℝ)+1)*reciprocalValue (d := d) x n=1

def slotCenter (x : Assignment) (z : Lattice d) : EPoint d :=
  WithLp.toLp 2 fun i => (2*(z i : ℝ)+slotShift x z i)*reciprocalValue (d := d) x (cellScale d-1)

def probeValue (x : Assignment) (a : Probe d) : EPoint d :=
  WithLp.toLp 2 fun i => (a.1 i : ℝ)*reciprocalValue (d := d) x a.2

theorem reciprocal_eq {x : Assignment} (h : ReciprocalCorrect (d := d) x) (n : ℕ) :
    reciprocalValue (d := d) x n=1/((n : ℝ)+1) := by
  apply (eq_div_iff (by positivity : (n : ℝ)+1 ≠ 0)).mpr
  simpa only [mul_comm] using h n

theorem slotShift_bound (x : Assignment) (z : Lattice d) (i : Fin d) : |slotShift x z i| ≤ 1 :=
  abs_le.mpr (x _).property

theorem slotCenter_eq {x : Assignment} (h : ReciprocalCorrect (d := d) x) (z : Lattice d) :
    slotCenter x z=cellCenter z (slotShift x z) := by
  have hn : cellScale d-1+1=cellScale d := Nat.sub_add_cancel (cellScale_pos d)
  have he : reciprocalValue (d := d) x (cellScale d-1)=1/(cellScale d : ℝ) := by
    rw [reciprocal_eq h]
    congr 1
    exact_mod_cast hn
  ext i
  simp only [slotCenter,cellCenter,PiLp.toLp_apply,he,div_eq_mul_inv,one_mul]

theorem probeValue_eq {x : Assignment} (h : ReciprocalCorrect (d := d) x) (a : Probe d) :
    probeValue x a=probe a := by
  ext i
  simp only [probeValue,probe,PiLp.toLp_apply,reciprocal_eq h,div_eq_mul_inv,one_mul]

def intervalZero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
def intervalOne : Set.Icc (-1 : ℝ) 1 := ⟨1,by norm_num⟩

def reciprocalInterval (n : ℕ) : Set.Icc (-1 : ℝ) 1 :=
  ⟨1/((n : ℝ)+1),by
    constructor
    · have h : (0 : ℝ) ≤ 1/((n : ℝ)+1) := by positivity
      linarith
    · rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)]
      linarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]⟩

structure SlotData (d : ℕ) where
  enabled : Bool
  shift : Fin d → Set.Icc (-1 : ℝ) 1
  rows : Fin d → Fin d → Set.Icc (-1 : ℝ) 1
  normal : Fin d → Set.Icc (-1 : ℝ) 1

def slotCode (s : SlotData d) (c : ℕ) : Set.Icc (-1 : ℝ) 1 :=
  match c.unpair with
  | (0,_) => if s.enabled then intervalOne else intervalZero
  | (1,i) => if h : i < d then s.shift ⟨i,h⟩ else intervalZero
  | (2,k) =>
    let (i,j) := k.unpair
    if hi : i < d then if hj : j < d then s.rows ⟨i,hi⟩ ⟨j,hj⟩ else intervalZero else intervalZero
  | (3,i) => if h : i < d then s.normal ⟨i,h⟩ else intervalZero
  | _ => intervalZero

def fromSlots (s : Lattice d → SlotData d) : Assignment := fun n =>
  ((Encodable.decode (α := Parameter d) n).map fun p => match p with
    | Sum.inl k => reciprocalInterval k
    | Sum.inr (z,c) => slotCode (s z) c).getD intervalZero

theorem fromSlots_at (s : Lattice d → SlotData d) (p : Parameter d) :
    fromSlots s (Encodable.encode p) = match p with
      | Sum.inl k => reciprocalInterval k
      | Sum.inr (z,c) => slotCode (s z) c := by
  unfold fromSlots
  rw [Encodable.encodek]
  rfl

@[simp] theorem fromSlots_reciprocal (s : Lattice d → SlotData d) (n : ℕ) :
    reciprocalValue (d := d) (fromSlots s) n=1/((n : ℝ)+1) := by
  simp only [reciprocalValue,reciprocalIndex,fromSlots_at]
  rfl

@[simp] theorem fromSlots_presence (s : Lattice d → SlotData d) (z : Lattice d) :
    presence (fromSlots s) z=if (s z).enabled then 1 else 0 := by
  simp only [presence,slotIndex,fromSlots_at]
  cases he : (s z).enabled <;> simp [slotCode,intervalOne,intervalZero,he]

@[simp] theorem fromSlots_shift (s : Lattice d → SlotData d) (z : Lattice d) (i : Fin d) :
    slotShift (fromSlots s) z i=(s z).shift i := by
  simp only [slotShift,slotIndex,fromSlots_at,slotCode,Nat.unpair_pair,dif_pos i.isLt]

@[simp] theorem fromSlots_rows (s : Lattice d → SlotData d) (z : Lattice d) (i j : Fin d) :
    slotRows (fromSlots s) z i j=(s z).rows i j := by
  simp only [slotRows,slotIndex,fromSlots_at,slotCode,Nat.unpair_pair,dif_pos i.isLt,dif_pos j.isLt]

@[simp] theorem fromSlots_normal (s : Lattice d → SlotData d) (z : Lattice d) (i : Fin d) :
    slotNormal (fromSlots s) z i=(s z).normal i := by
  simp only [slotNormal,slotIndex,fromSlots_at,slotCode,Nat.unpair_pair,dif_pos i.isLt]

theorem fromSlots_correct (s : Lattice d → SlotData d) : ReciprocalCorrect (d := d) (fromSlots s) := by
  intro n
  rw [fromSlots_reciprocal]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp


def emptySlotData (d : ℕ) : SlotData d :=
  ⟨false,fun _ => intervalZero,fun _ _ => intervalZero,fun _ => intervalZero⟩

def placeSlots {ι : Type*} (f : ι → Lattice d) (s : ι → SlotData d) (z : Lattice d) : SlotData d := by
  classical
  exact if h : ∃ i, f i=z then s h.choose else emptySlotData d

theorem placeSlots_at {ι : Type*} (f : ι → Lattice d) (hf : Function.Injective f)
    (s : ι → SlotData d) (i : ι) : placeSlots f s (f i)=s i := by
  classical
  let he : ∃ j, f j=f i := ⟨i,rfl⟩
  rw [placeSlots,dif_pos he]
  exact congrArg s (hf he.choose_spec)

theorem placeSlots_enabled {ι : Type*} (f : ι → Lattice d) (s : ι → SlotData d)
    (z : Lattice d) (h : (placeSlots f s z).enabled=true) :
    ∃ i, f i=z ∧ placeSlots f s z=s i := by
  classical
  by_cases he : ∃ i, f i=z
  · exact ⟨he.choose,he.choose_spec,by rw [placeSlots,dif_pos he]⟩
  · simp only [placeSlots,dif_neg he,emptySlotData,Bool.false_eq_true] at h

end
end TranslationTiling.EuclideanMembership
