import TranslationTiling.EuclideanMembership.ModelRealization

/-! An actual Euclidean tiling determines bounded slot parameters. -/
namespace TranslationTiling.EuclideanMembership
open Rotations.General (EPoint castPoint row)
open Rotations.General.Real
open scoped Matrix
noncomputable section
variable {d : ℕ} [NeZero d]

private def motionData (ar af : Bool) (m : RigidMotion d)
    (hm : AllowedLinear ar af m.rotation) (p : Lattice d) : SlotData d := by
  have hr := (allowedLinear_iff_rows ar af (row m.rotation) (row_transpose_mul m.rotation)).mp
    (by simpa only [matrixRotation_row] using hm)
  exact ⟨true,fun i => ⟨cellParameter (m.apply (castPoint p)) i,
      abs_le.mp (cellParameter_bound _ i)⟩,
    fun i j => ⟨row m.rotation i j,abs_le.mp (row_abs_le_one m.rotation i j)⟩,
    fun i => ⟨hr.choose i,abs_le.mp (hr.choose_spec.1 i)⟩⟩

private theorem motionData_allowed (ar af : Bool) (m : RigidMotion d)
    (hm : AllowedLinear ar af m.rotation) (p : Lattice d) :
    AllowedRows ar af (row m.rotation) (fun i => (motionData ar af m hm p).normal i) := by
  exact ((allowedLinear_iff_rows ar af (row m.rotation) (row_transpose_mul m.rotation)).mp
    (by simpa only [matrixRotation_row] using hm)).choose_spec.2

 theorem MotionTiles.model {P : Tile d} {ar af : Bool} (ht : MotionTiles P ar af) :
    ∃ x : Assignment, Model ar af P x := by
  obtain ⟨C,ha,hcover⟩ := ht
  have hP : P ≠ [] := by
    intro he
    obtain ⟨t,m,hm,hu⟩ := hcover.exists
    obtain ⟨y,hy,hmy⟩ := hm
    obtain ⟨p,hp,hv⟩ := hy
    simpa [he] using hp
  let p := anchorPoint P
  have hp : p ∈ P := anchorPoint_mem hP
  let M : C → RigidMotion d := Subtype.val
  let f : C → Lattice d := fun m => cellIndex ((M m).apply (castPoint p))
  have hf : Function.Injective f := cellIndex_injective_of_aeCover P hp M hcover
  let data : C → SlotData d := fun m => motionData ar af (M m) (ha m.val m.property) p
  let s := placeSlots f data
  let x := fromSlots s
  have hx : ReciprocalCorrect (d := d) x := fromSlots_correct s
  have hs (m : C) : s (f m)=data m := placeSlots_at f hf data m
  have he (z : Lattice d) : Enabled x z ↔ (s z).enabled=true := by
    simp only [Enabled,x,fromSlots_presence]
    cases (s z).enabled <;> norm_num
  have extract (z : Lattice d) (hz : Enabled x z) : ∃ m : C, f m=z := by
    obtain ⟨m,hm,hdata⟩ := placeSlots_enabled f data z ((he z).mp hz)
    exact ⟨m,hm⟩
  have hrows (m : C) : slotRows x (f m)=row (M m).rotation := by
    ext i j
    simp only [x,fromSlots_rows,hs,data,motionData]
  have hcenter (m : C) : slotCenter x (f m)=(M m).apply (castPoint p) := by
    rw [slotCenter_eq (fromSlots_correct s)]
    have hh : slotShift x (f m)=cellParameter ((M m).apply (castPoint p)) := by
      funext i
      simp only [x,fromSlots_shift,hs,data,motionData]
    rw [hh]
    exact cellCenter_index _
  have hactive (m : C) : Enabled x (f m) := by
    rw [he,hs]
    rfl
  have hrot (m : C) : (slotRows x (f m))ᵀ*slotRows x (f m)=1 := by
    rw [hrows]
    exact row_transpose_mul _
  have hm (m : C) (h : (slotRows x (f m))ᵀ*slotRows x (f m)=1) :
      motionOfSlot x P (f m) h=M m := motionOfSlot_eq x P (f m) h (M m) (hrows m) (hcenter m)
  refine ⟨x,fromSlots_correct s,?_,?_,?_⟩
  · intro z
    constructor
    · simp only [x,fromSlots_presence]
      cases (s z).enabled <;> simp
    · intro hz
      obtain ⟨m,rfl⟩ := extract z hz
      refine ⟨hrot m,?_⟩
      have hn : slotNormal x (f m)=fun i => ((data m).normal i : ℝ) := by
        funext i
        simp only [x,fromSlots_normal,hs]
      rw [hrows,hn]
      exact motionData_allowed ar af (M m) (ha m.val m.property) p
  · intro z w hzw hz hw q hq r hr a hboth
    obtain ⟨m,rfl⟩ := extract z hz
    obtain ⟨n,rfl⟩ := extract w hw
    have hmn : m ≠ n := fun he => hzw (congrArg f he)
    have hdis := hcover.interior_disjoint hmn
    apply Set.disjoint_left.mp hdis
    · apply motion_openVoxel_subset_interior P hq (M m)
      rw [← hm m (hrot m),motionOfSlot_open_iff]
      simpa only [probeValue_eq hx] using hboth.1
    · apply motion_openVoxel_subset_interior P hr (M n)
      rw [← hm n (hrot n),motionOfSlot_open_iff]
      simpa only [probeValue_eq hx] using hboth.2
  · intro a
    obtain ⟨m,hmemb⟩ := aeCover_covers_everywhere P hp M hcover (probe a)
    refine ⟨f m,placed_probe_cell_mem P hp (M m) a hmemb,hactive m,?_⟩
    have hh := (motionOfSlot_closed_iff x P (f m) (hrot m) (probe a)).mp
      (by simpa only [hm] using hmemb)
    simpa only [probeValue_eq hx] using hh

 theorem motionTiles_iff_model (P : Tile d) (ar af : Bool) :
    MotionTiles P ar af ↔ ∃ x : Assignment, Model ar af P x :=
  ⟨MotionTiles.model,fun ⟨_,h⟩ => h.realizes⟩
end
end TranslationTiling.EuclideanMembership
