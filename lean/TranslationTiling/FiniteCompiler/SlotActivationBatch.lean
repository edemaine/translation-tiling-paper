import TranslationTiling.FiniteCompiler.SharedActivationBatch

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I) (S : Finset I)
variable {Y J : Type*} [AddCommGroup Y]

def slotActivationSource (h : Plane) (x : Base L) : Base L :=
  (x.1-h, fun i => if i ∈ S then x.2 i - (h.1 : Low L i) else x.2 i)

/-- One batch fixes the square-coordinate offset of each selected slot and
leaves the high coordinate free in every other row. -/
def SlotActivationBatch (ψ : Factor L →+ Y) (h : Plane) (e : Y) (v : Ambient L) : Prop :=
  v.1 = h ∧ ψ v.2 = e ∧
    (∀ i ∈ S, (v.2.2 i).1.1 = (h.1 : Square L i)) ∧
    (∀ i ∉ S, CyclicShear.low (L.lowSize i) (v.2.2 i).1.1 = 0)

omit [Fintype I] in
theorem sub_point_slotActivationBatch (ψ : Factor L →+ Y) (h : Plane) (e : Y)
    (o : Outputs L) (v : Ambient L) (x : Base L) :
    SlotActivationBatch L S ψ h e (v-point L o x) ↔
      let y := baseProjection L v
      slotActivationSource L S h y = x ∧
      ψ (point L o x).2 + e = ψ v.2 ∧
      ∀ i ∈ S, o.high x i = highCoordinate L i v := by
  let y := baseProjection L v
  have sq (i : I) : ((v-point L o x).2.2 i).1.1 =
      (v.2.2 i).1.1 - CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i) := rfl
  have low (i : I) : CyclicShear.low (L.lowSize i) ((v-point L o x).2.2 i).1.1 =
      y.2 i - x.2 i := by rw [sq,map_sub,CyclicShear.low_shear]; rfl
  have sh (he : v.1-h = x.1) (i : I) (hi : y.2 i - (h.1 : Low L i) = x.2 i) :
      ((v-point L o x).2.2 i).1.1 = (h.1 : Square L i) ↔
      o.high x i = highCoordinate L i v := by
    have hp : y.1.1 - h.1 = x.1.1 := congrArg Prod.fst he
    have hs := CyclicShear.shear_source_add (L.lowSize i) y.1.1 h.1 (y.2 i)
      (h.1 : Low L i) (o.high x i) rfl
    rw [hp,hi] at hs
    rw [sq,sub_eq_iff_eq_add,add_comm (h.1 : Square L i) _, hs, ← shear_highCoordinate L i v]
    exact (CyclicShear.shear_injective (L.lowSize i) y.1.1 (y.2 i)).eq_iff.trans eq_comm
  constructor
  · rintro ⟨hh,hp,hs,ho⟩
    have he : v.1-h = x.1 := by
      change v.1 - x.1 = h at hh
      rw [sub_eq_iff_eq_add,add_comm,← sub_eq_iff_eq_add] at hh
      exact hh
    have hi (i : I) (hi : i ∈ S) : y.2 i - (h.1 : Low L i) = x.2 i := by
      have hf := congrArg (CyclicShear.low (L.lowSize i)) (hs i hi)
      rw [low] at hf
      have hcast : CyclicShear.low (L.lowSize i) (h.1 : Square L i) = (h.1 : Low L i) := by
        simp [CyclicShear.low]
      rw [hcast] at hf
      rwa [sub_eq_iff_eq_add,add_comm,← sub_eq_iff_eq_add] at hf
    refine ⟨Prod.ext he (funext fun i => ?_), ?_,fun i h => (sh he i (hi i h)).mp (hs i h)⟩
    · by_cases h : i ∈ S
      · exact ite_eq_left h |>.trans (hi i h)
      · exact ite_eq_right h |>.trans (sub_eq_zero.mp ((low i).symm.trans (ho i h)))
    · change ψ (v.2-(point L o x).2) = e at hp
      rw [map_sub,sub_eq_iff_eq_add,add_comm] at hp
      exact hp.symm
  · rintro ⟨hx,hp,hs⟩
    have he : v.1-h = x.1 := congrArg Prod.fst hx
    refine ⟨?_,?_,?_,?_⟩
    · change v.1 - x.1 = h
      rw [← he,sub_sub_cancel]
    · change ψ (v.2-(point L o x).2) = e
      rw [map_sub,← hp,add_sub_cancel_left]
    · intro i hi
      apply (sh he i ?_).mpr (hs i hi)
      have h := congrFun (congrArg Prod.snd hx) i
      simpa only [slotActivationSource,ite_eq_left hi] using h
    · intro i hi
      have h := congrFun (congrArg Prod.snd hx) i
      rw [low,sub_eq_zero]
      simpa only [slotActivationSource,ite_eq_right hi] using h

def slotActivationTile (ψ : Factor L →+ Y) [Fintype (Factor L)] [Fintype J]
    (h : J → Plane) (e : J → Y) : Finset (Ambient L) :=
  Finset.univ.biUnion fun j : J =>
    (Finset.univ.map ⟨fun a : Factor L => (h j,a), fun _ _ hh => congrArg Prod.snd hh⟩).filter
      (SlotActivationBatch L S ψ (h j) (e j))

theorem slotActivationTile_iff (ψ : Factor L →+ Y) [Fintype (Factor L)] [Fintype J]
    (h : J → Plane) (hh : Function.Injective h) (e : J → Y) (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ y : Y × (∀ i : {i : I // i ∈ S}, Low L i), ∃ v : Ambient L,
      baseProjection L v = x ∧ (ψ v.2,fun i : {i : I // i ∈ S} => highCoordinate L i v) = y) :
    Tiles (slotActivationTile L S ψ h e) (Set.range (point L o)) ↔
      ∀ x, Function.Bijective (fun j =>
        let u := slotActivationSource L S (h j) x
        (ψ (point L o u).2 + e j, fun i : {i : I // i ∈ S} => o.high u i)) := by
  let tgt (v : Ambient L) := (ψ v.2,fun i : {i : I // i ∈ S} => highCoordinate L i v)
  refine tiles_indexed_activation_iff _ _ (point_injective L o) (baseProjection L) tgt
    (fun x j => slotActivationSource L S (h j) x) (fun x a b he => hh ?_) _ htarget ?_
  · exact sub_right_inj.mp (congrArg Prod.fst he)
  · intro v x
    have hm (f : Ambient L) : f ∈ slotActivationTile L S ψ h e ↔
        ∃ j, SlotActivationBatch L S ψ (h j) (e j) f := by
      simp only [slotActivationTile,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,
        Finset.mem_map]
      constructor
      · rintro ⟨j,_,hj⟩
        exact ⟨j,hj⟩
      · rintro ⟨j,hj⟩
        exact ⟨j,⟨f.2,Prod.ext hj.1.symm rfl⟩,hj⟩
    rw [hm]
    apply exists_congr
    intro j
    rw [sub_point_slotActivationBatch]
    constructor
    · rintro ⟨rfl,h₁,h₂⟩
      exact ⟨rfl,Prod.ext h₁ (funext fun i => h₂ i i.property)⟩
    · rintro ⟨rfl,h⟩
      exact ⟨rfl,congrArg Prod.fst h,fun i hi => congrFun (congrArg Prod.snd h) ⟨i,hi⟩⟩

end

end TranslationTiling.FiniteCompiler.SharedCoordinates
