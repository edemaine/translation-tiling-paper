import TranslationTiling.Compiler.EffectiveLattice
import TranslationTiling.Compiler.ClosedGeometryBound
import TranslationTiling.Rails.Strips

namespace TranslationTiling.Compiler.StripLift
open Rails Rails.Strips
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The horizontal supports of the cyclic test tiles. -/
def TestSupport (H : ℕ) (p : Plane) : Prop :=
  p.1.natAbs≤H ∧ (p.2.natAbs≤175 ∨ ∃ s : ℕ, s≤16 ∧ p.2=-(s:ℤ)*p.1)

def TestSupportAt (M : ℕ) (H : ℕ → ℕ) (p : Plane) : Prop :=
  (p.1.natAbs≤H 0 ∧ p.2.natAbs≤M) ∨
    ∃ s : ℕ, s<17 ∧ p.1.natAbs≤H s ∧ p.2=-(s:ℤ)*p.1

private theorem difference_slots (M : ℕ) (H : ℕ → ℕ) (p : Plane) (hp : TestSupportAt M H p)
    (a b : ℤ) (ha : a.natAbs≤465) (hb : b.natAbs≤400) :
    Rails.point (201*p.1+a) (201*p.2+b) 0 ∈ slotsAt M H ∧
    Rails.point (-(201*p.1+a)) (-(201*p.2+b)) 0 ∈ slotsAt M H := by
  have hx (s : ℕ) (hp0 : p.1.natAbs≤H s) : (201*p.1+a).natAbs≤radius (H s) := by
    apply (Int.natAbs_add_le _ _).trans
    rw [Int.natAbs_mul]
    change 201*p.1.natAbs+a.natAbs≤_
    unfold radius
    omega
  have hb' : ∃ (s : ℕ), s<17 ∧ p.1.natAbs≤H s ∧ (201*p.2+b+(s:ℤ)*(201*p.1+a)).natAbs≤widthAt M s := by
    rcases hp with ⟨hx0,hh⟩ | ⟨s,hs,hx0,he⟩
    · refine ⟨0,by decide,hx0,?_⟩
      simp only [Nat.cast_zero,zero_mul,add_zero,widthAt,if_pos rfl]
      apply (Int.natAbs_add_le _ _).trans
      rw [Int.natAbs_mul]
      change 201*p.2.natAbs+b.natAbs≤201*M+400
      omega
    · by_cases hz : s=0
      · subst s
        refine ⟨0,by decide,hx0,?_⟩
        simp [he,widthAt]
        omega
      · refine ⟨s,hs,hx0,?_⟩
        rw [he,show 201*(-(s:ℤ)*p.1)+b+(s:ℤ)*(201*p.1+a)=b+(s:ℤ)*a by ring]
        apply (Int.natAbs_add_le _ _).trans
        rw [Int.natAbs_mul,Int.natAbs_natCast,widthAt,if_neg hz]
        exact Nat.add_le_add hb (Nat.mul_le_mul_left _ ha) |>.trans_eq (by ring)
  obtain ⟨s,hs,hx0,hb'⟩ := hb'
  constructor
  · exact (mem_slotsAt M H _).mpr ⟨s,hs,rfl,hx s hx0,hb'⟩
  · apply (mem_slotsAt M H _).mpr
    refine ⟨s,hs,rfl,?_,?_⟩
    · change (-(201*p.1+a)).natAbs≤radius (H s)
      rw [Int.natAbs_neg]
      exact hx s hx0
    · change (-(201*p.2+b)+(s:ℤ)*(-(201*p.1+a))).natAbs≤widthAt M s
      rw [show -(201*p.2+b)+(s:ℤ)*(-(201*p.1+a))=
        -(201*p.2+b+(s:ℤ)*(201*p.1+a)) by ring,Int.natAbs_neg]
      exact hb'

private theorem component_coords (Q j : ℕ) (hj : j≤5) {v : Lattice 3}
    (hv : v∈MSS.component Q j) :
    (v 0).natAbs≤400 ∧ (v 1).natAbs≤400 ∧
      ∃ b : ℕ, b≤1 ∧ (v 2-201*(b:ℤ)*Q).natAbs≤400 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · have hb := (Finset.mem_sdiff.mp hv).1
    exact ⟨Size.mss_base_coordinate_bound hb 0,Size.mss_base_coordinate_bound hb 1,
      0,by decide,by simpa using Size.mss_base_coordinate_bound hb 2⟩
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hb := (MSS.mem_box_iff j u).mp (Finset.mem_sdiff.mp hu).1
    refine ⟨?_,?_,1,by decide,?_⟩
    · have h := hb 0
      simp [MSS.kernelStep,MSS.marker] at h ⊢
      omega
    · have h := hb 1
      simp [MSS.kernelStep,MSS.marker] at h ⊢
      omega
    · have h := hb 2
      simp [MSS.kernelStep,MSS.marker] at h ⊢
      omega

private theorem frame_anchor (Q j : ℕ) (hj : 0<j) :
    Rails.point (13*j) 0 (201*Q) ∈ MSS.component Q j := by
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨Pi.single 0 (j:ℤ),MSS.axis_frame_vertex j hj,?_⟩
  ext i
  fin_cases i <;> simp [Rails.point,MSS.kernelStep,MSS.marker] <;> ring

private def lifted (d : CyclicTileData) : Finset (Lattice 3) :=
  CyclicQuotient.representatives d.1
    ((cyclicTileSet d.1 d.2).image (fun f => f-cyclicPoint d.1 (d.2.headD ((0,0),0))))

private theorem integer_mem (d : CyclicTileData) (hQ : 0<d.1) (v : Lattice 3) :
    v∈integerTile d ↔ v∈LatticeGeometry.assembled d.1 (lifted d) := by
  rw [←List.mem_toFinset,integerTile_toFinset,latticeRepresentatives_toFinset d.1 hQ]
  rfl

private theorem lifted_coords (d : CyclicTileData) (hQ : 0<d.1) {u : Lattice 3}
    (hu : u∈lifted d) :
    ∃ f∈d.2, u 0=f.1.1-(d.2.headD ((0,0),0)).1.1 ∧
      u 1=f.1.2-(d.2.headD ((0,0),0)).1.2 ∧ 0≤u 2 ∧ u 2<d.1 := by
  letI : NeZero d.1 := ⟨hQ.ne'⟩
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
  let y := ((cyclicPoint d.1 f - cyclicPoint d.1 (d.2.headD ((0,0),0))).2).val
  refine ⟨f,List.mem_toFinset.mp hf,rfl,rfl,?_,?_⟩
  · change 0≤(y:ℤ)
    positivity
  · change (y:ℤ)<d.1
    exact_mod_cast ZMod.val_lt ((cyclicPoint d.1 f - cyclicPoint d.1 (d.2.headD ((0,0),0))).2)

private theorem progression (d : CyclicTileData) (U : ℕ) (hU : 0<U) (hQ : 0<d.1)
    (hc : HasColumn d U) :
    ∃ s : ℕ, s<U ∧ ∀ z : ℕ, z<d.1 → z%U=s →
      Rails.point (-(d.2.headD ((0,0),0)).1.1) (-(d.2.headD ((0,0),0)).1.2) z∈lifted d := by
  letI : NeZero d.1 := ⟨hQ.ne'⟩
  obtain ⟨c,hc⟩ := hc
  let f₀ := cyclicPoint d.1 (d.2.headD ((0,0),0))
  let t := (c-f₀.2).val
  refine ⟨t%U,Nat.mod_lt _ hU,fun z hz hr => ?_⟩
  have he₀ : (z:ℤ)=(t:ℤ)+(U:ℤ)*((z/U:ℕ)-(t/U:ℕ) : ℤ) := by
    have hz' : ((z%U:ℕ):ℤ)+(U:ℤ)*(z/U:ℕ)=z := by exact_mod_cast Nat.mod_add_div z U
    have ht' : ((t%U:ℕ):ℤ)+(U:ℤ)*(t/U:ℕ)=t := by exact_mod_cast Nat.mod_add_div t U
    rw [hr] at hz'
    rw [mul_sub]
    linarith
  let k : ℤ := (z/U:ℕ)-(t/U:ℕ)
  have hcast : (z:ZMod d.1)=c-f₀.2+((U:ℤ)*k : ℤ) := by
    have he := congrArg (fun x : ℤ => (x:ZMod d.1)) he₀
    simpa only [Int.cast_natCast,Int.cast_add,ZMod.natCast_zmod_val,t,k] using he
  have hmem : ((0:Plane),c+((U:ℤ)*k:ℤ))-f₀ ∈
      (cyclicTileSet d.1 d.2).image (fun f => f-f₀) := Finset.mem_image.mpr ⟨_,hc k,rfl⟩
  have hm : CyclicQuotient.lift d.1 (((0:Plane),c+((U:ℤ)*k:ℤ))-f₀)∈lifted d :=
    CyclicQuotient.lift_mem_representatives d.1 hmem
  have hmod : (c+((U:ℤ)*k:ℤ)-f₀.2 : ZMod d.1)=(z:ZMod d.1) := by rw [hcast]; abel
  have he : CyclicQuotient.lift d.1 (((0:Plane),c+((U:ℤ)*k:ℤ))-f₀)=
      Rails.point (-(d.2.headD ((0,0),0)).1.1) (-(d.2.headD ((0,0),0)).1.2) z := by
    ext i
    fin_cases i
    · change 0-(d.2.headD ((0,0),0)).1.1=_
      simp [Rails.point]
    · change 0-(d.2.headD ((0,0),0)).1.2=_
      simp [Rails.point]
    · change (((c+((U:ℤ)*k:ℤ)-f₀.2 : ZMod d.1).val:ℕ):ℤ)=(z:ℤ)
      rw [hmod,ZMod.val_natCast,Nat.mod_eq_of_lt hz]
  rwa [he] at hm

theorem connectedAt (d : CyclicTileData) (M : ℕ) (H : ℕ → ℕ) (U : ℕ)
    (hQ : 0<d.1) (count : ℕ) (hcount : 0<count) (sampleHeight : Fin count → ℕ)
    (hheight : ∀ k, sampleHeight k<2*d.1)
    (hsample : ∀ k, Rails.point (-(d.2.headD ((0,0),0)).1.1)
        (-(d.2.headD ((0,0),0)).1.2) (sampleHeight k%d.1:ℕ)∈lifted d)
    (hgap : ∀ k l, l.val=k.val+1 → ((sampleHeight l:ℤ)-sampleHeight k).natAbs≤U)
    (hnear : ∀ z<2*d.1, ∃ k, ((sampleHeight k:ℤ)-z).natAbs≤U)
    (hsup : ∀ f∈d.2, TestSupportAt M H f.1) :
    FaceConnected (SlotAssembly.assemble (integerTile d) (slotsAt M H) (railHeight U)) := by
  let E := integerTile d
  let head := d.2.headD ((0,0),0)
  have anchor (k : Fin count) :
      ∃ v∈E, (v 0+201*head.1.1).natAbs≤65 ∧ v 1= -201*head.1.2 ∧
        v 2=201*(sampleHeight k:ℤ) := by
    by_cases hlo : sampleHeight k<d.1
    · let u := Rails.point (-head.1.1) (-head.1.2) (sampleHeight k%d.1:ℕ)
      refine ⟨LatticeGeometry.scaleHom u,(integer_mem d hQ _).mpr ?_,?_⟩
      · exact (LatticeGeometry.mem_assembled _ _ _).mpr
          ⟨u,hsample k,0,LatticeGeometry.zero_mem_part _ _,by simp⟩
      · change (201*(-head.1.1)+201*head.1.1).natAbs≤65 ∧
          201*(-head.1.2)= -201*head.1.2 ∧ 201*((sampleHeight k%d.1:ℕ):ℤ)=_
        rw [Nat.mod_eq_of_lt hlo]
        constructor
        · rw [show 201*(-head.1.1)+201*head.1.1=0 by ring]
          decide
        · constructor <;> ring
    · let u := Rails.point (-head.1.1) (-head.1.2) (sampleHeight k%d.1:ℕ)
      let j : ℕ := if u=0 then 5 else 4
      have hj : 0<j ∧ j≤5 := by dsimp [j]; split <;> decide
      let v := Rails.point (13*(j:ℤ)) 0 (201*(d.1:ℤ))
      have hv : v∈LatticeGeometry.part d.1 u := by
        have hh := frame_anchor d.1 j hj.1
        by_cases hu0 : u=0 <;> simpa [LatticeGeometry.part,j,v,hu0] using hh
      refine ⟨LatticeGeometry.scaleHom u+v,(integer_mem d hQ _).mpr ?_,?_⟩
      · exact (LatticeGeometry.mem_assembled _ _ _).mpr ⟨u,hsample k,v,hv,rfl⟩
      · change (201*(-head.1.1)+13*(j:ℤ)+201*head.1.1).natAbs≤65 ∧
          201*(-head.1.2)+0= -201*head.1.2 ∧
            201*((sampleHeight k%d.1:ℕ):ℤ)+201*d.1=_
        have hz : sampleHeight k%d.1+d.1=sampleHeight k := by
          have hdiv : sampleHeight k/d.1=1 := by
            apply Nat.div_eq_of_lt_le <;> have := hheight k <;> omega
          simpa [hdiv] using Nat.mod_add_div (sampleHeight k) d.1
        have hz' : ((sampleHeight k%d.1:ℕ):ℤ)+d.1=sampleHeight k := by exact_mod_cast hz
        constructor
        · rw [show 201*(-head.1.1)+13*(j:ℤ)+201*head.1.1=13*(j:ℤ) by ring,
            Int.natAbs_mul,Int.natAbs_natCast]
          change 13*j≤65
          omega
        · constructor
          · ring
          · linarith only [hz']
  let a (k : Fin count) : Lattice 3 := (anchor k).choose
  have ha (k : Fin count) := (anchor k).choose_spec
  let Rel (u v : Lattice 3) :=
    u∈E ∧ v∈E ∧ SlotAssembly.Hop (slotsAt M H) (railHeight U) u v
  have step_to_anchor {u : Lattice 3} (hu : u∈E) (k : Fin count)
      (hxy : ∃ p : Plane, TestSupportAt M H p ∧
        (u 0-a k 0-201*p.1).natAbs≤465 ∧ (u 1-a k 1-201*p.2).natAbs≤400)
      (hz : (a k 2-u 2).natAbs≤railHeight U) : Rel u (a k) := by
    obtain ⟨p,hp,hx,hy⟩ := hxy
    obtain ⟨hd,hd'⟩ := difference_slots M H p hp _ _ hx hy
    have hdx : 201*p.1+(u 0-a k 0-201*p.1)=u 0-a k 0 := by ring
    have hdy : 201*p.2+(u 1-a k 1-201*p.2)=u 1-a k 1 := by ring
    rw [hdx,hdy] at hd hd'
    have ex : -(u 0-a k 0)=a k 0-u 0 := by ring
    have ey : -(u 1-a k 1)=a k 1-u 1 := by ring
    rw [ex,ey] at hd'
    exact ⟨hu,(ha k).1,hz,hd,hd'⟩
  have anchor_step (k l : Fin count) (hkl : l.val=k.val+1) : Rel (a k) (a l) := by
    have hk := ha k
    have hl := ha l
    change a k∈E ∧ (a k 0+201*head.1.1).natAbs≤65 ∧ a k 1= -201*head.1.2 ∧
      a k 2=201*(sampleHeight k:ℤ) at hk
    change a l∈E ∧ (a l 0+201*head.1.1).natAbs≤65 ∧ a l 1= -201*head.1.2 ∧
      a l 2=201*(sampleHeight l:ℤ) at hl
    apply step_to_anchor hk.1 l
    · refine ⟨(0,0),by simp [TestSupportAt],?_⟩
      change (a k 0-a l 0-201*0).natAbs≤465 ∧ (a k 1-a l 1-201*0).natAbs≤400
      exact ⟨by have := hk.2.1; have := hl.2.1; omega,by rw [hk.2.2.1,hl.2.2.1]; omega⟩
    · rw [hl.2.2.2,hk.2.2.2,←mul_sub,Int.natAbs_mul]
      exact (Nat.mul_le_mul_left 201 (hgap k l hkl)).trans (by simp [railHeight])
  have attach {v : Lattice 3} (hv : v∈E) : ∃ k, Rel v (a k) := by
    obtain ⟨u,hu,w,hw,rfl⟩ := (LatticeGeometry.mem_assembled _ _ _).mp ((integer_mem d hQ v).mp hv)
    obtain ⟨f,hf,hx,hy,hz,hz'⟩ := lifted_coords d hQ hu
    let j : ℕ := if u=0 then 5 else 4
    have hw' : w∈MSS.component d.1 j := by
      by_cases hu0 : u=0 <;> simpa [LatticeGeometry.part,j,hu0] using hw
    have hj : j≤5 := by dsimp [j]; split <;> decide
    obtain ⟨h0,h1,b,hb,h2⟩ := component_coords d.1 j hj hw'
    let z : ℕ := (u 2).toNat+b*d.1
    have hzcast : (z:ℤ)=u 2+(b:ℤ)*d.1 := by simp [z,Int.toNat_of_nonneg hz]
    have hzlt : z<2*d.1 := by
      have hb' : b=0 ∨ b=1 := by omega
      rcases hb' with rfl|rfl <;> simp [z] <;> omega
    obtain ⟨k,hkz⟩ := hnear z hzlt
    have hk := ha k
    change a k∈E ∧ (a k 0+201*head.1.1).natAbs≤65 ∧ a k 1= -201*head.1.2 ∧
      a k 2=201*(sampleHeight k:ℤ) at hk
    refine ⟨k,step_to_anchor hv k ?_ ?_⟩
    · refine ⟨f.1,hsup f hf,?_⟩
      change (201*u 0+w 0-a k 0-201*f.1.1).natAbs≤465 ∧
        (201*u 1+w 1-a k 1-201*f.1.2).natAbs≤400
      change u 0=f.1.1-head.1.1 at hx
      change u 1=f.1.2-head.1.2 at hy
      rw [hx,hy,hk.2.2.1]
      exact ⟨by have := hk.2.1; omega,by omega⟩
    · change (a k 2-(201*u 2+w 2)).natAbs≤railHeight U
      rw [hk.2.2.2,show 201*(sampleHeight k:ℤ)-(201*u 2+w 2)=
        201*((sampleHeight k:ℤ)-z)+(201*(b:ℤ)*d.1-w 2) by rw [hzcast]; ring]
      apply (Int.natAbs_add_le _ _).trans
      rw [Int.natAbs_mul,show 201*(b:ℤ)*d.1-w 2=-(w 2-201*(b:ℤ)*d.1) by ring,Int.natAbs_neg]
      rw [show (201:ℤ).natAbs=201 by decide]
      have hm := Nat.mul_le_mul_left 201 hkz
      change 201*((sampleHeight k:ℤ)-(z:ℤ)).natAbs≤201*U at hm
      unfold railHeight
      omega
  apply SlotAssembly.connected _ (validAt M H) E (railHeight U) (pathAt M H)
  change ∀ u∈E, ∀ v∈E, Relation.ReflTransGen Rel u v
  intro u hu v hv
  have hSym : Symmetric Rel := fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩
  have rev {u v : Lattice 3} (h : Relation.ReflTransGen Rel u v) : Relation.ReflTransGen Rel v u := by
    induction h with
    | refl => exact .refl
    | tail _ hh ih => exact (Relation.ReflTransGen.single (hSym hh)).trans ih
  have chain (k : Fin count) : Relation.ReflTransGen Rel (a ⟨0,by omega⟩) (a k) := by
    induction heq : k.val using Nat.strong_induction_on generalizing k with
    | h n ih =>
      by_cases hz : k.val=0
      · have he : k=⟨0,by omega⟩ := Fin.ext hz
        rw [he]
      · let k' : Fin count := ⟨k.val-1,by omega⟩
        have h' : k'.val<n := by dsimp [k']; omega
        exact (ih _ h' k' rfl).tail (anchor_step k' k (by dsimp [k']; omega))
  obtain ⟨k,hk⟩ := attach hu
  obtain ⟨l,hl⟩ := attach hv
  exact (Relation.ReflTransGen.single hk).trans
    ((rev (chain k)).trans ((chain l).trans (Relation.ReflTransGen.single (hSym hl))))


theorem connected (d : CyclicTileData) (H U : ℕ) (hU : 0<U) (hQ : 0<d.1)
    (hdvd : U∣d.1) (hc : HasColumn d U)
    (hsup : ∀ f∈d.2, TestSupport H f.1) :
    FaceConnected (assemble (integerTile d) H U) := by
  obtain ⟨m,hm⟩ := hdvd
  have hmpos : 0<m := by by_contra! hn; simp [show m=0 by omega,hm] at hQ
  obtain ⟨s,hss,hprog⟩ := progression d U hU hQ hc
  let height (k : Fin (2*m)) := s+U*k.val
  have hheight (k : Fin (2*m)) : height k<2*d.1 := by
    dsimp [height]
    have hmul := Nat.mul_le_mul_left U (by omega : k.val+1≤2*m)
    rw [hm]
    nlinarith only [hmul,hss]
  apply connectedAt d 175 (fun _ => H) U hQ (2*m) (by omega) height hheight
  · intro k
    apply hprog
    · exact Nat.mod_lt _ hQ
    · have hd : (height k%d.1)%U=height k%U := Nat.mod_mod_of_dvd _ ⟨m,hm⟩
      rw [hd]
      simp [height,Nat.add_mod,Nat.mod_eq_of_lt hss]
  · intro k l hl
    simp only [height,hl,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    rw [show (s:ℤ)+(U:ℤ)*(k.val+1)-((s:ℤ)+U*k.val)=U by ring,Int.natAbs_natCast]
  · intro z hz
    let k : Fin (2*m) := ⟨z/U,(Nat.div_lt_iff_lt_mul hU).mpr (by rw [hm] at hz; nlinarith)⟩
    refine ⟨k,?_⟩
    have hdiv : ((z%U:ℕ):ℤ)+(U:ℤ)*(z/U:ℕ)=z := by exact_mod_cast Nat.mod_add_div z U
    have hrem := Nat.mod_lt z hU
    change (((s+U*(z/U):ℕ):ℤ)-(z:ℤ)).natAbs≤U
    rw [Nat.cast_add,Nat.cast_mul,show (s:ℤ)+(U:ℤ)*((z/U:ℕ):ℤ)-z=
      (s:ℤ)-((z%U:ℕ):ℤ) by linarith only [hdiv]]
    omega
  · intro f hf
    rcases hsup f hf with ⟨hx,hy|⟨s,hs,he⟩⟩
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr ⟨s,by omega,hx,he⟩

end
end TranslationTiling.Compiler.StripLift
