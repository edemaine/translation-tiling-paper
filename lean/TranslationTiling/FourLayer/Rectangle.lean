import TranslationTiling.Proofs.FacePaths
import TranslationTiling.Proofs.KimGeometry
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Int.Interval

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def Rect (r : Fin 3 → ℕ) (v : Lattice 3) : Prop := ∀ i, 0≤v i ∧ v i<(r i:ℤ)
def Boundary (r : Fin 3 → ℕ) (v : Lattice 3) : Prop :=
  Rect r v ∧ ∃ i, v i=0 ∨ v i=(r i:ℤ)-1

theorem boundary_path_zero (r : Fin 3 → ℕ) (hr : ∀ i, 0<r i) (q : Lattice 3)
    (hq : Boundary r q) : FacePath (Boundary r) q 0 := by
  obtain ⟨hqc,k,hk⟩ := hq
  let P := Boundary r
  let v := Function.update (0 : Lattice 3) k (q k)
  have first : FacePath P q v := by
    apply FacePath.box3 P (Function.update (0 : Lattice 3) k (q k))
      (Function.update (fun j => (r j:ℤ)-1) k (q k)) q v
    · intro j
      by_cases hj : j=k
      · subst j; simp
      · have := hqc j; simp [hj]; omega
    · intro j
      have := hr j
      by_cases hj : j=k
      · subst j; simp [v]
      · simp [v,hj]; omega
    · intro z hz
      refine ⟨?_,k,?_⟩
      · intro j
        have h := hz j
        have := hqc j
        by_cases hj : j=k
        · subst j; simp at h; omega
        · simp [hj] at h; omega
      · have h := hz k
        simp at h
        have he : z k=q k := by omega
        simpa only [he] using hk
  have last : FacePath P v (Function.update v k 0) := by
    apply FacePath.axis
    intro t ht hu
    have hqk := hqc k
    simp [v] at ht hu
    constructor
    · intro j
      have := hr j
      by_cases hj : j=k
      · subst j; simp; omega
      · simp [v,hj]; omega
    · obtain ⟨j,hj⟩ : ∃ j : Fin 3, j≠k := by
        fin_cases k
        · exact ⟨1,by decide⟩
        · exact ⟨0,by decide⟩
        · exact ⟨0,by decide⟩
      exact ⟨j,Or.inl (by simp [v,hj])⟩
  have he : Function.update v k 0=(0 : Lattice 3) := by simp [v,Function.update_idem]
  exact first.trans (he ▸ last)

theorem boundary_connected (r : Fin 3 → ℕ) (hr : ∀ i, 0<r i)
    {v w : Lattice 3} (hv : Boundary r v) (hw : Boundary r w) :
    FacePath (Boundary r) v w :=
  (boundary_path_zero r hr v hv).trans (FacePath.reverse (boundary_path_zero r hr w hw))

theorem boundary_difference {r : Fin 3 → ℕ} {u v : Lattice 3}
    (hu : Rect r u) (hv : Rect r v) (hne : u≠v) :
    ∃ x y, Boundary r x ∧ Boundary r y ∧ u+x=v+y ∧ x≠y := by
  have hu0 := hu 0; have hu1 := hu 1; have hu2 := hu 2
  have hv0 := hv 0; have hv1 := hv 1; have hv2 := hv 2
  let x : Lattice 3 := ![if u 0≤v 0 then (r 0:ℤ)-1 else 0,
    if u 1≤v 1 then v 1-u 1 else (r 1:ℤ)-1+(v 1-u 1),max (v 2-u 2) 0]
  let y : Lattice 3 := x-(v-u)
  have hx : Rect r x := by
    intro k
    fin_cases k <;> simp [x] <;> (try split_ifs) <;> omega
  have hy : Rect r y := by
    intro k
    fin_cases k <;> simp [x,y] <;> (try split_ifs) <;> omega
  have hxb : Boundary r x := by
    refine ⟨hx,0,?_⟩
    simp only [x,Matrix.cons_val_zero]
    split_ifs <;> omega
  have hyb : Boundary r y := by
    refine ⟨hy,1,?_⟩
    simp [x,y]
    split_ifs <;> omega
  have he : u+x=v+y := by dsimp [y]; abel
  refine ⟨x,y,hxb,hyb,he,?_⟩
  intro h
  rw [h] at he
  exact hne (add_right_cancel he)

/-- The neighbor relation in any finite set is a partial matching. -/
theorem exists_matching {m : ℕ} (f : Fin m → Lattice 3) (hf : Function.Injective f) (k : Fin 3) :
    ∃ p : Equiv.Perm (Fin m), ∀ i j, f j=f i+Pi.single k 1 → p j=i := by
  let Edges := {i : Fin m // ∃ j, f j=f i+Pi.single k 1}
  let target (i : Edges) : Fin m := Classical.choose i.property
  have he (i : Edges) : f (target i)=f i.val+Pi.single k 1 := Classical.choose_spec i.property
  have ht : Function.Injective target := by
    intro i j hij
    have h := (he i).symm.trans (congrArg f hij |>.trans (he j))
    exact Subtype.ext (hf (add_right_cancel h))
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair target (fun i : Edges => i.val) ht Subtype.val_injective
  refine ⟨p,fun i j hij => ?_⟩
  let e : Edges := ⟨i,j,hij⟩
  have hh : target e=j := hf ((he e).trans hij.symm)
  simpa only [hh] using hp e

end
end TranslationTiling.FourLayer
