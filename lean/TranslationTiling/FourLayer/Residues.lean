import TranslationTiling.FourLayer.Rigidity
import TranslationTiling.FourLayer.Rectangle

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def residue (s : Fin 3 → ℕ) (v : Lattice 3) : Lattice 3 := fun i => v i%(s i:ℤ)

def boxFinset (s : Fin 3 → ℕ) : Finset (Lattice 3) :=
  Fintype.piFinset (fun i => Finset.Ico 0 (s i:ℤ))

@[simp] theorem mem_boxFinset (s : Fin 3 → ℕ) (v : Lattice 3) : v∈boxFinset s ↔ Rect s v := by
  simp [boxFinset,Rect]

theorem residue_mem (s : Fin 3 → ℕ) (hs : ∀ i, 0<s i) (v : Lattice 3) : Rect s (residue s v) := by
  intro i
  have hi : (0:ℤ)<s i := by exact_mod_cast hs i
  exact ⟨Int.emod_nonneg _ (ne_of_gt hi),Int.emod_lt_of_pos _ hi⟩

theorem residue_self {s : Fin 3 → ℕ} {v : Lattice 3} (hv : Rect s v) : residue s v=v := by
  ext i
  exact Int.emod_eq_of_lt (hv i).1 (hv i).2

@[simp] theorem residue_grid_add (s : Fin 3 → ℕ) (u v : Lattice 3) :
    residue s (gridMap s u+v)=residue s v := by
  ext i
  simp [residue,gridMap,Int.add_emod]

/-- Choosing one representative of every rectangular residue class gives a
fundamental domain, even when the representatives have been relocated. -/
theorem representatives_fundamental (s : Fin 3 → ℕ) (hs : ∀ i, 0<s i)
    (f : {r : Lattice 3 // Rect s r} → Lattice 3)
    (hf : ∀ r, residue s (f r)=r.val) :
    ExactTiling (Set.range (gridMap s)) (Set.range f) := by
  rw [exactTiling_iff]
  intro x
  let r : {r : Lattice 3 // Rect s r} := ⟨residue s x,residue_mem s hs x⟩
  refine ⟨⟨f r,⟨r,rfl⟩⟩,?_,?_⟩
  · refine ⟨fun i => x i/(s i:ℤ)-(f r) i/(s i:ℤ),?_⟩
    ext i
    have hx := Int.emod_add_ediv_mul (x i) (s i:ℤ)
    have hv := Int.emod_add_ediv_mul ((f r) i) (s i:ℤ)
    have hr := congrFun (hf r) i
    change (f r) i%(s i:ℤ)=x i%(s i:ℤ) at hr
    change (s i:ℤ)*(x i/(s i:ℤ)-(f r) i/(s i:ℤ))=x i-(f r) i
    nlinarith only [hx,hv,hr]
  · intro g hg
    obtain ⟨a,ha⟩ := g.property
    obtain ⟨z,hz⟩ := hg
    have hx : x=gridMap s z+g.val := by rw [hz]; abel
    have hres : residue s g.val=residue s x := by rw [hx,residue_grid_add]
    have he : a=r := by
      apply Subtype.ext
      rw [← hf a]
      change residue s (f a)=residue s x
      rw [ha]
      exact hres
    apply Subtype.ext
    change g.val=f r
    rw [← ha,he]

end
end TranslationTiling.FourLayer
