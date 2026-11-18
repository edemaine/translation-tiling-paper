import TranslationTiling.Compiler.SmallTileChecked

namespace TranslationTiling.Compiler.SmallTile
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

def torusPattern (k code : ℕ) (x y : ZMod k) : Letter :=
  digit code (@ZMod.val k x+k*@ZMod.val k y)

theorem torus_edges {H V k code : ℕ} [NeZero k] (hk : 2≤k)
    (hc : torusOK H V k code=true) (x y : ZMod k) :
    edge H (torusPattern k code x y) (torusPattern k code (x+1) y)=true ∧
    edge V (torusPattern k code x y) (torusPattern k code x (y+1))=true := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hc (@ZMod.val k y)
    (List.mem_range.mpr (ZMod.val_lt y))) (@ZMod.val k x) (List.mem_range.mpr (ZMod.val_lt x))
  have h1 : (1 : ZMod k).val=1 := by
    rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by omega : 1<k)]
  simpa only [torusPattern,ZMod.val_add,h1,Bool.and_eq_true] using hh

theorem accepted_plane {H V : ℕ} (hc : Accepted H V) :
    ∃ a : ℤ×ℤ → Letter, ∀ p,
      edge H (a p) (a (p.1+1,p.2))=true ∧
      edge V (a p) (a (p.1,p.2+1))=true := by
  obtain ⟨b,c,hc⟩ := hc
  let k := if b then 3 else 2
  have hk : 2≤k := by dsimp [k]; split_ifs <;> decide
  letI : NeZero k := ⟨by omega⟩
  refine ⟨fun p => torusPattern k c.val (p.1 : ZMod k) (p.2 : ZMod k),fun p => ?_⟩
  simpa only [Int.cast_add,Int.cast_one] using torus_edges hk hc (p.1 : ZMod k) (p.2 : ZMod k)

def matching (f g : Letter → ℕ) : Matrix := fun a b => decide (f a=g b)

theorem matching_rectangular (f g : Letter → ℕ) : Rectangular (matching f g) := by
  intro a b c d ha hb
  have he : f a=f b := (of_decide_eq_true ha).trans (of_decide_eq_true hb).symm
  simp only [matching,he]

def horizontal (t : Letter → LeanWang.WangTile) : Matrix := matching (fun i => (t i).e) (fun i => (t i).w)
def verticalMatrix (t : Letter → LeanWang.WangTile) : Matrix := matching (fun i => (t i).n) (fun i => (t i).s)

theorem matrix_patch_accepted {r s : Matrix} (hr : Rectangular r) (hs : Rectangular s)
    {a : Fin 4 → Fin 4 → Letter}
    (hH : ∀ y : Fin 4, ∀ x : Fin 3, r (a y ⟨x.val,by omega⟩) (a y ⟨x.val+1,by omega⟩)=true)
    (hV : ∀ y : Fin 3, ∀ x : Fin 4, s (a ⟨y.val,by omega⟩ x) (a ⟨y.val+1,by omega⟩ x)=true) :
    Accepted (matrixCode r) (matrixCode s) := by
  obtain ⟨c,hc⟩ := exists_certificate (matrixCode_mem r hr) (matrixCode_mem s hs)
  apply accepted_of_certificate (a:=a) (c:=c) ?_ hc
  constructor
  · intro y x; rw [matrixCode_edge]; exact hH y x
  · intro y x; rw [matrixCode_edge]; exact hV y x

end TranslationTiling.Compiler.SmallTile
