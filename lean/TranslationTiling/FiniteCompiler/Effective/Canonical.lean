import TranslationTiling.Compiler.EffectiveStacking
import TranslationTiling.Compiler.EffectiveLists

/-! # Canonical finite tile families

A common finite coordinate box supplies a canonical ordering for each tile.
Removing duplicate canonical lists then gives exactly the number of distinct
mathematical test tiles, as required by the optimized stacking bound.
-/

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A numerical box of horizontal radius `H` and cyclic modulus `N`. -/
def pointUniverse (H N : ℕ) : List CyclicPoint :=
  (List.range (2 * H + 1)).flatMap fun (x : ℕ) =>
    (List.range (2 * H + 1)).flatMap fun (y : ℕ) =>
      (List.range N).map fun (z : ℕ) => (((x : ℤ) - H, (y : ℤ) - H), z)

theorem pointUniverse_primrec : Primrec (fun d : ℕ × ℕ => pointUniverse d.1 d.2) := by
  unfold pointUniverse
  fun_prop

theorem mem_pointUniverse (H N : ℕ) (f : CyclicPoint) :
    f ∈ pointUniverse H N ↔
      (-(H : ℤ) ≤ f.1.1 ∧ f.1.1 ≤ H) ∧
      (-(H : ℤ) ≤ f.1.2 ∧ f.1.2 ≤ H) ∧ f.2 < N := by
  simp only [pointUniverse, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x,hx,y,hy,z,hz,rfl⟩
    constructor
    · constructor <;> dsimp only <;> omega
    constructor
    · constructor <;> dsimp only <;> omega
    · exact hz
  · rintro ⟨hx,hy,hz⟩
    refine ⟨(f.1.1 + H).toNat,?_,(f.1.2 + H).toNat,?_,f.2,hz,?_⟩
    · omega
    · omega
    · apply Prod.ext
      · apply Prod.ext <;> dsimp only <;> omega
      · rfl

def normalizeCyclic (N : ℕ) (F : CyclicTile) : CyclicTile :=
  F.map fun f => (f.1,f.2 % N)

def canonicalTile (H N : ℕ) (F : CyclicTile) : CyclicTile :=
  (pointUniverse H N).filter fun f => decide (f ∈ normalizeCyclic N F)

theorem normalizeCyclic_primrec : Primrec (fun d : ℕ × CyclicTile => normalizeCyclic d.1 d.2) := by
  unfold normalizeCyclic
  fun_prop

theorem canonicalTile_primrec : Primrec (fun d : (ℕ × ℕ) × CyclicTile =>
    canonicalTile d.1.1 d.1.2 d.2) := by
  unfold canonicalTile
  apply filterList (pointUniverse_primrec.comp Primrec.fst)
  have hp : Primrec (fun d : ((ℕ × ℕ) × CyclicTile) × CyclicPoint =>
      (d.1.1.2,d.1.2)) := by fun_prop
  have hn : Primrec (fun d : ((ℕ × ℕ) × CyclicTile) × CyclicPoint =>
      normalizeCyclic d.1.1.2 d.1.2) := normalizeCyclic_primrec.comp hp
  exact memberList Primrec.snd hn

theorem canonicalTile_mem_bound (H N : ℕ) (F : CyclicTile) {f : CyclicPoint}
    (hf : f ∈ canonicalTile H N F) : f.2 < N :=
  ((mem_pointUniverse H N f).mp (List.mem_filter.mp hf).1).2.2

theorem cyclicPoint_injective_bounded {N : ℕ} {f g : CyclicPoint}
    (hf : f.2 < N) (hg : g.2 < N) (he : cyclicPoint N f = cyclicPoint N g) : f = g := by
  have hxy := congrArg Prod.fst he
  have hz := congrArg (fun p : Plane × ZMod N => p.2.val) he
  simp only [cyclicPoint, ZMod.val_natCast, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hg] at hz
  exact Prod.ext hxy hz

theorem canonicalTile_eq_of_image_eq (H N : ℕ) (F G : CyclicTile)
    (he : cyclicTileSet N (canonicalTile H N F) = cyclicTileSet N (canonicalTile H N G)) :
    canonicalTile H N F = canonicalTile H N G := by
  apply List.filter_congr
  intro f hf
  apply decide_eq_decide.mpr
  constructor
  · intro hF
    have hmemF : f ∈ canonicalTile H N F := List.mem_filter.mpr ⟨hf,decide_eq_true hF⟩
    have him : cyclicPoint N f ∈ cyclicTileSet N (canonicalTile H N G) := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hmemF,rfl⟩
    obtain ⟨g,hg,hgf⟩ := Finset.mem_image.mp him
    have hg' := List.mem_toFinset.mp hg
    have hfg := cyclicPoint_injective_bounded (canonicalTile_mem_bound H N _ hg')
      ((mem_pointUniverse H N f).mp hf).2.2 hgf
    subst g
    exact of_decide_eq_true (List.mem_filter.mp hg').2
  · intro hG
    have hmemG : f ∈ canonicalTile H N G := List.mem_filter.mpr ⟨hf,decide_eq_true hG⟩
    have him : cyclicPoint N f ∈ cyclicTileSet N (canonicalTile H N F) := by
      rw [he]
      exact Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hmemG,rfl⟩
    obtain ⟨g,hg,hgf⟩ := Finset.mem_image.mp him
    have hg' := List.mem_toFinset.mp hg
    have hfg := cyclicPoint_injective_bounded (canonicalTile_mem_bound H N _ hg')
      ((mem_pointUniverse H N f).mp hf).2.2 hgf
    subst g
    exact of_decide_eq_true (List.mem_filter.mp hg').2

/-- Canonicalization preserves a tile whose horizontal support lies in the box. -/
theorem canonicalTile_correct (H N : ℕ) (hN : 0 < N) (F : CyclicTile)
    (hb : ∀ f ∈ F, (-(H : ℤ) ≤ f.1.1 ∧ f.1.1 ≤ H) ∧
      (-(H : ℤ) ≤ f.1.2 ∧ f.1.2 ≤ H)) :
    cyclicTileSet N (canonicalTile H N F) = cyclicTileSet N F := by
  ext p
  constructor
  · intro hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hp
    have hn := of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hf)).2
    obtain ⟨g,hg,hgf⟩ := List.mem_map.mp hn
    subst f
    refine Finset.mem_image.mpr ⟨g,List.mem_toFinset.mpr hg,?_⟩
    simp [cyclicPoint, ZMod.natCast_mod]
  · intro hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hp
    have hf' := List.mem_toFinset.mp hf
    refine Finset.mem_image.mpr ⟨(f.1,f.2 % N),List.mem_toFinset.mpr ?_,?_⟩
    · apply List.mem_filter.mpr
      refine ⟨(mem_pointUniverse H N _).mpr ⟨(hb f hf').1,(hb f hf').2,Nat.mod_lt _ hN⟩,?_⟩
      exact decide_eq_true (List.mem_map.mpr ⟨f,hf',rfl⟩)
    · simp [cyclicPoint, ZMod.natCast_mod]

def canonicalFamily (H N : ℕ) (Fs : List CyclicTile) : List CyclicTile :=
  (Fs.map (canonicalTile H N)).dedup

theorem canonicalFamily_primrec : Primrec (fun d : (ℕ × ℕ) × List CyclicTile =>
    canonicalFamily d.1.1 d.1.2 d.2) := by
  unfold canonicalFamily
  have hp : Primrec (fun z : ((ℕ × ℕ) × List CyclicTile) × CyclicTile =>
      (z.1.1,z.2)) := by fun_prop
  have hm : Primrec (fun d : (ℕ × ℕ) × List CyclicTile =>
      d.2.map (canonicalTile d.1.1 d.1.2)) :=
    mapList Primrec.snd (canonicalTile_primrec.comp hp)
  exact dedup_primrec.comp hm

/-- Duplicate descriptions have no cost in the optimized family count. -/
theorem canonicalFamily_length (H N : ℕ) (Fs : List CyclicTile) :
    (canonicalFamily H N Fs).length =
      ((canonicalFamily H N Fs).toFinset.image (cyclicTileSet N)).card := by
  rw [Finset.card_image_iff.mpr ?_]
  · exact (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm
  · intro F hF G hG he
    obtain ⟨F',hF',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp (List.mem_toFinset.mp hF))
    obtain ⟨G',hG',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp (List.mem_toFinset.mp hG))
    exact canonicalTile_eq_of_image_eq H N F' G' he

end TranslationTiling.FiniteCompiler.Effective
