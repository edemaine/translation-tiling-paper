import TranslationTiling.FiniteCompiler.Effective.AxisSlotGuardedDeck
import TranslationTiling.FiniteCompiler.Effective.AxisSlotEncoding

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open PairSmall GuardedCompiler SharedCoordinates Effective Compiler Compiler.Effective
open scoped Classical
noncomputable section

local instance slotDeckFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((axisRadix m w)^k))
local instance slotDeckAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : AxisParameters k m)

private abbrev Mask := Finset (SharedCoordinates.Ambient s.layout)

def markerDeck : List (Mask s) :=
  (Finset.univ : Finset (WangSlot k m × Fin 3)).toList.flatMap fun (i,j) => s.markerTests i j

def fallbackDeck : List (Mask s) :=
  (Finset.univ : Finset (Bool × Fin m × Bool)).toList.flatMap fun (g,i,a) => s.fallbackTests g i a

def activationDeck (hw : w ≤ m) : List (Mask s) :=
  ((Finset.univ : Finset (Bool × Fin k)).toList).flatMap fun (g,d) =>
    ((Finset.univ : Finset {S : Finset (Fin m) // S.card = m+1-w}).toList).map fun S =>
      s.activationTest g d S.val (selected_nonempty hw S.property)

def guardDeck : List (Mask s) :=
  (patterns c).attach.map fun p => s.guardMask c p.val p.property

def seedDeck : List (Mask s) :=
  ((Finset.univ : Finset (Σ _ : Fin 2, Σ i : Fin 18,
      Letter (system c) (arithmeticColumn i))).filter
    fun q => ¬ LetterSeedSet (system c) q.1 (arithmeticColumn q.2.1) q.2.2).toList.map
      fun ⟨t,i,a⟩ => s.seedMask c t i a

def slotDeck (hwm : w ≤ m) : List (Mask s) :=
  productKernel s.layout :: (s.arithmeticTiles ++ s.anchorTests ++ s.markerDeck ++
    s.fallbackDeck ++ s.activationDeck hwm ++ s.seedDeck c ++ s.guardDeck c)

private theorem markerDeck_iff (F : Mask s) :
    F ∈ s.markerDeck ↔ ∃ i j, F ∈ s.markerTests i j := by
  simp only [markerDeck,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,Prod.exists]

private theorem fallbackDeck_iff (F : Mask s) :
    F ∈ s.fallbackDeck ↔ ∃ g i a, F ∈ s.fallbackTests g i a := by
  simp only [fallbackDeck,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,Prod.exists]

private theorem activationDeck_iff (hwm : w ≤ m) (F : Mask s) :
    F ∈ s.activationDeck hwm ↔
      ∃ g, ∃ d, ∃ S : Finset (Fin m), ∃ hS : S.card = m+1-w,
        s.activationTest g d S (selected_nonempty hwm hS) = F := by
  simp only [activationDeck,List.mem_flatMap,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,
    Prod.exists,Subtype.exists]

private theorem seedDeck_iff (F : Mask s) :
    F ∈ s.seedDeck c ↔ ∃ t i a, ¬ LetterSeedSet (system c) t (arithmeticColumn i) a ∧
      s.seedMask c t i a = F := by
  simp only [seedDeck,List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,
    true_and,Sigma.exists]

private theorem guardDeck_iff (F : Mask s) :
    F ∈ s.guardDeck c ↔ ∃ (p : PartialTest (system c)) (hp : p ∈ patterns c), s.guardMask c p hp = F := by
  simp only [guardDeck,List.mem_map, List.mem_attach, true_and, Subtype.exists]

theorem slotDeck_membership (hwm : w ≤ m) (F : Mask s) :
    F ∈ s.slotDeck c hwm ↔
    F = productKernel s.layout ∨ F ∈ s.arithmeticTiles ∨ F ∈ s.anchorTests ∨
      (∃ i j, F ∈ s.markerTests i j) ∨ (∃ g i a, F ∈ s.fallbackTests g i a) ∨
      (∃ g, ∃ d, ∃ S : Finset (Fin m), ∃ hS : S.card = m+1-w,
        s.activationTest g d S (selected_nonempty hwm hS) = F) ∨
      (∃ t i a, ¬ LetterSeedSet (system c) t (arithmeticColumn i) a ∧ s.seedMask c t i a = F) ∨
      (∃ (p : PartialTest (system c)) (hp : p ∈ patterns c), s.guardMask c p hp = F) := by
  simp only [slotDeck,List.mem_cons,List.mem_append,or_assoc,markerDeck_iff,fallbackDeck_iff,
    activationDeck_iff,seedDeck_iff,guardDeck_iff]

/-- The positive mixed-slope masks implement the guarded Wang simulation. -/
theorem slotDeck_iff (hwm : w ≤ m) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (SharedCoordinates.Ambient s.layout),
      ∀ F ∈ s.slotDeck c hwm, Tiles F A := by
  have hm := s.slotDeck_membership c hwm
  constructor
  · intro h
    obtain ⟨o,hd,hf,ha,hs,hp⟩ := s.slot_complete c hwm h
    refine ⟨Set.range (SharedCoordinates.point s.layout o),fun F hF => ?_⟩
    rcases (hm F).mp hF with rfl | h | h | ⟨i,j,h⟩ | ⟨g,i,a,h⟩ | ⟨g,d,S,hS,rfl⟩ |
      ⟨t,i,a,he,rfl⟩ | ⟨p,hp',rfl⟩
    · exact (productKernel_iff s.layout _).mpr ⟨o,rfl⟩
    · exact hd.1 F h
    · exact hd.2.1 F h
    · exact hd.2.2 i j F h
    · exact hf g i a F h
    · exact ha g d S hS
    · exact hs t i a he
    · exact hp p hp'
  · rintro ⟨A,hA⟩
    obtain ⟨o,rfl⟩ := (productKernel_iff s.layout A).mp (hA _ (List.mem_cons_self ..))
    apply s.slot_sound c hwm o
    · refine ⟨fun F h => ?_,fun F h => ?_,fun i j F h => ?_⟩
      · exact hA F ((hm F).mpr (Or.inr (Or.inl h)))
      · exact hA F ((hm F).mpr (Or.inr (Or.inr (Or.inl h))))
      · exact hA F ((hm F).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,j,h⟩)))))
    · intro g i a F h
      exact hA F ((hm F).mpr (by right; right; right; right; left; exact ⟨g,i,a,h⟩))
    · intro g d S hS
      exact hA _ ((hm _).mpr (by right; right; right; right; right; left; exact ⟨g,d,S,hS,rfl⟩))
    · intro t i a ha
      exact hA _ ((hm _).mpr (by right; right; right; right; right; right; left; exact ⟨t,i,a,ha,rfl⟩))
    · intro p hp
      exact hA _ ((hm _).mpr (by right; right; right; right; right; right; right; exact ⟨p,hp,rfl⟩))

theorem slotCyclicDeck_iff (hwm : w ≤ m) :
    let Fs := (s.slotDeck c hwm).map s.encodeTile
    LeanWang.TilesPlane T ↔ ∃ A : Set (Plane × ZMod (order s.layout)),
      ∀ i : Fin Fs.length, Tiles (cyclicTileSet (order s.layout) (Fs.getD i.val [])) A :=
  (s.slotDeck_iff c hwm).trans (s.encodeDeck_iff _).symm

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
