import TranslationTiling.FiniteCompiler.ProjectedBounds

namespace TranslationTiling.FiniteCompiler.PairSmall
open Compiler (CyclicTile cyclicTileSet cyclicPoint)
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] family roleEquiv arity pEquiv qEquiv
variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d) (E : EncodingParameters (system code))
local instance projectedGeometryFamily : AlphabetFamily (system code) := family code

def projectedFamily : List CyclicTile := ((projectedDeck E (boardProjections code)).toList).map (numericalTile E)

theorem projectedFamily_length : (projectedFamily code E).length=(projectedDeck E (boardProjections code)).card := by
  simp [projectedFamily]

theorem projectedFamily_nonempty : 0<(projectedFamily code E).length := by
  rw [projectedFamily_length code E,Finset.card_pos]
  exact projectedDeck_nonempty E _

theorem projectedFamily_tile_nonempty : ∀ F∈projectedFamily code E, F≠[] := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  have hne := projectedDeck_tile_nonempty E _ (Finset.mem_toList.mp hG)
  intro he
  have hh := numericalTile_correct E G
  rw [he] at hh
  have hn := hne.image (FiniteCompiler.ambientCyclicEquiv E)
  have hh' : (∅ : Finset (Plane × ZMod E.cyclicOrder))=G.image (FiniteCompiler.ambientCyclicEquiv E) := by
    simpa only [cyclicTileSet,List.toFinset_nil,Finset.image_empty] using hh
  have hfalse : (∅ : Finset (Plane × ZMod E.cyclicOrder)).Nonempty := by rw [hh']; exact hn
  exact Finset.not_nonempty_empty hfalse

theorem projectedFamily_mass : ∀ F∈projectedFamily code E,
    (cyclicTileSet E.cyclicOrder F).card≤MassSize.mass E := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  rw [numericalTile_correct E,Finset.card_image_of_injective _ (FiniteCompiler.ambientCyclicEquiv E).injective]
  exact projectedDeck_mass E _ (Finset.mem_toList.mp hG)

theorem projectedFamily_horizontal {H : ℕ} (hH : CompactSupport.Bound E H) :
    ∀ F∈projectedFamily code E, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  change (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.1.natAbs≤H ∧
    (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.2.natAbs≤H
  rw [numericalPoint_first,ambient_first]
  exact projectedDeck_horizontal E _ hH (slope_bound code) (Finset.mem_toList.mp hG) ha

theorem projectedFamily_solution :
    LeanWang.TilesPlane T ↔ ∃ B : Set (Plane × ZMod E.cyclicOrder),
      ∀ i : Fin (projectedFamily code E).length,
        Tiles (cyclicTileSet E.cyclicOrder ((projectedFamily code E).getD i.val [])) B := by
  rw [projected_iff_wang code E]
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨FiniteCompiler.ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm := getD_mem_of_lt (projectedFamily code E) i.val [] i.isLt
    obtain ⟨G,hG,he⟩ := List.mem_map.mp hm
    rw [←he,numericalTile_correct E]
    exact ambient_covers E _ A (hA _ (Finset.mem_toList.mp hG))
  · rintro ⟨B,hB⟩
    refine ⟨(FiniteCompiler.ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    have hm : numericalTile E F∈projectedFamily code E :=
      List.mem_map.mpr ⟨F,Finset.mem_toList.mpr hF,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi,he,numericalTile_correct E] at h
    exact ambient_uncovers E _ B h

variable (H : ℕ)

def projectedCompiled : Tile 3 :=
  let d := freshStack (max (projectedFamily code E).length (256^2),E.cyclicOrder,256^4,projectedFamily code E)
  Rails.connectedTile (Compiler.integerTile d) H (max (H^2) d.1)

theorem projectedCompiled_facts (hH : 1≤H) (hsupport : CompactSupport.Bound E H)
    (hp : ∀ i, E.primeAt i≤65536) :
    projectedCompiled code E H≠[] ∧ FaceConnected (projectedCompiled code E H) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (projectedCompiled code E H)) ∧
    (projectedCompiled code E H).length≤
      (2^24*(MassSize.mass E*freshCap (max (projectedFamily code E).length (256^2)) (256^4)))*
      (549072*8003^4)*H^2*max (H^2)
        (E.cyclicOrder*freshCap (max (projectedFamily code E).length (256^2)) (256^4)) := by
  let G := projectedFamily code E
  let X := max G.length (256^2)
  have hP : 256^4≤X^2 := by
    calc
      256^4 = (256^2)^2 := by norm_num
      _ ≤ X^2 := Nat.pow_le_pow_left (le_max_right _ _) 2
  have hpr := primeBound code E hp
  obtain ⟨hm,hne,hR,hiff⟩ := freshStack_facts X E.cyclicOrder (256^4) G
    E.cyclicOrder_pos (projectedFamily_nonempty code E) (le_max_left _ _) hP hpr
    (projectedFamily_tile_nonempty code E)
  have hmass := freshStack_mass X E.cyclicOrder (256^4) G E.cyclicOrder_pos
    (projectedFamily_nonempty code E) (le_max_left _ _) hP hpr _ (projectedFamily_mass code E)
  have hstack : ∀ f∈(freshStack (X,E.cyclicOrder,256^4,G)).2,
      f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H :=
    stackCodes_horizontal _ _ G H (projectedFamily_horizontal code E hsupport)
  unfold projectedCompiled
  generalize hd : freshStack (X,E.cyclicOrder,256^4,G)=d at hm hne hR hiff hmass hstack ⊢
  have hrect := Compiler.Size.integerTile_rectangle_bound d H (max (H^2) d.1) hm
    (le_max_right _ _) hne hstack
  refine ⟨Rails.connectedTile_nonempty _ _ _ (Compiler.integerTile_nonempty d hne),
    Rails.connectedTile_connected _ _ _ hrect,?_,?_⟩
  · exact (projectedFamily_solution code E).trans (hiff.trans
      ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
        (Rails.connectedTile_correct _ H (max (H^2) d.1)).symm))
  · have hvol := Compiler.Size.integerTile_cubeCount_mass d hm
    have hh := Rails.connectedTile_length_mass (Compiler.integerTile d) H (max (H^2) d.1) hH (le_max_left _ _)
    apply hh.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hvol.trans (Nat.mul_le_mul_left _ hmass)))) (max_le_max_left _ hR)


end
end TranslationTiling.FiniteCompiler.PairSmall
