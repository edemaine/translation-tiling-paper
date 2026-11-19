import TranslationTiling.FiniteCompiler.PairSmallBounds
import TranslationTiling.FiniteCompiler.Effective.CompactFamilyCompiler

namespace TranslationTiling.FiniteCompiler.PairSmall
open Compiler (CyclicTile cyclicTileSet cyclicPoint)
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
attribute [local irreducible] family roleEquiv arity pEquiv qEquiv
section
variable [SeedFrame]
def numericalPoint (N : ℕ) (g : Plane × ZMod N) : Compiler.CyclicPoint :=
  (g.1,@ZMod.val N g.2)

theorem numericalPoint_first (N : ℕ) (g : Plane × ZMod N) : (numericalPoint N g).1=g.1 := rfl

theorem ambient_first {S : System} [AlphabetFamily S] (E : EncodingParameters S) (g : Ambient E) :
    (FiniteCompiler.ambientCyclicEquiv E g).1=g.1 := rfl

theorem numericalPoint_correct (N : ℕ) [NeZero N] (g : Plane × ZMod N) :
    cyclicPoint N (numericalPoint N g)=g := by
  simp [cyclicPoint,numericalPoint]

variable {S : System} [AlphabetFamily S] (E : EncodingParameters S)

def numericalTile (F : Finset (Ambient E)) : CyclicTile :=
  ((F.image (FiniteCompiler.ambientCyclicEquiv E)).toList).map (numericalPoint E.cyclicOrder)

theorem numericalTile_correct (F : Finset (Ambient E)) :
    cyclicTileSet E.cyclicOrder (numericalTile E F)=F.image (FiniteCompiler.ambientCyclicEquiv E) := by
  let G := F.image (FiniteCompiler.ambientCyclicEquiv E)
  change (G.toList.map (numericalPoint E.cyclicOrder)).toFinset.image
    (cyclicPoint E.cyclicOrder)=G
  ext g
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨a,⟨p,hp,rfl⟩,he⟩
    have he' : p=g := by simpa only [numericalPoint_correct] using he
    exact he' ▸ hp
  · intro hg
    exact ⟨numericalPoint E.cyclicOrder g,⟨g,hg,rfl⟩,numericalPoint_correct _ g⟩

end

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d) (E : EncodingParameters (system code))
local instance : AlphabetFamily (system code) := family code

def numericalFamily : List CyclicTile := ((testTiles E).toList).map (numericalTile E)

theorem numericalFamily_length : (numericalFamily code E).length=(testTiles E).card := by
  simp [numericalFamily]

theorem numericalFamily_nonempty : 0<(numericalFamily code E).length := by
  rw [numericalFamily_length code E,Finset.card_pos]
  exact FiniteCompiler.testTiles_nonempty E

theorem numericalFamily_tile_nonempty : ∀ F∈numericalFamily code E, F≠[] := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  have hne := FiniteCompiler.nonempty_of_mem_testTiles E (Finset.mem_toList.mp hG)
  intro he
  have hh := numericalTile_correct E G
  rw [he] at hh
  have hn := hne.image (FiniteCompiler.ambientCyclicEquiv E)
  have hh' : (∅ : Finset (Plane × ZMod E.cyclicOrder))=G.image (FiniteCompiler.ambientCyclicEquiv E) := by
    simpa only [cyclicTileSet,List.toFinset_nil,Finset.image_empty] using hh
  have hfalse : (∅ : Finset (Plane × ZMod E.cyclicOrder)).Nonempty := by rw [hh']; exact hn
  exact Finset.not_nonempty_empty hfalse

theorem numericalFamily_mass : ∀ F∈numericalFamily code E,
    (cyclicTileSet E.cyclicOrder F).card≤MassSize.mass E := by
  intro F hF
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  rw [numericalTile_correct E,Finset.card_image_of_injective _ (FiniteCompiler.ambientCyclicEquiv E).injective]
  exact test_card code E (Finset.mem_toList.mp hG)

theorem numericalFamily_horizontal {H : ℕ} (hH : CompactSupport.Bound E H) :
    ∀ F∈numericalFamily code E, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H := by
  intro F hF f hf
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hg)
  change (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.1.natAbs≤H ∧
    (numericalPoint E.cyclicOrder (FiniteCompiler.ambientCyclicEquiv E a)).1.2.natAbs≤H
  rw [numericalPoint_first,ambient_first]
  exact test_horizontal code E hH (Finset.mem_toList.mp hG) ha

theorem ambient_covers [SeedFrame] {S : System} [AlphabetFamily S] (E : EncodingParameters S)
    (F : Finset (Ambient E)) (A : Set (Ambient E)) (h : Tiles F A) :
    Tiles (F.image (FiniteCompiler.ambientCyclicEquiv E)) (FiniteCompiler.ambientCyclicEquiv E '' A) :=
  Compiler.covers_image (G:=Ambient E) (H:=Plane × ZMod E.cyclicOrder) _ F A h

theorem ambient_uncovers [SeedFrame] {S : System} [AlphabetFamily S] (E : EncodingParameters S)
    (F : Finset (Ambient E)) (B : Set (Plane × ZMod E.cyclicOrder))
    (h : Tiles (F.image (FiniteCompiler.ambientCyclicEquiv E)) B) :
    Tiles F ((FiniteCompiler.ambientCyclicEquiv E).symm '' B) := by
  have hh := Compiler.covers_image (G:=Plane × ZMod E.cyclicOrder) (H:=Ambient E)
    (FiniteCompiler.ambientCyclicEquiv E).symm _ B h
  simpa only [Finset.image_image,Function.comp_def,AddEquiv.symm_apply_apply,Finset.image_id'] using hh

theorem numericalFamily_solution :
    LeanWang.TilesPlane T ↔ ∃ B : Set (Plane × ZMod E.cyclicOrder),
      ∀ i : Fin (numericalFamily code E).length,
        Tiles (cyclicTileSet E.cyclicOrder ((numericalFamily code E).getD i.val [])) B := by
  rw [finite_system_iff_wang code E]
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨FiniteCompiler.ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm := getD_mem_of_lt (numericalFamily code E) i.val [] i.isLt
    obtain ⟨G,hG,he⟩ := List.mem_map.mp hm
    rw [←he,numericalTile_correct E]
    exact ambient_covers E _ A (hA _ (Finset.mem_toList.mp hG))
  · rintro ⟨B,hB⟩
    refine ⟨(FiniteCompiler.ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    have hm : numericalTile E F∈numericalFamily code E :=
      List.mem_map.mpr ⟨F,Finset.mem_toList.mpr hF,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have h := hB ⟨i,hi⟩
    rw [List.getD_eq_getElem _ _ hi,he,numericalTile_correct E] at h
    exact ambient_uncovers E _ B h

variable (H : ℕ)

def compiled : Tile 3 :=
  let d := freshStack (max (numericalFamily code E).length (256^2),E.cyclicOrder,256^4,numericalFamily code E)
  Rails.connectedTile (Compiler.integerTile d) H (max (H^2) d.1)

theorem primeBound (hp : ∀ i, E.primeAt i≤65536) : PrimeBound E.cyclicOrder (256^4) := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q∣E.cyclicOrder
    · right
      by_contra hl
      have hlarge : 256^4<q := by omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤256^4) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (by rw [residueModulus_eq]; decide) (by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q])
      have hi (i : Channel (system code)) : Nat.Coprime q (E.blockModulus i) := by
        have hr : Nat.Coprime q (E.r i) := by
          rw [E.r_eq_prod]
          apply Nat.coprime_fintype_prod_right_iff.mpr
          intro j
          exact hcop _ (E.prime_isPrime _).pos ((hp _).trans (by norm_num))
        exact ((hr.pow_right 2).mul_right (hcop _ (E.prime_isPrime _).pos
          ((hp _).trans (by norm_num)))).mul_right
          (hcop _ (E.prime_isPrime _).pos ((hp _).trans (by norm_num)))
      have ht : Nat.Coprime q E.cyclicOrder :=
        (hR.pow_right 2).mul_right (Nat.coprime_fintype_prod_right_iff.mpr hi)
      exact (hprime.coprime_iff_not_dvd.mp ht) hd
    · exact Or.inl hd
  · exact Or.inl hprime

theorem compiled_facts (hH : 1≤H) (hsupport : CompactSupport.Bound E H)
    (hp : ∀ i, E.primeAt i≤65536) :
    compiled code E H≠[] ∧ FaceConnected (compiled code E H) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compiled code E H)) ∧
    (compiled code E H).length≤
      (2^24*(MassSize.mass E*freshCap (max (numericalFamily code E).length (256^2)) (256^4)))*
      (549072*8003^4)*H^2*max (H^2)
        (E.cyclicOrder*freshCap (max (numericalFamily code E).length (256^2)) (256^4)) := by
  let G := numericalFamily code E
  let X := max G.length (256^2)
  have hP : 256^4≤X^2 := by
    calc
      256^4 = (256^2)^2 := by norm_num
      _ ≤ X^2 := Nat.pow_le_pow_left (le_max_right _ _) 2
  have hpr := primeBound code E hp
  obtain ⟨hm,hne,hR,hiff⟩ := freshStack_facts X E.cyclicOrder (256^4) G
    E.cyclicOrder_pos (numericalFamily_nonempty code E) (le_max_left _ _) hP hpr
    (numericalFamily_tile_nonempty code E)
  have hmass := freshStack_mass X E.cyclicOrder (256^4) G E.cyclicOrder_pos
    (numericalFamily_nonempty code E) (le_max_left _ _) hP hpr _ (numericalFamily_mass code E)
  have hstack : ∀ f∈(freshStack (X,E.cyclicOrder,256^4,G)).2,
      f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H :=
    stackCodes_horizontal _ _ G H (numericalFamily_horizontal code E hsupport)
  unfold compiled
  generalize hd : freshStack (X,E.cyclicOrder,256^4,G)=d at hm hne hR hiff hmass hstack ⊢
  have hrect := Compiler.Size.integerTile_rectangle_bound d H (max (H^2) d.1) hm
    (le_max_right _ _) hne hstack
  refine ⟨Rails.connectedTile_nonempty _ _ _ (Compiler.integerTile_nonempty d hne),
    Rails.connectedTile_connected _ _ _ hrect,?_,?_⟩
  · exact (numericalFamily_solution code E).trans (hiff.trans
      ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
        (Rails.connectedTile_correct _ H (max (H^2) d.1)).symm))
  · have hvol := Compiler.Size.integerTile_cubeCount_mass d hm
    have hh := Rails.connectedTile_length_mass (Compiler.integerTile d) H (max (H^2) d.1) hH (le_max_left _ _)
    apply hh.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hvol.trans (Nat.mul_le_mul_left _ hmass)))) (max_le_max_left _ hR)

end
end TranslationTiling.FiniteCompiler.PairSmall
