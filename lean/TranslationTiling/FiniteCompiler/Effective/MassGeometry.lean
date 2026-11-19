import TranslationTiling.FiniteCompiler.MassBounds
import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FourLayer.Compiler

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem family_mass (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (F : CyclicTile) (hf : F∈canonicalInputFamily (parameterData T,p)) :
    (cyclicTileSet (parameters T).cyclicOrder F).card≤MassSize.mass (parameters T) := by
  have hm : F.toFinset.image (decodeNumericalPoint (parameters T))∈testTiles (parameters T) := by
    rw [←canonicalInputFamily_correct T p hp hpos hS]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hf,rfl⟩
  have hh := MassSize.test_card (parameters T) _ hm
  rw [decodedTile_eq_image,Finset.card_image_of_injective _ (ambientCyclicEquiv (parameters T)).symm.injective] at hh
  exact hh

theorem stack_mass (N P : ℕ) (hN : 0<N) (Fs : List CyclicTile) (hs : 0<Fs.length)
    (c : PartitionCertificate) (hc : PartitionValid (Fs.length-1) P c) (hcop : Nat.Coprime N c.1)
    (J : ℕ) (hJ : ∀ F∈Fs, (cyclicTileSet N F).card≤J) :
    (cyclicTileSet (N*c.1) (stackCodes (N,c,Fs))).card≤J*c.1 := by
  letI : NeZero N := ⟨hN.ne'⟩
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  have hp : Stacking.IsColorPartition (stackParts Fs.length c.1 c.2) := by
    have hh : Stacking.IsColorPartition
        (fun i : Fin (Fs.length-1+1) => (Finset.univ : Finset (ZMod c.1)).filter
          (fun j => c.2.getD j.val 0=i.val)) ∧
        Stacking.HasFullDifferences
        (fun i : Fin (Fs.length-1+1) => (Finset.univ : Finset (ZMod c.1)).filter
          (fun j => c.2.getD j.val 0=i.val)) := certificateParts_correct _ _ c hc
    have he : Fs.length-1+1=Fs.length := by omega
    rw [he] at hh
    exact hh.1
  rw [stackCodes_correct hcop,Finset.card_image_of_injective _ (stackCyclicEquiv hcop).injective,
    Stacking.card_stack hp]
  calc
    _ ≤ ∑ i : Fin Fs.length, J*(stackParts Fs.length c.1 c.2 i).card :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hJ _ (getD_mem_of_lt Fs i [] i.isLt)))
    _ = J*c.1 := by rw [←Finset.mul_sum,hp.sum_card,ZMod.card]

theorem freshStack_mass (X N P : ℕ) (Fs : List CyclicTile) (hN : 0<N)
    (hs : 0<Fs.length) (hX : Fs.length≤X) (hP : P≤X^2) (hpr : PrimeBound N P)
    (J : ℕ) (hJ : ∀ F∈Fs, (cyclicTileSet N F).card≤J) :
    (cyclicTileSet (freshStack (X,N,P,Fs)).1 (freshStack (X,N,P,Fs)).2).card≤J*freshCap X P := by
  have hr : FreshReady (Fs.length-1,N,P,X) := ⟨hN,by change Fs.length-1+1≤X; omega,hP,hpr⟩
  have hc := freshPartition_spec _ hr
  exact (stack_mass N P hN Fs hs _ hc.1 hc.2.1 J hJ).trans (Nat.mul_le_mul_left J hc.2.2)

end
end TranslationTiling.FiniteCompiler.Effective

namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem integerTile_cubeCount_mass (d : CyclicTileData) (hm : 0<d.1) :
    cubeCount (integerTile d)≤2^24*(cyclicTileSet d.1 d.2).card := by
  letI : NeZero d.1 := ⟨hm.ne'⟩
  unfold cubeCount
  rw [integerTile_toFinset,latticeRepresentatives_toFinset d.1 hm d.2]
  apply (assembled_card_le _ _).trans
  have hh : (CyclicQuotient.representatives d.1
      ((cyclicTileSet d.1 d.2).image (fun f => f-cyclicPoint d.1 (d.2.headD ((0,0),0))))).card≤
      (cyclicTileSet d.1 d.2).card := Finset.card_image_le.trans Finset.card_image_le
  exact (Nat.mul_le_mul_right _ hh).trans_eq (Nat.mul_comm _ _)

theorem integerTile_cubeCount_sharp (d : CyclicTileData) (hm : 0<d.1) :
    cubeCount (integerTile d)≤mssPieceCap*(cyclicTileSet d.1 d.2).card := by
  letI : NeZero d.1 := ⟨hm.ne'⟩
  unfold cubeCount
  rw [integerTile_toFinset,latticeRepresentatives_toFinset d.1 hm d.2]
  apply (assembled_card_le_sharp _ _).trans
  have hh : (CyclicQuotient.representatives d.1
      ((cyclicTileSet d.1 d.2).image (fun f => f-cyclicPoint d.1 (d.2.headD ((0,0),0))))).card≤
      (cyclicTileSet d.1 d.2).card := Finset.card_image_le.trans Finset.card_image_le
  exact (Nat.mul_le_mul_right _ hh).trans_eq (Nat.mul_comm _ _)

end
end TranslationTiling.Compiler.Size

namespace TranslationTiling.FourLayer
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem connectedTile_length_mass (E : Tile 3) (H M : ℕ) (hH : 1≤H) (hHM : H≤M) :
    (connectedTile E H M).length≤Compiler.Size.cubeCount E*(972*36*8003^4)*H^2*M^2 := by
  have hA : side H≤8003*H := by unfold side radius; omega
  have hB : max (side H) (side M)≤8003*M := by unfold side radius at *; omega
  have hs := shell_length_le (side H) (max (side H) (side M)) (by unfold side; omega) (le_max_left _ _)
  have hlen : (assembly (shifted E H M) (side H) (max (side H) (side M))).length=
      E.dedup.length*(shell (side H) (max (side H) (side M))).length := by
    simp [assembly,shifted,List.length_flatMap,List.length_map,Function.comp_def,List.map_const,List.sum_replicate]
  have hraw : E.dedup.length=Compiler.Size.cubeCount E := by rw [←List.card_toFinset]; rfl
  calc
    _ ≤ (assembly (shifted E H M) (side H) (max (side H) (side M))).length := by
      simpa only [connectedTile,List.card_toFinset] using List.toFinset_card_le
        (assembly (shifted E H M) (side H) (max (side H) (side M)))
    _ ≤ Compiler.Size.cubeCount E*(972*(6*(8003*H)*(8003*M))^2) := by
      rw [hlen,hraw]
      exact Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hA) hB) 2)))
    _ = _ := by ring

end
end TranslationTiling.FourLayer

namespace TranslationTiling.FiniteCompiler.MassSize
noncomputable section
set_option maxHeartbeats 1000000

theorem geometry_bound {P w H M J : ℕ} (hP : 962≤P)
    (hH : H≤P^199) (hM : M≤P^(21*w+31)*3^(2*w+2))
    (hJ : J≤P^(12*w+23)*3^(2*w+2)) :
    (2^24*J)*(972*36*8003^4)*H^2*M^2≤P^(55*w+494) := by
  have hk : 2^24*972*36*8003^4≤P^10 :=
    (by norm_num : 2^24*972*36*8003^4≤962^10).trans (Nat.pow_le_pow_left hP 10)
  have hthree : 3^(6*w+6)≤P^(w+1) := by
    calc
      _ = (3^6)^(w+1) := by rw [←pow_mul]; congr 1
      _ ≤ _ := Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ = (2^24*972*36*8003^4)*H^2*M^2*J := by ring
    _ ≤ P^10*(P^199)^2*(P^(21*w+31)*3^(2*w+2))^2*(P^(12*w+23)*3^(2*w+2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 2))
        (Nat.pow_le_pow_left hM 2)) hJ
    _ = P^(54*w+493)*3^(6*w+6) := by
      simp only [mul_pow,←pow_mul]
      ring_nf
    _ ≤ P^(54*w+493)*P^(w+1) := Nat.mul_le_mul_left _ hthree
    _ = _ := by rw [←pow_add]; congr 1; ring

end
end TranslationTiling.FiniteCompiler.MassSize
