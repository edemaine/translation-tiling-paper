import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.ReservedStripLift

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective Compiler.StripLift

noncomputable section

/-- Input order, prime cap, test cap, vertical period, horizontal radius and test family. -/
abbrev GuardedAssemblyData := ((ℕ × ℕ × ℕ) × ℕ × ℕ) × List CyclicTile

private def guardedReserveData (z : GuardedAssemblyData) : ReserveData :=
  ((z.2.length-1,z.1.1.1,z.1.1.2.1,z.1.1.2.2),0,z.1.2.1)

@[fun_prop] private theorem guardedReserveData_primrec : Primrec guardedReserveData := by
  unfold guardedReserveData
  fun_prop

private def guardedAssemblyWith (H : ℕ → ℕ) (z : GuardedAssemblyData) : Tile 3 :=
  let c := reservedPartition (guardedReserveData z)
  let data := (z.1.1.1*c.1, stackCodes (z.1.1.1,c,z.2))
  Rails.SlotAssembly.assemble (integerTile data)
    (Rails.Strips.slotsAt 35 H) (Rails.Strips.railHeight (3*z.1.2.1+1))

def guardedAssembly (z : GuardedAssemblyData) : Tile 3 :=
  guardedAssemblyWith (fun _ => z.1.2.2) z

abbrev GuardedAssemblyBySlopeData := ((ℕ × ℕ × ℕ) × ℕ × List ℕ) × List CyclicTile

private def withUniformData (z : GuardedAssemblyBySlopeData) : GuardedAssemblyData :=
  ((z.1.1,z.1.2.1,0),z.2)

def guardedAssemblyBySlope (z : GuardedAssemblyBySlopeData) : Tile 3 :=
  guardedAssemblyWith (fun s => z.1.2.2.getD s 0) (withUniformData z)

theorem guardedAssembly_computable : Computable guardedAssembly := by
  have hc := reservedPartition_computable.comp guardedReserveData_primrec.to_comp
  have hdata : Primrec (fun z : GuardedAssemblyData × PartitionCertificate =>
      (z.1.1.1.1*z.2.1, stackCodes (z.1.1.1.1,z.2,z.1.2))) :=
    (by fun_prop : Primrec (fun z : GuardedAssemblyData × PartitionCertificate => z.1.1.1.1*z.2.1)).pair
      (stackCodes_primrec.comp (by fun_prop))
  have htile := integerTile_primrec.to_comp.comp (hdata.to_comp.comp (Computable.id.pair hc))
  have hrest : Primrec (fun z : GuardedAssemblyData =>
      (Rails.Strips.slotsAt 35 (fun _ => z.1.2.2), Rails.Strips.railHeight (3*z.1.2.1+1))) := by
    unfold Rails.Strips.railHeight
    have hh : Primrec (fun z : GuardedAssemblyData => ((35 : ℕ),z.1.2.2)) := by fun_prop
    exact (Rails.Strips.uniformSlots_primrec.comp hh).pair (by fun_prop)
  exact (Rails.SlotAssembly.assemble_computable.comp (htile.pair hrest.to_comp)).of_eq (fun _ => rfl)

theorem guardedAssemblyBySlope_computable : Computable guardedAssemblyBySlope := by
  have hc := reservedPartition_computable.comp (guardedReserveData_primrec.comp
    (show Primrec withUniformData by unfold withUniformData; fun_prop)).to_comp
  have hdata : Primrec (fun z : GuardedAssemblyBySlopeData × PartitionCertificate =>
      (z.1.1.1.1*z.2.1, stackCodes (z.1.1.1.1,z.2,z.1.2))) :=
    (by fun_prop : Primrec (fun z : GuardedAssemblyBySlopeData × PartitionCertificate => z.1.1.1.1*z.2.1)).pair
      (stackCodes_primrec.comp (by fun_prop))
  have htile := integerTile_primrec.to_comp.comp (hdata.to_comp.comp (Computable.id.pair hc))
  have hrest : Primrec (fun z : GuardedAssemblyBySlopeData =>
      (Rails.Strips.slotsAt 35 (fun s => z.1.2.2.getD s 0), Rails.Strips.railHeight (3*z.1.2.1+1))) := by
    unfold Rails.Strips.railHeight
    have hh : Primrec (fun z : GuardedAssemblyBySlopeData => ((35 : ℕ),z.1.2.2)) := by fun_prop
    exact (Rails.Strips.listSlots_primrec.comp hh).pair (by fun_prop)
  exact (Rails.SlotAssembly.assemble_computable.comp (htile.pair hrest.to_comp)).of_eq (fun _ => rfl)

private theorem guardedAssemblyWith_facts {N P X R J : ℕ} {H : ℕ → ℕ} {Fs : List CyclicTile}
    (hN : 0 < N) (hP : 3 < P) (hX : 2313 ≤ X) (hpr : PrimeBound N P)
    (hP₁ : P ≤ X^2) (hP₂ : P+3 ≤ 2*X^2)
    (hR : 0 < R) (hRN : R ≤ N) (hs : 0 < Fs.length) (hsX : Fs.length ≤ X)
    (hne : ∀ F ∈ Fs, F ≠ [])
    (hmass : ∀ F ∈ Fs, (cyclicTileSet N F).card ≤ J)
    (hstrip : ∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 H f.1)
    (hker : ∀ k : ℤ, (((0:Plane),((R:ℤ)*k:ℤ)) : Plane × ZMod N)∈
      cyclicTileSet N (Fs.getD 0 [])) :
    let U := guardedAssemblyWith H (((N,P,X),R,0),Fs)
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ B : Set (Plane × ZMod N),
        ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet N (Fs.getD i.val [])) B) ↔
        TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 H R J (reservedPrimeCap X P) := by
  let z : GuardedAssemblyData := (((N,P,X),R,0),Fs)
  let d := guardedReserveData z
  have hl : 5 ≤ Stacking.differenceLog X := by
    unfold Stacking.differenceLog
    have hh := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : 2*X≠0)).mpr
      (show 2^4 ≤ 2*X by omega)
    omega
  have hd : ReserveReady d :=
    ⟨⟨hN,by change Fs.length-1+1 ≤ X; omega,hP₁,hpr⟩,
      by change 0 < Fs.length-1+1; omega,hl,hP₂⟩
  let c := reservedPartition d
  let data := (N*c.1, stackCodes (N,c,Fs))
  obtain ⟨hc,hcop,hbound,hres⟩ := reservedPartition_prime_spec d hd
  have hq : P < c.1 := hc.2.1
  have hpos : 0 < data.1 := Nat.mul_pos hN hc.1.pos
  have hnq : 3*R < 2*data.1 := by
    have h₁ := Nat.mul_le_mul_right c.1 hRN
    have h₂ := Nat.mul_lt_mul_of_pos_left (show 3 < c.1 by omega) hR
    change _ < 2*(N*c.1)
    omega
  have hbase := stackCodes_nonempty N c Fs hs hc hne
  have hcol : HasForwardColumn data (3*R) :=
    stack_hasForwardColumn N P Fs c hc hcop hN ⟨0,hs⟩ R hR hres hker
  let slots := Rails.Strips.slotsAt 35 H
  let height := Rails.Strips.railHeight (3*R+1)
  have hU := Rails.SlotAssembly.correct _ (Rails.Strips.validAt 35 H)
    (integerTile data) height
  refine ⟨Rails.SlotAssembly.nonempty _ (Rails.Strips.validAt 35 H) _ _
      (integerTile_nonempty data hbase),
    connected_forward data 35 H (3*R) hpos hnq hcol (stack_support N c Fs _ hstrip), ?_, ?_⟩
  · exact (stackCodes_correct_coprime N P hN Fs hs c hc hcop).trans
      ((integerTile_correct MSS.rigidity data hpos hbase).trans hU.symm)
  · exact reservedVolume data hpos 35 H R J c.1 _ hbound
      (stack_mass N P hN Fs hs c hc hcop _ hmass)


theorem guardedAssembly_facts {N P X R H J : ℕ} {Fs : List CyclicTile}
    (hN : 0 < N) (hP : 3 < P) (hX : 2313 ≤ X) (hpr : PrimeBound N P)
    (hP₁ : P ≤ X^2) (hP₂ : P+3 ≤ 2*X^2)
    (hR : 0 < R) (hRN : R ≤ N) (hs : 0 < Fs.length) (hsX : Fs.length ≤ X)
    (hne : ∀ F ∈ Fs, F ≠ [])
    (hmass : ∀ F ∈ Fs, (cyclicTileSet N F).card ≤ J)
    (hstrip : ∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 (fun _ => H) f.1)
    (hker : ∀ k : ℤ, (((0:Plane),((R:ℤ)*k:ℤ)) : Plane × ZMod N)∈
      cyclicTileSet N (Fs.getD 0 [])) :
    let U := guardedAssembly (((N,P,X),R,H),Fs)
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ B : Set (Plane × ZMod N),
        ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet N (Fs.getD i.val [])) B) ↔
        TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => H) R J (reservedCap X P) := by
  obtain ⟨hne,hc,he,hv⟩ := guardedAssemblyWith_facts (H := fun _ => H) hN hP hX hpr hP₁ hP₂
    hR hRN hs hsX hne hmass hstrip hker
  exact ⟨hne,hc,he,hv.trans (reservedVolumeCap_mono (reservedPrimeCap_le_reservedCap X P))⟩

theorem guardedAssemblyBySlope_facts {N P X R J : ℕ} {H : List ℕ} {Fs : List CyclicTile}
    (hN : 0 < N) (hP : 3 < P) (hX : 2313 ≤ X) (hpr : PrimeBound N P)
    (hP₁ : P ≤ X^2) (hP₂ : P+3 ≤ 2*X^2)
    (hR : 0 < R) (hRN : R ≤ N) (hs : 0 < Fs.length) (hsX : Fs.length ≤ X)
    (hne : ∀ F ∈ Fs, F ≠ [])
    (hmass : ∀ F ∈ Fs, (cyclicTileSet N F).card ≤ J)
    (hstrip : ∀ F ∈ Fs, ∀ f ∈ F, TestSupportAt 35 (fun s => H.getD s 0) f.1)
    (hker : ∀ k : ℤ, (((0:Plane),((R:ℤ)*k:ℤ)) : Plane × ZMod N)∈
      cyclicTileSet N (Fs.getD 0 [])) :
    let U := guardedAssemblyBySlope (((N,P,X),R,H),Fs)
    U ≠ [] ∧ FaceConnected U ∧
      ((∃ B : Set (Plane × ZMod N),
        ∀ i : Fin Fs.length, FiniteCompiler.Tiles (cyclicTileSet N (Fs.getD i.val [])) B) ↔
        TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun s => H.getD s 0) R J (reservedPrimeCap X P) := guardedAssemblyWith_facts (H := fun s => H.getD s 0) hN hP hX hpr hP₁ hP₂
    hR hRN hs hsX hne hmass hstrip hker

end
end TranslationTiling.FiniteCompiler.Effective
