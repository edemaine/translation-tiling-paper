import TranslationTiling.Compiler.EffectiveGraphCompiler
import TranslationTiling.Compiler.EffectiveInvarianceTiles
import TranslationTiling.Compiler.Dependence

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

abbrev DependenceSlot := Fin (Fintype.card (DependenceIndex []))

noncomputable def dependenceIndex : DependenceSlot → DependenceIndex [] :=
  (Fintype.equivFin _).symm

noncomputable def dependenceHorizontal (s : DependenceSlot) : Plane :=
  (dependenceShift baseParameters (dependenceIndex s)).1

noncomputable def dependenceCoefficient (s : DependenceSlot) (i : FixedChannel) : ℕ :=
  match dependenceIndex s with
  | .inl ⟨_, j⟩ => if i = j.val then 1 else 0
  | .inr _ => 0

theorem dependenceCoefficient_val (T : LeanWang.TileSet) (s : DependenceSlot)
    (i : FixedChannel) :
    dependenceCoefficient s i % (parameters T).r i =
      ((dependenceShift (parameters T) (dependenceIndex s)).2 i).val := by
  unfold dependenceCoefficient
  cases dependenceIndex s with
  | inl d =>
    rcases d with ⟨j, k⟩
    by_cases hi : i = k.val
    · subst i
      simp [dependenceShift, lowGenerator, ZMod.val_one]
      simpa only [Nat.cast_one] using
        (ZMod.val_natCast (n := (parameters T).r k.val) 1).symm
    · simp only [if_neg hi, dependenceShift, lowGenerator, Function.update_of_ne hi,
        Pi.zero_apply, ZMod.val_zero, Nat.zero_mod]
  | inr d =>
    cases d <;> simp only [dependenceShift, Pi.zero_apply, ZMod.val_zero, Nat.zero_mod]

noncomputable def dependenceCongruences (T : LeanWang.TileSet)
    (s : DependenceSlot) : CongruenceList :=
  (Finset.univ : Finset FixedChannel).toList.map fun i =>
    (numericalR T i, dependenceCoefficient s i % numericalR T i)

theorem dependenceCongruences_computable : Computable (fun z :
    LeanWang.TileSet × DependenceSlot => dependenceCongruences z.1 z.2) := by
  have hp : Primrec (fun z : (LeanWang.TileSet × DependenceSlot) × FixedChannel =>
      (z.1.1, z.2)) := by fun_prop
  have hr := numericalR_computable.comp hp.to_comp
  have hc0 : Primrec (fun z : DependenceSlot × FixedChannel =>
      dependenceCoefficient z.1 z.2) := finiteFunction_primrec _
  have hpc : Primrec (fun z : (LeanWang.TileSet × DependenceSlot) × FixedChannel =>
      (z.1.2, z.2)) := by fun_prop
  have hc := hc0.comp hpc
  have hmod := Primrec.nat_mod.to_comp.comp hc.to_comp hr
  have hg := hr.pair hmod
  have h := computableListMap
    (f := fun _ : LeanWang.TileSet × DependenceSlot =>
      (Finset.univ : Finset FixedChannel).toList)
    (g := fun z i => (numericalR z.1 i, dependenceCoefficient z.2 i % numericalR z.1 i))
    (Computable.const _) hg
  exact h

noncomputable def dependenceCompiler (T : LeanWang.TileSet)
    (s : DependenceSlot) : List NumericalPoint :=
  let i := dependenceChannel (dependenceIndex s)
  invarianceCodes (numericalOrder T) (channelModuli T)
    (usefulPrime (.inl i)) (usefulPrime (.inr i))
    (dependenceHorizontal s) (dependenceCongruences T s)

theorem dependenceCompiler_computable : Computable (fun z :
    LeanWang.TileSet × DependenceSlot => dependenceCompiler z.1 z.2) := by
  have hfixed : Primrec (fun s : DependenceSlot =>
      ((usefulPrime (.inl (dependenceChannel (dependenceIndex s))),
        usefulPrime (.inr (dependenceChannel (dependenceIndex s)))), dependenceHorizontal s)) :=
    finiteFunction_primrec _
  have hfixed' : Primrec (fun z : LeanWang.TileSet × DependenceSlot =>
      ((usefulPrime (.inl (dependenceChannel (dependenceIndex z.2))),
        usefulPrime (.inr (dependenceChannel (dependenceIndex z.2)))), dependenceHorizontal z.2)) :=
    hfixed.comp Primrec.snd
  have hdata := ((numericalOrder_computable.comp Computable.fst).pair
    (channelModuli_computable.comp Computable.fst)).pair
    ((Computable.fst.comp hfixed'.to_comp).pair
      ((Computable.snd.comp hfixed'.to_comp).pair dependenceCongruences_computable))
  have h := invarianceCodes_primrec.to_comp.comp hdata
  exact h

theorem dependenceCompiler_correct (T : LeanWang.TileSet) (s : DependenceSlot) :
    (dependenceCompiler T s).toFinset.image (decodeNumericalPoint (parameters T)) =
      dependenceTile (parameters T) (dependenceIndex s) := by
  have hcs : dependenceCongruences T s =
      (Finset.univ : Finset FixedChannel).toList.map fun i =>
        ((parameters T).r i, ((dependenceShift (parameters T) (dependenceIndex s)).2 i).val) := by
    unfold dependenceCongruences
    apply List.map_congr_left
    intro i _
    rw [numericalR_eq, dependenceCoefficient_val]
  have hh : dependenceHorizontal s =
      (dependenceShift (parameters T) (dependenceIndex s)).1 := by
    unfold dependenceHorizontal
    cases dependenceIndex s with
    | inl d => rfl
    | inr d => cases d <;> rfl
  unfold dependenceCompiler dependenceTile
  have hi : @dependenceChannel [] (dependenceIndex s) =
      @dependenceChannel T (dependenceIndex s) := by
    cases dependenceIndex s with
    | inl d => rfl
    | inr d => cases d <;> rfl
  simp only [hi]
  rw [numericalOrder_eq, channelModuli_eq, hcs, hh]
  simpa only [parameters_a, parameters_b] using
    invarianceCodes_correct (parameters T) (dependenceChannel (dependenceIndex s))
      (dependenceShift (parameters T) (dependenceIndex s))

noncomputable def dependenceFamily (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  (List.ofFn (id : DependenceSlot → DependenceSlot)).map (dependenceCompiler T)

theorem dependenceFamily_computable : Computable dependenceFamily := by
  exact computableListMap (Computable.const _) dependenceCompiler_computable

theorem dependenceFamily_correct (T : LeanWang.TileSet) :
    ((dependenceFamily T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset = dependenceTiles (parameters T) := by
  unfold dependenceFamily
  rw [List.map_map]
  simp only [Function.comp_def, dependenceCompiler_correct]
  ext F
  simp only [List.mem_toFinset, List.mem_map, List.mem_ofFn, id_eq, exists_eq_left,
    dependenceTiles, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, h⟩
    exact ⟨dependenceIndex s, h.2⟩
  · rintro ⟨d, h⟩
    refine ⟨(Fintype.equivFin _) d, ?_⟩
    exact ⟨⟨_, rfl⟩, by simpa only [dependenceIndex, Equiv.symm_apply_apply] using h⟩

end TranslationTiling.Compiler.Effective
