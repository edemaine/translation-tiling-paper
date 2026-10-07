import TranslationTiling.Compiler.EffectiveCycleTables

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

/-- A numerical table of a function on a rectangular useful-coordinate space.
The table may contain padding; only indices below a*b are ever read. -/
noncomputable def functionTable {a b : ℕ} (length : ℕ) (f : ZMod a × ZMod b → ℕ) : List ℕ :=
  (List.range length).map fun k => f ((k / b : ℕ), (k : ℕ))

def rectangularIndex (b : ℕ) (x y : ℕ) : ℕ := x * b + y

theorem rectangularIndex_lt {a b : ℕ} [NeZero a] [NeZero b]
    (e : ZMod a × ZMod b) : rectangularIndex b e.1.val e.2.val < a * b := by
  have hx := ZMod.val_lt e.1
  have hy := ZMod.val_lt e.2
  have hm := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hx)
  rw [Nat.succ_mul] at hm
  unfold rectangularIndex
  omega

theorem functionTable_apply {a b : ℕ} [NeZero a] [NeZero b]
    (length : ℕ) (hbound : a * b ≤ length) (f : ZMod a × ZMod b → ℕ)
    (e : ZMod a × ZMod b) :
    (functionTable length f).getD (rectangularIndex b e.1.val e.2.val) 0 = f e := by
  have hi := lt_of_lt_of_le (rectangularIndex_lt e) hbound
  have hdiv : rectangularIndex b e.1.val e.2.val / b = e.1.val := by
    unfold rectangularIndex
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (NeZero.pos b),
      Nat.div_eq_of_lt (ZMod.val_lt e.2), Nat.zero_add]
  have hmod : rectangularIndex b e.1.val e.2.val % b = e.2.val := by
    unfold rectangularIndex
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt e.2)]
  have hcast : ((rectangularIndex b e.1.val e.2.val / b : ℕ) : ZMod a) = e.1 := by
    rw [hdiv, ZMod.natCast_zmod_val]
  have hcast' : ((rectangularIndex b e.1.val e.2.val : ℕ) : ZMod b) = e.2 := by
    apply ZMod.val_injective b
    simpa only [ZMod.val_natCast] using hmod
  simp only [functionTable, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some, hcast, hcast']

theorem mem_functionTable {a b : ℕ} (length : ℕ) (f : ZMod a × ZMod b → ℕ)
    (x : ℕ) (hx : x ∈ functionTable length f) : ∃ e, f e = x := by
  obtain ⟨k, _, he⟩ := List.mem_map.mp hx
  exact ⟨((k / b : ℕ), (k : ℕ)), he⟩

/-- Every finite function satisfying the subgroup test has an enumerated table. -/
theorem functionTable_mem_subgroupTables {a b : ℕ} (length r : ℕ) (otherPrimes : List ℕ)
    (f : ZMod a × ZMod b → ℕ)
    (hf : ∀ e, f e < r ∧ KernelTest otherPrimes (f e)) :
    functionTable length f ∈ subgroupTables r otherPrimes length := by
  apply (mem_subgroupTables _ _ _ _).mpr
  refine ⟨by simp only [functionTable, List.length_map, List.length_range], ?_⟩
  intro x hx
  obtain ⟨e, rfl⟩ := mem_functionTable length f x hx
  exact hf e

theorem exists_functionTable {a b : ℕ} [NeZero a] [NeZero b]
    (length r : ℕ) (hbound : a * b ≤ length) (otherPrimes : List ℕ)
    (f : ZMod a × ZMod b → ℕ)
    (hf : ∀ e, f e < r ∧ KernelTest otherPrimes (f e)) :
    ∃ xs ∈ subgroupTables r otherPrimes length, ∀ e,
      xs.getD (rectangularIndex b e.1.val e.2.val) 0 = f e :=
  ⟨functionTable length f, functionTable_mem_subgroupTables _ _ _ f hf,
    functionTable_apply length hbound f⟩

theorem subgroupTables_getD (length r : ℕ) (hr : 0 < r) (otherPrimes : List ℕ)
    (xs : List ℕ) (hxs : xs ∈ subgroupTables r otherPrimes length) (k : ℕ) :
    xs.getD k 0 < r ∧ KernelTest otherPrimes (xs.getD k 0) := by
  have hmem := (mem_subgroupTables _ _ _ _).mp hxs
  by_cases hk : k < xs.length
  · apply hmem.2
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      using List.getElem_mem hk
  · have hn : xs[k]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_none]
    exact ⟨hr, by intro d hd; exact Nat.zero_mod d⟩

end TranslationTiling.Compiler.Effective
