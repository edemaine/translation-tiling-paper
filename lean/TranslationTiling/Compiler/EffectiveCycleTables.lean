import TranslationTiling.Compiler.EffectiveAlphabet
import TranslationTiling.Compiler.EffectiveGraphTiles
import TranslationTiling.Compiler.CyclicCRT

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

/-- Cartesian product of a variable list of finite alphabets. -/
def mixedProducts {α : Type*} (alphabets : List (List α)) : List (List α) :=
  alphabets.foldr (fun alphabet tails =>
    alphabet.flatMap fun a => tails.map (List.cons a)) [[]]

theorem mixedProducts_primrec {α : Type*} [Primcodable α] :
    Primrec (mixedProducts (α := α)) := by
  have hstep : Primrec (fun p : List (List α) × (List α × List (List α)) =>
      p.2.1.flatMap fun a => p.2.2.map (List.cons a)) := by fun_prop
  have h := foldList (f := id) (g := fun _ : List (List α) => [[]])
    (h := fun _ p => p.1.flatMap fun a => p.2.map (List.cons a))
    Primrec.id (Primrec.const [[]]) hstep
  exact h

theorem mem_mixedProducts {α : Type*} (alphabets : List (List α)) (xs : List α) :
    xs ∈ mixedProducts alphabets ↔ List.Forall₂ (fun a alphabet => a ∈ alphabet) xs alphabets := by
  induction alphabets generalizing xs with
  | nil => cases xs <;> simp [mixedProducts]
  | cons alphabet alphabets ih =>
    cases xs with
    | nil => simp [mixedProducts]
    | cons x xs =>
      change x :: xs ∈ alphabet.flatMap (fun a => (mixedProducts alphabets).map (List.cons a)) ↔ _
      simp only [List.mem_flatMap, List.mem_map, List.cons.injEq, List.forall₂_cons]
      constructor
      · rintro ⟨a, ha, ys, hys, hax, hy⟩
        subst a ys
        exact ⟨ha, (ih xs).mp hys⟩
      · rintro ⟨hx, hxs⟩
        exact ⟨x, hx, xs, (ih xs).mpr hxs, rfl, rfl⟩

def subgroupCodes (r : ℕ) (otherPrimes : List ℕ) : List ℕ :=
  (List.range r).filter fun n => decide (KernelTest otherPrimes n)

theorem subgroupCodes_primrec : Primrec (fun z : ℕ × List ℕ => subgroupCodes z.1 z.2) := by
  unfold subgroupCodes
  apply filterList (by fun_prop)
  exact kernelTest_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)

def subgroupTables (r : ℕ) (otherPrimes : List ℕ) (length : ℕ) : List (List ℕ) :=
  strings (subgroupCodes r otherPrimes) length

theorem subgroupTables_primrec : Primrec (fun z : ℕ × List ℕ × ℕ =>
    subgroupTables z.1 z.2.1 z.2.2) := by
  have hd : Primrec (fun z : ℕ × List ℕ × ℕ => (z.1, z.2.1)) := by fun_prop
  have ha := subgroupCodes_primrec.comp hd
  have h := strings_primrec.comp (ha.pair (Primrec.snd.comp Primrec.snd))
  exact h

theorem mem_subgroupTables (r : ℕ) (otherPrimes : List ℕ) (length : ℕ) (xs : List ℕ) :
    xs ∈ subgroupTables r otherPrimes length ↔ xs.length = length ∧
      ∀ n ∈ xs, n < r ∧ KernelTest otherPrimes n := by
  rw [subgroupTables, mem_strings]
  simp only [subgroupCodes, List.mem_filter, List.mem_range, decide_eq_true_eq]

open scoped Classical

noncomputable def otherDigitPrimes {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : Label T i) : List ℕ :=
  ((Finset.univ : Finset (Label T i)).filter (· ≠ j)).toList.map (E.digitPrime i)

theorem kernelTest_digitSubgroup {T : LeanWang.TileSet} (E : EncodingParameters T)
    (i : Channel T) (j : Label T i) (n : ℕ) :
    KernelTest (otherDigitPrimes E i j) n ↔ (n : K E i) ∈ digitSubgroup E i j := by
  have hcast (k : Label T i) : digitEquiv E i (n : K E i) k = (n : ZMod (E.digitPrime i k)) := by
    have h := map_natCast (digitEquivRing E i) n
    exact congrFun h k
  simp only [KernelTest, otherDigitPrimes, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and, mem_digitSubgroup, hcast]
  constructor
  · intro h k hk
    apply ZMod.val_injective (E.digitPrime i k)
    simpa only [ZMod.val_natCast, ZMod.val_zero] using h _ ⟨k, hk, rfl⟩
  · intro h r ⟨k, hk, he⟩
    subst r
    simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val (h k hk)

end TranslationTiling.Compiler.Effective
