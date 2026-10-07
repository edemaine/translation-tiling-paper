import TranslationTiling.Compiler.EffectiveWordRuleCorrect

namespace TranslationTiling.Compiler.Effective

def symbols (T : LeanWang.TileSet) : List RawSymbol :=
  (List.range (Sudoku.p - 1)).flatMap fun a =>
    (List.range (Sudoku.q - 1)).flatMap fun b => T.map fun t => (a + 1, b + 1, t)

@[fun_prop] theorem symbols_primrec : Primrec symbols := by unfold symbols; fun_prop

theorem mem_symbols (T : LeanWang.TileSet) (s : RawSymbol) :
    s ∈ symbols T ↔ ∃ j : Sudoku.Symbol T, rawSymbol j = s := by
  letI : Fact Sudoku.p.Prime := ⟨by decide⟩
  letI : Fact Sudoku.q.Prime := ⟨by decide⟩
  constructor
  · intro hs
    obtain ⟨a, ha, b, hb, t, ht, rfl⟩ :=
      (by simpa only [symbols, List.mem_flatMap, List.mem_map] using hs :
        ∃ a ∈ List.range (Sudoku.p - 1), ∃ b ∈ List.range (Sudoku.q - 1),
          ∃ t ∈ T, (a + 1, b + 1, t) = s)
    have hap : a + 1 < Sudoku.p := by have := List.mem_range.mp ha; omega
    have hbq : b + 1 < Sudoku.q := by have := List.mem_range.mp hb; omega
    have han : ((a + 1 : ℕ) : ZMod Sudoku.p) ≠ 0 := by
      intro he
      have hv := congrArg ZMod.val he
      simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hap] at hv
      omega
    have hbn : ((b + 1 : ℕ) : ZMod Sudoku.q) ≠ 0 := by
      intro he
      have hv := congrArg ZMod.val he
      simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hbq] at hv
      omega
    refine ⟨(Units.mk0 ((a + 1 : ℕ) : ZMod Sudoku.p) han,
      Units.mk0 ((b + 1 : ℕ) : ZMod Sudoku.q) hbn, ⟨t, ht⟩), ?_⟩
    simp only [rawSymbol, Units.val_mk0, ZMod.val_natCast, Nat.mod_eq_of_lt hap,
      Nat.mod_eq_of_lt hbq]
  · rintro ⟨j, rfl⟩
    have ha : 0 < j.1.val.val := by
      apply Nat.pos_of_ne_zero
      intro h
      exact Units.ne_zero j.1 ((ZMod.val_eq_zero _).mp h)
    have hb : 0 < j.2.1.val.val := by
      apply Nat.pos_of_ne_zero
      intro h
      exact Units.ne_zero j.2.1 ((ZMod.val_eq_zero _).mp h)
    have hap := ZMod.val_lt j.1.val
    have hbq := ZMod.val_lt j.2.1.val
    simp only [symbols, List.mem_flatMap, List.mem_map]
    refine ⟨j.1.val.val - 1, List.mem_range.mpr (by omega),
      j.2.1.val.val - 1, List.mem_range.mpr (by omega), j.2.2.val, j.2.2.property, ?_⟩
    simp only [rawSymbol]
    congr 2 <;> omega

theorem rawSymbol_injective (T : LeanWang.TileSet) : Function.Injective (rawSymbol (T := T)) := by
  intro j k h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun z : RawSymbol => z.2.1) h
  have h3 := congrArg (fun z : RawSymbol => z.2.2) h
  exact Prod.ext (Units.ext (ZMod.val_injective Sudoku.p h1))
    (Prod.ext (Units.ext (ZMod.val_injective Sudoku.q h2)) (Subtype.ext h3))

def strings {α : Type*} (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (strings alphabet n).map (List.cons a)

theorem strings_primrec {α : Type*} [Primcodable α] :
    Primrec (fun z : List α × ℕ => strings z.1 z.2) := by
  have hstep : Primrec₂ (fun (z : List α × ℕ) (p : ℕ × List (List α)) =>
      z.1.flatMap fun a => p.2.map (List.cons a)) := by
    change Primrec _
    fun_prop
  have hp := Primrec.nat_rec' (g := fun _ : List α × ℕ => ([[]] : List (List α)))
    (h := fun z p => z.1.flatMap fun a => p.2.map (List.cons a))
    Primrec.snd (Primrec.const _) hstep
  apply hp.of_eq
  intro z
  induction z.2 with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, strings, ih]

theorem mem_strings {α : Type*} (alphabet : List α) (n : ℕ) (xs : List α) :
    xs ∈ strings alphabet n ↔ xs.length = n ∧ ∀ a ∈ xs, a ∈ alphabet := by
  induction n generalizing xs with
  | zero =>
    constructor
    · intro h
      have he : xs = [] := by simpa only [strings, List.mem_singleton] using h
      subst xs
      simp
    · rintro ⟨hlen, _⟩
      have he : xs = [] := List.length_eq_zero_iff.mp hlen
      subst xs
      simp [strings]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨a, ha, ys, hys, rfl⟩ :=
        (by simpa only [strings, List.mem_flatMap, List.mem_map] using h :
          ∃ a ∈ alphabet, ∃ ys ∈ strings alphabet n, a :: ys = xs)
      obtain ⟨hlen, hmem⟩ := (ih ys).mp hys
      exact ⟨by simp [hlen], fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ ha) (hmem x)⟩
    · rintro ⟨hlen, hmem⟩
      cases xs with
      | nil => simp at hlen
      | cons a ys =>
        apply List.mem_flatMap.mpr
        refine ⟨a, hmem a (by simp), List.mem_map.mpr ⟨ys, ?_, rfl⟩⟩
        exact (ih ys).mpr ⟨by simpa using hlen, fun x hx => hmem x (List.mem_cons_of_mem _ hx)⟩

def emptyRawSymbol : RawSymbol := (0, 0, LeanWang.WangTile.ofTuple (0, 0, 0, 0))

def wordOfList (xs : List RawSymbol) : RawWord := fun n => xs.getD n.val emptyRawSymbol

@[fun_prop] theorem wordOfList_primrec : Primrec wordOfList := by
  apply piValue
  intro n
  exact (Primrec.list_getD emptyRawSymbol).comp Primrec.id (Primrec.const n.val)

def words (T : LeanWang.TileSet) : List RawWord :=
  (strings (symbols T) Sudoku.Width).map wordOfList

@[fun_prop] theorem words_primrec : Primrec words := by
  unfold words
  apply mapList (strings_primrec.comp (symbols_primrec.pair (Primrec.const Sudoku.Width)))
  fun_prop

theorem mem_words (T : LeanWang.TileSet) (w : RawWord) :
    w ∈ words T ↔ ∃ W : Sudoku.Column → Sudoku.Symbol T, rawWord W = w := by
  classical
  constructor
  · intro hw
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hlen, hmem⟩ := (mem_strings _ _ _).mp hxs
    have hsymbols (n : Sudoku.Column) : ∃ j : Sudoku.Symbol T, rawSymbol j = wordOfList xs n := by
      apply (mem_symbols T _).mp
      apply hmem
      have hn : n.val < xs.length := by rw [hlen]; exact n.isLt
      simpa [wordOfList, List.getD_eq_getElem?_getD, hn] using List.getElem_mem hn
    refine ⟨fun n => Classical.choose (hsymbols n), ?_⟩
    funext n
    exact Classical.choose_spec (hsymbols n)
  · rintro ⟨W, rfl⟩
    apply List.mem_map.mpr
    refine ⟨List.ofFn (rawWord W), (mem_strings _ _ _).mpr ⟨by simp only [List.length_ofFn], ?_⟩, ?_⟩
    · intro j hj
      obtain ⟨n, rfl⟩ := List.mem_ofFn.mp hj
      exact (mem_symbols T _).mpr ⟨W n, rfl⟩
    · funext n
      simp only [wordOfList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        dif_pos n.isLt, Option.getD_some]

def allowedWordCodes (T : LeanWang.TileSet) : List RawWord :=
  (words T).filter fun w => decide (WordTest T w)

theorem allowedWordCodes_primrec : Primrec allowedWordCodes := filterList words_primrec wordTest_primrec

theorem mem_allowedWordCodes (T : LeanWang.TileSet) (w : RawWord) :
    w ∈ allowedWordCodes T ↔
      ∃ W : Sudoku.Column → Sudoku.Symbol T, rawWord W = w ∧ Sudoku.Allowed T W := by
  simp only [allowedWordCodes, List.mem_filter, decide_eq_true_eq, mem_words]
  constructor
  · rintro ⟨⟨W, rfl⟩, hw⟩
    exact ⟨W, rfl, (wordTest_iff W).mp hw⟩
  · rintro ⟨W, rfl, hW⟩
    exact ⟨⟨W, rfl⟩, (wordTest_iff W).mpr hW⟩

end TranslationTiling.Compiler.Effective
