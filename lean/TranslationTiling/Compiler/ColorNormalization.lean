import TranslationTiling.Compiler.EffectiveAlphabet
import Mathlib.Data.List.Basic

/-! Color names are irrelevant to Wang tilability, but not to the numerical
prime choices in the compiler. Renumber the colors by first occurrence before
stating a bound that depends only on the number of input tiles. -/

namespace TranslationTiling.Compiler.Size

open LeanWang
open TranslationTiling.Compiler.Effective

def colors (T : TileSet) : List ℕ := T.flatMap fun t => [t.n, t.s, t.e, t.w]

def rename (f : ℕ → ℕ) (t : WangTile) : WangTile :=
  ⟨f t.n, f t.s, f t.e, f t.w⟩

def normalize (T : TileSet) : TileSet := T.map (rename (colors T).idxOf)

@[simp] theorem colors_length (T : TileSet) : (colors T).length = 4 * T.length := by
  induction T with
  | nil => simp [colors]
  | cons t T ih =>
    change ([t.n, t.s, t.e, t.w] ++ colors T).length = 4 * (T.length + 1)
    simp only [List.length_append, List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem normalize_length (T : TileSet) : (normalize T).length = T.length := by
  simp [normalize]

theorem colors_mem {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    t.n ∈ colors T ∧ t.s ∈ colors T ∧ t.e ∈ colors T ∧ t.w ∈ colors T := by
  have h : ∀ c ∈ [t.n, t.s, t.e, t.w], c ∈ colors T := fun c hc =>
    List.mem_flatMap.mpr ⟨t, ht, hc⟩
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩

theorem normalize_colors_lt {T : TileSet} {t : WangTile} (ht : t ∈ normalize T) :
    t.n < 4 * T.length ∧ t.s < 4 * T.length ∧
      t.e < 4 * T.length ∧ t.w < 4 * T.length := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hn, hs, he, hw⟩ := colors_mem hu
  have hbound (c : ℕ) (hc : c ∈ colors T) : (colors T).idxOf c < 4 * T.length := by
    simpa only [colors_length] using List.idxOf_lt_length_of_mem hc
  exact ⟨hbound _ hn, hbound _ hs, hbound _ he, hbound _ hw⟩

theorem normalize_tilesPlane (T : TileSet) : TilesPlane (normalize T) ↔ TilesPlane T := by
  have decode (t : WangTile) (ht : t ∈ T) :
      rename (fun c => (colors T).getD c 0) (rename (colors T).idxOf t) = t := by
    obtain ⟨hn, hs, he, hw⟩ := colors_mem ht
    have hget (c : ℕ) (hc : c ∈ colors T) :
        (colors T).getD ((colors T).idxOf c) 0 = c := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (List.idxOf_lt_length_of_mem hc), List.getElem_idxOf]
    cases t
    simp only [rename, WangTile.mk.injEq]
    exact ⟨hget _ hn, hget _ hs, hget _ he, hget _ hw⟩
  constructor
  · rintro ⟨x, hx, hy⟩
    let y (p : ℤ × ℤ) : TileIn T :=
      ⟨rename (fun c => (colors T).getD c 0) (x p).val, by
        obtain ⟨t, ht, he⟩ := List.mem_map.mp (x p).property
        rw [← he, decode t ht]
        exact ht⟩
    refine ⟨y, ?_, ?_⟩
    · intro p
      exact congrArg (fun c => (colors T).getD c 0) (hx p)
    · intro p
      exact congrArg (fun c => (colors T).getD c 0) (hy p)
  · rintro ⟨x, hx, hy⟩
    refine ⟨fun p => ⟨rename (colors T).idxOf (x p).val,
      List.mem_map.mpr ⟨_, (x p).property, rfl⟩⟩, ?_, ?_⟩
    · intro p
      exact congrArg (colors T).idxOf (hx p)
    · intro p
      exact congrArg (colors T).idxOf (hy p)

@[fun_prop] theorem colors_primrec : Primrec colors := by
  unfold colors
  fun_prop

theorem normalize_primrec : Primrec normalize := by
  unfold normalize
  apply mapList Primrec.id
  have hi : Primrec (fun p : TileSet × ℕ => (colors p.1).idxOf p.2) := by
    exact Primrec.list_idxOf.comp Primrec.snd (colors_primrec.comp Primrec.fst)
  have hr : Primrec (fun p : TileSet × WangTile =>
      ((colors p.1).idxOf p.2.n, (colors p.1).idxOf p.2.s,
       (colors p.1).idxOf p.2.e, (colors p.1).idxOf p.2.w)) := by
    exact (hi.comp (Primrec.fst.pair (WangTile.n_primrec.comp Primrec.snd))).pair
      ((hi.comp (Primrec.fst.pair (WangTile.s_primrec.comp Primrec.snd))).pair
        ((hi.comp (Primrec.fst.pair (WangTile.e_primrec.comp Primrec.snd))).pair
          (hi.comp (Primrec.fst.pair (WangTile.w_primrec.comp Primrec.snd)))))
  exact ((Primrec.of_equiv_symm (e := WangTile.equivTuple)).comp hr).of_eq (fun _ => rfl)

end TranslationTiling.Compiler.Size
