import TranslationTiling.Compiler.SizeBound
import TranslationTiling.Compiler.EffectiveChoices

/-! A fixed finite domain for a fixed number of Wang tiles. -/
namespace TranslationTiling.Compiler.Size
open LeanWang Compiler.Effective
noncomputable section
local instance : BEq TileSet := instBEqOfDecidableEq

theorem inputs_pos {n : ℕ} (hn : 0<n) : 0<(inputs n).length := by
  rw [inputs_length]
  exact pow_pos (by omega) _

def inputIndex (n : ℕ) (hn : 0<n) (T : TileSet) : Fin (inputs n).length :=
  ⟨(inputs n).idxOf (normalize T) % (inputs n).length,Nat.mod_lt _ (inputs_pos hn)⟩

theorem inputIndex_primrec (n : ℕ) (hn : 0<n) : Primrec (inputIndex n hn) := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.nat_mod.comp
    (Primrec.list_idxOf.comp normalize_primrec (Primrec.const (inputs n))) (Primrec.const _)

def decodeInput (n : ℕ) (i : Fin (inputs n).length) : TileSet := (inputs n).get i

theorem decodeInput_length (n : ℕ) (i : Fin (inputs n).length) : (decodeInput n i).length=n :=
  ((mem_strings _ _ _).mp (List.get_mem (inputs n) i)).1

theorem decodeInput_index (n : ℕ) (hn : 0<n) (T : TileSet) (hT : T.length=n) :
    decodeInput n (inputIndex n hn T)=normalize T := by
  have hm : normalize T∈inputs n := by simpa only [hT] using normalize_mem_inputs T
  have hi := List.idxOf_lt_length_of_mem hm
  unfold decodeInput inputIndex
  simp only [List.get_eq_getElem,Nat.mod_eq_of_lt hi,List.getElem_idxOf]

end
end TranslationTiling.Compiler.Size
