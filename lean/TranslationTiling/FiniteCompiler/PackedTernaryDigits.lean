import TranslationTiling.FiniteCompiler.PackedTernaryLayout
import TranslationTiling.FiniteCompiler.Effective.MixedCode

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall
open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def radixDigit (r k i v : ℕ) : ℕ :=
  if i < 18 then v else v / r^((i-18)%k)%r

variable {T : LeanWang.TileSet} {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
  (C : Code T (radixLayoutProfile r k).radices.prod)

local instance packedTernaryDigitsAlphabet : AlphabetFamily (system C) := GuardedCompiler.alphabet C

local notation "p" => radixLayoutProfile r k

private theorem arithmeticFibre_index (i : Column (system C)) (j : (p).Fibre i)
    (hi : i.val < 18) : j.val.val = i.val := by
  have he := congrArg Fin.val j.property
  rw [origin_val] at he
  split_ifs at he <;> omega

private theorem wangFibre_nonarithmetic (i : Column (system C)) (j : (p).Fibre i)
    (hi : 18 ≤ i.val) : 18 ≤ j.val.val := by
  have he := congrArg Fin.val j.property
  rw [origin_val] at he
  split_ifs at he <;> omega

include hk hr in
private theorem digit_in_range (i : Column (system C)) (v : Letter (system C) i)
    (j : (p).Fibre i) : radixDigit r k j.val.val v.val < (p).arity j.val.val := by
  by_cases hi : i.val < 18
  · have hj := arithmeticFibre_index C i j hi
    unfold radixDigit
    rw [hj, if_pos hi]
    have hv := v.isLt
    change v.val < PairSmall.arity (p).radices.prod i at hv
    rw [arity_original, if_pos hi] at hv
    rw [radixLayout_arity hk (show i.val < (p).width from hj ▸ j.val.isLt), if_pos hi]
    exact hv
  · have hj := wangFibre_nonarithmetic C i j (by omega)
    unfold radixDigit
    rw [if_neg (by omega), radixLayout_arity hk j.val.isLt]
    simp only [if_neg (by omega : ¬ j.val.val < 9), if_neg (by omega : ¬ j.val.val < 18)]
    exact Nat.mod_lt _ hr

private def toDigits (i : Column (system C)) (v : Letter (system C) i)
    (j : (p).Fibre i) : Fin ((p).arity j.val.val) :=
  ⟨radixDigit r k j.val.val v.val, digit_in_range hk hr C i v j⟩

private theorem toDigits_injective (i : Column (system C)) :
    Function.Injective (toDigits hk hr C i) := by
  intro v u he
  have h (j : (p).Fibre i) : radixDigit r k j.val.val v.val = radixDigit r k j.val.val u.val :=
    congrArg Fin.val (congrFun he j)
  by_cases hi : i.val < 18
  · obtain ⟨j,hj⟩ := (packedRadix_layout p hk hr rfl).cover i
    have hv := h ⟨j,hj⟩
    unfold radixDigit at hv
    simp only [if_pos (arithmeticFibre_index C i ⟨j,hj⟩ hi ▸ hi)] at hv
    exact Fin.ext hv
  · apply Fin.ext
    have hv := v.isLt
    have hu := u.isLt
    change v.val < PairSmall.arity (p).radices.prod i at hv
    change u.val < PairSmall.arity (p).radices.prod i at hu
    have hcap : PairSmall.arity (p).radices.prod i = r^k := by
      rw [arity_original, if_neg (by omega), if_neg hi]
      simp [radixLayoutProfile,List.prod_replicate]
    rw [hcap] at hv hu
    apply FiniteCompiler.Effective.eq_of_digits hr hv hu
    intro a ha
    let t : Fin 2 := ⟨i.val-18, by have h : i.val < 20 := i.isLt; omega⟩
    have he : (⟨18+t.val,by have := t.isLt; omega⟩ : Fin 20) = i := Fin.ext (by dsimp [t]; omega)
    let j : (p).Fibre i := ⟨⟨18+t.val*k+a,by
      rw [radixLayout_width]
      have ht := t.isLt
      have ht' : t.val*k ≤ k := (Nat.mul_le_mul_right k (show t.val ≤ 1 by omega)).trans_eq (one_mul k)
      omega⟩, (wangFibre_iff p _ t).mpr (by
        simp only [Fin.val_mk,radixLayoutProfile,List.length_replicate,Nat.add_mul,one_mul]
        omega) |>.trans he⟩
    have hout := h j
    unfold radixDigit at hout
    have hj₀ : ¬ j.val.val < 18 := by dsimp [j]; omega
    have hmod : (j.val.val-18)%k = a := by
      dsimp [j]
      rw [show 18+t.val*k+a-18=t.val*k+a by omega, Nat.mul_add_mod_self_right,
        Nat.mod_eq_of_lt ha]
    simpa only [if_neg hj₀,hmod] using hout

/-- The refinement uses the usual radix-r digits of each Wang label index. -/
def explicitRadixCode (i : Column (system C)) :
    Letter (system C) i ≃ ((j : (p).Fibre i) → Fin ((p).arity j.val.val)) := by
  apply Equiv.ofBijective (toDigits hk hr C i)
  refine ⟨toDigits_injective hk hr C i,?_⟩
  let e := letterCode p (packedRadix_layout p hk hr rfl) C i
  intro u
  obtain ⟨j,hj⟩ := Finite.surjective_of_injective ((toDigits_injective hk hr C i).comp e.symm.injective) u
  exact ⟨e.symm j,hj⟩

theorem explicitRadixCode_val (i : Column (system C)) (v : Letter (system C) i) (j : (p).Fibre i) :
    (explicitRadixCode hk hr C i v j).val = radixDigit r k j.val.val v.val := rfl

end
end TranslationTiling.FiniteCompiler.Packed
