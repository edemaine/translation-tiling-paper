import TranslationTiling.FiniteCompiler.SlotShift

namespace TranslationTiling.FiniteCompiler.SlotShift

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d] {m : ZMod d → ℕ}

/-- On a fixed target high fibre, the block coordinates restore the
corresponding shift coordinates up to a translation. The resulting
bijection determines the shift index and then the low inputs. -/
theorem block_map_bijective (hm : ∀ j, 1 < m j) {K : Type*}
    (high : Shift m → K ≃ K)
    (S : K → Set (ZMod d)) (hne : ∀ k, (S k).Nonempty)
    (c : K → Shift m) :
    Function.Bijective (fun (v : K × Shift m) =>
      let k := high v.2 v.1
      (c k + restore (S k) v.2, k)) := by
  let f : K × Shift m → Shift m × K := fun v =>
    let k := high v.2 v.1
    (c k + restore (S k) v.2,k)
  change Function.Bijective f
  constructor
  · intro v w he
    have hk : high v.2 v.1 = high w.2 w.1 := congrArg Prod.snd he
    have h := congrArg Prod.fst he
    change c (high v.2 v.1) + restore (S (high v.2 v.1)) v.2 =
      c (high w.2 w.1) + restore (S (high w.2 w.1)) w.2 at h
    rw [hk] at h
    have hu : v.2 = w.2 := (restore_bijective hm (hne _)).1 (add_left_cancel h)
    apply Prod.ext _ hu
    rw [hu] at hk
    exact (high w.2).injective hk
  · rintro ⟨z,k⟩
    obtain ⟨u,hu⟩ := (restore_bijective hm (hne k)).2 (z-c k)
    refine ⟨((high u).symm k,u),?_⟩
    change (c (high u ((high u).symm k)) + restore (S (high u ((high u).symm k))) u,
      high u ((high u).symm k)) = (z,k)
    rw [(high u).apply_symm_apply,hu,add_sub_cancel]

end

end TranslationTiling.FiniteCompiler.SlotShift
