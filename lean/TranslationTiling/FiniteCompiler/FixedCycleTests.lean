import TranslationTiling.FiniteCompiler.SparseCycleTests

namespace TranslationTiling.FiniteCompiler

variable [SeedFrame]
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

def digitGenerator (i : Channel T) (j : Label T i) : K E i :=
  (E.r i / E.digitPrime i j : ℕ)

theorem digitGenerator_mem (i : Channel T) (j : Label T i) :
    digitGenerator E i j ∈ digitSubgroup E i j := by
  have hr : E.r i / E.digitPrime i j =
      ∏ k ∈ (Finset.univ.erase j), E.digitPrime i k := by
    rw [E.r_eq_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    exact Nat.mul_div_cancel _ (E.prime_isPrime (.inr (.inr ⟨i,j⟩))).pos
  intro k hk
  change digitEquiv E i (E.r i / E.digitPrime i j : ℕ) k=0
  rw [show digitEquiv E i (E.r i / E.digitPrime i j : ℕ) k =
      (E.r i / E.digitPrime i j : ZMod (E.digitPrime i k)) from
    congrFun (map_natCast (digitEquivRing E i) _) k]
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  rw [hr]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ _⟩)

theorem digitGenerator_ne_zero (i : Channel T) (j : Label T i) :
    digitGenerator E i j ≠ 0 := by
  have hp := E.prime_isPrime (.inr (.inr ⟨i,j⟩))
  have hle := Nat.le_of_dvd (E.r_pos i) (digitPrime_dvd_r E i j)
  have hpos := Nat.div_pos hle hp.pos
  have hlt := Nat.div_lt_self (E.r_pos i) hp.one_lt
  intro he
  change ((E.r i / E.digitPrime i j : ℕ) : ZMod (E.r i))=0 at he
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) ((ZMod.natCast_eq_zero_iff _ _).mp he)

theorem digitGenerator_spans (i : Channel T) (j : Label T i)
    (u : K E i) (hu : u ∈ digitSubgroup E i j) :
    ∃ n : ℕ, n • digitGenerator E i j = u := by
  let : Fact (E.digitPrime i j).Prime := ⟨E.prime_isPrime (.inr (.inr ⟨i,j⟩))⟩
  let v := digitEquiv E i (digitGenerator E i j) j
  have hv : v≠0 := by
    intro he
    apply digitGenerator_ne_zero E i j
    apply (digitEquiv E i).injective
    ext k
    by_cases hk : k=j
    · subst k; simpa only [map_zero,Pi.zero_apply] using he
    · simpa only [map_zero,Pi.zero_apply] using digitGenerator_mem E i j k hk
  let a := digitEquiv E i u j / v
  refine ⟨a.val,?_⟩
  apply (digitEquiv E i).injective
  ext k
  simp only [map_nsmul,Pi.smul_apply]
  by_cases hk : k=j
  · subst k
    change a.val • v = digitEquiv E i u j
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hv
  · rw [digitGenerator_mem E i j k hk,hu k hk,nsmul_zero]

omit [SeedFrame] in
/-- A generator detects every nonconstant restriction to a coset. -/
theorem digitActive_generator_step {M Y : Type*} [AddCommGroup M]
    {U : AddSubgroup M} (s : U) (hspan : ∀ u ∈ U, ∃ n : ℕ, n • (s : M) = u)
    (g : M → Y) (hg : DigitActive g U) :
    ∃ w, g w ≠ g (w - (s : M)) := by
  by_contra hn
  have hstep : ∀ w, g w=g (w-(s : M)) := by simpa using hn
  have hiter (w : M) (n : ℕ) : g w=g (w-n • (s : M)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ = g (w-n • (s : M)) := ih
        _ = g ((w-n • (s : M))-(s : M)) := hstep _
        _ = _ := by congr 1; rw [succ_nsmul]; abel
  obtain ⟨w,w',hmem,hne⟩ := hg
  obtain ⟨n,hn⟩ := hspan _ hmem
  exact hne (by simpa only [hn,sub_sub_cancel] using hiter w n)

def cycleGeneratorMaps {I : Type*} {M N : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Zero (N i)] [∀ i, DecidableEq (N i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ I) (U : ∀ j, AddSubgroup (M (cycle j)))
    (step : ∀ j, U j) : ∀ j, N (cycle (j-1)) → U j :=
  fun j e => if e = 0 then 0 else step j

/-- Fixed-cycle exclusion depends only on the observed additive coordinates. -/
theorem cycleMap_generator_bijective_iff {I : Type*} [Fintype I] {M N : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Fintype (N i)]
    [∀ i, DecidableEq (N i)] {t : ℕ} [NeZero t] (cycle : ZMod t ↪ I) (U : ∀ j, AddSubgroup (M (cycle j)))
    (step : ∀ j, U j) (hspan : ∀ j u, u ∈ U j → ∃ n : ℕ, n • (step j : M (cycle j)) = u)
    (g : ∀ i, M i → N i) :
    (∀ k, Function.Bijective (cycleMap cycle U (cycleGeneratorMaps cycle U step) g k)) ↔
    ∃ j, ¬ DigitActive (g (cycle j)) (U j) := by
  classical
  constructor
  · intro hall
    by_contra hn
    have hactive : ∀ j, DigitActive (g (cycle j)) (U j) := by
      simpa only [not_exists,not_not] using hn
    choose w hw using fun j => digitActive_generator_step (step j) (hspan j) (g (cycle j)) (hactive j)
    let e₀ : ∀ j, N (cycle j) := fun j => g (cycle j) (w j)-
      g (cycle j) (w j-(step j : M (cycle j)))
    have he₀ (j) : e₀ j≠0 := sub_ne_zero.mpr (hw j)
    let e : ∀ i, N i := cycleExtend cycle e₀
    let k : ∀ i, M i := cycleExtend cycle w
    have hcol : cycleMap cycle U
        (cycleGeneratorMaps cycle U step) g k 0 =
        cycleMap cycle U
        (cycleGeneratorMaps cycle U step) g k e := by
      funext i
      by_cases hi : ∃ j, cycle j=i
      · obtain ⟨j,rfl⟩ := hi
        simp only [cycleMap_apply_cycle,k,e,cycleExtend_apply,Pi.zero_apply,
          cycleGeneratorMaps,ite_true,ZeroMemClass.coe_zero,sub_zero,zero_add,
          ite_eq_right (he₀ (j-1))]
        change g (cycle j) (w j) =
          (g (cycle j) (w j)-g (cycle j) (w j-(step j : M (cycle j))))+
            g (cycle j) (w j-(step j : M (cycle j)))
        exact (sub_add_cancel _ _).symm
      · have hoff : ∀ j, cycle j≠i := by simpa only [not_exists] using hi
        simp only [cycleMap,Pi.zero_apply,e,cycleExtend_eq_zero cycle e₀ hoff,
          cycleShift_eq_zero cycle _ _ _ hoff,sub_zero,zero_add]
    have he : e=0 := ((hall k).1 hcol).symm
    apply he₀ 0
    have hh := congrFun he (cycle 0)
    simpa only [e,cycleExtend_apply,Pi.zero_apply] using hh
  · rintro ⟨j,hj⟩ k
    exact cycleMap_bijective_of_inactive cycle _ _ g k j hj

theorem digitActive_step (i : Channel T) (j : Label T i) (g : K E i → P E i)
    (hg : DigitActive g (digitSubgroup E i j)) :
    ∃ w, g w ≠ g (w-digitGenerator E i j) :=
  digitActive_generator_step ⟨digitGenerator E i j,digitGenerator_mem E i j⟩
    (fun u hu => digitGenerator_spans E i j u hu) g hg

def fixedCycleMaps {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) :
    ∀ j, P E (cycle (j-1)) → digitSubgroup E (cycle j) (labels j) :=
  fun j e => if e=0 then 0 else ⟨digitGenerator E (cycle j) (labels j),digitGenerator_mem E _ _⟩

theorem fixedCycleMap_bijective_iff {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j))
    (g : ∀ i, K E i → P E i) :
    (∀ k, Function.Bijective (cycleMap cycle (fun j => digitSubgroup E (cycle j) (labels j))
      (fixedCycleMaps E cycle labels) g k)) ↔
    ∃ j, ¬ DigitActive (g (cycle j)) (digitSubgroup E (cycle j) (labels j)) :=
  cycleMap_generator_bijective_iff cycle _ (fun j => ⟨digitGenerator E (cycle j) (labels j), digitGenerator_mem E _ _⟩)
    (fun j u hu => digitGenerator_spans E (cycle j) (labels j) u hu) g

def fixedCycleTiles {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) : Finset (Finset (Ambient E)) :=
  {cycleTile E cycle labels (fixedCycleMaps E cycle labels)}

theorem fixedCycleTiles_subset_cycleTiles {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    fixedCycleTiles E cycle labels ⊆ cycleTiles E cycle labels := by
  intro F hF
  obtain rfl := Finset.mem_singleton.mp hF
  exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem nonempty_of_mem_fixedCycleTiles {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j))
    {F : Finset (Ambient E)} (hF : F∈fixedCycleTiles E cycle labels) : F.Nonempty :=
  nonempty_of_mem_cycleTiles E cycle labels (fixedCycleTiles_subset_cycleTiles E cycle labels hF)

theorem fixed_cycle_exclusion_iff {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j))
    (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F∈fixedCycleTiles E cycle labels, Tiles F (graph o)) ↔
      ∀ x, ∃ j, ¬ Active E o (cycle j) x (labels j) := by
  simp only [fixedCycleTiles,Finset.mem_singleton,forall_eq]
  rw [cycleTile_iff E cycle labels _ o (usefulAt E o) (usefulAt_factor E hdep)]
  exact forall_congr' (fun x => fixedCycleMap_bijective_iff E cycle labels (fun i => usefulAt E o i x))

theorem fixedCycleTiles_card_le {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    (fixedCycleTiles E cycle labels).card ≤
      ∏ j, Fintype.card (P E (cycle (j-1))) * Fintype.card (digitSubgroup E (cycle j) (labels j)) := by
  change 1≤_
  apply Finset.one_le_prod
  intro j _
  exact Nat.mul_pos (Fintype.card_pos) (Fintype.card_pos)

end
end TranslationTiling.FiniteCompiler
