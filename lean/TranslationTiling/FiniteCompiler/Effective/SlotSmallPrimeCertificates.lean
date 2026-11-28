import TranslationTiling.FiniteCompiler.Effective.SlotPrimeSelection

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

private theorem certifiedShortCap (t c : ℕ) (primes : List ℕ)
    (hcount : primes.length = c) (hnd : primes.Nodup)
    (hr : ∀ p ∈ primes, t < p ∧ p ≤ t+32*(c+1))
    (hp : ∀ p ∈ primes, p.Prime)
    (hs : t+32*(c+1) ≤ guardedPrimeCap (t+c+16))
    (hw : t+32*(c+1) ≤ slotWindowCap t c) :
    slotSearchCap t c = t+32*(c+1) := by
  apply slotSearchCap_eq_short hs hw
  have hsub : primes.toFinset ⊆ (slotPrimeInterval t (t+32*(c+1))).toFinset := by
    intro p h
    have hm := List.mem_toFinset.mp h
    exact List.mem_toFinset.mpr (mem_slotPrimeInterval.mpr ⟨hp p hm,hr p hm⟩)
  have h := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rwa [List.toFinset_card_of_nodup hnd,hcount] at h

theorem slotSearchCap_2048_4 : slotSearchCap 2048 4 = 2208 := by
  apply certifiedShortCap _ _ [2053, 2063, 2069, 2081]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2048_16 : slotSearchCap 2048 16 = 2592 := by
  apply certifiedShortCap _ _ [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
      2129, 2131, 2137, 2141, 2143, 2153]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2208_6 : slotSearchCap 2208 6 = 2432 := by
  apply certifiedShortCap _ _ [2213, 2221, 2237, 2239, 2243, 2251]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2208_12 : slotSearchCap 2208 12 = 2624 := by
  apply certifiedShortCap _ _ [2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2592_24 : slotSearchCap 2592 24 = 3392 := by
  apply certifiedShortCap _ _ [2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671,
      2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719,
      2729, 2731, 2741, 2749]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2592_48 : slotSearchCap 2592 48 = 4160 := by
  apply certifiedShortCap _ _ [2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671,
      2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719,
      2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797,
      2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879,
      2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2592_72 : slotSearchCap 2592 72 = 4928 := by
  apply certifiedShortCap _ _ [2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671,
      2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719,
      2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797,
      2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879,
      2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963,
      2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049,
      3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163,
      3167, 3169]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_5369856_2 : slotSearchCap 5369856 2 = 5369952 := by
  apply certifiedShortCap _ _ [5369857, 5369863]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_5793792_4 : slotSearchCap 5793792 4 = 5793952 := by
  apply certifiedShortCap _ _ [5793847, 5793871, 5793883, 5793899]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_8792064_8 : slotSearchCap 8792064 8 = 8792352 := by
  apply certifiedShortCap _ _ [8792087, 8792099, 8792101, 8792123, 8792129, 8792131, 8792137, 8792197]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_10782720_16 : slotSearchCap 10782720 16 = 10783264 := by
  apply certifiedShortCap _ _ [10782721, 10782731, 10782763, 10782767, 10782817, 10782829, 10782839, 10782847, 10782853, 10782857,
      10782887, 10782901, 10782907, 10782911, 10782953, 10782971]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_12773376_24 : slotSearchCap 12773376 24 = 12774176 := by
  apply certifiedShortCap _ _ [12773381, 12773393, 12773413, 12773429, 12773447, 12773459, 12773471, 12773513, 12773521, 12773531,
      12773549, 12773557, 12773587, 12773597, 12773609, 12773627, 12773653, 12773669, 12773693, 12773699,
      12773701, 12773711, 12773737, 12773741]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2208_18 : slotSearchCap 2208 18 = 2816 := by
  apply certifiedShortCap _ _ [2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_6217728_6 : slotSearchCap 6217728 6 = 6217952 := by
  apply certifiedShortCap _ _ [6217741, 6217747, 6217777, 6217789, 6217811, 6217817]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_2048_32 : slotSearchCap 2048 32 = 3104 := by
  apply certifiedShortCap _ _ [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293]
  · decide
  · decide
  · decide
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide


theorem slotSearchCap_3104_96 : slotSearchCap 3104 96 = 6208 := by
  apply certifiedShortCap _ _ [3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191,
      3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271,
      3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347,
      3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449,
      3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527,
      3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583,
      3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671,
      3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739,
      3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833,
      3847, 3851, 3853, 3863, 3877, 3881]
  · decide
  · decide +kernel
  · decide +kernel
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_19269632_32 : slotSearchCap 19269632 32 = 19270688 := by
  apply certifiedShortCap _ _ [19269647, 19269661, 19269673, 19269683, 19269703, 19269727, 19269739, 19269769, 19269779, 19269787,
      19269797, 19269829, 19269841, 19269847, 19269851, 19269869, 19269881, 19269907, 19269967, 19269973,
      19269979, 19269989, 19270019, 19270051, 19270073, 19270079, 19270087, 19270157, 19270169, 19270177,
      19270183, 19270187]
  · decide
  · decide +kernel
  · decide +kernel
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_3104_144 : slotSearchCap 3104 144 = 7744 := by
  apply certifiedShortCap _ _ [3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191,
      3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271,
      3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347,
      3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449,
      3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527,
      3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583,
      3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671,
      3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739,
      3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833,
      3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917,
      3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003,
      4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079,
      4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157,
      4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243,
      4253, 4259, 4261, 4271]
  · decide
  · decide +kernel
  · decide +kernel
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

theorem slotSearchCap_24037376_48 : slotSearchCap 24037376 48 = 24038944 := by
  apply certifiedShortCap _ _ [24037379, 24037423, 24037441, 24037459, 24037469, 24037471, 24037487, 24037499, 24037511, 24037529,
      24037537, 24037543, 24037561, 24037577, 24037579, 24037589, 24037591, 24037597, 24037621, 24037649,
      24037669, 24037681, 24037729, 24037733, 24037747, 24037751, 24037763, 24037777, 24037787, 24037789,
      24037801, 24037823, 24037859, 24037877, 24037913, 24037919, 24037933, 24037939, 24037943, 24037961,
      24037963, 24037969, 24037997, 24037999, 24038023, 24038039, 24038057, 24038083]
  · decide
  · decide +kernel
  · decide +kernel
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  · decide
  · decide

end TranslationTiling.FiniteCompiler.Packed
