import Erdos684Lean.Code
import Erdos684Lean.Kummer
import Erdos684Lean.AsymptoticsPNT

/-!
# The four carry ranges (paper Section 6)

For the selected multiplier `t` and `n = n_t = tL - h - 1`, uniformly for `1 ≤ k ≤ K`:

* range (I)   `D1 ≤ log C(h+k, h) ≤ (1/20 + o(1)) M`   (paper Lemma 6.1);
* range (II)  `D2 ≤ (1/10 + o(1)) M`                    (paper Lemma 6.2);
* range (III) `D3 ≤ ψ(K) - θ(K) = o(M)`                 (paper (58));
* range (IV)  `D4 ≤ Z(t) < βM`                          (paper (59)).
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-! ### Range (I) -/

/-- Paper Lemma 6.1, first part: range (I) is a subsum of `log C(h+k,h)`. -/
theorem D1_le {M t k : ℕ} (ht : hof P M + 1 ≤ t * Lof M) :
    D1 M (nOf P M t) k ≤ Real.log ((hof P M + k).choose (hof P M)) := by
  have hchoose : ((hof P M + k).choose (hof P M)) =
      ∏ p ∈ range (hof P M + k + 1), p ^ ((hof P M + k).choose (hof P M)).factorization p :=
    (Nat.prod_pow_factorization_choose (hof P M + k) (hof P M) (Nat.le_add_right _ _)).symm
  -- per-prime bound: the carries at levels `p^a ≤ M` are carries of `C(h+k, h)`
  have key : ∀ p ∈ primesLE k,
      (∑ a ∈ Ico 1 (nOf P M t + 1),
        if nOf P M t % p ^ a < k % p ^ a ∧ p ^ a ≤ M then Real.log p else 0)
        ≤ (((hof P M + k).choose (hof P M)).factorization p : ℝ) * Real.log p := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
    have hb : Nat.log p (hof P M + k) < max (nOf P M t + 1) (Nat.log p (hof P M + k) + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    rw [Nat.choose_symm_add, Nat.factorization_choose' hpp hb]
    norm_cast
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    obtain ⟨⟨h1a, han⟩, hcar, hpaM⟩ := ha
    refine ⟨⟨h1a, lt_of_lt_of_le han (le_max_left _ _)⟩, ?_⟩
    have hq : 0 < p ^ a := pow_pos hpp.pos a
    have hdvd : p ^ a ∣ t * Lof M := Dvd.dvd.mul_left (dvd_Lof hq hpaM) t
    have hcar' : (t * Lof M - hof P M - 1) % p ^ a < k % p ^ a := hcar
    have := (carry_identity (k := k) hq hdvd ht).mp hcar'
    rw [add_comm]
    exact this
  calc D1 M (nOf P M t) k
      ≤ ∑ p ∈ primesLE k, (((hof P M + k).choose (hof P M)).factorization p : ℝ) * Real.log p :=
        Finset.sum_le_sum key
    _ ≤ ∑ p ∈ range (hof P M + k + 1),
          (((hof P M + k).choose (hof P M)).factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_range]
          have := (Nat.mem_primesLE.mp hp).1
          omega
        · intro p _ _
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    _ = Real.log ((hof P M + k).choose (hof P M)) := by
        conv_rhs => rw [hchoose]
        push_cast
        rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro p _
          rw [Real.log_pow]
        · intro p _
          rcases Nat.eq_zero_or_pos p with rfl | hp
          · simp [Nat.factorization_zero_right]
          · exact pow_ne_zero _ (by exact_mod_cast hp.ne')

/-- `log C(h+k, h) ≤ h (1 + log (1 + k/h))` for `h ≥ 1` (paper, elementary estimate). -/
theorem log_choose_le {h k : ℕ} (hh : 0 < h) :
    Real.log ((h + k).choose h) ≤ h * (1 + Real.log (1 + (k : ℝ) / h)) := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hpos : (0:ℝ) < (h + k).choose h := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right h k)
  have h1 : ((h + k).choose h : ℝ) ≤ ((h + k : ℕ) : ℝ) ^ h / (h.factorial : ℝ) :=
    Nat.choose_le_pow_div h (h + k)
  have h2 : (h : ℝ) ^ h / (h.factorial : ℝ) ≤ Real.exp h :=
    Real.pow_div_factorial_le_exp _ hhR.le h
  have hfact : (0:ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have h3 : ((h + k : ℕ) : ℝ) ^ h / (h.factorial : ℝ)
      = (1 + (k:ℝ) / h) ^ h * ((h:ℝ) ^ h / h.factorial) := by
    push_cast
    rw [show (1 + (k:ℝ) / h) = ((h:ℝ) + k) / h by field_simp, div_pow]
    field_simp
  have h4 : ((h + k).choose h : ℝ) ≤ (1 + (k:ℝ) / h) ^ h * Real.exp h := by
    calc ((h + k).choose h : ℝ) ≤ ((h + k : ℕ) : ℝ) ^ h / (h.factorial : ℝ) := h1
      _ = (1 + (k:ℝ) / h) ^ h * ((h:ℝ) ^ h / h.factorial) := h3
      _ ≤ (1 + (k:ℝ) / h) ^ h * Real.exp h := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
  have h5 : 0 < 1 + (k:ℝ) / h := by positivity
  calc Real.log ((h + k).choose h)
      ≤ Real.log ((1 + (k:ℝ) / h) ^ h * Real.exp h) := Real.log_le_log hpos h4
    _ = h * Real.log (1 + (k:ℝ) / h) + h := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    _ = h * (1 + Real.log (1 + (k:ℝ) / h)) := by ring

/-- Paper (48): range (I) is at most `(1/20 + ε) M` eventually, uniformly in `k ≤ K`. -/
theorem D1_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ t k : ℕ, 1 ≤ t → k ≤ Kof P M →
      D1 M (nOf P M t) k ≤ (1 / 20 + ε) * M := by
  have hlog41 : 0 ≤ 1 + Real.log 41 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 41 by norm_num)
    linarith
  filter_upwards [eventually_gt_atTop 0, eventually_hof_pos P, eventually_two_hof_lt P,
    eventually_A_ge P (Real.exp 1), eventually_K_div_hof_le P,
    (tendsto_loglogA_div_logA P).eventually_lt_const (show (0:ℝ) < 10 * ε by linarith),
    (tendsto_logA P).eventually_ge_atTop ((1 + Real.log 41) / (10 * ε))]
    with M hM hh h2h hAe hKh hll hlA
  intro t k ht hkK
  have he1 : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  have hA1 : 1 < A P M := lt_of_lt_of_le he1 hAe
  have hA0 : 0 < A P M := by linarith
  have hlogA1 : 1 ≤ Real.log (A P M) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hAe
  have hlogA0 : 0 < Real.log (A P M) := by linarith
  have hllA : 0 ≤ Real.log (Real.log (A P M)) := Real.log_nonneg hlogA1
  have hhR : (0:ℝ) < hof P M := by exact_mod_cast hh
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have htL : hof P M + 1 ≤ t * Lof M := by
    have := le_Lof hM
    calc hof P M + 1 ≤ M := by omega
      _ ≤ Lof M := this
      _ ≤ t * Lof M := Nat.le_mul_of_pos_left _ ht
  have hkh : (k:ℝ) / hof P M ≤ (Kof P M : ℝ) / hof P M := by
    apply div_le_div_of_nonneg_right _ hhR.le
    exact_mod_cast hkK
  have hlog1 : Real.log (1 + (k:ℝ) / hof P M)
      ≤ Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M)) := by
    rw [← Real.log_mul (by norm_num) hA0.ne', ← Real.log_mul (by positivity) hlogA0.ne']
    apply Real.log_le_log (by positivity)
    linarith
  have hhM := hof_le P M hA1
  have hfrac : (1 + Real.log 41) / Real.log (A P M) ≤ 10 * ε := by
    rw [div_le_iff₀ hlogA0]
    rw [div_le_iff₀ (by linarith)] at hlA
    linarith
  calc D1 M (nOf P M t) k ≤ Real.log ((hof P M + k).choose (hof P M)) := D1_le P htL
    _ ≤ hof P M * (1 + Real.log (1 + (k:ℝ) / hof P M)) := log_choose_le hh
    _ ≤ hof P M * (1 + Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M))) := by
        apply mul_le_mul_of_nonneg_left _ hhR.le
        linarith
    _ ≤ (M / (20 * Real.log (A P M)))
          * (1 + Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M))) := by
        apply mul_le_mul_of_nonneg_right hhM
        linarith
    _ = (M / 20) * (1 + (1 + Real.log 41) / Real.log (A P M)
          + Real.log (Real.log (A P M)) / Real.log (A P M)) := by
        field_simp
        ring
    _ ≤ (M / 20) * (1 + 10 * ε + 10 * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = (1 / 20 + ε) * M := by ring

/-! ### Range (II) -/

/-- Paper (52)–(53): a contributing prime `M < p ≤ k` with `[n]_p = p - 1 - d_p`, `d_p < 2h`,
lies in `(k/m, (k+2h)/m]` for `m = ⌊k/p⌋ + 1`, and `2 ≤ m`, `(k + 2h)/m > M`. -/
theorem contributing_prime_mem {p k h d : ℕ} (hp : 0 < p) (hpk : p ≤ k)
    (hd : 1 ≤ d) (hd2 : d ≤ 2 * h - 1) (hcarry : p - 1 - d < k % p) :
    2 ≤ k / p + 1 ∧ (k : ℝ) / ((k / p + 1 : ℕ) : ℝ) < p ∧
      (p : ℝ) ≤ (k + 2 * h) / ((k / p + 1 : ℕ) : ℝ) := by
  have hdiv := Nat.div_add_mod k p
  have hmod := Nat.mod_lt k hp
  have hq : 0 < k / p := Nat.div_pos hpk hp
  have e : p * (k / p + 1) = p * (k / p) + p := by ring
  have hlt : k < p * (k / p + 1) := by
    rw [e]
    generalize p * (k / p) = X at hdiv ⊢
    omega
  have hle : p * (k / p + 1) ≤ k + 2 * h := by
    rw [e]
    generalize p * (k / p) = X at hdiv ⊢
    omega
  have hm : (0:ℝ) < ((k / p + 1 : ℕ) : ℝ) := by positivity
  refine ⟨by omega, ?_, ?_⟩
  · rw [div_lt_iff₀ hm]
    exact_mod_cast hlt
  · rw [le_div_iff₀ hm]
    exact_mod_cast hle

/-- The sum of `log p` over primes in a real interval `(y₁, y₂]` equals `θ(y₂) - θ(y₁)`. -/
theorem sum_log_primes_Ioc {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) :
    ∑ p ∈ (primesLE ⌊y₂⌋₊).filter (fun p : ℕ => y₁ < (p : ℝ)), Real.log p = θ y₂ - θ y₁ := by
  rw [Chebyshev.theta_eq_sum_primesLE y₂, Chebyshev.theta_eq_sum_primesLE y₁]
  have hsub : primesLE ⌊y₁⌋₊ ⊆ primesLE ⌊y₂⌋₊ := Nat.primesLE_mono (Nat.floor_mono h12)
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp2, hpp⟩, hy⟩
    exact ⟨⟨hp2, hpp⟩, fun h => absurd hy (not_lt.mpr ((Nat.le_floor_iff h0).mp h.1))⟩
  · rintro ⟨⟨hp2, hpp⟩, hn⟩
    refine ⟨⟨hp2, hpp⟩, ?_⟩
    by_contra hy
    exact hn ⟨Nat.le_floor (not_lt.mp hy), hpp⟩

/-- Paper (57), first inequality: range (II) is at most the sum over active indices of
`θ((k+2h)/m) - θ(k/m)`. -/
theorem D2_le_theta_sum {M t k : ℕ} (hh : 0 < hof P M) (h2h : 2 * hof P M < M)
    (ht : hof P M + 1 ≤ t * Lof M) (hkK : k ≤ Kof P M) (hA : 1 ≤ A P M)
    (hsel : ∀ p ∈ PMK P M, t * Lof M % p < hof P M ∨ p - hof P M < t * Lof M % p) :
    D2 M (nOf P M t) k ≤
      ∑ m ∈ (Icc 2 (⌊A P M⌋₊ + 1)).filter (fun m : ℕ => (M : ℝ) < (k + 2 * hof P M : ℝ) / (m : ℝ)),
        (θ ((k + 2 * hof P M : ℝ) / (m : ℝ)) - θ ((k : ℝ) / (m : ℝ))) := by
  set Act := (Icc 2 (⌊A P M⌋₊ + 1)).filter
    (fun m : ℕ => (M : ℝ) < (k + 2 * hof P M : ℝ) / (m : ℝ)) with hAct
  set I : ℕ → Finset ℕ := fun m =>
    (primesLE ⌊(k + 2 * hof P M : ℝ) / (m : ℝ)⌋₊).filter
      (fun p : ℕ => (k : ℝ) / (m : ℝ) < (p : ℝ)) with hI
  set S := (primesLE k).filter (fun p => nOf P M t % p < k % p ∧ M < p) with hS
  have hlog0 : ∀ p : ℕ, 0 ≤ Real.log p := Real.log_natCast_nonneg
  -- Step 1: only the level `a = 1` contributes
  have step1 : D2 M (nOf P M t) k ≤ ∑ p ∈ S, Real.log p := by
    unfold D2 Dpart
    rw [hS, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    have hcongr : ∀ a ∈ Ico 1 (nOf P M t + 1),
        (if nOf P M t % p ^ a < k % p ^ a ∧ (a = 1 ∧ M < p) then Real.log p else 0)
        = if a = 1 then (if nOf P M t % p < k % p ∧ M < p then Real.log p else 0) else 0 := by
      intro a _
      by_cases ha : a = 1
      · subst ha
        simp
      · simp [ha]
    refine (Finset.sum_congr rfl hcongr).le.trans ?_
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp [hlog0]
  -- Step 2: every contributing prime lies in one of the active intervals
  have key : ∀ p ∈ S, ∃ m ∈ Act, p ∈ I m := by
    intro p hp
    rw [hS, Finset.mem_filter, Nat.mem_primesLE] at hp
    obtain ⟨⟨hpk, hpp⟩, hcar, hMp⟩ := hp
    have hp0 : 0 < p := hpp.pos
    have hM0 : 0 < M := by omega
    have hpPMK : p ∈ PMK P M := by
      rw [PMK, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨le_trans hpk hkK, hpp⟩, hMp⟩
    obtain ⟨d, hd1, hd2, hnp⟩ := fold hh (by omega : 2 * hof P M < p) ht (hsel p hpPMK)
    have hcar' : p - 1 - d < k % p := by
      have hnp' : nOf P M t % p = p - 1 - d := hnp
      rwa [hnp'] at hcar
    obtain ⟨hm2, hlt, hle⟩ := contributing_prime_mem hp0 hpk hd1 hd2 hcar'
    refine ⟨k / p + 1, ?_, ?_⟩
    · rw [hAct, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hm2, ?_⟩, ?_⟩
      · have hA0 : 0 ≤ A P M := by linarith
        have hKA := Kof_le P M hA0
        have hpR : (0:ℝ) < p := by exact_mod_cast hp0
        have hMR : (0:ℝ) < M := by exact_mod_cast hM0
        have hMpR : (M:ℝ) ≤ p := by exact_mod_cast hMp.le
        have hkKR : (k:ℝ) ≤ Kof P M := by exact_mod_cast hkK
        have hfl : ((k / p : ℕ) : ℝ) ≤ A P M := by
          calc ((k / p : ℕ) : ℝ) ≤ (k : ℝ) / p := Nat.cast_div_le
            _ ≤ (Kof P M : ℝ) / p := div_le_div_of_nonneg_right hkKR hpR.le
            _ ≤ (Kof P M : ℝ) / M :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg _) hMR hMpR
            _ ≤ A P M := by
                rw [div_le_iff₀ hMR]
                exact hKA
        have := Nat.le_floor hfl
        omega
      · exact lt_of_lt_of_le (by exact_mod_cast hMp) hle
    · rw [hI]
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨Nat.le_floor hle, hpp⟩, hlt⟩
  -- Step 3: double counting
  have step3 : ∑ p ∈ S, Real.log p ≤ ∑ m ∈ Act, ∑ p ∈ I m, Real.log p := by
    calc ∑ p ∈ S, Real.log p
        ≤ ∑ p ∈ S, ∑ m ∈ Act, (if p ∈ I m then Real.log p else 0) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨m, hm, hpm⟩ := key p hp
          calc Real.log p = (if p ∈ I m then Real.log p else 0) := by rw [if_pos hpm]
            _ ≤ ∑ m ∈ Act, (if p ∈ I m then Real.log p else 0) :=
              Finset.single_le_sum (f := fun m => if p ∈ I m then Real.log p else 0)
                (fun m _ => by split_ifs <;> simp [hlog0]) hm
      _ = ∑ m ∈ Act, ∑ p ∈ S, (if p ∈ I m then Real.log p else 0) := Finset.sum_comm
      _ = ∑ m ∈ Act, ∑ p ∈ S.filter (fun p => p ∈ I m), Real.log p := by
          apply Finset.sum_congr rfl
          intro m _
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ m ∈ Act, ∑ p ∈ I m, Real.log p := by
          apply Finset.sum_le_sum
          intro m _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact (Finset.mem_filter.mp hp).2
          · intro p _ _
            exact hlog0 p
  -- Step 4: the prime-interval sums are differences of `θ`
  have step4 : ∀ m ∈ Act, ∑ p ∈ I m, Real.log p
      = θ ((k + 2 * hof P M : ℝ) / (m : ℝ)) - θ ((k : ℝ) / (m : ℝ)) := by
    intro m _
    rw [hI]
    apply sum_log_primes_Ioc
    · positivity
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      linarith [(Nat.cast_nonneg (hof P M) : (0:ℝ) ≤ hof P M)]
  calc D2 M (nOf P M t) k ≤ ∑ p ∈ S, Real.log p := step1
    _ ≤ ∑ m ∈ Act, ∑ p ∈ I m, Real.log p := step3
    _ = ∑ m ∈ Act, (θ ((k + 2 * hof P M : ℝ) / (m : ℝ)) - θ ((k : ℝ) / (m : ℝ))) :=
        Finset.sum_congr rfl step4

/-- `Σ_{2 ≤ m ≤ N} 1/m ≤ log N` (Mathlib `harmonic_le_one_add_log`). -/
theorem sum_inv_le_log (N : ℕ) : ∑ m ∈ Icc 2 N, (1 : ℝ) / m ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  have e : Icc 2 N = (Icc 1 N).erase 1 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_erase]
    omega
  have h2 := Finset.sum_erase_add (Icc 1 N) (fun i : ℕ => ((i : ℝ))⁻¹)
    (Finset.left_mem_Icc.mpr hN)
  simp only [Nat.cast_one, inv_one] at h2
  rw [e]
  simp only [one_div]
  linarith

/-- Paper Lemma 6.2: range (II) is at most `(1/10 + ε) M` eventually, uniformly in `k ≤ K`. -/
theorem D2_bound (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ t k : ℕ, 1 ≤ t → k ≤ Kof P M →
      (∀ p ∈ PMK P M, t * Lof M % p < hof P M ∨ p - hof P M < t * Lof M % p) →
      D2 M (nOf P M t) k ≤ (1 / 10 + ε) * M := by
  filter_upwards [eventually_gt_atTop 0, eventually_hof_pos P, eventually_two_hof_lt P,
    eventually_A_ge P (Real.exp 1), eventually_theta_interval P hPNT (ε / 2) (by linarith),
    (tendsto_logA1_div_logA P).eventually_lt_const (show (1:ℝ) < 1 + 5 * ε by linarith)]
    with M hM hh h2h hAe hE hlA1
  intro t k ht hkK hsel
  obtain ⟨E, hE0, hEA, hEint⟩ := hE
  have he1 : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  have hA1 : 1 < A P M := lt_of_lt_of_le he1 hAe
  have hA : 1 ≤ A P M := hA1.le
  have hlogA1 : 1 ≤ Real.log (A P M) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hAe
  have hlogA0 : 0 < Real.log (A P M) := by linarith
  have hhR : (0:ℝ) < hof P M := by exact_mod_cast hh
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h2hR : 2 * (hof P M : ℝ) < M := by exact_mod_cast h2h
  have htL : hof P M + 1 ≤ t * Lof M := by
    have := le_Lof hM
    calc hof P M + 1 ≤ M := by omega
      _ ≤ Lof M := this
      _ ≤ t * Lof M := Nat.le_mul_of_pos_left _ ht
  have hkKR : (k:ℝ) ≤ Kof P M := by exact_mod_cast hkK
  set Act := (Icc 2 (⌊A P M⌋₊ + 1)).filter
    (fun m : ℕ => (M : ℝ) < (k + 2 * hof P M : ℝ) / (m : ℝ)) with hAct
  -- each active term is at most `2h/m + E`
  have hterm : ∀ m ∈ Act,
      θ ((k + 2 * hof P M : ℝ) / (m : ℝ)) - θ ((k : ℝ) / (m : ℝ))
        ≤ 2 * (hof P M : ℝ) / m + E := by
    intro m hm
    rw [hAct, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm2, _⟩, hMm⟩ := hm
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm2
    have hm0 : (0:ℝ) < m := by linarith
    have hy1 : (M:ℝ) / 2 ≤ (k:ℝ) / m := by
      have hsplit : (k:ℝ) / m = (k + 2 * hof P M : ℝ) / m - 2 * (hof P M : ℝ) / m := by
        rw [← sub_div]
        ring
      have h2 : 2 * (hof P M : ℝ) / m ≤ hof P M := by
        rw [div_le_iff₀ hm0]
        nlinarith
      linarith
    have hy12 : (k:ℝ) / m ≤ (k + 2 * hof P M : ℝ) / m := by
      apply div_le_div_of_nonneg_right _ hm0.le
      linarith
    have hy2 : (k + 2 * hof P M : ℝ) / m ≤ Kof P M + 2 * hof P M := by
      calc (k + 2 * hof P M : ℝ) / m ≤ (k + 2 * hof P M : ℝ) / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
        _ = k + 2 * hof P M := div_one _
        _ ≤ Kof P M + 2 * hof P M := by linarith
    have := hEint _ _ hy1 hy12 hy2
    calc _ ≤ ((k + 2 * hof P M : ℝ) / m - (k:ℝ) / m) + E := this
      _ = 2 * (hof P M : ℝ) / m + E := by
        rw [← sub_div]
        ring
  have hsum2 : ∑ m ∈ Act, (2 * (hof P M : ℝ) / m + E)
      = 2 * hof P M * ∑ m ∈ Act, (1:ℝ) / m + Act.card * E := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hcard : (Act.card : ℝ) ≤ A P M + 1 := by
    have h1 : Act.card ≤ (Icc 2 (⌊A P M⌋₊ + 1)).card := Finset.card_filter_le _ _
    rw [Nat.card_Icc] at h1
    have h2 : (⌊A P M⌋₊ : ℝ) ≤ A P M := Nat.floor_le (by linarith)
    have h4 : (⌊A P M⌋₊ + 1 + 1 - 2 : ℕ) = ⌊A P M⌋₊ := by omega
    rw [h4] at h1
    have h3 : (Act.card : ℝ) ≤ (⌊A P M⌋₊ : ℝ) := by exact_mod_cast h1
    linarith
  have hinv : ∑ m ∈ Act, (1:ℝ) / m ≤ Real.log (A P M + 1) := by
    calc ∑ m ∈ Act, (1:ℝ) / m ≤ ∑ m ∈ Icc 2 (⌊A P M⌋₊ + 1), (1:ℝ) / m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun m _ _ => by positivity)
      _ ≤ Real.log ((⌊A P M⌋₊ + 1 : ℕ) : ℝ) := sum_inv_le_log _
      _ ≤ Real.log (A P M + 1) := by
          apply Real.log_le_log (by positivity)
          push_cast
          linarith [Nat.floor_le (show 0 ≤ A P M by linarith)]
  have hhM := hof_le P M hA1
  have hlogA1' : 0 ≤ Real.log (A P M + 1) := Real.log_nonneg (by linarith)
  have hfrac : Real.log (A P M + 1) ≤ (1 + 5 * ε) * Real.log (A P M) := by
    rw [div_lt_iff₀ hlogA0] at hlA1
    linarith
  have hMlog : 0 ≤ 2 * ((M:ℝ) / (20 * Real.log (A P M))) :=
    mul_nonneg (by norm_num) (div_nonneg hMR.le (by linarith))
  calc D2 M (nOf P M t) k
      ≤ ∑ m ∈ Act, (θ ((k + 2 * hof P M : ℝ) / (m : ℝ)) - θ ((k : ℝ) / (m : ℝ))) :=
        D2_le_theta_sum P hh h2h htL hkK hA hsel
    _ ≤ ∑ m ∈ Act, (2 * (hof P M : ℝ) / m + E) := Finset.sum_le_sum hterm
    _ = 2 * hof P M * ∑ m ∈ Act, (1:ℝ) / m + Act.card * E := hsum2
    _ ≤ 2 * hof P M * Real.log (A P M + 1) + (A P M + 1) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hinv (by positivity))
          (mul_le_mul_of_nonneg_right hcard hE0)
    _ ≤ 2 * (M / (20 * Real.log (A P M))) * Real.log (A P M + 1) + ε / 2 * M :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhM (by norm_num)) hlogA1')
          hEA
    _ ≤ 2 * (M / (20 * Real.log (A P M))) * ((1 + 5 * ε) * Real.log (A P M)) + ε / 2 * M :=
        add_le_add (mul_le_mul_of_nonneg_left hfrac hMlog) le_rfl
    _ = (1 / 10 + ε) * M := by
        field_simp
        ring

/-! ### Range (III) -/

/-- Paper (58): range (III) is at most `ψ(K) - θ(K)`. -/
theorem D3_le {M K n k : ℕ} (hkK : k ≤ K) : D3 M K n k ≤ ψ K - θ K := by
  have hterm : ∀ p ∈ primesLE k,
      (∑ a ∈ Ico 1 (n + 1),
        if n % p ^ a < k % p ^ a ∧ (2 ≤ a ∧ M < p ^ a ∧ p ^ a ≤ K) then Real.log p else 0)
        ≤ ((Nat.log p K : ℝ) - 1) * Real.log p := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hpk, hpp⟩ := hp
    have hp1 : 1 < p := hpp.one_lt
    have hlog1 : 1 ≤ Nat.log p K := Nat.le_log_of_pow_le hp1 (by rw [pow_one]; omega)
    calc _ ≤ ∑ a ∈ Ico 1 (n + 1), if 2 ≤ a ∧ p ^ a ≤ K then Real.log p else 0 := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd ⟨h1.2.1, h1.2.2.2⟩ h2
          · exact Real.log_natCast_nonneg p
          · exact le_rfl
      _ = ((Ico 1 (n + 1)).filter (fun a => 2 ≤ a ∧ p ^ a ≤ K)).card * Real.log p := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Nat.log p K : ℝ) - 1) * Real.log p := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
          have hsub : (Ico 1 (n + 1)).filter (fun a => 2 ≤ a ∧ p ^ a ≤ K)
              ⊆ Icc 2 (Nat.log p K) := by
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at ha ⊢
            exact ⟨ha.2.1, Nat.le_log_of_pow_le hp1 ha.2.2⟩
          have hc := Finset.card_le_card hsub
          rw [Nat.card_Icc] at hc
          have h' : ((Nat.log p K + 1 - 2 : ℕ) : ℝ) = (Nat.log p K : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            push_cast
            ring
          rw [← h']
          exact_mod_cast hc
  calc D3 M K n k ≤ ∑ p ∈ primesLE k, ((Nat.log p K : ℝ) - 1) * Real.log p :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ primesLE K, ((Nat.log p K : ℝ) - 1) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hkK)
        intro p hp _
        rw [Nat.mem_primesLE] at hp
        have hlog1 : 1 ≤ Nat.log p K :=
          Nat.le_log_of_pow_le hp.2.one_lt (by rw [pow_one]; exact hp.1)
        apply mul_nonneg _ (Real.log_natCast_nonneg p)
        have : (1:ℝ) ≤ Nat.log p K := by exact_mod_cast hlog1
        linarith
    _ = ψ K - θ K := by
        rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _
        ring

theorem D3_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ n k : ℕ, k ≤ Kof P M → D3 M (Kof P M) n k ≤ ε * M := by
  filter_upwards [eventually_gt_atTop 0, eventually_M_lt_Kof P,
    (tendsto_sqrtK_logK_div P).eventually_lt_const (show (0:ℝ) < ε / 2 by linarith)]
    with M hM hMK hsq
  intro n k hkK
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hK1 : (1:ℝ) ≤ Kof P M := by exact_mod_cast (show 1 ≤ Kof P M by omega)
  rw [div_lt_iff₀ hMR] at hsq
  calc D3 M (Kof P M) n k ≤ ψ (Kof P M) - θ (Kof P M) := D3_le hkK
    _ ≤ 2 * √(Kof P M : ℝ) * Real.log (Kof P M) := Chebyshev.psi_sub_theta_le hK1
    _ ≤ ε * M := by linarith

/-! ### Range (IV) -/

/-- Paper (59): range (IV) is at most `Z(t)`. -/
theorem D4_le {M t k : ℕ} (hkK : k ≤ Kof P M) : D4 (Kof P M) (nOf P M t) k ≤ Z P M t := by
  have hterm : ∀ p ∈ primesLE k,
      (∑ a ∈ Ico 1 (nOf P M t + 1),
        if nOf P M t % p ^ a < k % p ^ a ∧ Kof P M < p ^ a then Real.log p else 0)
        ≤ (ell P M t p : ℝ) * Real.log p := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hpk, hpp⟩ := hp
    rw [← Finset.sum_filter]
    calc _ ≤ ∑ a ∈ (Ico (aOf P M p) (nOf P M t + 1)).filter
              (fun a => nOf P M t % p ^ a < Kof P M), Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
            obtain ⟨⟨_, han⟩, hcar, hKa⟩ := ha
            have hp2 := hpp.two_le
            have hK0 : Kof P M ≠ 0 := by omega
            refine ⟨⟨?_, han⟩, ?_⟩
            · unfold aOf
              exact Nat.succ_le_of_lt ((Nat.log_lt_iff_lt_pow hpp.one_lt hK0).mpr hKa)
            · rw [Nat.mod_eq_of_lt (by omega : k < p ^ a)] at hcar
              omega
          · intro a _ _
            exact Real.log_natCast_nonneg p
      _ = (ell P M t p : ℝ) * Real.log p := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rfl
  calc D4 (Kof P M) (nOf P M t) k ≤ ∑ p ∈ primesLE k, (ell P M t p : ℝ) * Real.log p :=
        Finset.sum_le_sum hterm
    _ ≤ Z P M t := by
        unfold Z
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hkK)
        intro p _ _
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-! ### The budget -/



/-- Paper (47): for the selected multiplier, `D_n(k) ≤ (β + 3/20 + ε) M` uniformly for
`1 ≤ k ≤ K`, eventually in `M`. -/
theorem budget (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ t : ℕ, Selected P M t → ∀ k : ℕ, 1 ≤ k → k ≤ Kof P M →
      D (nOf P M t) k ≤ (P.beta + 3 / 20 + ε) * M := by
  filter_upwards [D1_bound P (ε / 3) (by linarith), D2_bound P hPNT (ε / 3) (by linarith),
    D3_bound P (ε / 3) (by linarith), eventually_M_lt_Kof P] with M h1 h2 h3 hMK
  intro t hsel k _ hkK
  unfold Selected at hsel
  obtain ⟨hτ, _, hZ, hsel4⟩ := hsel
  have ht0 : (0:ℝ) < t := lt_trans (Real.exp_pos _) hτ
  have ht0' : 0 < t := by exact_mod_cast ht0
  have ht : 1 ≤ t := ht0'
  rw [D_split hMK.le hkK]
  have hD1 := h1 t k ht hkK
  have hD2 := h2 t k ht hkK hsel4
  have hD3 := h3 (nOf P M t) k hkK
  have hD4 := D4_le P (t := t) hkK
  linarith

end Erdos684
