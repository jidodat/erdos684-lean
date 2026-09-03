import Erdos684Lean.Select
import Erdos684Lean.Budget

/-!
# Completion and optimization (paper Section 7)

* `prop_fixed` — paper Proposition 7.1: for fixed parameters and all large `M` there is `n` with
  `f(n) > K` and `(1+τ-ε) M ≤ log n ≤ (1+σ+ε) M`.
* `main_theorem` — paper Theorem 1.2, (4): for every `ε > 0` there are infinitely many `n` with
  `f(n) > (1/2 - ε) log n · log log n / log log log n`.
* `unbounded` — paper (5): `f(n)/log n` is unbounded.

All results are conditional on `PNTHyp` (the prime number theorem with a power-of-logarithm
remainder), the single external analytic input.
-/

open Finset Real Filter Topology
open scoped Chebyshev

namespace Erdos684

variable (P : Params)

/-- The real-cast form of `n_t = tL - h - 1`, together with the lower bound `n_t ≥ tL/2`. -/
private theorem nOf_cast_bounds {M t : ℕ} (ht : 1 ≤ t) (hL : 2 * (hof P M + 1) ≤ Lof M) :
    (nOf P M t : ℝ) = t * Lof M - (hof P M + 1) ∧ (t : ℝ) * Lof M / 2 ≤ nOf P M t := by
  have hh1 : hof P M + 1 ≤ t * Lof M := by
    calc hof P M + 1 ≤ Lof M := by omega
      _ ≤ t * Lof M := Nat.le_mul_of_pos_left _ ht
  have hn : (nOf P M t : ℝ) = t * Lof M - (hof P M + 1) := by
    unfold nOf
    rw [Nat.sub_sub, Nat.cast_sub hh1]
    push_cast
    ring
  refine ⟨hn, ?_⟩
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hLR : (2 : ℝ) * (hof P M + 1) ≤ Lof M := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have h1 : (1 : ℝ) * Lof M ≤ t * Lof M := mul_le_mul_of_nonneg_right htR hLpos.le
  rw [hn]
  linarith

/-- `log n_t = log t + log L + o(1)` in the form of two-sided bounds (paper (63)). -/
theorem log_nOf_bounds {M t : ℕ} (ht : 1 ≤ t) (hL : 2 * (hof P M + 1) ≤ Lof M) :
    Real.log t + Real.log (Lof M) - Real.log 2 ≤ Real.log (nOf P M t) ∧
      Real.log (nOf P M t) ≤ Real.log t + Real.log (Lof M) := by
  obtain ⟨hn, hlow⟩ := nOf_cast_bounds P ht hL
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hLpos : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have hh0 : (0 : ℝ) ≤ hof P M + 1 := by positivity
  have htL : (0 : ℝ) < t * Lof M / 2 := by positivity
  have hnpos : (0 : ℝ) < nOf P M t := lt_of_lt_of_le htL hlow
  constructor
  · calc Real.log t + Real.log (Lof M) - Real.log 2 = Real.log (t * Lof M / 2) := by
          rw [Real.log_div (by positivity) (by norm_num), Real.log_mul htR.ne' hLpos.ne']
      _ ≤ Real.log (nOf P M t) := Real.log_le_log htL hlow
  · calc Real.log (nOf P M t) ≤ Real.log (t * Lof M) :=
          Real.log_le_log hnpos (by rw [hn]; linarith)
      _ = Real.log t + Real.log (Lof M) := Real.log_mul htR.ne' hLpos.ne'

/-! ### Auxiliary eventual facts about iterated logarithms -/

private theorem eventually_log_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

private theorem eventually_loglog_ge (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ Real.log (Real.log n) :=
  (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop c

private theorem eventually_logloglog_ge (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ Real.log (Real.log (Real.log n)) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop c

/-- Paper Proposition 7.1. -/
theorem prop_fixed (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∃ n : ℕ,
      (1 + P.tau - ε) * M ≤ Real.log n ∧ Real.log n ≤ (1 + P.sigma + ε) * M ∧
        (Kof P M : ℕ∞) < fThr n := by
  -- the internal margin `ε'`
  obtain ⟨ε', hε'pos, hε'1, hε'2, hε'3⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε / 2 ∧ ε' ≤ 1 / 2 ∧
      5 * ε' ≤ 2 * (1 + P.tau) - P.beta - 3 / 20 := by
    have hg : 0 < 2 * (1 + P.tau) - P.beta - 3 / 20 := by have := P.tau_gt; linarith
    refine ⟨min (ε / 2) (min (1 / 2) ((2 * (1 + P.tau) - P.beta - 3 / 20) / 5)),
      lt_min (by linarith) (lt_min (by norm_num) (by linarith)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    have h5 : min (ε / 2) (min (1 / 2) ((2 * (1 + P.tau) - P.beta - 3 / 20) / 5)) ≤
        (2 * (1 + P.tau) - P.beta - 3 / 20) / 5 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hM1 : ∀ᶠ M : ℕ in atTop, Real.log 2 / ε' ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hM2 : ∀ᶠ M : ℕ in atTop, 96 * P.c + 1 ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_selected P hPNT, budget P hPNT ε' hε'pos,
    eventually_psi_close hPNT ε' hε'pos, eventually_two_hof_lt P, eventually_A_ge P 1,
    eventually_loglog_ge 1, hM1, hM2, eventually_ge_atTop 8] with M hsel hbud hψ h2h hA hll hM1 hM2
    hM3
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := hsel
  have hMR : (8 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMpos : (0 : ℝ) < M := by linarith
  have hLR : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have hlogL : Real.log (Lof M) = ψ M := log_Lof M
  have hψ1 : (1 - ε') * M ≤ Real.log (Lof M) := by
    rw [hlogL]; have := (abs_le.1 hψ).1; linarith
  have hψ2 : Real.log (Lof M) ≤ (1 + ε') * M := by
    rw [hlogL]; have := (abs_le.1 hψ).2; linarith
  -- `L ≥ e^{M/2} ≥ M³/48`
  have hLexp : Real.exp ((M : ℝ) / 2) ≤ Lof M := by
    rw [← Real.exp_log hLR]
    apply Real.exp_le_exp.2
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - ε') hMpos.le
    linarith
  have hLcube : (M : ℝ) ^ 3 / 48 ≤ Lof M := by
    have h := Real.pow_div_factorial_le_exp ((M : ℝ) / 2) (by positivity) 3
    have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    calc (M : ℝ) ^ 3 / 48 = ((M : ℝ) / 2) ^ 3 / 6 := by ring
      _ ≤ Real.exp ((M : ℝ) / 2) := h
      _ ≤ Lof M := hLexp
  have hM3cube : (M : ℝ) + 1 ≤ (M : ℝ) ^ 3 / 48 := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M - 8)
      (by linarith : (0 : ℝ) ≤ M + 8)) hMpos.le
    linarith
  have hLM : 2 * (hof P M + 1) ≤ Lof M := by
    have h1 : ((M + 1 : ℕ) : ℝ) ≤ Lof M := by push_cast; linarith
    have h2 : M + 1 ≤ Lof M := by exact_mod_cast h1
    omega
  -- `t ≥ 1`
  have htpos : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht1
  have ht1' : 1 ≤ t := by
    have : 0 < t := by exact_mod_cast htpos
    omega
  -- the bounds on `log n`
  obtain ⟨hlo, hhi⟩ := log_nOf_bounds P ht1' hLM
  obtain ⟨hn, hnlow⟩ := nOf_cast_bounds P ht1' hLM
  have hlogt1 : P.tau * M < Real.log t := (Real.lt_log_iff_exp_lt htpos).2 ht1
  have hlogt2 : Real.log t ≤ P.sigma * M := by
    calc Real.log t ≤ Real.log (Real.exp (P.sigma * M)) :=
          Real.log_le_log htpos (le_trans (by exact_mod_cast ht2) (Jof_le P M))
      _ = P.sigma * M := Real.log_exp _
  have hlog2 : Real.log 2 ≤ ε' * M := by
    rw [div_le_iff₀ hε'pos] at hM1; linarith
  have hnlo : (1 + P.tau - 2 * ε') * M ≤ Real.log (nOf P M t) := by linarith
  have hnhi : Real.log (nOf P M t) ≤ (1 + P.sigma + ε') * M := by linarith
  -- `K < n`
  have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlogM_le : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hMpos]
  have hA_le : A P M ≤ P.c * M := by
    unfold A
    calc P.c * Real.log M / Real.log (Real.log M) ≤ P.c * Real.log M :=
          div_le_self (by have := P.c_pos; positivity) hll
      _ ≤ P.c * M := mul_le_mul_of_nonneg_left hlogM_le P.c_pos.le
  have hK : (Kof P M : ℝ) ≤ P.c * M ^ 2 := by
    calc (Kof P M : ℝ) ≤ A P M * M := Kof_le P M (by linarith)
      _ ≤ P.c * M * M := mul_le_mul_of_nonneg_right hA_le hMpos.le
      _ = P.c * M ^ 2 := by ring
  have hn_lo : (M : ℝ) ^ 3 / 96 ≤ nOf P M t := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1'
    have h1 : (1 : ℝ) * Lof M ≤ t * Lof M := mul_le_mul_of_nonneg_right htR hLR.le
    calc (M : ℝ) ^ 3 / 96 = ((M : ℝ) ^ 3 / 48) / 2 := by ring
      _ ≤ (Lof M : ℝ) / 2 := by linarith
      _ ≤ (t : ℝ) * Lof M / 2 := by linarith
      _ ≤ nOf P M t := hnlow
  have hM3pos : (0 : ℝ) < (M : ℝ) ^ 3 / 96 := by positivity
  have hnpos : (0 : ℝ) < nOf P M t := lt_of_lt_of_le hM3pos hn_lo
  have hKn : Kof P M < nOf P M t := by
    have : (Kof P M : ℝ) < nOf P M t := by
      have hsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      have := mul_pos hsq (by linarith : (0 : ℝ) < M - 96 * P.c)
      calc (Kof P M : ℝ) ≤ P.c * M ^ 2 := hK
        _ < (M : ℝ) ^ 3 / 96 := by linarith
        _ ≤ nOf P M t := hn_lo
    exact_mod_cast this
  -- the threshold
  have hfin : (Kof P M : ℕ∞) < fThr (nOf P M t) := by
    apply lt_fThr_of_forall
    intro k hk1 hkK
    have hkn : k ≤ nOf P M t := le_trans hkK hKn.le
    have hD := hbud t ⟨ht1, ht2, ht3, ht4⟩ k hk1 hkK
    have hlogu : Real.log (uPart (nOf P M t) k) ≤ Real.log ((nOf P M t : ℝ) ^ 2) := by
      rw [log_uPart_eq_D hkn, Real.log_pow]
      push_cast
      have := mul_nonneg
        (by linarith : (0 : ℝ) ≤ 2 * (1 + P.tau) - P.beta - 3 / 20 - 5 * ε') hMpos.le
      calc D (nOf P M t) k ≤ (P.beta + 3 / 20 + ε') * M := hD
        _ ≤ 2 * ((1 + P.tau - 2 * ε') * M) := by linarith
        _ ≤ 2 * Real.log (nOf P M t) := by linarith
    have hupos : (0 : ℝ) < uPart (nOf P M t) k := by exact_mod_cast uPart_pos _ _
    have := (Real.log_le_log_iff hupos (by positivity)).1 hlogu
    exact_mod_cast this
  refine ⟨nOf P M t, ?_, ?_, hfin⟩
  · have := mul_nonneg (by linarith : (0 : ℝ) ≤ ε - 2 * ε') hMpos.le
    linarith
  · have := mul_nonneg (by linarith : (0 : ℝ) ≤ ε - ε') hMpos.le
    linarith

/-- The optimized parameters of paper (67). -/
noncomputable def optParams (δ β : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hβ : 0 < β) : Params where
  lam := 1 - δ
  beta := β
  c := (1 - 2 * δ) * β
  sigma := (2 + δ) * β
  tau := β
  lam_pos := by linarith
  lam_lt_one := by linarith
  beta_pos := hβ
  c_pos := by nlinarith
  c_lt := by nlinarith
  sigma_gt := by nlinarith
  tau_lt := by nlinarith
  tau_gt := by nlinarith

/-- The real-number estimate behind the main theorem: with `X = log n`, `M ≤ X ≤ s M`,
`a = (1/2 - ε) s`, `b = log s` and `c - a ≥ 1`, the quantity
`(1/2 - ε) X log X / log log X` is at most `c M log M / log log M - 1` once `log M ≥ a b + 1`. -/
private theorem final_estimate {ε s a b c M X : ℝ} (hε4 : ε ≤ 1 / 4) (hs1 : 1 ≤ s)
    (ha : a = (1 / 2 - ε) * s) (hb : b = Real.log s) (hca : 1 ≤ c - a) (hM : 1 ≤ M)
    (hlogM : 1 ≤ Real.log M) (hllM : 1 ≤ Real.log (Real.log M))
    (hlogM' : a * b + 1 ≤ Real.log M) (hX1 : M ≤ X) (hX2 : X ≤ s * M) :
    (1 / 2 - ε) * X * Real.log X / Real.log (Real.log X) ≤
      c * M * Real.log M / Real.log (Real.log M) - 1 := by
  have hMpos : 0 < M := by linarith
  have hXpos : 0 < X := by linarith
  have h12 : 0 ≤ 1 / 2 - ε := by linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; exact Real.log_nonneg hs1
  have hlogX1 : Real.log M ≤ Real.log X := Real.log_le_log hMpos hX1
  have hlogX2 : Real.log X ≤ b + Real.log M := by
    rw [hb, ← Real.log_mul (by linarith) hMpos.ne']
    exact Real.log_le_log hXpos hX2
  have hlogX_pos : 0 < Real.log X := by linarith
  have hlll : Real.log (Real.log M) ≤ Real.log (Real.log X) :=
    Real.log_le_log (by linarith) hlogX1
  have hllM_pos : 0 < Real.log (Real.log M) := by linarith
  have hllM_le : Real.log (Real.log M) ≤ M := by
    have h1 := Real.log_le_sub_one_of_pos hMpos
    have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log M)
    linarith
  -- the ratio is at most `a M (b + log M) / log log M`
  have hratio : (1 / 2 - ε) * X * Real.log X / Real.log (Real.log X) ≤
      a * M * (b + Real.log M) / Real.log (Real.log M) := by
    apply div_le_div₀ (mul_nonneg (mul_nonneg ha0 hMpos.le) (by linarith)) _ hllM_pos hlll
    rw [ha]
    calc (1 / 2 - ε) * X * Real.log X
        ≤ (1 / 2 - ε) * (s * M) * (b + Real.log M) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hX2 h12) hlogX2 hlogX_pos.le
          positivity
      _ = (1 / 2 - ε) * s * M * (b + Real.log M) := by ring
  -- `a M (b + log M) / log log M ≤ c M log M / log log M - 1`
  have hbound : a * M * (b + Real.log M) / Real.log (Real.log M) ≤
      c * M * Real.log M / Real.log (Real.log M) - 1 := by
    have h1 : c * M * Real.log M / Real.log (Real.log M) - 1
        = (c * M * Real.log M - Real.log (Real.log M)) / Real.log (Real.log M) := by
      field_simp
    rw [h1, div_le_div_iff_of_pos_right hllM_pos]
    have h2 : M * (a * b + 1) ≤ M * Real.log M := mul_le_mul_of_nonneg_left hlogM' hMpos.le
    have h3 : (1 : ℝ) * (M * Real.log M) ≤ (c - a) * (M * Real.log M) :=
      mul_le_mul_of_nonneg_right hca (by positivity)
    linarith
  exact hratio.trans hbound

/-- The main theorem for `ε ≤ 1/4`, with the explicit choice `δ = ε/8`, `β = 64/ε`. -/
private theorem main_aux (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
          Real.log (Real.log (Real.log n)) →
        (k : ℕ∞) < fThr n := by
  let P : Params := optParams (ε / 8) (64 / ε) (by positivity) (by linarith) (by positivity)
  have hc : P.c = (1 - 2 * (ε / 8)) * (64 / ε) := rfl
  have hσ : P.sigma = (2 + ε / 8) * (64 / ε) := rfl
  have hτ : P.tau = 64 / ε := rfl
  -- the constants `s = 1 + σ + ε/2`, `a = (1/2 - ε) s`, `b = log s`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + P.sigma + ε / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 / 2 - ε) * s := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.log s := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hs, hσ]; have : 0 ≤ (2 + ε / 8) * (64 / ε) := by positivity
    linarith
  have hca : 1 ≤ P.c - a := by
    rw [ha, hs, hc, hσ]
    have : (1 - 2 * (ε / 8)) * (64 / ε) - (1 / 2 - ε) * (1 + (2 + ε / 8) * (64 / ε) + ε / 2)
        = 215 / 2 + 35 / 4 * ε + ε ^ 2 / 2 := by
      field_simp; ring
    rw [this]; nlinarith
  have hτ1 : 1 ≤ 1 + P.tau - ε / 2 := by
    rw [hτ]
    have : (1 : ℝ) ≤ 64 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  clear hc hσ hτ
  -- all eventual facts in `M`
  have hall : ∀ᶠ M : ℕ in atTop,
      (∃ n : ℕ, (1 + P.tau - ε / 2) * M ≤ Real.log n ∧ Real.log n ≤ (1 + P.sigma + ε / 2) * M ∧
        (Kof P M : ℕ∞) < fThr n) ∧
      1 ≤ Real.log M ∧ 1 ≤ Real.log (Real.log M) ∧ a * b + 1 ≤ Real.log M ∧ 1 ≤ M := by
    filter_upwards [prop_fixed P hPNT (ε / 2) (by positivity), eventually_log_ge 1,
      eventually_loglog_ge 1, eventually_log_ge (a * b + 1), eventually_ge_atTop 1]
      with M h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hall
  obtain ⟨⟨n, hn1, hn2, hn3⟩, hlogM, hllM, hlogM', hM1⟩ := hM₀ (max M₀ N) (le_max_left _ _)
  have hMN : N ≤ max M₀ N := le_max_right _ _
  have hMR : (1 : ℝ) ≤ (max M₀ N : ℕ) := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < (max M₀ N : ℕ) := by linarith
  -- `log n ≥ M`
  have hX1 : ((max M₀ N : ℕ) : ℝ) ≤ Real.log n := by
    calc ((max M₀ N : ℕ) : ℝ) = 1 * (max M₀ N : ℕ) := by ring
      _ ≤ (1 + P.tau - ε / 2) * (max M₀ N : ℕ) := mul_le_mul_of_nonneg_right hτ1 hMpos.le
      _ ≤ Real.log n := hn1
  have hXpos : 0 < Real.log n := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hXpos
      exact absurd hXpos (lt_irrefl 0)
    · exact_mod_cast h
  refine ⟨n, ?_, ?_⟩
  · -- `n ≥ N`
    have h1 : ((N : ℕ) : ℝ) + 1 ≤ n := by
      calc ((N : ℕ) : ℝ) + 1 ≤ ((max M₀ N : ℕ) : ℝ) + 1 := by
            have : ((N : ℕ) : ℝ) ≤ (max M₀ N : ℕ) := by exact_mod_cast hMN
            linarith
        _ ≤ Real.exp (max M₀ N : ℕ) := Real.add_one_le_exp _
        _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.2 hX1
        _ = n := Real.exp_log hnpos
    have h2 : N + 1 ≤ n := by exact_mod_cast h1
    omega
  · intro k hk
    have hX2 : Real.log n ≤ s * (max M₀ N : ℕ) := by rw [hs]; exact hn2
    have hest := final_estimate hε4 hs1 ha hb hca hMR hlogM hllM hlogM' hX1 hX2
    have hAM : A P (max M₀ N) * (max M₀ N : ℕ) =
        P.c * (max M₀ N : ℕ) * Real.log (max M₀ N : ℕ) / Real.log (Real.log (max M₀ N : ℕ)) := by
      unfold A; ring
    have hkK : (k : ℝ) < Kof P (max M₀ N) := by
      calc (k : ℝ) ≤ _ := hk
        _ ≤ _ := hest
        _ = A P (max M₀ N) * (max M₀ N : ℕ) - 1 := by rw [hAM]
        _ < Kof P (max M₀ N) := Kof_gt P _
    have hkK' : k < Kof P (max M₀ N) := by exact_mod_cast hkK
    calc (k : ℕ∞) < (Kof P (max M₀ N) : ℕ∞) := by exact_mod_cast hkK'
      _ < fThr n := hn3

/-- Paper Theorem 1.2, (4), in the equivalent "infinitely many `n`" form:
for every `ε > 0` there are arbitrarily large `n` with
`f(n) > (1/2 - ε) log n · log log n / log log log n`. -/
theorem main_theorem (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
          Real.log (Real.log (Real.log n)) →
        (k : ℕ∞) < fThr n := by
  have hε' : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have h := main_aux hPNT (min ε (1 / 4)) hε' (min_le_right _ _)
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log n * Real.log (Real.log n) / Real.log (Real.log (Real.log n)) := by
    filter_upwards [eventually_log_ge 0, eventually_loglog_ge 0, eventually_logloglog_ge 0]
      with n h1 h2 h3
    exact div_nonneg (mul_nonneg h1 h2) h3
  refine (h.and_eventually hpos).mono ?_
  rintro n ⟨hn, hX⟩ k hk
  apply hn k
  calc (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) := hk
    _ = (1 / 2 - ε) * (Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n))) := by ring
    _ ≤ (1 / 2 - min ε (1 / 4)) * (Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n))) := by
        apply mul_le_mul_of_nonneg_right _ hX
        linarith [min_le_left ε (1 / 4)]
    _ = (1 / 2 - min ε (1 / 4)) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) := by ring

/-- `log y ≤ 2 √y` for `y > 0`. -/
private theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h1 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
  linarith

/-- The elementary estimate `C X ≤ (1/4) X y / z` when `X ≥ 0`, `z > 0`, `z ≤ 2 √y` and
`y ≥ max 1 (64 C²)`. -/
private theorem unbounded_estimate {C X y z : ℝ} (hX : 0 ≤ X) (hy1 : 1 ≤ y)
    (hy2 : 64 * C ^ 2 ≤ y) (hz0 : 0 < z) (hz : z ≤ 2 * Real.sqrt y) :
    C * X ≤ (1 / 2 - 1 / 4) * X * y / z := by
  have hsqrt : 8 * |C| ≤ Real.sqrt y := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith [sq_abs C]
  have h4Cz : 4 * C * z ≤ y := by
    have h1 : C * z ≤ |C| * z := mul_le_mul_of_nonneg_right (le_abs_self C) hz0.le
    have h2 : |C| * z ≤ |C| * (2 * Real.sqrt y) := mul_le_mul_of_nonneg_left hz (abs_nonneg C)
    have h3 : 8 * |C| * Real.sqrt y ≤ Real.sqrt y * Real.sqrt y :=
      mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg y)
    have h4 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    linarith
  rw [le_div_iff₀ hz0]
  have := mul_nonneg hX (sub_nonneg.2 h4Cz)
  linarith

/-- Paper (5): `limsup f(n)/log n = ∞`, i.e. for every `C` there are arbitrarily large `n`
with `f(n) > C log n`. -/
theorem unbounded (hPNT : PNTHyp) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ C * Real.log n → (k : ℕ∞) < fThr n := by
  have hev : ∀ᶠ n : ℕ in atTop, C * Real.log n ≤
      (1 / 2 - 1 / 4) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) := by
    filter_upwards [eventually_log_ge 0, eventually_loglog_ge (max 1 (64 * C ^ 2)),
      eventually_logloglog_ge 1] with n hX hy hz
    have hy1 : 1 ≤ Real.log (Real.log n) := le_trans (le_max_left _ _) hy
    have hy2 : 64 * C ^ 2 ≤ Real.log (Real.log n) := le_trans (le_max_right _ _) hy
    exact unbounded_estimate hX hy1 hy2 (by linarith) (log_le_two_sqrt (by linarith))
  refine ((main_theorem hPNT (1 / 4) (by norm_num)).and_eventually hev).mono ?_
  rintro n ⟨hn, hle⟩ k hk
  exact hn k (hk.trans hle)

end Erdos684
