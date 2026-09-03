import Erdos684Lean.AsymptoticsPNT

/-!
# Code entropy (paper Lemma 3.1): `log C_M ≤ (c + o(1)) M`

The paper evaluates `Σ_{M<p≤K} log(p/h)` by partial summation.  We use the elementary upper bound
`log(p/h) ≤ log p · log(K/h) / log K` (valid since `x ↦ 1 - log h / log x` is increasing), so that
`Σ_{M<p≤K} log(p/h) ≤ θ(K) log(K/h) / log K`, together with `θ(K) ≤ (1+o(1))K` and
`A log A / log M → c`.  Only the upper bound is needed.
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-- `log (⌊p/h⌋ + 1) ≤ log (p/h) + h/p` for `0 < h ≤ p`. -/
theorem log_cell_le {p h : ℕ} (hh : 0 < h) (hp : h ≤ p) :
    Real.log ((p / h : ℕ) + 1 : ℝ) ≤ Real.log ((p : ℝ) / h) + (h : ℝ) / p := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hp' : (0 : ℝ) < p := lt_of_lt_of_le hh' (by exact_mod_cast hp)
  have h1 : ((p / h : ℕ) : ℝ) ≤ (p : ℝ) / h := Nat.cast_div_le
  have hq : 0 < (p : ℝ) / h := by positivity
  have h2 : (p : ℝ) / h + 1 = (p : ℝ) / h * (1 + (h : ℝ) / p) := by
    field_simp
  calc Real.log ((p / h : ℕ) + 1 : ℝ) ≤ Real.log ((p : ℝ) / h + 1) :=
        Real.log_le_log (by positivity) (by linarith)
    _ = Real.log ((p : ℝ) / h) + Real.log (1 + (h : ℝ) / p) := by
        rw [h2, Real.log_mul hq.ne' (by positivity)]
    _ ≤ Real.log ((p : ℝ) / h) + (h : ℝ) / p := by
        have := Real.log_le_sub_one_of_pos (x := 1 + (h : ℝ) / p) (by positivity)
        linarith

/-- `log (p/h) / log p ≤ log (K/h) / log K` for `1 ≤ h`, `1 < p ≤ K`. -/
theorem log_ratio_mono {p K h : ℝ} (hh : 1 ≤ h) (hp : 1 < p) (hpK : p ≤ K) :
    Real.log (p / h) ≤ Real.log p * (Real.log (K / h) / Real.log K) := by
  have hh0 : 0 < h := by linarith
  have hp0 : 0 < p := by linarith
  have hK : 1 < K := lt_of_lt_of_le hp hpK
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg hh
  have hpK' : Real.log p ≤ Real.log K := Real.log_le_log hp0 hpK
  rw [Real.log_div hp0.ne' hh0.ne', Real.log_div (by linarith) hh0.ne', ← mul_div_assoc,
    le_div_iff₀ hlogK]
  nlinarith [mul_le_mul_of_nonneg_right hpK' hlogh]

/-- Paper Lemma 3.1 (upper bound). -/
theorem log_CM_le (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, Real.log (CM P M) ≤ (P.c + ε) * M := by
  have hc := P.c_pos
  set δ : ℝ := ε / (4 * P.c) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδc : (1 + δ) * P.c = P.c + ε / 4 := by
    rw [hδ]
    field_simp
  -- the limits
  have hlogA := tendsto_logA P
  have hlog41 : Tendsto (fun M : ℕ => Real.log 41 / Real.log (A P M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogA
  have hinvK : Tendsto (fun M : ℕ => Real.log M / Real.log (Kof P M)) atTop (𝓝 1) := by
    have := (tendsto_logK_div_log P).inv₀ one_ne_zero
    simpa [inv_div] using this
  have hinv20 : Tendsto (fun M : ℕ => (20 * Real.log (A P M))⁻¹) atTop (𝓝 0) :=
    (hlogA.const_mul_atTop (by norm_num : (0 : ℝ) < 20)).inv_tendsto_atTop
  have hT1 : Tendsto (fun M : ℕ => (1 + δ) * (A P M * Real.log (A P M) / Real.log M) *
      (Real.log M / Real.log (Kof P M)) *
      (Real.log 41 / Real.log (A P M) + 1 + Real.log (Real.log (A P M)) / Real.log (A P M)))
      atTop (𝓝 ((1 + δ) * P.c * 1 * (0 + 1 + 0))) :=
    ((tendsto_const_nhds.mul (tendsto_A_logA_div_log P)).mul hinvK).mul
      ((hlog41.add tendsto_const_nhds).add (tendsto_loglogA_div_logA P))
  have hT2 : Tendsto (fun M : ℕ => (1 + δ) * (A P M / Real.log M) * (20 * Real.log (A P M))⁻¹)
      atTop (𝓝 ((1 + δ) * 0 * 0)) :=
    (tendsto_const_nhds.mul (tendsto_A_div_log P)).mul hinv20
  have hlt1 : (1 + δ) * P.c * 1 * (0 + 1 + 0) < P.c + ε / 2 := by
    rw [mul_one, add_zero, zero_add, mul_one, hδc]
    linarith
  have hE1 := hT1.eventually_le_const hlt1
  have hE2 := hT2.eventually_le_const
    (by simp only [mul_zero]; positivity : (1 + δ) * 0 * 0 < ε / 2)
  filter_upwards [eventually_hof_pos P, eventually_gt_atTop 1, eventually_M_lt_Kof P,
    eventually_A_ge P (Real.exp 1), eventually_theta_Kof_le P hPNT δ hδ0,
    eventually_K_div_hof_le P, hE1, hE2] with M hh hM hMK hA hθ hKh h1 h2
  set h := hof P M with hh_def
  set K := Kof P M with hK_def
  -- basic facts
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hA1 : 1 < A P M := by
    have := Real.add_one_le_exp 1
    linarith
  have hA0 : 0 < A P M := by linarith
  have hlogA1 : 1 ≤ Real.log (A P M) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hA
  have hlogA0 : 0 < Real.log (A P M) := by linarith
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ M / (20 * Real.log (A P M)) := hof_le P M hA1
  have hhM : (h : ℝ) < M := by
    calc (h : ℝ) ≤ M / (20 * Real.log (A P M)) := hhle
      _ ≤ M / 20 := div_le_div_of_nonneg_left hM0.le (by norm_num) (by linarith)
      _ < M := by linarith
  have hhM' : (h : ℝ) / M ≤ (20 * Real.log (A P M))⁻¹ := by
    rw [div_le_iff₀ hM0, inv_mul_eq_div]
    exact hhle
  have hMK' : (M : ℝ) < K := by exact_mod_cast hMK
  have hK1 : (1 : ℝ) < K := by linarith
  have hlogK : 0 < Real.log K := Real.log_pos hK1
  have hKA : (K : ℝ) ≤ A P M * M := Kof_le P M hA0.le
  have hθ0 : 0 ≤ θ K := Chebyshev.theta_nonneg _
  have hθ' : θ K ≤ (1 + δ) * (A P M * M) :=
    hθ.trans (mul_le_mul_of_nonneg_left hKA (by linarith))
  -- `log (K/h) ≤ log 41 + log A + log log A`
  have hlogKh : Real.log ((K : ℝ) / h) ≤
      Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M)) := by
    calc Real.log ((K : ℝ) / h) ≤ Real.log (1 + (K : ℝ) / h) :=
          Real.log_le_log (by positivity) (by linarith)
      _ ≤ Real.log (41 * A P M * Real.log (A P M)) := Real.log_le_log (by positivity) hKh
      _ = Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M)) := by
          rw [Real.log_mul (by positivity) hlogA0.ne', Real.log_mul (by norm_num) hA0.ne']
  have hR0 : 0 ≤ Real.log ((K : ℝ) / h) / Real.log K := by
    apply div_nonneg _ hlogK.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hh0]
    linarith
  -- the pointwise bound
  have hpt : ∀ p ∈ PMK P M, Real.log ((p / h : ℕ) + 1 : ℝ) ≤
      Real.log p * (Real.log ((K : ℝ) / h) / Real.log K) + (h : ℝ) / M := by
    intro p hp
    have hp' : M < p := (Finset.mem_filter.1 hp).2
    have hpK : p ≤ K := (Nat.mem_primesLE.1 (Finset.mem_filter.1 hp).1).1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast lt_trans hM hp'
    have hpM : (M : ℝ) < p := by exact_mod_cast hp'
    have hhp : h ≤ p := by
      have : (h : ℝ) ≤ p := by linarith
      exact_mod_cast this
    calc Real.log ((p / h : ℕ) + 1 : ℝ) ≤ Real.log ((p : ℝ) / h) + (h : ℝ) / p :=
          log_cell_le hh hhp
      _ ≤ Real.log p * (Real.log ((K : ℝ) / h) / Real.log K) + (h : ℝ) / M :=
          add_le_add (log_ratio_mono hh1 hp1 (by exact_mod_cast hpK))
            (div_le_div_of_nonneg_left hh0.le hM0 hpM.le)
  -- `log C_M` as a sum
  have hlogCM : Real.log (CM P M) = ∑ p ∈ PMK P M, Real.log ((p / h : ℕ) + 1 : ℝ) := by
    rw [CM]
    push_cast
    exact Real.log_prod (fun p _ => by positivity)
  have hsum : ∑ p ∈ PMK P M, Real.log p ≤ θ K := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p _ _
    exact Real.log_natCast_nonneg p
  have hcard := card_PMK_le P M hM
  calc Real.log (CM P M) = ∑ p ∈ PMK P M, Real.log ((p / h : ℕ) + 1 : ℝ) := hlogCM
    _ ≤ ∑ p ∈ PMK P M, (Real.log p * (Real.log ((K : ℝ) / h) / Real.log K) + (h : ℝ) / M) :=
        Finset.sum_le_sum hpt
    _ = (∑ p ∈ PMK P M, Real.log p) * (Real.log ((K : ℝ) / h) / Real.log K)
          + (PMK P M).card * ((h : ℝ) / M) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ θ K * (Real.log ((K : ℝ) / h) / Real.log K)
          + (θ K / Real.log M) * ((h : ℝ) / M) :=
        add_le_add (mul_le_mul hsum le_rfl hR0 hθ0)
          (mul_le_mul hcard le_rfl (by positivity) (by positivity))
    _ ≤ ((1 + δ) * (A P M * M)) *
            ((Real.log 41 + Real.log (A P M) + Real.log (Real.log (A P M))) / Real.log K)
          + ((1 + δ) * (A P M * M) / Real.log M) * (20 * Real.log (A P M))⁻¹ :=
        add_le_add (mul_le_mul hθ' (div_le_div_of_nonneg_right hlogKh hlogK.le) hR0 (by positivity))
          (mul_le_mul (div_le_div_of_nonneg_right hθ' hlogM.le) hhM' (by positivity)
            (by positivity))
    _ = M * ((1 + δ) * (A P M * Real.log (A P M) / Real.log M) *
            (Real.log M / Real.log K) *
            (Real.log 41 / Real.log (A P M) + 1 + Real.log (Real.log (A P M)) / Real.log (A P M)))
          + M * ((1 + δ) * (A P M / Real.log M) * (20 * Real.log (A P M))⁻¹) := by
        field_simp
    _ ≤ M * (P.c + ε / 2) + M * (ε / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hM0.le) (mul_le_mul_of_nonneg_left h2 hM0.le)
    _ = (P.c + ε) * M := by ring

end Erdos684
