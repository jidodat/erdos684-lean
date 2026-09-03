import Erdos684Lean.Defs
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Discharging the prime-number-theorem hypothesis

`PrimeNumberTheoremAnd.MediumPNT` (Kontorovich–Tao et al.) gives
`ψ(x) = x + O(x·exp(−c (log x)^{1/10}))`.  Together with Mathlib's
`ψ(x) − θ(x) ≤ 2√x log x` this yields `θ(x) = x + O(x / log² x)`, i.e. `PNTHyp`.
-/

open Filter Topology Real Asymptotics
open scoped Chebyshev

namespace Erdos684

/-- The prime number theorem with a power-of-logarithm remainder, derived from `MediumPNT`. -/
theorem pntHyp : PNTHyp := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C₁, hC₁, hb⟩ := hO.exists_pos
  -- (E1) the `MediumPNT` bound, with norms removed
  have E1 : ∀ᶠ x : ℝ in atTop,
      |ψ x - x| ≤ C₁ * (x * exp (-(c * log x ^ ((1 : ℝ) / 10)))) := by
    filter_upwards [hb.bound, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hx
    rwa [abs_of_nonneg (mul_nonneg hx0 (Real.exp_pos _).le), neg_mul] at hx
  -- (E2) `C₁ (log x)^2 exp(-c (log x)^{1/10}) → 0`
  have hz : Tendsto (fun x : ℝ => c * log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp tendsto_log_atTop).const_mul_atTop hc
  have E2 : ∀ᶠ x : ℝ in atTop,
      (C₁ / c ^ 20) * ((c * log x ^ ((1 : ℝ) / 10)) ^ 20 * exp (-(c * log x ^ ((1 : ℝ) / 10))))
        < 1 / 2 := by
    have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).comp hz).const_mul (C₁ / c ^ 20)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  -- (E3) `(log x / 2)^3 exp(-(log x)/2) → 0`
  have E3 : ∀ᶠ x : ℝ in atTop, (log x / 2) ^ 3 * exp (-(log x / 2)) < 1 / 32 := by
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      (tendsto_log_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    exact h.eventually (gt_mem_nhds (by norm_num))
  have E4 : ∀ᶠ x : ℝ in atTop, 1 ≤ log x := tendsto_log_atTop.eventually_ge_atTop 1
  have E5 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x := eventually_ge_atTop 2
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 (E1.and (E2.and (E3.and (E4.and E5))))
  -- the large-`x` regime
  have key : ∀ x, x₁ ≤ x → |θ x - x| ≤ x / log x ^ 2 := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx₁ x hx
    have hx0 : 0 < x := by linarith
    have hL0 : 0 ≤ log x := by linarith
    have hL2 : 0 < log x ^ 2 := by nlinarith
    -- (i) `C₁ x exp(-z) ≤ x / log x ^ 2 / 2`
    have hpow : (c * log x ^ ((1 : ℝ) / 10)) ^ 20 = c ^ 20 * log x ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (log x ^ _), ← Real.rpow_mul hL0]
      norm_num
    have hc20 : c ^ 20 ≠ 0 := by positivity
    have h2' : C₁ * log x ^ 2 * exp (-(c * log x ^ ((1 : ℝ) / 10))) < 1 / 2 := by
      rw [hpow] at h2
      calc C₁ * log x ^ 2 * exp (-(c * log x ^ ((1 : ℝ) / 10)))
          = C₁ * log x ^ 2 * exp (-(c * log x ^ ((1 : ℝ) / 10))) * (c ^ 20 / c ^ 20) := by
            rw [div_self hc20, mul_one]
        _ = (C₁ / c ^ 20) * (c ^ 20 * log x ^ 2 * exp (-(c * log x ^ ((1 : ℝ) / 10)))) := by ring
        _ < 1 / 2 := h2
    have hi : C₁ * (x * exp (-(c * log x ^ ((1 : ℝ) / 10)))) ≤ x / log x ^ 2 / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hL2]
      have := mul_le_mul_of_nonneg_left h2'.le hx0.le
      nlinarith
    -- (ii) `2 √x log x ≤ x / log x ^ 2 / 2`
    have hs : exp (log x / 2) = √x := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
      congr 1; ring
    have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
    rw [Real.exp_neg, hs] at h3
    have h3' : 4 * log x ^ 3 ≤ √x := by
      have := (mul_inv_lt_iff₀ hs0).1 h3
      have e : (log x / 2) ^ 3 = log x ^ 3 / 8 := by ring
      rw [e] at this
      linarith
    have hii : 2 * √x * log x ≤ x / log x ^ 2 / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hL2]
      have := mul_le_mul_of_nonneg_left h3' hs0.le
      have := Real.mul_self_sqrt hx0.le
      nlinarith
    -- assemble
    have hpt := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)
    have hθψ := Chebyshev.theta_le_psi x
    have hA := abs_le.1 (h1.trans hi)
    rw [abs_le]
    constructor <;> linarith
  -- the final constant and case split
  refine ⟨max 1 ((log 4 + 1) * log (max x₁ 2) ^ 2), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < log x := Real.log_pos (by linarith)
  have hL2 : 0 < log x ^ 2 := by positivity
  rcases le_or_gt x₁ x with h | h
  · calc |θ x - x| ≤ x / log x ^ 2 := key x h
      _ ≤ max 1 ((log 4 + 1) * log (max x₁ 2) ^ 2) * x / log x ^ 2 :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_left hx0.le (le_max_left _ _)) hL2.le
  · have hxx₂ : x ≤ max x₁ 2 := h.le.trans (le_max_left _ _)
    have hlog : log x ≤ log (max x₁ 2) := Real.log_le_log hx0 hxx₂
    have hlog4 : 0 < log 4 := Real.log_pos (by norm_num)
    have hbound : |θ x - x| ≤ (log 4 + 1) * x := by
      have := Chebyshev.theta_le_log4_mul_x hx0.le
      have := Chebyshev.theta_nonneg x
      rw [abs_le]
      constructor <;> nlinarith
    have hsq : log x ^ 2 ≤ log (max x₁ 2) ^ 2 := pow_le_pow_left₀ hL0.le hlog 2
    calc |θ x - x| ≤ (log 4 + 1) * x := hbound
      _ ≤ (log 4 + 1) * log (max x₁ 2) ^ 2 * x / log x ^ 2 := by
          rw [le_div_iff₀ hL2]
          have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (log 4 + 1) * x)
          nlinarith
      _ ≤ max 1 ((log 4 + 1) * log (max x₁ 2) ^ 2) * x / log x ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le) hL2.le

end Erdos684
