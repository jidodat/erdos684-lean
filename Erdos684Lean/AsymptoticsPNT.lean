import Erdos684Lean.Asymptotics

/-!
# Consequences of the prime number theorem hypothesis `PNTHyp`

This is the only file in which the external analytic input is consumed directly.
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-! ### Auxiliary facts -/

/-- `PNTHyp` with a nonnegative constant. -/
private theorem pnt_nonneg (hPNT : PNTHyp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |θ x - x| ≤ C * x / (Real.log x) ^ 2 := by
  obtain ⟨C, hC⟩ := hPNT
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  refine (hC x hx).trans ?_
  have hx0 : 0 ≤ x := by linarith
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0

/-- `C / log² M → 0`. -/
private theorem tendsto_const_div_log_sq (C : ℝ) :
    Tendsto (fun M : ℕ => C / (Real.log M) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun M : ℕ => (Real.log M) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h1
  exact Tendsto.div_atTop tendsto_const_nhds h2

/-- `2 √M log M ≤ δ M` eventually. -/
private theorem eventually_sqrt_log_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, 2 * Real.sqrt M * Real.log M ≤ δ * M := by
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).def
    (by positivity : (0:ℝ) < δ / 2)
  have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [hlo', eventually_ge_atTop 1] with M hM hM1
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hM1' : (1:ℝ) ≤ M := by exact_mod_cast hM1
  rw [← Real.sqrt_eq_rpow] at hM
  simp only [Real.norm_eq_abs] at hM
  rw [abs_of_nonneg (Real.log_nonneg hM1'), abs_of_nonneg (Real.sqrt_nonneg _)] at hM
  have hs : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
  have hsn : 0 ≤ Real.sqrt (M:ℝ) := Real.sqrt_nonneg _
  calc 2 * Real.sqrt M * Real.log M ≤ 2 * Real.sqrt M * (δ / 2 * Real.sqrt M) := by
        apply mul_le_mul_of_nonneg_left hM; positivity
    _ = δ * (Real.sqrt M * Real.sqrt M) := by ring
    _ = δ * M := by rw [hs]

/-- For `0 < L ≤ log y`, `0 ≤ C`, `0 ≤ y ≤ B`: `C y / log² y ≤ C B / L²`. -/
private theorem pnt_err_le {C L y B : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hLy : L ≤ Real.log y)
    (hy : 0 ≤ y) (hyB : y ≤ B) : C * y / (Real.log y) ^ 2 ≤ C * B / L ^ 2 := by
  apply div_le_div₀ (mul_nonneg hC (hy.trans hyB)) (mul_le_mul_of_nonneg_left hyB hC)
    (by positivity)
  exact pow_le_pow_left₀ hL.le hLy 2

/-! ### Consequences of the prime number theorem -/

/-- `ψ(M) = M + o(M)`, hence `log L = (1 + o(1)) M` (paper (14)). -/
theorem eventually_psi_close (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, |ψ M - M| ≤ ε * M := by
  obtain ⟨C, hC0, hC⟩ := pnt_nonneg hPNT
  have h1 : ∀ᶠ M : ℕ in atTop, C / (Real.log M) ^ 2 < ε / 2 :=
    (tendsto_order.1 (tendsto_const_div_log_sq C)).2 (ε / 2) (by positivity)
  have h2 := eventually_sqrt_log_le (ε / 2) (by positivity)
  filter_upwards [h1, h2, eventually_ge_atTop 2] with M hM1 hM2 hM3
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hM2' : (2:ℝ) ≤ M := by exact_mod_cast hM3
  have hM1' : (1:ℝ) ≤ M := by linarith
  have hθ := hC M hM2'
  have hθ' : C * M / (Real.log M) ^ 2 ≤ ε / 2 * M := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hM1.le hM0
  have hθ2 := abs_le.1 (hθ.trans hθ')
  have hψ1 := Chebyshev.theta_le_psi (M : ℝ)
  have hψ2 := Chebyshev.psi_sub_theta_le hM1'
  rw [abs_le]
  constructor <;> nlinarith

/-- `θ(K) ≤ (1 + ε) K`. -/
theorem eventually_theta_Kof_le (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, θ (Kof P M) ≤ (1 + ε) * Kof P M := by
  obtain ⟨C, hC0, hC⟩ := pnt_nonneg hPNT
  have h1 : ∀ᶠ M : ℕ in atTop, C / (Real.log M) ^ 2 < ε :=
    (tendsto_order.1 (tendsto_const_div_log_sq C)).2 ε hε
  filter_upwards [h1, eventually_M_lt_Kof P, eventually_ge_atTop 2] with M hM1 hMK hM2
  have hM2' : (2:ℝ) ≤ M := by exact_mod_cast hM2
  have hMK' : (M:ℝ) < Kof P M := by exact_mod_cast hMK
  have hK2 : (2:ℝ) ≤ Kof P M := by linarith
  have hK0 : (0:ℝ) ≤ Kof P M := by linarith
  have hlog : Real.log M ≤ Real.log (Kof P M) := Real.log_le_log (by linarith) hMK'.le
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hθ := abs_le.1 (hC _ hK2)
  have herr : C * Kof P M / (Real.log (Kof P M)) ^ 2 ≤ ε * Kof P M := by
    rw [mul_div_right_comm]
    apply mul_le_mul_of_nonneg_right _ hK0
    calc C / (Real.log (Kof P M)) ^ 2 ≤ C / (Real.log M) ^ 2 :=
          div_le_div_of_nonneg_left hC0 (by positivity) (pow_le_pow_left₀ hlogM.le hlog 2)
      _ ≤ ε := hM1.le
  linarith [hθ.2]

/-- The short-interval bound of paper (56), summed over at most `A + 1` active indices:
for `M/2 ≤ y₁ ≤ y₂ ≤ K + 2h`, `θ(y₂) - θ(y₁) ≤ (y₂ - y₁) + E_M` with `(A+1) E_M ≤ ε M`. -/
theorem eventually_theta_interval (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∃ E : ℝ, 0 ≤ E ∧ (A P M + 1) * E ≤ ε * M ∧
      ∀ y₁ y₂ : ℝ, (M : ℝ) / 2 ≤ y₁ → y₁ ≤ y₂ → y₂ ≤ Kof P M + 2 * hof P M →
        θ y₂ - θ y₁ ≤ (y₂ - y₁) + E := by
  obtain ⟨C, hC0, hC⟩ := pnt_nonneg hPNT
  have hq : Tendsto (fun M : ℕ =>
      4 * C * (A P M * (Kof P M + 2 * hof P M) / (M * Real.log (M / 2) ^ 2))) atTop (𝓝 0) := by
    simpa using (tendsto_AK_div_log_sq P).const_mul (4 * C)
  have hq' : ∀ᶠ M : ℕ in atTop,
      4 * C * (A P M * (Kof P M + 2 * hof P M) / (M * Real.log (M / 2) ^ 2)) < ε :=
    (tendsto_order.1 hq).2 ε hε
  filter_upwards [hq', eventually_A_ge P 1, eventually_ge_atTop 4] with M hMq hMA hM4
  have hM4' : (4:ℝ) ≤ M := by exact_mod_cast hM4
  have hM0 : (0:ℝ) < M := by linarith
  have hL : 0 < Real.log ((M:ℝ) / 2) := Real.log_pos (by linarith)
  set L := Real.log ((M:ℝ) / 2) with hLdef
  set B : ℝ := Kof P M + 2 * hof P M with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨2 * C * B / L ^ 2, by positivity, ?_, ?_⟩
  · have hmul : A P M * B / (M * L ^ 2) * M = A P M * B / L ^ 2 := by
      field_simp
    have hE0 : 0 ≤ 2 * C * B / L ^ 2 := by positivity
    calc (A P M + 1) * (2 * C * B / L ^ 2) ≤ (2 * A P M) * (2 * C * B / L ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hE0
      _ = 4 * C * (A P M * B / L ^ 2) := by ring
      _ = 4 * C * (A P M * B / (M * L ^ 2)) * M := by rw [← hmul]; ring
      _ ≤ ε * M := mul_le_mul_of_nonneg_right hMq.le hM0.le
  · intro y₁ y₂ hy₁ hy₁₂ hy₂
    have hy₁2 : 2 ≤ y₁ := by linarith
    have hy₂2 : 2 ≤ y₂ := by linarith
    have hL₁ : L ≤ Real.log y₁ := Real.log_le_log (by linarith) hy₁
    have hL₂ : L ≤ Real.log y₂ := Real.log_le_log (by linarith) (by linarith)
    have h₁ := abs_le.1 (hC y₁ hy₁2)
    have h₂ := abs_le.1 (hC y₂ hy₂2)
    have e₁ := pnt_err_le hC0 hL hL₁ (by linarith) (by linarith : y₁ ≤ B)
    have e₂ := pnt_err_le hC0 hL hL₂ (by linarith) hy₂
    have : 2 * C * B / L ^ 2 = C * B / L ^ 2 + C * B / L ^ 2 := by ring
    rw [this]
    linarith [h₁.1, h₂.2]

/-- Chebyshev's bound `θ(x) ≤ x log 4` (Mathlib), in the form `#{M < p ≤ K} ≤ θ(K)/log M`. -/
theorem card_PMK_le (M : ℕ) (hM : 1 < M) :
    ((PMK P M).card : ℝ) ≤ θ (Kof P M) / Real.log M := by
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  rw [le_div_iff₀ hlogM, Chebyshev.theta_eq_sum_primesLE_log]
  have h1 : (PMK P M).card • Real.log M ≤ ∑ p ∈ PMK P M, Real.log p := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    simp only [PMK, Finset.mem_filter] at hp
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast hp.2.le)
  rw [nsmul_eq_mul] at h1
  refine h1.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)

end Erdos684
