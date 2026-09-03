import Erdos684Lean.Defs

/-!
# Asymptotic facts about the scales (paper (14) and the `o(·)` bookkeeping)

All statements are for a fixed parameter tuple `P` and `M → ∞` (paper, end of Section 1).
The prime-number-theorem input `PNTHyp` is used only in the last section.
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-! ### Auxiliary real-analytic facts -/

/-- `y / log y → ∞`. -/
private theorem tendsto_id_div_log : Tendsto (fun y : ℝ => y / Real.log y) atTop atTop := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact div_pos (Real.log_pos hy) (by linarith)
  refine h1.inv_tendsto_nhdsGT_zero.congr fun y => ?_
  simp [inv_div]

private theorem tendsto_logM : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_loglog : Tendsto (fun M : ℕ => Real.log (Real.log M)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logM

private theorem eventually_logM_pos : ∀ᶠ M : ℕ in atTop, 0 < Real.log M :=
  tendsto_logM.eventually_gt_atTop 0

private theorem eventually_loglog_pos : ∀ᶠ M : ℕ in atTop, 0 < Real.log (Real.log M) :=
  tendsto_loglog.eventually_gt_atTop 0

private theorem tendsto_loglog_div_log :
    Tendsto (fun M : ℕ => Real.log (Real.log M) / Real.log M) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_logM

/-! ### The scale `A` -/

theorem tendsto_A : Tendsto (A P) atTop atTop := by
  have h := (tendsto_id_div_log.comp tendsto_logM).const_mul_atTop P.c_pos
  refine h.congr fun M => ?_
  simp only [Function.comp_apply, A, mul_div_assoc]

theorem eventually_A_ge (C : ℝ) : ∀ᶠ M : ℕ in atTop, C ≤ A P M :=
  (tendsto_A P).eventually_ge_atTop C

theorem tendsto_logA : Tendsto (fun M : ℕ => Real.log (A P M)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_A P)

/-- `A / log M = c / log log M → 0`. -/
theorem tendsto_A_div_log : Tendsto (fun M : ℕ => A P M / Real.log M) atTop (𝓝 0) := by
  have h : Tendsto (fun M : ℕ => P.c / Real.log (Real.log M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_loglog
  refine h.congr' ?_
  filter_upwards [eventually_logM_pos, eventually_loglog_pos] with M h1 h2
  simp only [A]
  field_simp

/-- `log A = log c + log log M - log log log M` eventually. -/
private theorem eventually_logA_eq : ∀ᶠ M : ℕ in atTop,
    Real.log (A P M) =
      Real.log P.c + Real.log (Real.log M) - Real.log (Real.log (Real.log M)) := by
  filter_upwards [eventually_logM_pos, eventually_loglog_pos] with M h1 h2
  simp only [A]
  rw [Real.log_div (mul_pos P.c_pos h1).ne' h2.ne', Real.log_mul P.c_pos.ne' h1.ne']

/-- `log A / log log M → 1`. -/
theorem tendsto_logA_div_loglog :
    Tendsto (fun M : ℕ => Real.log (A P M) / Real.log (Real.log M)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun M : ℕ => Real.log P.c / Real.log (Real.log M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_loglog
  have h2 : Tendsto (fun M : ℕ => Real.log (Real.log (Real.log M)) / Real.log (Real.log M))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_loglog
  have h := (h1.add (tendsto_const_nhds (x := (1 : ℝ)))).sub h2
  rw [show (0 : ℝ) + 1 - 0 = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_logA_eq P, eventually_loglog_pos] with M hM h2
  rw [hM]
  field_simp

/-- `A log A / log M → c` (paper, proof of Lemma 3.1). -/
theorem tendsto_A_logA_div_log :
    Tendsto (fun M : ℕ => A P M * Real.log (A P M) / Real.log M) atTop (𝓝 P.c) := by
  have h := (tendsto_logA_div_loglog P).const_mul P.c
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_logM_pos, eventually_loglog_pos] with M h1 h2
  simp only [A]
  field_simp

/-- `log log A / log A → 0`. -/
theorem tendsto_loglogA_div_logA :
    Tendsto (fun M : ℕ => Real.log (Real.log (A P M)) / Real.log (A P M)) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_logA P)

/-- `log (A + 1) / log A → 1`. -/
theorem tendsto_logA1_div_logA :
    Tendsto (fun M : ℕ => Real.log (A P M + 1) / Real.log (A P M)) atTop (𝓝 1) := by
  have hup : Tendsto (fun M : ℕ => 1 + Real.log 2 / Real.log (A P M)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := Real.log 2)).div_atTop (tendsto_logA P))
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_A_ge P 2] with M hA
    have hlog : 0 < Real.log (A P M) := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlog, one_mul]
    exact Real.log_le_log (by linarith) (by linarith)
  · filter_upwards [eventually_A_ge P 2] with M hA
    have hlog : 0 < Real.log (A P M) := Real.log_pos (by linarith)
    have h1 : Real.log (A P M + 1) ≤ Real.log (A P M * 2) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by linarith) (by norm_num)] at h1
    have e : (1 + Real.log 2 / Real.log (A P M)) * Real.log (A P M)
        = Real.log (A P M) + Real.log 2 := by
      field_simp
    rw [div_le_iff₀ hlog, e]
    exact h1

/-- `log A / log M → 0`. -/
private theorem tendsto_logA_div_log :
    Tendsto (fun M : ℕ => Real.log (A P M) / Real.log M) atTop (𝓝 0) := by
  have h := (tendsto_logA_div_loglog P).mul tendsto_loglog_div_log
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_loglog_pos, eventually_logM_pos] with M h2 h1
  field_simp

/-- `A ≤ c log M` eventually. -/
private theorem eventually_A_le : ∀ᶠ M : ℕ in atTop, A P M ≤ P.c * Real.log M := by
  filter_upwards [tendsto_loglog.eventually_ge_atTop 1, eventually_logM_pos] with M h1 h2
  exact div_le_self (mul_pos P.c_pos h2).le h1

/-- `M / log A → ∞`. -/
private theorem tendsto_M_div_logA :
    Tendsto (fun M : ℕ => (M : ℝ) / Real.log (A P M)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id_div_log.comp tendsto_natCast_atTop_atTop)
  filter_upwards [(tendsto_logA_div_log P).eventually_lt_const one_pos, eventually_logM_pos,
    (tendsto_logA P).eventually_gt_atTop 0] with M h1 h2 h3
  simp only [Function.comp_apply]
  rw [div_lt_iff₀ h2, one_mul] at h1
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) h3 h1.le

private theorem tendsto_M_div_mul_logA (k : ℝ) (hk : 0 < k) :
    Tendsto (fun M : ℕ => (M : ℝ) / (k * Real.log (A P M))) atTop atTop := by
  refine ((tendsto_M_div_logA P).atTop_div_const hk).congr fun M => ?_
  rw [div_div, mul_comm]

/-! ### The scales `h`, `K`, `J`, `L` -/

theorem hof_le (M : ℕ) (hA : 1 < A P M) : (hof P M : ℝ) ≤ M / (20 * Real.log (A P M)) :=
  Nat.floor_le (div_nonneg (Nat.cast_nonneg _) (by linarith [Real.log_pos hA]))

theorem eventually_hof_ge : ∀ᶠ M : ℕ in atTop, (M : ℝ) / (40 * Real.log (A P M)) ≤ hof P M := by
  filter_upwards [(tendsto_M_div_mul_logA P 20 (by norm_num)).eventually_ge_atTop 2] with M h
  have h1 := Nat.lt_floor_add_one ((M : ℝ) / (20 * Real.log (A P M)))
  have h2 : (M : ℝ) / (40 * Real.log (A P M)) = (M : ℝ) / (20 * Real.log (A P M)) / 2 := by
    rw [div_div]; congr 1; ring
  rw [h2]
  unfold hof
  linarith

theorem tendsto_hof : Tendsto (fun M => (hof P M : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_hof_ge P) (tendsto_M_div_mul_logA P 40 (by norm_num))

theorem eventually_hof_pos : ∀ᶠ M : ℕ in atTop, 0 < hof P M := by
  filter_upwards [(tendsto_hof P).eventually_gt_atTop 0] with M h
  exact_mod_cast h

/-- `2h < M` (paper (14)). -/
theorem eventually_two_hof_lt : ∀ᶠ M : ℕ in atTop, 2 * hof P M < M := by
  filter_upwards [eventually_A_ge P 2, (tendsto_logA P).eventually_ge_atTop 1,
    eventually_ge_atTop 1] with M hA hL hM
  have h1 := hof_le P M (by linarith)
  have hL0 : 0 < Real.log (A P M) := by linarith
  rw [le_div_iff₀ (by positivity)] at h1
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hh : (0 : ℝ) ≤ hof P M := Nat.cast_nonneg _
  have : (2 : ℝ) * hof P M < M := by nlinarith [mul_nonneg hh (sub_nonneg.2 hL)]
  exact_mod_cast this

/-- `h / M → 0`. -/
theorem tendsto_hof_div : Tendsto (fun M : ℕ => (hof P M : ℝ) / M) atTop (𝓝 0) := by
  have hup : Tendsto (fun M : ℕ => 1 / (20 * Real.log (A P M))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_logA P).const_mul_atTop (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun M => by positivity
  · filter_upwards [eventually_A_ge P 2, eventually_gt_atTop 0] with M hA hM
    have hL0 : 0 < Real.log (A P M) := Real.log_pos (by linarith)
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have h1 := hof_le P M (by linarith)
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_le_div_iff₀ hM' (by positivity), one_mul]
    exact h1

theorem Kof_le (M : ℕ) (hA : 0 ≤ A P M) : (Kof P M : ℝ) ≤ A P M * M :=
  Nat.floor_le (mul_nonneg hA (Nat.cast_nonneg _))

theorem Kof_gt (M : ℕ) : A P M * M - 1 < Kof P M := by
  have := Nat.lt_floor_add_one (A P M * M)
  unfold Kof
  linarith

/-- `M < K` (paper (14)). -/
theorem eventually_M_lt_Kof : ∀ᶠ M : ℕ in atTop, M < Kof P M := by
  filter_upwards [eventually_A_ge P 2, eventually_ge_atTop 1] with M hA hM
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 := Kof_gt P M
  have : (M : ℝ) < Kof P M := by
    nlinarith [mul_le_mul_of_nonneg_right hA (by linarith : (0 : ℝ) ≤ M)]
  exact_mod_cast this

/-- `K < M²` (paper (14): `K = o(M²)`). -/
theorem eventually_Kof_lt_sq : ∀ᶠ M : ℕ in atTop, Kof P M < M ^ 2 := by
  filter_upwards [eventually_A_ge P 0, eventually_A_le P,
    (tendsto_id_div_log.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (P.c + 1),
    eventually_logM_pos, eventually_gt_atTop 0] with M hA0 hAc hdiv hlog hM
  simp only [Function.comp_apply] at hdiv
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [le_div_iff₀ hlog] at hdiv
  have hAM : A P M < M := by nlinarith
  have : (Kof P M : ℝ) < (M : ℝ) ^ 2 := by
    calc (Kof P M : ℝ) ≤ A P M * M := Kof_le P M hA0
      _ < M * M := by nlinarith
      _ = (M : ℝ) ^ 2 := by ring
  exact_mod_cast this

/-- `log K / log M → 1`. -/
theorem tendsto_logK_div_log :
    Tendsto (fun M : ℕ => Real.log (Kof P M) / Real.log M) atTop (𝓝 1) := by
  have hup : Tendsto (fun M : ℕ => 1 + Real.log (A P M) / Real.log M) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_logA_div_log P)
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_M_lt_Kof P, eventually_gt_atTop 1] with M hK hM
    have hM' : (1 : ℝ) < M := by exact_mod_cast hM
    have hK' : (M : ℝ) < Kof P M := by exact_mod_cast hK
    rw [le_div_iff₀ (Real.log_pos hM'), one_mul]
    exact Real.log_le_log (by linarith) hK'.le
  · filter_upwards [eventually_A_ge P 2, eventually_gt_atTop 1] with M hA hM
    have hM' : (1 : ℝ) < M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    have hlog := Real.log_pos hM'
    have hK := Kof_le P M (by linarith)
    have hKpos : (0 : ℝ) < Kof P M := by
      have := Kof_gt P M
      nlinarith
    have e : (1 + Real.log (A P M) / Real.log M) * Real.log M
        = Real.log M + Real.log (A P M) := by
      field_simp
    have h1 := Real.log_le_log hKpos hK
    rw [Real.log_mul (by linarith) hM0.ne'] at h1
    rw [div_le_iff₀ hlog, e]
    linarith

private theorem tendsto_log_cube_div :
    Tendsto (fun M : ℕ => Real.log M ^ 3 / M) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine this.congr fun M => ?_
  simp [Function.comp_apply]

/-- `√K log K / M → 0` (used for `ψ - θ = O(√K log K)`). -/
theorem tendsto_sqrtK_logK_div :
    Tendsto (fun M : ℕ => Real.sqrt (Kof P M) * Real.log (Kof P M) / M) atTop (𝓝 0) := by
  have hc := P.c_pos
  have hup : Tendsto (fun M : ℕ => Real.sqrt (4 * P.c * (Real.log M ^ 3 / M))) atTop (𝓝 0) := by
    have := (tendsto_log_cube_div.const_mul (4 * P.c)).sqrt
    rwa [mul_zero, Real.sqrt_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_M_lt_Kof P, eventually_gt_atTop 1] with M hK hM
    have hM' : (1 : ℝ) < M := by exact_mod_cast hM
    have hK' : (M : ℝ) < Kof P M := by exact_mod_cast hK
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Kof P M)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) this) (Nat.cast_nonneg _)
  · filter_upwards [eventually_A_ge P 2, eventually_A_le P, eventually_gt_atTop 1,
      (tendsto_logA_div_log P).eventually_lt_const one_pos, eventually_M_lt_Kof P]
      with M hA hAc hM hlogA hMK
    have hM' : (1 : ℝ) < M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    have hlog := Real.log_pos hM'
    have hK := Kof_le P M (by linarith)
    have hMK' : (M : ℝ) < Kof P M := by exact_mod_cast hMK
    have hKpos : (0 : ℝ) < Kof P M := by linarith
    have hlogK0 : 0 ≤ Real.log (Kof P M) := Real.log_nonneg (by linarith)
    have hlogK : Real.log (Kof P M) ≤ 2 * Real.log M := by
      rw [div_lt_iff₀ hlog, one_mul] at hlogA
      calc Real.log (Kof P M) ≤ Real.log (A P M * M) := Real.log_le_log hKpos hK
        _ = Real.log (A P M) + Real.log M := Real.log_mul (by linarith) hM0.ne'
        _ ≤ 2 * Real.log M := by linarith
    have hKc : (Kof P M : ℝ) ≤ P.c * Real.log M * M :=
      hK.trans (mul_le_mul_of_nonneg_right hAc hM0.le)
    rw [Real.le_sqrt (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlogK0) (Nat.cast_nonneg _))
      (by positivity), div_pow, mul_pow, Real.sq_sqrt hKpos.le, div_le_iff₀ (by positivity)]
    have e : 4 * P.c * (Real.log M ^ 3 / M) * (M : ℝ) ^ 2
        = (P.c * Real.log M * M) * (4 * Real.log M ^ 2) := by
      field_simp
    rw [e]
    have h2 : Real.log (Kof P M) ^ 2 ≤ (2 * Real.log M) ^ 2 := pow_le_pow_left₀ hlogK0 hlogK 2
    calc (Kof P M : ℝ) * Real.log (Kof P M) ^ 2
        ≤ (P.c * Real.log M * M) * (2 * Real.log M) ^ 2 :=
          mul_le_mul hKc h2 (by positivity) (by positivity)
      _ = (P.c * Real.log M * M) * (4 * Real.log M ^ 2) := by ring

/-- `K^{(1+λ)/2} / M → 0` (paper, end of proof of Lemma 4.1). -/
theorem tendsto_K_rpow_div :
    Tendsto (fun M : ℕ => (Kof P M : ℝ) ^ ((1 + P.lam) / 2) / M) atTop (𝓝 0) := by
  have hc := P.c_pos
  set s : ℝ := (1 + P.lam) / 2 with hs
  have hs0 : 0 < s := by have := P.lam_pos; rw [hs]; linarith
  have hs1 : 0 < 1 - s := by have := P.lam_lt_one; rw [hs]; linarith
  have hup : Tendsto (fun M : ℕ => P.c ^ s * (Real.log M ^ s / (M : ℝ) ^ (1 - s)))
      atTop (𝓝 0) := by
    have := ((isLittleO_log_rpow_rpow_atTop s hs1).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (P.c ^ s)
    rw [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun M => by positivity
  · filter_upwards [eventually_A_ge P 2, eventually_A_le P, eventually_gt_atTop 1] with M hA hAc hM
    have hM' : (1 : ℝ) < M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    have hlog := Real.log_pos hM'
    have hKc : (Kof P M : ℝ) ≤ P.c * Real.log M * M :=
      (Kof_le P M (by linarith)).trans (mul_le_mul_of_nonneg_right hAc hM0.le)
    have hMs : (0 : ℝ) < (M : ℝ) ^ s := Real.rpow_pos_of_pos hM0 s
    calc (Kof P M : ℝ) ^ s / M ≤ (P.c * Real.log M * M) ^ s / M := by
          gcongr
      _ = P.c ^ s * (Real.log M ^ s / (M : ℝ) ^ (1 - s)) := by
          rw [Real.mul_rpow (by positivity) hM0.le, Real.mul_rpow hc.le hlog.le,
            Real.rpow_sub hM0, Real.rpow_one]
          field_simp

/-- `A (K + 2h) / (M log² (M/2)) → 0` (the PNT-remainder cost in paper Lemma 6.2). -/
theorem tendsto_AK_div_log_sq :
    Tendsto (fun M : ℕ => A P M * (Kof P M + 2 * hof P M) / (M * Real.log (M / 2) ^ 2))
      atTop (𝓝 0) := by
  have hup : Tendsto
      (fun M : ℕ => 4 * ((A P M / Real.log M) ^ 2 + (A P M / Real.log M) / Real.log M))
      atTop (𝓝 0) := by
    have h1 := (tendsto_A_div_log P).pow 2
    have h2 := (tendsto_A_div_log P).div_atTop tendsto_logM
    have := (h1.add h2).const_mul 4
    have h0 : (4 : ℝ) * (0 ^ 2 + 0) = 0 := by norm_num
    rwa [h0] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_A_ge P 0] with M hA
    positivity
  · filter_upwards [eventually_A_ge P 2, eventually_two_hof_lt P, eventually_ge_atTop 4,
      tendsto_logM.eventually_ge_atTop (2 * Real.log 2)] with M hA hh hM hlog
    have hM' : (4 : ℝ) ≤ M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogM : 0 < Real.log M := by linarith
    have hK := Kof_le P M (by linarith)
    have hh' : (2 : ℝ) * hof P M ≤ M := by exact_mod_cast hh.le
    have hlogM2 : Real.log (M / 2) = Real.log M - Real.log 2 :=
      Real.log_div hM0.ne' (by norm_num)
    have hhalf : Real.log M / 2 ≤ Real.log (M / 2) := by rw [hlogM2]; linarith
    have hpos2 : 0 < Real.log (M / 2) := by linarith
    have hA0 : 0 ≤ A P M := by linarith
    rw [div_le_iff₀ (by positivity)]
    have e : 4 * ((A P M / Real.log M) ^ 2 + A P M / Real.log M / Real.log M)
        * (M * Real.log (M / 2) ^ 2)
        = A P M * (A P M + 1) * M * (4 * Real.log (M / 2) ^ 2 / Real.log M ^ 2) := by
      field_simp
    rw [e]
    have hsq : 1 ≤ 4 * Real.log (M / 2) ^ 2 / Real.log M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul hhalf hhalf (by linarith) hpos2.le]
    calc A P M * (Kof P M + 2 * hof P M) ≤ A P M * (A P M * M + M) := by gcongr
      _ = A P M * (A P M + 1) * M * 1 := by ring
      _ ≤ A P M * (A P M + 1) * M * (4 * Real.log (M / 2) ^ 2 / Real.log M ^ 2) := by
          gcongr

/-- `(K + 2h) / (h M) · ... ` auxiliary: `log (1 + K/h) - log A → ` bounded by `log log A + O(1)`;
we record the form actually used: eventually `1 + K/h ≤ 41 A log A`. -/
theorem eventually_K_div_hof_le :
    ∀ᶠ M : ℕ in atTop, 1 + (Kof P M : ℝ) / hof P M ≤ 41 * A P M * Real.log (A P M) := by
  filter_upwards [eventually_A_ge P 2, (tendsto_logA P).eventually_ge_atTop 1,
    eventually_hof_ge P, eventually_gt_atTop 0] with M hA hL hh hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hL0 : 0 < Real.log (A P M) := by linarith
  have hh0 : (0 : ℝ) < hof P M := lt_of_lt_of_le (by positivity) hh
  have hK := Kof_le P M (by linarith)
  have h1 : (Kof P M : ℝ) / hof P M ≤ 40 * A P M * Real.log (A P M) := by
    rw [div_le_iff₀ hh0]
    calc (Kof P M : ℝ) ≤ A P M * M := hK
      _ = 40 * A P M * Real.log (A P M) * (M / (40 * Real.log (A P M))) := by
          field_simp
      _ ≤ 40 * A P M * Real.log (A P M) * hof P M := by gcongr
  have h2 : 1 ≤ A P M * Real.log (A P M) := by nlinarith
  linarith

/-- `J ≤ e^{σM}` and `e^{σM} - 1 < J`. -/
theorem Jof_le (M : ℕ) : (Jof P M : ℝ) ≤ Real.exp (P.sigma * M) :=
  Nat.floor_le (Real.exp_pos _).le

theorem Jof_gt (M : ℕ) : Real.exp (P.sigma * M) - 1 < Jof P M := by
  have := Nat.lt_floor_add_one (Real.exp (P.sigma * M))
  unfold Jof
  linarith

theorem eventually_Jof_pos : ∀ᶠ M : ℕ in atTop, 0 < Jof P M := by
  have hσ : 0 < P.sigma := by
    have := P.sigma_gt
    have := P.beta_pos
    linarith
  refine Eventually.of_forall fun M => ?_
  exact Nat.floor_pos.2 (Real.one_le_exp (mul_nonneg hσ.le (Nat.cast_nonneg _)))

/-- `log L = ψ(M)` (Mathlib `Chebyshev.psi_eq_log_lcmUpto`). -/
theorem log_Lof (M : ℕ) : Real.log (Lof M) = ψ M := by
  rw [Lof, Chebyshev.psi_eq_log_lcmUpto]

theorem dvd_Lof {q M : ℕ} (hq : 0 < q) (hqM : q ≤ M) : q ∣ Lof M :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨hq, hqM⟩)

theorem Lof_pos (M : ℕ) : 0 < Lof M := Nat.lcmUpto_pos M

theorem le_Lof {M : ℕ} (hM : 0 < M) : M ≤ Lof M :=
  Nat.le_of_dvd (Lof_pos M) (dvd_Lof hM le_rfl)

/-- `ν_p(L) = log_p M` (Mathlib `Nat.factorization_lcmUpto`). -/
theorem factorization_Lof (M : ℕ) {p : ℕ} (hp : p.Prime) :
    (Lof M).factorization p = Nat.log p M :=
  Nat.factorization_lcmUpto M hp

end Erdos684
