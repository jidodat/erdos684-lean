import Erdos684Lean.Anchor
import Erdos684Lean.Code
import Erdos684Lean.Entropy
import Erdos684Lean.TailBound

/-!
# Anchored-fibre selection (paper Section 5, (42)–(43))

Combining the code entropy (Lemma 3.1), the tail bound (Lemma 4.1) and the anchored-fibre lemma
(Lemma 5.1) yields, for all large `M`, a multiplier `t` with `e^{τM} < t ≤ J`, `Z(t) < βM`, and
`‖tL‖_p < h` for every prime `M < p ≤ K`.
-/

open Finset Real Filter Topology

namespace Erdos684

variable (P : Params)

/-- `|F_M| ≤ e^{τM} + |Bad|`. -/
theorem card_Forb_le (M : ℕ) :
    ((Forb P M).card : ℝ) ≤ Real.exp (P.tau * M) + (Bad P M).card := by
  set S : Finset ℕ :=
    (Icc 1 (Jof P M)).filter (fun t : ℕ => (t : ℝ) ≤ Real.exp (P.tau * M)) with hS
  have hsub : Forb P M ⊆ S ∪ Bad P M := by
    intro t ht
    simp only [Forb, Finset.mem_filter] at ht
    simp only [hS, Bad, Finset.mem_union, Finset.mem_filter]
    rcases ht.2 with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨ht.1, h⟩
  have hsub2 : S ⊆ Icc 1 ⌊Real.exp (P.tau * M)⌋₊ := by
    intro t ht
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at ht
    rw [Finset.mem_Icc]
    exact ⟨ht.1.1, Nat.le_floor ht.2⟩
  have h1 : (Forb P M).card ≤ ⌊Real.exp (P.tau * M)⌋₊ + (Bad P M).card := by
    calc (Forb P M).card ≤ (S ∪ Bad P M).card := Finset.card_le_card hsub
      _ ≤ S.card + (Bad P M).card := Finset.card_union_le _ _
      _ ≤ (Icc 1 ⌊Real.exp (P.tau * M)⌋₊).card + (Bad P M).card := by
        exact Nat.add_le_add_right (Finset.card_le_card hsub2) _
      _ = ⌊Real.exp (P.tau * M)⌋₊ + (Bad P M).card := by
        rw [Nat.card_Icc]
        simp
  have h2 : ((⌊Real.exp (P.tau * M)⌋₊ : ℕ) : ℝ) ≤ Real.exp (P.tau * M) :=
    Nat.floor_le (Real.exp_pos _).le
  calc ((Forb P M).card : ℝ)
      ≤ ((⌊Real.exp (P.tau * M)⌋₊ + (Bad P M).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (⌊Real.exp (P.tau * M)⌋₊ : ℝ) + (Bad P M).card := by push_cast; ring
    _ ≤ _ := by linarith

/-- Paper (42): `C_M (|F_M| + 1) < J + 1` for all large `M`. -/
theorem eventually_anchor_condition (hPNT : PNTHyp) :
    ∀ᶠ M : ℕ in atTop, CM P M * ((Forb P M).card + 1) < Jof P M + 1 := by
  -- a small margin `δ` with `δ ≤ σ - c - τ`, `δ ≤ λβ - c`, `δ ≤ σ - c`
  obtain ⟨δ, hδpos, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ P.sigma - P.c - P.tau ∧
      δ ≤ P.lam * P.beta - P.c ∧ δ ≤ P.sigma - P.c := by
    refine ⟨min (P.sigma - P.c - P.tau) (min (P.lam * P.beta - P.c) (P.sigma - P.c)), ?_,
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
    have := P.tau_lt
    have := P.c_lt
    have := P.c_pos
    have := P.sigma_gt
    have := P.beta_pos
    have : P.lam * P.beta < P.beta := mul_lt_of_lt_one_left P.beta_pos P.lam_lt_one
    simp only [lt_min_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  set ε : ℝ := δ / 4 with hε
  have hεpos : 0 < ε := by positivity
  have h1 := log_CM_le P hPNT ε hεpos
  have h2 := tail_bound P ε hεpos
  have h3 : ∀ᶠ M : ℕ in atTop, 3 / ε ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (3 / ε)
  filter_upwards [h1, h2, h3] with M hM1 hM2 hM3
  have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- `C_M ≤ e^{(c+ε)M}`
  have hCMpos : 0 < CM P M := Finset.prod_pos fun _ _ => Nat.succ_pos _
  have hCMreal : (CM P M : ℝ) ≤ Real.exp ((P.c + ε) * M) := by
    have hpos : (0 : ℝ) < CM P M := by exact_mod_cast hCMpos
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hM1
  have hF := card_Forb_le P M
  have hJle := Jof_le P M
  have hJgt := Jof_gt P M
  -- `e^{εM} ≥ 4`
  have hexp4 : (4 : ℝ) ≤ Real.exp (ε * M) := by
    have : 3 ≤ ε * M := by
      rw [div_le_iff₀ hεpos] at hM3
      linarith
    linarith [Real.add_one_le_exp (ε * M)]
  have key : (CM P M : ℝ) * ((Forb P M).card + 1) < Jof P M + 1 := by
    have hBad : ((Bad P M).card : ℝ) ≤
        2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M) := by
      calc ((Bad P M).card : ℝ)
          ≤ 2 * Jof P M * Real.exp ((-P.lam * P.beta + ε) * M) := hM2
        _ ≤ 2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M) := by gcongr
    have hForb : ((Forb P M).card : ℝ) + 1 ≤
        Real.exp (P.tau * M) + 2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M)
          + 1 := by linarith
    have hprod : (CM P M : ℝ) * ((Forb P M).card + 1) ≤
        Real.exp ((P.c + ε) * M) *
          (Real.exp (P.tau * M) + 2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M)
            + 1) :=
      mul_le_mul hCMreal hForb (by positivity) (Real.exp_pos _).le
    -- the three terms are each `≤ e^{(σ-ε)M}` (the middle one up to the factor 2)
    have t1 : Real.exp ((P.c + ε) * M) * Real.exp (P.tau * M) ≤ Real.exp ((P.sigma - ε) * M) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : (P.c + ε) * M + P.tau * M = (P.c + ε + P.tau) * M := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hMnn
      linarith
    have t2 : Real.exp ((P.c + ε) * M) *
        (2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M)) ≤
        2 * Real.exp ((P.sigma - ε) * M) := by
      have : Real.exp ((P.c + ε) * M) *
          (2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M)) =
          2 * Real.exp ((P.c + ε) * M + P.sigma * M + (-P.lam * P.beta + ε) * M) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have : (P.c + ε) * M + P.sigma * M + (-P.lam * P.beta + ε) * M =
          (P.c + ε + P.sigma + (-P.lam * P.beta + ε)) * M := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hMnn
      linarith
    have t3 : Real.exp ((P.c + ε) * M) ≤ Real.exp ((P.sigma - ε) * M) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hMnn
      linarith
    have hsum : Real.exp ((P.c + ε) * M) *
        (Real.exp (P.tau * M) + 2 * Real.exp (P.sigma * M) * Real.exp ((-P.lam * P.beta + ε) * M)
          + 1) ≤ 4 * Real.exp ((P.sigma - ε) * M) := by
      rw [mul_add, mul_add, mul_one]
      linarith
    have h4 : 4 * Real.exp ((P.sigma - ε) * M) ≤ Real.exp (P.sigma * M) := by
      calc 4 * Real.exp ((P.sigma - ε) * M)
          ≤ Real.exp (ε * M) * Real.exp ((P.sigma - ε) * M) := by gcongr
        _ = Real.exp (P.sigma * M) := by
          rw [← Real.exp_add]
          congr 1
          ring
    linarith
  exact_mod_cast key

/-- Paper (43): a selected multiplier exists for all large `M`. -/
theorem eventually_selected (hPNT : PNTHyp) : ∀ᶠ M : ℕ in atTop, ∃ t, Selected P M t := by
  filter_upwards [eventually_anchor_condition P hPNT, eventually_hof_pos P,
    eventually_two_hof_lt P, eventually_M_lt_Kof P] with M hcond hh h2h hMK
  obtain ⟨i, j, hij, hjJ, hcode, hnot⟩ := anchor (Jof P M) (code P M) (codeSet P M)
    (fun j _ => code_mem_codeSet P M j) (Forb P M) (by rw [card_codeSet]; exact hcond)
  refine ⟨j - i, ?_⟩
  have hmem : j - i ∈ Icc 1 (Jof P M) := by
    rw [Finset.mem_Icc]
    omega
  have hnot' : ¬ (((j - i : ℕ) : ℝ) ≤ Real.exp (P.tau * M) ∨ P.beta * M ≤ Z P M (j - i)) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hmem, h⟩)
  push Not at hnot'
  refine ⟨hnot'.1, by omega, hnot'.2, ?_⟩
  intro p hp
  have hpM : M < p := (Finset.mem_filter.mp hp).2
  have hcell : (i * Lof M % p) / hof P M = (j * Lof M % p) / hof P M := by
    have := congrFun hcode ⟨p, hp⟩
    simpa only [code] using this
  exact equal_cell hh (by omega) hij hcell

end Erdos684
