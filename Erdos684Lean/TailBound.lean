import Erdos684Lean.TailCount

/-!
# The high-power tail, exponential estimate (paper Lemma 4.1, Steps 3–4)

* `log_Qr_le` — paper (32)–(34): `log Q(r) ≤ 2 W(r) + (ψ(K) - θ(K))`.
* `tail_bound` — paper (24): `#{1 ≤ t ≤ J : Z(t) ≥ βM} ≤ 2J exp(-λβM + o(M))`.
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-- Paper (33): the overhead identity.  For `M < K < M²`,
`Σ_{p ≤ M} (a_p - 1 - b_p) log p = (ψ(K) - θ(K)) - (ψ(M) - θ(M))`. -/
theorem overhead_identity {M : ℕ} (hMK : M < Kof P M) (hK : Kof P M < M ^ 2) :
    ∑ p ∈ primesLE M, ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p
      = (ψ (Kof P M) - θ (Kof P M)) - (ψ M - θ M) := by
  rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hsub : primesLE M ⊆ primesLE (Kof P M) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hMK.le, hp.2⟩
  have hKM : ∑ p ∈ primesLE (Kof P M),
        ((Nat.log p (Kof P M) : ℝ) * Real.log p - Real.log p)
      = ∑ p ∈ primesLE M, ((Nat.log p (Kof P M) : ℝ) * Real.log p - Real.log p) := by
    symm
    apply Finset.sum_subset hsub
    intro p hpK hpM
    rw [Nat.mem_primesLE] at hpK hpM
    have hMp : M < p := not_le.mp (fun h => hpM ⟨h, hpK.2⟩)
    have h1 : Nat.log p (Kof P M) = 1 := by
      rw [Nat.log_eq_one_iff']
      refine ⟨hpK.1, ?_⟩
      calc Kof P M < M ^ 2 := hK
        _ ≤ p * p := by nlinarith
    rw [h1]
    simp
  rw [hKM, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hle : Nat.log p M ≤ Nat.log p (Kof P M) := Nat.log_mono_right hMK.le
  have h : aOf P M p - 1 - Nat.log p M = Nat.log p (Kof P M) - Nat.log p M := by
    unfold aOf; omega
  rw [h, Nat.cast_sub hle]
  ring

/-- Paper (34): `log Q(r) ≤ 2 W(r) + (ψ(K) - θ(K))` for every profile supported on primes
`≤ K`. -/
theorem log_Qr_le {M : ℕ} (hMK : M < Kof P M) (hK : Kof P M < M ^ 2) (r : ℕ → ℕ) :
    Real.log (Qr P M r) ≤ 2 * Wr P M r + (ψ (Kof P M) - θ (Kof P M)) := by
  have hsupp : ∀ p ∈ supp P M r, p.Prime ∧ p ≤ Kof P M ∧ 0 < r p := by
    intro p hp
    simp only [supp, Finset.mem_filter, Nat.mem_primesLE] at hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  -- `log Q(r) = Σ_{supp} (a_p + r_p - 1 - b_p) log p`
  have hlog : Real.log (Qr P M r) =
      ∑ p ∈ supp P M r, ((aOf P M p + r p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p := by
    unfold Qr
    push_cast
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p _
      unfold Qp
      push_cast
      rw [Real.log_pow]
    · intro p hp
      unfold Qp
      have := (hsupp p hp).1.pos
      positivity
  have hb : ∀ p ∈ supp P M r, Nat.log p M + 1 ≤ aOf P M p := by
    intro p _
    unfold aOf
    have := Nat.log_mono_right (b := p) hMK.le
    omega
  have hsplit : ∀ p ∈ supp P M r,
      ((aOf P M p + r p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p =
        (r p : ℝ) * Real.log p + ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have := hb p hp
    have h : aOf P M p + r p - 1 - Nat.log p M = r p + (aOf P M p - 1 - Nat.log p M) := by
      omega
    rw [h, Nat.cast_add, add_mul]
  rw [hlog, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the first sum is `W(r)`
  have hW : ∑ p ∈ supp P M r, (r p : ℝ) * Real.log p = Wr P M r := by
    unfold Wr supp
    apply Finset.sum_filter_of_ne
    intro p _ hne
    rcases Nat.eq_zero_or_pos (r p) with h | h
    · simp [h] at hne
    · exact h
  -- the overhead sum
  have hover : ∑ p ∈ supp P M r, ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p
      ≤ Wr P M r + (ψ (Kof P M) - θ (Kof P M)) := by
    calc ∑ p ∈ supp P M r, ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p
        ≤ ∑ p ∈ supp P M r,
            ((if p ≤ M then ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p else 0)
              + (r p : ℝ) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpK, hrp⟩ := hsupp p hp
          have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          split_ifs with hpM
          · have : 0 ≤ (r p : ℝ) * Real.log p := by positivity
            linarith
          · have hMp : M < p := not_le.mp hpM
            have h0 : Nat.log p M = 0 := Nat.log_of_lt hMp
            have h1 : Nat.log p (Kof P M) = 1 := by
              rw [Nat.log_eq_one_iff']
              refine ⟨hpK, ?_⟩
              calc Kof P M < M ^ 2 := hK
                _ ≤ p * p := by nlinarith
            have h2 : aOf P M p - 1 - Nat.log p M = 1 := by unfold aOf; omega
            rw [h2]
            have : (1 : ℝ) ≤ r p := by exact_mod_cast hrp
            push_cast
            nlinarith
      _ = ∑ p ∈ (supp P M r).filter (· ≤ M),
            ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p + Wr P M r := by
          rw [Finset.sum_add_distrib, Finset.sum_filter, hW]
      _ ≤ ∑ p ∈ primesLE M, ((aOf P M p - 1 - Nat.log p M : ℕ) : ℝ) * Real.log p
            + Wr P M r := by
          refine add_le_add ?_ le_rfl
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter] at hp
            rw [Nat.mem_primesLE]
            exact ⟨hp.2, (hsupp p hp.1).1⟩
          · intro p _ _
            have := Real.log_natCast_nonneg p
            positivity
      _ = (ψ (Kof P M) - θ (Kof P M)) - (ψ M - θ M) + Wr P M r := by
          rw [overhead_identity P hMK hK]
      _ ≤ Wr P M r + (ψ (Kof P M) - θ (Kof P M)) := by
          have := Chebyshev.theta_le_psi (M : ℝ)
          linarith
  rw [hW]
  linarith

/-! ### The Euler-product error -/

/-- Termwise bound for the Euler-product error: with `c₀ = 1 - 2^{λ-1}`, every summand is at most
`(2/c₀) K^{λ/2}` for `p ≤ √K`, and at most `(2/c₀) K p^{λ-2}` for `p > √K`. -/
private lemma euler_term_le {M p : ℕ} (hp : p.Prime) (hpK : p ≤ Kof P M) :
    2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))
      ≤ (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
        (if p ≤ Nat.sqrt (Kof P M) then (Kof P M : ℝ) ^ (P.lam / 2)
          else (Kof P M : ℝ) * (p : ℝ) ^ (P.lam - 2)) := by
  have hlam := P.lam_pos
  have hlam1 := P.lam_lt_one
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hK0 : (0 : ℝ) ≤ Kof P M := Nat.cast_nonneg _
  -- `w = 2^{1-λ} > 1`, `2^{λ-1} = w⁻¹`
  have hwpos : (0 : ℝ) < (2 : ℝ) ^ (1 - P.lam) := Real.rpow_pos_of_pos (by norm_num) _
  have hw1 : (1 : ℝ) < (2 : ℝ) ^ (1 - P.lam) := Real.one_lt_rpow (by norm_num) (by linarith)
  have h2inv : (2 : ℝ) ^ (P.lam - 1) = ((2 : ℝ) ^ (1 - P.lam))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  have hc₀pos : 0 < 1 - (2 : ℝ) ^ (P.lam - 1) := by
    rw [h2inv]
    have := inv_lt_one_of_one_lt₀ hw1
    linarith
  -- `u = p^{1-λ}`, `c₀ u ≤ u - 1`
  have hupos : (0 : ℝ) < (p : ℝ) ^ (1 - P.lam) := Real.rpow_pos_of_pos hp0 _
  have hwu : (2 : ℝ) ^ (1 - P.lam) ≤ (p : ℝ) ^ (1 - P.lam) :=
    Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
  have hcu : (1 - (2 : ℝ) ^ (P.lam - 1)) * (p : ℝ) ^ (1 - P.lam) ≤ (p : ℝ) ^ (1 - P.lam) - 1 := by
    rw [h2inv]
    have h1 : 1 ≤ (p : ℝ) ^ (1 - P.lam) / (2 : ℝ) ^ (1 - P.lam) := (one_le_div hwpos).mpr hwu
    rw [div_eq_mul_inv] at h1
    nlinarith
  have hXpos : (0 : ℝ) < (p : ℝ) ^ (aOf P M p - 1) := pow_pos hp0 _
  -- step 1: replace `u - 1` by `c₀ u`
  have h1 : 2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))
      ≤ (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
        ((Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * (p : ℝ) ^ (1 - P.lam))) := by
    rw [show (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
        ((Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * (p : ℝ) ^ (1 - P.lam)))
        = 2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) *
            ((1 - (2 : ℝ) ^ (P.lam - 1)) * (p : ℝ) ^ (1 - P.lam))) by
      field_simp]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hcu hXpos.le
  refine h1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  split_ifs with hpN
  · -- `p ≤ √K`: `K/(X u) < p/u = p^λ ≤ K^{λ/2}`
    have hKX : (Kof P M : ℝ) < (p : ℝ) ^ (aOf P M p - 1) * p := by
      have h := Kof_lt_pow_aOf P (M := M) hp
      have ha : aOf P M p = (aOf P M p - 1) + 1 := by unfold aOf; omega
      rw [ha, pow_succ] at h
      exact_mod_cast h
    have hpu : (p : ℝ) / (p : ℝ) ^ (1 - P.lam) = (p : ℝ) ^ P.lam := by
      have : (p : ℝ) ^ P.lam = (p : ℝ) ^ (1 : ℝ) / (p : ℝ) ^ (1 - P.lam) := by
        rw [← Real.rpow_sub hp0]
        congr 1
        ring
      rw [this, Real.rpow_one]
    have hp2K : ((p : ℝ)) ^ 2 ≤ Kof P M := by exact_mod_cast Nat.le_sqrt'.mp hpN
    calc (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * (p : ℝ) ^ (1 - P.lam))
        ≤ (p : ℝ) ^ (aOf P M p - 1) * p / ((p : ℝ) ^ (aOf P M p - 1) * (p : ℝ) ^ (1 - P.lam)) := by
          gcongr
      _ = (p : ℝ) / (p : ℝ) ^ (1 - P.lam) := by
          field_simp
      _ = (p : ℝ) ^ P.lam := hpu
      _ = ((p : ℝ) ^ (2 : ℝ)) ^ (P.lam / 2) := by
          rw [← Real.rpow_mul hp0.le]
          congr 1
          ring
      _ = ((p : ℝ) ^ 2) ^ (P.lam / 2) := by rw [Real.rpow_two]
      _ ≤ (Kof P M : ℝ) ^ (P.lam / 2) := Real.rpow_le_rpow (by positivity) hp2K (by linarith)
  · -- `p > √K`: `X ≥ p`, so `K/(X u) ≤ K/(p u) = K p^{λ-2}`
    have hpX : (p : ℝ) ≤ (p : ℝ) ^ (aOf P M p - 1) := by
      calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℝ) ^ (aOf P M p - 1) := by
          apply pow_le_pow_right₀ hp1.le
          have := two_le_aOf P (M := M) hp hpK
          omega
    have hpu : (p : ℝ) * (p : ℝ) ^ (1 - P.lam) = (p : ℝ) ^ (2 - P.lam) := by
      rw [show (2 : ℝ) - P.lam = 1 + (1 - P.lam) by ring, Real.rpow_add hp0, Real.rpow_one]
    calc (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * (p : ℝ) ^ (1 - P.lam))
        ≤ (Kof P M : ℝ) / ((p : ℝ) * (p : ℝ) ^ (1 - P.lam)) := by
          apply div_le_div_of_nonneg_left hK0 (by positivity)
          exact mul_le_mul_of_nonneg_right hpX hupos.le
      _ = (Kof P M : ℝ) * (p : ℝ) ^ (P.lam - 2) := by
          rw [hpu, show P.lam - 2 = -(2 - P.lam) by ring, Real.rpow_neg hp0.le, div_eq_mul_inv]

/-- The Euler-product error (paper (38)): for fixed `λ < 1`,
`Σ_{p ≤ K} 2K / (p^{a_p-1} (p^{1-λ} - 1)) ≤ C_λ K^{(1+λ)/2}`. -/
theorem euler_error : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ M : ℕ, 2 ≤ Kof P M →
    ∑ p ∈ primesLE (Kof P M),
      2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))
      ≤ Cl * (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
  have hlam := P.lam_pos
  have hlam1 := P.lam_lt_one
  have hc₀pos : 0 < 1 - (2 : ℝ) ^ (P.lam - 1) := by
    have : (2 : ℝ) ^ (P.lam - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hwpos : (0 : ℝ) < (2 : ℝ) ^ (1 - P.lam) := Real.rpow_pos_of_pos (by norm_num) _
  have h2inv : (2 : ℝ) ^ (P.lam - 1) = ((2 : ℝ) ^ (1 - P.lam))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  have hC₂pos : 0 < (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam) := div_pos hwpos (by linarith)
  refine ⟨2 / (1 - (2 : ℝ) ^ (P.lam - 1)) * (1 + (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam)),
    by positivity, ?_⟩
  intro M hK2
  have hKpos : (0 : ℝ) < Kof P M := by exact_mod_cast (by omega : 0 < Kof P M)
  have hN1 : 1 ≤ Nat.sqrt (Kof P M) := Nat.sqrt_pos.mpr (by omega)
  have hNK : Nat.sqrt (Kof P M) ≤ Kof P M := Nat.sqrt_le_self _
  have hN1r : (1 : ℝ) ≤ Nat.sqrt (Kof P M) := by exact_mod_cast hN1
  have hNr : (Nat.sqrt (Kof P M) : ℝ) ≤ Real.sqrt (Kof P M) := by
    rw [Real.le_sqrt (by positivity) hKpos.le]
    exact_mod_cast Nat.sqrt_le' (Kof P M)
  have hNr2 : Real.sqrt (Kof P M) / 2 ≤ Nat.sqrt (Kof P M) := by
    have h : Kof P M < (2 * Nat.sqrt (Kof P M)) ^ 2 := by
      have := Nat.lt_succ_sqrt' (Kof P M)
      nlinarith
    have h' : Real.sqrt (Kof P M) < 2 * Nat.sqrt (Kof P M) := by
      rw [Real.sqrt_lt' (by positivity)]
      exact_mod_cast h
    linarith
  -- the two partial sums
  have hA : ∑ p ∈ (primesLE (Kof P M)).filter (· ≤ Nat.sqrt (Kof P M)),
      (Kof P M : ℝ) ^ (P.lam / 2) ≤ (Nat.sqrt (Kof P M) : ℝ) * (Kof P M : ℝ) ^ (P.lam / 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hcard : ((primesLE (Kof P M)).filter (· ≤ Nat.sqrt (Kof P M))).card
        ≤ Nat.sqrt (Kof P M) := by
      calc _ ≤ (Finset.Icc 1 (Nat.sqrt (Kof P M))).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.mem_filter, Nat.mem_primesLE] at hp
            rw [Finset.mem_Icc]
            exact ⟨hp.1.2.one_lt.le, hp.2⟩
        _ = Nat.sqrt (Kof P M) := by simp
    exact_mod_cast hcard
  have hB : ∑ p ∈ (primesLE (Kof P M)).filter (fun p => ¬ p ≤ Nat.sqrt (Kof P M)),
      (Kof P M : ℝ) * (p : ℝ) ^ (P.lam - 2)
      ≤ (Kof P M : ℝ) * ((Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1) / (1 - P.lam)) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hKpos.le
    calc ∑ p ∈ (primesLE (Kof P M)).filter (fun p => ¬ p ≤ Nat.sqrt (Kof P M)),
          (p : ℝ) ^ (P.lam - 2)
        ≤ ∑ p ∈ (Finset.Ico (Nat.sqrt (Kof P M)) (Kof P M)).image (fun i : ℕ => i + 1),
            ((p : ℕ) : ℝ) ^ (P.lam - 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter, Nat.mem_primesLE, not_le] at hp
            rw [Finset.mem_image]
            exact ⟨p - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
          · intro p _ _
            positivity
      _ = ∑ i ∈ Finset.Ico (Nat.sqrt (Kof P M)) (Kof P M), ((i + 1 : ℕ) : ℝ) ^ (P.lam - 2) := by
          rw [Finset.sum_image (add_left_injective 1).injOn]
      _ ≤ ∫ x in (Nat.sqrt (Kof P M) : ℝ)..(Kof P M : ℝ), x ^ (P.lam - 2) := by
          apply AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (P.lam - 2)) hNK
          apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
          intro x hx
          simp only [Set.mem_Icc] at hx
          simp only [Set.mem_Ioi]
          linarith
      _ = ((Kof P M : ℝ) ^ (P.lam - 2 + 1) - (Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 2 + 1))
            / (P.lam - 2 + 1) := by
          rw [integral_rpow]
          right
          refine ⟨by intro h; linarith, ?_⟩
          intro h
          rw [Set.mem_uIcc] at h
          rcases h with h | h <;> linarith
      _ ≤ (Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1) / (1 - P.lam) := by
          rw [show P.lam - 2 + 1 = P.lam - 1 by ring]
          have hKr : 0 ≤ (Kof P M : ℝ) ^ (P.lam - 1) := by positivity
          rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - P.lam), div_mul_eq_mul_div,
            div_le_iff_of_neg (by linarith : P.lam - 1 < 0)]
          nlinarith [mul_nonneg hKr (by linarith : (0 : ℝ) ≤ 1 - P.lam)]
  -- the two partial sums bounded by `K^{(1+λ)/2}`
  have hA' : (Nat.sqrt (Kof P M) : ℝ) * (Kof P M : ℝ) ^ (P.lam / 2)
      ≤ (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
    calc (Nat.sqrt (Kof P M) : ℝ) * (Kof P M : ℝ) ^ (P.lam / 2)
        ≤ (Kof P M : ℝ) ^ ((1 : ℝ) / 2) * (Kof P M : ℝ) ^ (P.lam / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rwa [← Real.sqrt_eq_rpow]
      _ = (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
          rw [← Real.rpow_add hKpos]
          congr 1
          ring
  have hB' : (Kof P M : ℝ) * ((Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1) / (1 - P.lam))
      ≤ (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam) * (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
    have hNpow : (Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1)
        ≤ (2 : ℝ) ^ (1 - P.lam) * (Kof P M : ℝ) ^ ((P.lam - 1) / 2) := by
      calc (Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1)
          ≤ (Real.sqrt (Kof P M) / 2) ^ (P.lam - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hNr2 (by linarith)
        _ = (2 : ℝ) ^ (1 - P.lam) * (Kof P M : ℝ) ^ ((P.lam - 1) / 2) := by
            rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hKpos.le, h2inv, div_inv_eq_mul, mul_comm]
            congr 2
            ring
    calc (Kof P M : ℝ) * ((Nat.sqrt (Kof P M) : ℝ) ^ (P.lam - 1) / (1 - P.lam))
        ≤ (Kof P M : ℝ) * (((2 : ℝ) ^ (1 - P.lam) * (Kof P M : ℝ) ^ ((P.lam - 1) / 2))
            / (1 - P.lam)) := by
          gcongr
      _ = (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam) *
            ((Kof P M : ℝ) ^ (1 : ℝ) * (Kof P M : ℝ) ^ ((P.lam - 1) / 2)) := by
          rw [Real.rpow_one]
          ring
      _ = (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam) * (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
          rw [← Real.rpow_add hKpos]
          congr 2
          ring
  calc ∑ p ∈ primesLE (Kof P M),
        2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))
      ≤ ∑ p ∈ primesLE (Kof P M), (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
          (if p ≤ Nat.sqrt (Kof P M) then (Kof P M : ℝ) ^ (P.lam / 2)
            else (Kof P M : ℝ) * (p : ℝ) ^ (P.lam - 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Nat.mem_primesLE] at hp
        exact euler_term_le P hp.2 hp.1
    _ = (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
          (∑ p ∈ (primesLE (Kof P M)).filter (· ≤ Nat.sqrt (Kof P M)),
              (Kof P M : ℝ) ^ (P.lam / 2)
            + ∑ p ∈ (primesLE (Kof P M)).filter (fun p => ¬ p ≤ Nat.sqrt (Kof P M)),
              (Kof P M : ℝ) * (p : ℝ) ^ (P.lam - 2)) := by
        rw [← Finset.mul_sum, Finset.sum_ite]
    _ ≤ (2 / (1 - (2 : ℝ) ^ (P.lam - 1))) *
          ((Kof P M : ℝ) ^ ((1 + P.lam) / 2)
            + (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam) * (Kof P M : ℝ) ^ ((1 + P.lam) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (hA.trans hA') (hB.trans hB')
    _ = 2 / (1 - (2 : ℝ) ^ (P.lam - 1)) * (1 + (2 : ℝ) ^ (1 - P.lam) / (1 - P.lam)) *
          (Kof P M : ℝ) ^ ((1 + P.lam) / 2) := by
        ring

/-! ### The tail bound -/

/-- The per-prime weight `g_p(j)`: `g_p(0) = 1` and `g_p(j) = p^{λj} · 2K / p^{a_p + j - 1}` for
`j ≥ 1`. -/
private noncomputable def Gw (M p j : ℕ) : ℝ :=
  ((p : ℝ) ^ P.lam) ^ j *
    (if 0 < j then 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + j - 1) else 1)

private lemma Gw_nonneg {M p j : ℕ} : 0 ≤ Gw P M p j := by
  unfold Gw
  apply mul_nonneg (by positivity)
  split_ifs <;> positivity

/-- The geometric-series bound (paper (37)):
`Σ_{j ≤ R} g_p(j) ≤ 1 + 2K / (p^{a_p-1} (p^{1-λ} - 1))`. -/
private lemma Gw_sum_le {M p : ℕ} (hp : p.Prime) (R : ℕ) :
    ∑ j ∈ range (R + 1), Gw P M p j ≤
      1 + 2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1)) := by
  have hlam := P.lam_pos
  have hlam1 := P.lam_lt_one
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hK0 : (0 : ℝ) ≤ Kof P M := Nat.cast_nonneg _
  have hv0 : 0 < (p : ℝ) ^ P.lam := Real.rpow_pos_of_pos hp0 _
  have hvp : (p : ℝ) ^ P.lam < p := by
    calc (p : ℝ) ^ P.lam < (p : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hp1 hlam1
      _ = p := Real.rpow_one _
  have hu : (p : ℝ) ^ (1 - P.lam) = p / (p : ℝ) ^ P.lam := by
    rw [Real.rpow_sub hp0, Real.rpow_one]
  have hX0 : (0 : ℝ) < (p : ℝ) ^ (aOf P M p - 1) := pow_pos hp0 _
  have hG : ∀ j : ℕ, Gw P M p (j + 1) =
      2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ P.lam / p) ^ (j + 1) := by
    intro j
    unfold Gw
    rw [if_pos (Nat.succ_pos j)]
    have h : aOf P M p + (j + 1) - 1 = (aOf P M p - 1) + (j + 1) := by unfold aOf; omega
    rw [h, pow_add, div_pow]
    field_simp
    ring
  have hG0 : Gw P M p 0 = 1 := by
    unfold Gw
    simp
  rw [Finset.sum_range_succ', hG0, Finset.sum_congr rfl (fun j _ => hG j), ← Finset.mul_sum]
  have hq0 : 0 ≤ (p : ℝ) ^ P.lam / p := by positivity
  have hq1 : (p : ℝ) ^ P.lam / p < 1 := (div_lt_one hp0).mpr hvp
  have hgeom : ∑ j ∈ range R, ((p : ℝ) ^ P.lam / p) ^ (j + 1)
      ≤ ((p : ℝ) ^ P.lam / p) / (1 - (p : ℝ) ^ P.lam / p) := by
    have h2 : ∑ j ∈ range R, ((p : ℝ) ^ P.lam / p) ^ (j + 1)
        = ∑ i ∈ Finset.Ico 1 (R + 1), ((p : ℝ) ^ P.lam / p) ^ i := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro j _
      rw [add_comm]
    rw [h2]
    simpa using geom_sum_Ico_le_of_lt_one (m := 1) (n := R + 1) hq0 hq1
  have hsub : 0 < 1 - (p : ℝ) ^ P.lam / p := by linarith
  have hpv : 0 < (p : ℝ) - (p : ℝ) ^ P.lam := by linarith
  calc 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p - 1) *
          ∑ j ∈ range R, ((p : ℝ) ^ P.lam / p) ^ (j + 1) + 1
      ≤ 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p - 1) *
          (((p : ℝ) ^ P.lam / p) / (1 - (p : ℝ) ^ P.lam / p)) + 1 := by
        gcongr
    _ = 1 + 2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1)) := by
        rw [hu]
        have e1 : ((p : ℝ) ^ P.lam / p) / (1 - (p : ℝ) ^ P.lam / p)
            = (p : ℝ) ^ P.lam / ((p : ℝ) - (p : ℝ) ^ P.lam) := by
          field_simp
        have e2 : (p : ℝ) / (p : ℝ) ^ P.lam - 1
            = ((p : ℝ) - (p : ℝ) ^ P.lam) / (p : ℝ) ^ P.lam := by
          field_simp
        rw [e1, e2]
        field_simp
        ring

/-- Extension by zero of a function defined on a finset. -/
private def extZero (s : Finset ℕ) (f : ∀ p ∈ s, ℕ) : ℕ → ℕ :=
  fun p => if h : p ∈ s then f p h else 0

/-- Fubini for the product-cell family (paper (37)):
`Σ_{r} ∏_p g_p(r_p) = ∏_p Σ_j g_p(j)` over the box `[0, R]^s`. -/
private lemma sum_pi_prod (s : Finset ℕ) (R : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ f ∈ s.pi (fun _ => range (R + 1)), ∏ p ∈ s, G p (extZero s f p)
      = ∏ p ∈ s, ∑ j ∈ range (R + 1), G p j := by
  rw [Finset.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  conv_lhs => rw [← Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro x _
  simp only [extZero, dif_pos x.2]

/-- Per-profile count, second form: if `Q(r) ≤ J` then
`#depthEvent r ≤ 2J ∏_{p ∈ supp} 2K / p^{a_p + r_p - 1}`. -/
private lemma count_profile' {M : ℕ} (hMK : M < Kof P M) (hhL : hof P M + 1 ≤ Lof M)
    (r : ℕ → ℕ) (hQJ : Qr P M r ≤ Jof P M) :
    ((depthEvent P M r).card : ℝ) ≤ 2 * Jof P M *
      ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1) := by
  have hsupp : ∀ p ∈ supp P M r, p.Prime ∧ p ≤ Kof P M ∧ 0 < r p := by
    intro p hp
    simp only [supp, Finset.mem_filter, Nat.mem_primesLE] at hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  have hQpos : 0 < Qr P M r := by
    unfold Qr
    apply Finset.prod_pos
    intro p hp
    unfold Qp
    exact pow_pos (hsupp p hp).1.pos _
  have hQr : (0 : ℝ) < Qr P M r := by exact_mod_cast hQpos
  have hQJr : (Qr P M r : ℝ) ≤ Jof P M := by exact_mod_cast hQJ
  have hRr : 0 ≤ Rr P M r := by
    unfold Rr
    apply Finset.prod_nonneg
    intro p _
    positivity
  calc ((depthEvent P M r).card : ℝ)
      ≤ Rr P M r * ((Jof P M : ℝ) / Qr P M r + 1) := count_profile P hMK hhL r
    _ ≤ Rr P M r * (2 * Jof P M / Qr P M r) := by
        apply mul_le_mul_of_nonneg_left _ hRr
        have : 1 ≤ (Jof P M : ℝ) / Qr P M r := (one_le_div hQr).mpr hQJr
        rw [mul_div_assoc]
        linarith
    _ = 2 * Jof P M * (Rr P M r / Qr P M r) := by ring
    _ = 2 * Jof P M *
          ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1) := by
        congr 1
        unfold Rr Qr
        push_cast
        rw [← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        unfold gp Qp
        push_cast
        have hb : Nat.log p M ≤ aOf P M p + r p - 1 := by
          unfold aOf
          have := Nat.log_mono_right (b := p) hMK.le
          omega
        rw [div_div, ← pow_add, Nat.add_sub_of_le hb]

/-- Per-profile count, weighted form (paper (36)): if `Q(r) ≤ J` and `W(r) ≥ βM` then
`#depthEvent r ≤ 2J e^{-λβM} ∏_{p ≤ K} g_p(r_p)`. -/
private lemma count_weighted {M : ℕ} (hMK : M < Kof P M) (hhL : hof P M + 1 ≤ Lof M)
    (r : ℕ → ℕ) (hQJ : Qr P M r ≤ Jof P M) (hW : P.beta * M ≤ Wr P M r) :
    ((depthEvent P M r).card : ℝ) ≤ 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
      ∏ p ∈ primesLE (Kof P M), Gw P M p (r p) := by
  have h1 := count_profile' P hMK hhL r hQJ
  have hexp : Real.exp (P.lam * Wr P M r)
      = ∏ p ∈ primesLE (Kof P M), ((p : ℝ) ^ P.lam) ^ (r p) := by
    unfold Wr
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
    congr 1
    ring
  have hge : 1 ≤ Real.exp (-(P.lam * P.beta * M)) * Real.exp (P.lam * Wr P M r) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [P.lam_pos]
  have hprod : ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1)
      = ∏ p ∈ primesLE (Kof P M),
          (if 0 < r p then 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1) else 1) := by
    unfold supp
    rw [Finset.prod_filter]
  have hnn : 0 ≤ ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1) := by
    apply Finset.prod_nonneg
    intro p _
    positivity
  calc ((depthEvent P M r).card : ℝ)
      ≤ 2 * Jof P M * ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1) := h1
    _ ≤ 2 * Jof P M * ((Real.exp (-(P.lam * P.beta * M)) * Real.exp (P.lam * Wr P M r)) *
          ∏ p ∈ supp P M r, 2 * (Kof P M : ℝ) / (p : ℝ) ^ (aOf P M p + r p - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_left hnn hge
    _ = 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
          ∏ p ∈ primesLE (Kof P M), Gw P M p (r p) := by
        rw [hexp, hprod, mul_assoc (Real.exp _), ← Finset.prod_mul_distrib, ← mul_assoc]
        simp only [Gw]

/-- Paper Lemma 4.1 in the form used later: for every `ε > 0`, eventually
`#Bad ≤ 2 J exp((-λβ + ε) M)`. -/
theorem tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      ((Bad P M).card : ℝ) ≤ 2 * Jof P M * Real.exp ((-P.lam * P.beta + ε) * M) := by
  classical
  obtain ⟨Cl, hCl0, hCl⟩ := euler_error P
  have hlam := P.lam_pos
  have hbeta := P.beta_pos
  have hη : 0 < P.sigma - 2 * P.beta := by
    have := P.sigma_gt
    linarith
  -- the eventual facts
  have e1 := eventually_M_lt_Kof P
  have e2 := eventually_Kof_lt_sq P
  have e3 := eventually_hof_pos P
  have e4 := eventually_two_hof_lt P
  have e5 : ∀ᶠ M : ℕ in atTop, 2 ≤ M := eventually_ge_atTop 2
  have e6 : ∀ᶠ M : ℕ in atTop,
      Real.sqrt (Kof P M) * Real.log (Kof P M) / M < (P.sigma - 2 * P.beta) / 8 :=
    (tendsto_order.1 (tendsto_sqrtK_logK_div P)).2 _ (by positivity)
  have e7 : ∀ᶠ M : ℕ in atTop, (Kof P M : ℝ) ^ ((1 + P.lam) / 2) / M < ε / (Cl + 1) :=
    (tendsto_order.1 (tendsto_K_rpow_div P)).2 _ (by positivity)
  have e8 : ∀ᶠ M : ℕ in atTop, 2 * Real.log 2 / (P.sigma - 2 * P.beta) ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with M hMK hK hh h2h hM2 hsq hrp hMη
  -- basic facts about the scales
  have hMpos : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hK2 : 2 ≤ Kof P M := by omega
  have hK1r : (1 : ℝ) ≤ Kof P M := by exact_mod_cast (by omega : 1 ≤ Kof P M)
  have hhL : hof P M + 1 ≤ Lof M := by
    have := le_Lof (M := M) hMpos
    omega
  have hlogK0 : 0 ≤ Real.log (Kof P M) := Real.log_nonneg hK1r
  have hsqrt1 : 1 ≤ Real.sqrt (Kof P M) := Real.one_le_sqrt.mpr hK1r
  have hsqlog : Real.sqrt (Kof P M) * Real.log (Kof P M) ≤ (P.sigma - 2 * P.beta) / 8 * M := by
    rw [div_lt_iff₀ hMr] at hsq
    exact hsq.le
  have hlogK : Real.log (Kof P M) ≤ (P.sigma - 2 * P.beta) / 8 * M := by
    nlinarith
  have hpsi : ψ (Kof P M) - θ (Kof P M) ≤ (P.sigma - 2 * P.beta) / 4 * M := by
    have := Chebyshev.psi_sub_theta_le hK1r
    linarith
  have hlog2 : Real.log 2 ≤ (P.sigma - 2 * P.beta) / 2 * M := by
    rw [div_le_iff₀ hη] at hMη
    linarith
  have heul : Cl * (Kof P M : ℝ) ^ ((1 + P.lam) / 2) ≤ ε * M := by
    rw [div_lt_iff₀ hMr] at hrp
    calc Cl * (Kof P M : ℝ) ^ ((1 + P.lam) / 2) ≤ (Cl + 1) * (ε / (Cl + 1) * M) := by
          apply mul_le_mul (by linarith) hrp.le (by positivity) (by positivity)
      _ = ε * M := by field_simp
  -- `Q(r) ≤ J` for every admissible profile
  have hQJ : ∀ r : ℕ → ℕ, (∀ p, p ∉ primesLE (Kof P M) → r p = 0) →
      Wr P M r < P.beta * M + Real.log (Kof P M) → Qr P M r ≤ Jof P M := by
    intro r hr hWr
    have hlogQ := log_Qr_le P hMK hK r
    have hQpos : 0 < Qr P M r := by
      unfold Qr
      apply Finset.prod_pos
      intro p hp
      unfold Qp
      simp only [supp, Finset.mem_filter, Nat.mem_primesLE] at hp
      exact pow_pos hp.1.2.pos _
    have hQr : (0 : ℝ) < Qr P M r := by exact_mod_cast hQpos
    have h1 : Real.log (Qr P M r) ≤ P.sigma * M - Real.log 2 := by
      linarith
    have h2 : (Qr P M r : ℝ) ≤ Real.exp (P.sigma * M) / 2 := by
      calc (Qr P M r : ℝ) = Real.exp (Real.log (Qr P M r)) := (Real.exp_log hQr).symm
        _ ≤ Real.exp (P.sigma * M - Real.log 2) := Real.exp_le_exp.mpr h1
        _ = Real.exp (P.sigma * M) / 2 := by rw [Real.exp_sub, Real.exp_log two_pos]
    have h3 : (1 : ℝ) ≤ Qr P M r := by exact_mod_cast hQpos
    have h4 := Jof_gt P M
    have : (Qr P M r : ℝ) ≤ Jof P M := by linarith
    exact_mod_cast this
  -- the finite family of profiles
  set R : ℕ := ⌈(P.beta * M + Real.log (Kof P M)) / Real.log 2⌉₊ with hR
  set F : Finset (∀ p ∈ primesLE (Kof P M), ℕ) :=
    (primesLE (Kof P M)).pi (fun _ => range (R + 1)) with hF
  set F' := F.filter (fun f => P.beta * M ≤ Wr P M (extZero (primesLE (Kof P M)) f) ∧
    Wr P M (extZero (primesLE (Kof P M)) f) < P.beta * M + Real.log (Kof P M)) with hF'
  have hw : ∀ p ∈ primesLE (Kof P M), 0 < Real.log p ∧ Real.log p ≤ Real.log (Kof P M) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    exact ⟨Real.log_pos (by exact_mod_cast hp.2.one_lt),
      Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast hp.1)⟩
  have hcover : Bad P M ⊆
      F'.biUnion (fun f => depthEvent P M (extZero (primesLE (Kof P M)) f)) := by
    intro t ht
    simp only [Bad, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨⟨ht1, htJ⟩, hZ⟩ := ht
    obtain ⟨r, hrℓ, hr0, hrT, hrT'⟩ := prefix_profile (primesLE (Kof P M))
      (fun p => Real.log p) (Real.log (Kof P M)) hw (fun p => ell P M t p) (P.beta * M)
      (by positivity) hZ
    have hrR : ∀ p ∈ primesLE (Kof P M), r p < R + 1 := by
      intro p hp
      have hlp := hw p hp
      have hlog2 : Real.log 2 ≤ Real.log p := by
        rw [Nat.mem_primesLE] at hp
        exact Real.log_le_log two_pos (by exact_mod_cast hp.2.two_le)
      have hsingle : (r p : ℝ) * Real.log p
          ≤ ∑ q ∈ primesLE (Kof P M), (r q : ℝ) * Real.log q := by
        apply Finset.single_le_sum (f := fun q => (r q : ℝ) * Real.log q) _ hp
        intro q hq
        have := (hw q hq).1
        positivity
      have hlt : (r p : ℝ) * Real.log 2 < P.beta * M + Real.log (Kof P M) := by
        calc (r p : ℝ) * Real.log 2 ≤ (r p : ℝ) * Real.log p :=
              mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
          _ ≤ _ := hsingle
          _ < _ := hrT'
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlt' : (r p : ℝ) < (P.beta * M + Real.log (Kof P M)) / Real.log 2 := by
        rw [lt_div_iff₀ hlog2pos]
        exact hlt
      have hle : (r p : ℝ) ≤ R := hlt'.le.trans (Nat.le_ceil _)
      have : r p ≤ R := by exact_mod_cast hle
      omega
    have hext : extZero (primesLE (Kof P M)) (fun p _ => r p) = r := by
      funext p
      simp only [extZero]
      split_ifs with hp
      · rfl
      · exact (hr0 p hp).symm
    rw [Finset.mem_biUnion]
    refine ⟨fun p _ => r p, ?_, ?_⟩
    · rw [hF', Finset.mem_filter, hext, hF, Finset.mem_pi]
      refine ⟨fun p hp => ?_, hrT, hrT'⟩
      rw [Finset.mem_range]
      exact hrR p hp
    · rw [hext]
      simp only [depthEvent, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ht1, htJ⟩, fun p _ => hrℓ p⟩
  -- counting
  have hcount : ((Bad P M).card : ℝ)
      ≤ ∑ f ∈ F', ((depthEvent P M (extZero (primesLE (Kof P M)) f)).card : ℝ) := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hterm : ∀ f ∈ F', ((depthEvent P M (extZero (primesLE (Kof P M)) f)).card : ℝ) ≤
      2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
        ∏ p ∈ primesLE (Kof P M), Gw P M p (extZero (primesLE (Kof P M)) f p) := by
    intro f hf
    rw [hF', Finset.mem_filter] at hf
    apply count_weighted P hMK hhL _ _ hf.2.1
    apply hQJ _ _ hf.2.2
    intro p hp
    simp only [extZero, dif_neg hp]
  have hGnn : ∀ f, 0 ≤ 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
      ∏ p ∈ primesLE (Kof P M), Gw P M p (extZero (primesLE (Kof P M)) f p) := by
    intro f
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro p _
    exact Gw_nonneg P
  have hx_nonneg : ∀ p ∈ primesLE (Kof P M),
      0 ≤ 2 * (Kof P M : ℝ) / ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have : 1 ≤ (p : ℝ) ^ (1 - P.lam) :=
      Real.one_le_rpow (by exact_mod_cast hp.2.one_lt.le) (by linarith [P.lam_lt_one])
    apply div_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    linarith
  calc ((Bad P M).card : ℝ)
      ≤ ∑ f ∈ F', ((depthEvent P M (extZero (primesLE (Kof P M)) f)).card : ℝ) := hcount
    _ ≤ ∑ f ∈ F', 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
          ∏ p ∈ primesLE (Kof P M), Gw P M p (extZero (primesLE (Kof P M)) f p) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ f ∈ F, 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
          ∏ p ∈ primesLE (Kof P M), Gw P M p (extZero (primesLE (Kof P M)) f p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun f _ _ => hGnn f)
    _ = 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
          ∏ p ∈ primesLE (Kof P M), ∑ j ∈ range (R + 1), Gw P M p j := by
        rw [← Finset.mul_sum, hF, sum_pi_prod]
    _ ≤ 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) *
          ∏ p ∈ primesLE (Kof P M), (1 + 2 * (Kof P M : ℝ) /
            ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.prod_le_prod
        · intro p _
          apply Finset.sum_nonneg
          intro j _
          exact Gw_nonneg P
        · intro p hp
          exact Gw_sum_le P (Nat.mem_primesLE.mp hp).2 R
    _ ≤ 2 * Jof P M * Real.exp (-(P.lam * P.beta * M)) * Real.exp (ε * M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∏ p ∈ primesLE (Kof P M), (1 + 2 * (Kof P M : ℝ) /
                ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1)))
            ≤ ∏ p ∈ primesLE (Kof P M), Real.exp (2 * (Kof P M : ℝ) /
                ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))) := by
              apply Finset.prod_le_prod
              · intro p hp
                have := hx_nonneg p hp
                linarith
              · intro p _
                linarith [Real.add_one_le_exp (2 * (Kof P M : ℝ) /
                  ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1)))]
          _ = Real.exp (∑ p ∈ primesLE (Kof P M), 2 * (Kof P M : ℝ) /
                ((p : ℝ) ^ (aOf P M p - 1) * ((p : ℝ) ^ (1 - P.lam) - 1))) :=
              (Real.exp_sum _ _).symm
          _ ≤ Real.exp (ε * M) := by
              apply Real.exp_le_exp.mpr
              exact (hCl M hK2).trans heul
    _ = 2 * Jof P M * Real.exp ((-P.lam * P.beta + ε) * M) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end Erdos684
