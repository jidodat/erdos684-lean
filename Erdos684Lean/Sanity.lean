import Erdos684Lean.MainUnconditional

/-!
# Sanity checks

Machine-checked evidence that the definitions `uPart` and `fThr` of `Erdos684Lean.Defs` are
faithful to the paper and non-degenerate, together with the paper's literal `limsup` form of
Theorem 1.2, (4).

* `uPart_mul_eq_choose` — `u(n,k)` is exactly the part of `C(n,k)` supported on primes `≤ k`:
  multiplying it by the part supported on primes `> k` recovers `C(n,k)`.
* `lt_fThr_iff` — `K < f(n)` iff `u(n,k) ≤ n²` for every `1 ≤ k ≤ min(K, n)` (paper (7), both
  directions).
* `fThr_eq_top_iff` — `f(n) = ∞` iff `u(n,k) ≤ n²` for every `1 ≤ k ≤ n`.
* `main_theorem_limsup` — the paper's (4) as a `limsup` in `ℝ≥0∞`:
  `1/2 ≤ limsup_n f(n) · log log log n / (log n · log log n)`.
-/

open Filter Topology Real
open scoped ENNReal

namespace Erdos684

/-! ## `uPart` is the `≤ k`-smooth part of the binomial coefficient -/

theorem uPart_mul_eq_choose {n k : ℕ} (hkn : k ≤ n) :
    uPart n k * ∏ p ∈ (n.choose k).primeFactors.filter (fun p => k < p),
      p ^ (n.choose k).factorization p = n.choose k := by
  have hne : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  -- the `≤ k` part of the product over `primeFactors` is `uPart n k`
  have h1 : ∏ p ∈ (n.choose k).primeFactors.filter (fun p => p ≤ k),
      p ^ (n.choose k).factorization p = uPart n k := by
    unfold uPart
    apply Finset.prod_subset
    · intro p hp
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.1⟩
    · intro p hp hpn
      have hpk : p ≤ k := Nat.le_of_mem_primesLE hp
      have h0 : (n.choose k).factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        intro hmem
        exact hpn (Finset.mem_filter.mpr ⟨hmem, hpk⟩)
      rw [h0, pow_zero]
  have h2 := Nat.prod_factorization_pow_eq_self hne
  rw [Finsupp.prod, Nat.support_factorization] at h2
  conv_rhs => rw [← h2]
  rw [← Finset.prod_filter_mul_prod_filter_not (n.choose k).primeFactors (fun p => p ≤ k), h1]
  congr 1
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, not_le]

/-! ## The threshold `f(n)` -/

theorem lt_fThr_iff {n K : ℕ} :
    (K : ℕ∞) < fThr n ↔ ∀ k, 1 ≤ k → k ≤ K → k ≤ n → uPart n k ≤ n ^ 2 := by
  constructor
  · intro h k hk1 hkK hkn
    by_contra hc
    push Not at hc
    have hmem : (k : ℕ∞) ∈
        (fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ n ^ 2 < uPart n k} :=
      ⟨k, ⟨hk1, hkn, hc⟩, rfl⟩
    have hle : fThr n ≤ (k : ℕ∞) := sInf_le hmem
    have hKk : (K : ℕ∞) < (k : ℕ∞) := lt_of_lt_of_le h hle
    exact absurd (ENat.coe_lt_coe.mp hKk) (not_lt.mpr hkK)
  · intro h
    unfold fThr
    refine lt_of_lt_of_le (b := ((K + 1 : ℕ) : ℕ∞))
      (by exact_mod_cast Nat.lt_succ_self K) (le_sInf ?_)
    rintro _ ⟨k, ⟨hk1, hkn, hlt⟩, rfl⟩
    refine ENat.coe_le_coe.mpr ?_
    by_contra hc
    push Not at hc
    exact absurd hlt (not_lt.mpr (h k hk1 (by omega) hkn))

theorem fThr_eq_top_iff (n : ℕ) :
    fThr n = ⊤ ↔ ∀ k, 1 ≤ k → k ≤ n → uPart n k ≤ n ^ 2 := by
  unfold fThr
  rw [sInf_eq_top]
  constructor
  · intro h k hk1 hkn
    by_contra hc
    push Not at hc
    exact ENat.coe_ne_top k (h _ ⟨k, ⟨hk1, hkn, hc⟩, rfl⟩)
  · rintro h _ ⟨k, ⟨hk1, hkn, hlt⟩, rfl⟩
    exact absurd hlt (not_lt.mpr (h k hk1 hkn))

/-! ## The `limsup` form of paper (4) -/

/-- The normalized threshold `f(n) · log log log n / (log n · log log n)` in `ℝ≥0∞`. -/
noncomputable def normThr (n : ℕ) : ℝ≥0∞ :=
  (fThr n : ℝ≥0∞) *
    ENNReal.ofReal (Real.log (Real.log (Real.log n)) / (Real.log n * Real.log (Real.log n)))

/-- For every `0 < ε < 1/2`, `1/2 − ε ≤ limsup_n normThr n`. -/
theorem ofReal_le_limsup_normThr (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ENNReal.ofReal (1 / 2 - ε) ≤ limsup normThr atTop := by
  apply le_limsup_of_frequently_le'
  -- eventually all three iterated logarithms are positive
  have hl : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hl
  have hlll : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hll
  have hev : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ∧ 0 < Real.log (Real.log n) ∧
      0 < Real.log (Real.log (Real.log n)) :=
    (hl.eventually_gt_atTop 0).and ((hll.eventually_gt_atTop 0).and (hlll.eventually_gt_atTop 0))
  refine ((main_theorem_unconditional ε hε).and_eventually hev).mono ?_
  rintro n ⟨hP, hl0, hll0, hlll0⟩
  set l := Real.log n with hl_def
  set ll := Real.log (Real.log n) with hll_def
  set lll := Real.log (Real.log (Real.log n)) with hlll_def
  have hhalf : 0 < 1 / 2 - ε := by linarith
  set Y : ℝ := (1 / 2 - ε) * l * ll / lll with hY_def
  have hY : 0 < Y := by positivity
  -- the floor of `Y` is below the threshold
  have hk : (⌊Y⌋₊ : ℕ∞) < fThr n := hP ⌊Y⌋₊ (Nat.floor_le hY.le)
  have hk1 : ((⌊Y⌋₊ + 1 : ℕ) : ℕ∞) ≤ fThr n := by
    push_cast
    exact (ENat.add_one_le_iff (ENat.coe_ne_top _)).mpr hk
  have hk2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤ (fThr n : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr hk1
  have hY1 : ENNReal.ofReal Y ≤ (fThr n : ℝ≥0∞) := by
    refine le_trans ?_ hk2
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact (Nat.lt_floor_add_one Y).le)
  -- `Y · (lll / (l · ll)) = 1/2 − ε`
  have hprod : Y * (lll / (l * ll)) = 1 / 2 - ε := by
    rw [hY_def]
    field_simp
  unfold normThr
  calc ENNReal.ofReal (1 / 2 - ε)
      = ENNReal.ofReal Y * ENNReal.ofReal (lll / (l * ll)) := by
        rw [← ENNReal.ofReal_mul hY.le, hprod]
    _ ≤ (fThr n : ℝ≥0∞) * ENNReal.ofReal (lll / (l * ll)) := by gcongr

/-- Paper Theorem 1.2, (4), in its literal `limsup` form:
`limsup_{n→∞} f(n) · log log log n / (log n · log log n) ≥ 1/2`, with `f(n) ∈ ℕ∞` coerced to
`ℝ≥0∞` (so `f(n) = ∞` contributes `∞`). -/
theorem main_theorem_limsup :
    (1 / 2 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (fThr n : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  change (1 / 2 : ℝ≥0∞) ≤ limsup normThr atTop
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  set δ : ℝ := min (ε : ℝ) (1 / 4) with hδ_def
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ2 : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ (ε : ℝ) := min_le_left _ _
  calc (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    _ ≤ ENNReal.ofReal (1 / 2 - δ) + ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) ε.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (1 / 2 - δ) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ limsup normThr atTop + ε := by
        have := ofReal_le_limsup_normThr δ hδ0 hδ2
        gcongr

end Erdos684

#print axioms Erdos684.main_theorem_limsup
