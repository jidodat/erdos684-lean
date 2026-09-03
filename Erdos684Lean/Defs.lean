import Mathlib

/-!
# Erdős Problem 684 — definitions

Formalization of J. H. Bae, *Unbounded logarithmic limsup in Erdős Problem 684 via
shifted carry scheduling* (arXiv:2604.23784v3).

This file contains all definitions shared by the other files:

* `uPart n k` — the part of `n.choose k` supported on primes `≤ k` (paper (1));
* `fThr n`    — the threshold `f(n) ∈ ℕ∞` (paper (2));
* `PNTHyp`    — the single external analytic input (a prime number theorem with a
  power-of-logarithm error term, de la Vallée Poussin 1899);
* `Params`    — the fixed parameter tuple `(λ, β, c, σ, τ)` of paper (11)–(12);
* the scales `A, K, h, J, L` of paper (13);
* the multiplier integers `n_t = tL - h - 1` and the tail functional `Z(t)` (paper (22)–(23));
* the product-cell code (paper (15)) and its codeword count `CM` (paper (16));
* the carry sum `D n k = log u(n,k)` and its four ranges (paper Section 6).
-/

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

/-! ## The function `f(n)` -/

/-- `u(n,k) = ∏_{p ≤ k} p^{ν_p(C(n,k))}` — paper (1). -/
def uPart (n k : ℕ) : ℕ := ∏ p ∈ primesLE k, p ^ (n.choose k).factorization p

/-- `f(n) = min {1 ≤ k ≤ n : u(n,k) > n^2}`, with `f(n) = ⊤` when the set is empty — paper (2). -/
noncomputable def fThr (n : ℕ) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ n ^ 2 < uPart n k})

/-! ## The external analytic input -/

/-- The prime number theorem with the classical power-of-logarithm remainder term
(de la Vallée Poussin): `θ(x) = x + O(x / log² x)`.  This is the only statement used in the
formalization that is not proved from Mathlib; it is weaker than the exponential remainder
(paper (8)). -/
def PNTHyp : Prop := ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |θ x - x| ≤ C * x / (Real.log x) ^ 2

/-! ## Parameters and scales -/

/-- The fixed parameter tuple of paper (11)–(12). -/
structure Params where
  lam : ℝ
  beta : ℝ
  c : ℝ
  sigma : ℝ
  tau : ℝ
  lam_pos : 0 < lam
  lam_lt_one : lam < 1
  beta_pos : 0 < beta
  c_pos : 0 < c
  c_lt : c < lam * beta
  sigma_gt : 2 * beta < sigma
  tau_lt : tau < sigma - c
  tau_gt : beta + 3 / 20 < 2 * (1 + tau)

variable (P : Params)

/-- `A = c log M / log log M` — paper (13). -/
noncomputable def A (M : ℕ) : ℝ := P.c * Real.log M / Real.log (Real.log M)

/-- `K = ⌊A M⌋` — paper (13). -/
noncomputable def Kof (M : ℕ) : ℕ := ⌊A P M * M⌋₊

/-- `h = ⌊M / (20 log A)⌋` — paper (13). -/
noncomputable def hof (M : ℕ) : ℕ := ⌊(M : ℝ) / (20 * Real.log (A P M))⌋₊

/-- `J = ⌊e^{σM}⌋` — paper (13). -/
noncomputable def Jof (M : ℕ) : ℕ := ⌊Real.exp (P.sigma * M)⌋₊

/-- `L = lcm(1, …, M)` — paper (13). -/
def Lof (M : ℕ) : ℕ := Nat.lcmUpto M

/-- `n_t = tL - h - 1` — paper (22). -/
noncomputable def nOf (M t : ℕ) : ℕ := t * Lof M - hof P M - 1

/-- The primes in `(M, K]`. -/
noncomputable def PMK (M : ℕ) : Finset ℕ := (primesLE (Kof P M)).filter (fun p => M < p)

/-! ## The high-power tail -/

/-- `a_p = min {a ≥ 2 : p^a > K} = log_p K + 1` for primes `p ≤ K` — paper (25). -/
noncomputable def aOf (M p : ℕ) : ℕ := Nat.log p (Kof P M) + 1

/-- `ℓ_p(t)` — the number of levels `a ≥ a_p` at which `[n_t]_{p^a} < K` (paper Step 1 of
Lemma 4.1).  By nestedness this is the length of the initial true segment. -/
noncomputable def ell (M t p : ℕ) : ℕ :=
  #{a ∈ Ico (aOf P M p) (nOf P M t + 1) | nOf P M t % p ^ a < Kof P M}

/-- `Z(t) = Σ_p ℓ_p(t) log p` — paper (23), (26). -/
noncomputable def Z (M t : ℕ) : ℝ := ∑ p ∈ primesLE (Kof P M), (ell P M t p : ℝ) * Real.log p

/-- The bad multipliers `{1 ≤ t ≤ J : Z(t) ≥ βM}`. -/
noncomputable def Bad (M : ℕ) : Finset ℕ := (Icc 1 (Jof P M)).filter (fun t => P.beta * M ≤ Z P M t)

/-! ## The product-cell code -/

/-- The product-cell code — paper (15): `j ↦ (⌊[jL]_p / h⌋)_{M < p ≤ K}`. -/
noncomputable def code (M j : ℕ) : PMK P M → ℕ := fun p => (j * Lof M % (p : ℕ)) / hof P M

/-- The finite set of possible codewords. -/
noncomputable def codeSet (M : ℕ) : Finset (PMK P M → ℕ) :=
  Fintype.piFinset (fun p : PMK P M => range ((p : ℕ) / hof P M + 1))

/-- `C_M = ∏_{M<p≤K} (⌊p/h⌋ + 1) ≥ ∏ ⌈p/h⌉` — paper (16). -/
noncomputable def CM (M : ℕ) : ℕ := ∏ p ∈ PMK P M, (p / hof P M + 1)

/-- The forbidden differences — paper (41). -/
noncomputable def Forb (M : ℕ) : Finset ℕ :=
  (Icc 1 (Jof P M)).filter (fun t => (t : ℝ) ≤ Real.exp (P.tau * M) ∨ P.beta * M ≤ Z P M t)

/-- The selection property of the multiplier `t` — paper (43): `e^{τM} < t ≤ J`, `Z(t) < βM`, and
`‖tL‖_p < h` for every prime `M < p ≤ K` (expressed as `[tL]_p < h ∨ p - h < [tL]_p`). -/
def Selected (M t : ℕ) : Prop :=
  Real.exp (P.tau * M) < t ∧ t ≤ Jof P M ∧ Z P M t < P.beta * M ∧
    ∀ p ∈ PMK P M, t * Lof M % p < hof P M ∨ p - hof P M < t * Lof M % p

/-! ## Carries -/

/-- The carry sum `D_n(k) = Σ_{p ≤ k} Σ_{a ≥ 1} log p · 1{[n]_{p^a} < [k]_{p^a}}` — paper (6),
(46).  Levels `a > n` contribute nothing, so the inner sum is truncated at `n`. -/
noncomputable def D (n k : ℕ) : ℝ :=
  ∑ p ∈ primesLE k, ∑ a ∈ Ico 1 (n + 1), if n % p ^ a < k % p ^ a then Real.log p else 0

/-- The part of `D n k` restricted by a predicate on the level `(p, a)`. -/
noncomputable def Dpart (n k : ℕ) (cond : ℕ → ℕ → Prop) [∀ p a, Decidable (cond p a)] : ℝ :=
  ∑ p ∈ primesLE k, ∑ a ∈ Ico 1 (n + 1),
    if n % p ^ a < k % p ^ a ∧ cond p a then Real.log p else 0

/-- Range (I): `p^a ≤ M`. -/
noncomputable def D1 (M n k : ℕ) : ℝ := Dpart n k (fun p a => p ^ a ≤ M)

/-- Range (II): `a = 1` and `M < p`. -/
noncomputable def D2 (M n k : ℕ) : ℝ := Dpart n k (fun p a => a = 1 ∧ M < p)

/-- Range (III): `a ≥ 2` and `M < p^a ≤ K`. -/
noncomputable def D3 (M K n k : ℕ) : ℝ := Dpart n k (fun p a => 2 ≤ a ∧ M < p ^ a ∧ p ^ a ≤ K)

/-- Range (IV): `p^a > K`. -/
noncomputable def D4 (K n k : ℕ) : ℝ := Dpart n k (fun p a => K < p ^ a)

end Erdos684
