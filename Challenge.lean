/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
import Mathlib

/-!
# Erdős Problem 684: `f(n)/log n` is unbounded

This is the statement of record for the Palomar submission.  It imports Mathlib only, introduces
the two definitions of the problem, and states the principal results of the paper

> J. H. Bae, *Unbounded logarithmic limsup in Erdős Problem 684 via shifted carry scheduling*,
> arXiv:2604.23784 (v3, September 2026).

## The problem

For `0 ≤ k ≤ n` write `C(n,k) = u·v`, where the only primes dividing `u` lie in `[2,k]` and the
only primes dividing `v` lie in `(k,n]`.  Let `f(n)` be the least `k` with `u > n²`.  Erdős (1979)
asked for bounds on `f(n)`; the question is recorded as
[Problem 684](https://www.erdosproblems.com/684) in Bloom's database.  Mahler's theorem gives
`f(n) → ∞` ineffectively.  Alexeev, Putterman, Sawhney, Sellke and Valiant (arXiv:2603.29961) proved
`f(n) ≪ (log n)²` and exhibited infinitely many `n` with `f(n) ≥ (1/2 − o(1)) log n`.

## The results stated here

* `Erdos684.Palomar.u n k` is the factor `u` above: the product over primes `p ≤ k` of
  `p^{ν_p(C(n,k))}`, with `ν_p` the exponent of `p` (Mathlib's `Nat.factorization`).
* `Erdos684.Palomar.f n` is `f(n)`, as an element of `ℕ∞`: the infimum of the naturals
  `1 ≤ k ≤ n` with `n² < u n k`, and `⊤` (that is, `+∞`) when there is no such `k`.
* `Erdos684.Palomar.lt_f_iff` fixes the meaning of the threshold: `K < f(n)` holds exactly when
  `u(n,k) ≤ n²` for every `1 ≤ k ≤ min(K, n)`.
* `Erdos684.Palomar.u_mul_eq_choose` fixes the meaning of `u`: multiplying `u(n,k)` by the part of
  `C(n,k)` supported on the primes exceeding `k` recovers `C(n,k)`.
* `Erdos684.Palomar.main_theorem` is Theorem 1.2 of the paper in its "infinitely many `n`" form:
  for every `ε > 0` there are arbitrarily large `n` such that every natural
  `k ≤ (1/2 − ε)·log n·log log n / log log log n` satisfies `k < f(n)`; equivalently
  `f(n) > (1/2 − ε) log n · log log n / log log log n` for infinitely many `n`.
* `Erdos684.Palomar.main_theorem_limsup` is the same theorem in the paper's `limsup` form, (4):
  `1/2 ≤ limsup_n f(n)·log log log n /(log n·log log n)`, computed in `ℝ≥0∞` with `f(n) = ⊤`
  allowed.
* `Erdos684.Palomar.unbounded` is the paper's (5): for every real `C` there are arbitrarily large
  `n` with `f(n) > C log n`, i.e. `limsup f(n)/log n = ∞`.

All logarithms are natural.  `∃ᶠ n in atTop, P n` means that `P n` holds for infinitely many `n`.

## What the proof uses

The proofs live in the `Erdos684Lean` library of this repository and are compared against these
statements by Comparator.  They use Mathlib and, for the prime number theorem, the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project
(Kontorovich, Tao et al.): the bound `ψ(x) = x + O(x·exp(−c (log x)^{1/10}))` (`MediumPNT`) together
with Mathlib's `ψ(x) − θ(x) ≤ 2√x log x` yields `θ(x) = x + O(x/log² x)`, the only analytic input of
the paper.  The theorems below therefore carry no hypotheses, and every compared declaration is to
depend on `propext`, `Classical.choice` and `Quot.sound` only.

Nothing here is claimed beyond the paper: the result is a lower bound on the worst-case side of
Erdős's question, the exact order of `f(n)` remains open, and the general upper bound `(log n)²` of
Alexeev et al. is the best known.
-/

open Filter Topology Real
open scoped ENNReal

namespace Erdos684.Palomar

/-- `u(n,k) = ∏_{p ≤ k} p^{ν_p(C(n,k))}`: the factor of `C(n,k)` supported on the primes `≤ k`
(paper (1)). -/
def u (n k : ℕ) : ℕ := ∏ p ∈ Nat.primesLE k, p ^ (n.choose k).factorization p

/-- `f(n) = min {1 ≤ k ≤ n : u(n,k) > n²}` as an element of `ℕ∞`, with `f(n) = ⊤` when the set is
empty (paper (2)). -/
noncomputable def f (n : ℕ) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ n ^ 2 < u n k})

/-- `u(n,k)` is exactly the part of `C(n,k)` supported on primes `≤ k`: multiplying it by the part
supported on primes `> k` recovers `C(n,k)`. -/
theorem u_mul_eq_choose {n k : ℕ} (hkn : k ≤ n) :
    u n k * ∏ p ∈ (n.choose k).primeFactors.filter (fun p => k < p),
      p ^ (n.choose k).factorization p = n.choose k := by
  sorry

/-- `K < f(n)` holds exactly when `u(n,k) ≤ n²` for every `1 ≤ k ≤ min(K, n)`. -/
theorem lt_f_iff {n K : ℕ} :
    (K : ℕ∞) < f n ↔ ∀ k, 1 ≤ k → k ≤ K → k ≤ n → u n k ≤ n ^ 2 := by
  sorry

/-- **Theorem 1.2 of the paper** (infinitely-often form).  For every `ε > 0` there are arbitrarily
large `n` such that `f(n) > (1/2 − ε) · log n · log log n / log log log n`. -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
          Real.log (Real.log (Real.log n)) →
        (k : ℕ∞) < f n := by
  sorry

/-- **Theorem 1.2 of the paper**, `limsup` form (paper (4)):
`limsup_{n→∞} f(n) · log log log n / (log n · log log n) ≥ 1/2`, in `ℝ≥0∞`. -/
theorem main_theorem_limsup :
    (1 / 2 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (f n : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  sorry

/-- **Paper (5)**: `f(n)/log n` is unbounded — for every `C` there are arbitrarily large `n` with
`f(n) > C log n`. -/
theorem unbounded (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ C * Real.log n → (k : ℕ∞) < f n := by
  sorry

end Erdos684.Palomar
