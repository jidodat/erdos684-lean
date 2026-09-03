/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
import Erdos684Lean

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved.  The definitions `u` and `f` are repeated verbatim so
that they are the same declarations as in the Challenge; they are definitionally equal to
`Erdos684.uPart` and `Erdos684.fThr` of the development library, and each theorem is a thin bridge
to the corresponding theorem of that library:

* `u_mul_eq_choose`   ← `Erdos684.uPart_mul_eq_choose`   (`Sanity.lean`)
* `lt_f_iff`          ← `Erdos684.lt_fThr_iff`           (`Sanity.lean`)
* `main_theorem`      ← `Erdos684.main_theorem_unconditional` (`MainUnconditional.lean`)
* `main_theorem_limsup` ← `Erdos684.main_theorem_limsup` (`Sanity.lean`)
* `unbounded`         ← `Erdos684.unbounded_unconditional` (`MainUnconditional.lean`)
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

theorem u_eq : u = Erdos684.uPart := rfl

theorem f_eq : f = Erdos684.fThr := rfl

/-- `u(n,k)` is exactly the part of `C(n,k)` supported on primes `≤ k`. -/
theorem u_mul_eq_choose {n k : ℕ} (hkn : k ≤ n) :
    u n k * ∏ p ∈ (n.choose k).primeFactors.filter (fun p => k < p),
      p ^ (n.choose k).factorization p = n.choose k := by
  rw [u_eq]; exact Erdos684.uPart_mul_eq_choose hkn

/-- `K < f(n)` holds exactly when `u(n,k) ≤ n²` for every `1 ≤ k ≤ min(K, n)`. -/
theorem lt_f_iff {n K : ℕ} :
    (K : ℕ∞) < f n ↔ ∀ k, 1 ≤ k → k ≤ K → k ≤ n → u n k ≤ n ^ 2 := by
  rw [f_eq, u_eq]; exact Erdos684.lt_fThr_iff

/-- **Theorem 1.2 of the paper** (infinitely-often form). -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
          Real.log (Real.log (Real.log n)) →
        (k : ℕ∞) < f n := by
  rw [f_eq]; exact Erdos684.main_theorem_unconditional ε hε

/-- **Theorem 1.2 of the paper**, `limsup` form (paper (4)). -/
theorem main_theorem_limsup :
    (1 / 2 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (f n : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  rw [f_eq]; exact Erdos684.main_theorem_limsup

/-- **Paper (5)**: `f(n)/log n` is unbounded. -/
theorem unbounded (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ C * Real.log n → (k : ℕ∞) < f n := by
  rw [f_eq]; exact Erdos684.unbounded_unconditional C

end Erdos684.Palomar
