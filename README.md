# Lean 4 formalization of arXiv:2604.23784v3 (Erdős Problem 684) — unconditional version

Formalization of J. H. Bae, *Unbounded logarithmic limsup in Erdős Problem 684 via shifted carry
scheduling* (September 2026), in Lean 4.32.2 + Mathlib, with the prime number theorem supplied by the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project so that the
main theorem carries **no hypothesis at all**.

The proof of the paper is formalized in the twelve files `Defs.lean` … `Main.lean`, where the prime
number theorem enters only as an explicit hypothesis `PNTHyp` (so `Erdos684.main_theorem (hPNT : PNTHyp) …`
is checkable with Mathlib alone).  `PNTHyp` is then *proved*
(`Erdos684.pntHyp`, file `PNT.lean`) from `PrimeNumberTheoremAnd.MediumPNT`
(`ψ(x) = x + O(x·exp(−c (log x)^{1/10}))`, sorry-free, standard axioms only) and Mathlib's
`ψ(x) − θ(x) ≤ 2√x log x`.

## Statement

`Erdos684.main_theorem_unconditional` (in `Erdos684Lean/MainUnconditional.lean`):

```
theorem main_theorem_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1/2 - ε) * log n * log (log n) / log (log (log n)) → (k : ℕ∞) < fThr n
```

and `Erdos684.unbounded_unconditional (C : ℝ) : ∃ᶠ n in atTop, ∀ k, (k:ℝ) ≤ C * log n → (k:ℕ∞) < fThr n`.
The conditional forms remain as `Erdos684.main_theorem (hPNT : PNTHyp) …` (in `Main.lean`):

```
theorem main_theorem (hPNT : PNTHyp) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1/2 - ε) * log n * log (log n) / log (log (log n)) → (k : ℕ∞) < fThr n
```

i.e. for every `ε > 0` there are arbitrarily large `n` with
`f(n) > (1/2 − ε) log n · log log n / log log log n` — this is paper (4) in its equivalent
"infinitely often" form.  `Erdos684.unbounded` is paper (5).

## The prime number theorem input

`PNTHyp : ∃ C, ∀ x ≥ 2, |θ(x) − x| ≤ C x / (log x)²` — the prime number theorem with the classical
power-of-logarithm remainder (de la Vallée Poussin 1899).  This is *weaker* than the exponential
remainder (8) quoted in the paper.  In this project it is a theorem (`Erdos684.pntHyp`), so `#print axioms Erdos684.main_theorem_unconditional`
must list only `propext`, `Classical.choice`, `Quot.sound`.

Everything else (Chebyshev's bound `θ(x) ≤ x log 4`, `ψ − θ ≤ 2√x log x`, `ψ(n) = log lcm(1..n)`,
Kummer's carry formula, CRT) is taken from Mathlib.

## Deviations from the paper (all simplifications, none weakening the result)

1. **Lemma 3.1 (code entropy).**  Only the upper bound `log C_M ≤ (c+o(1))M` is needed.  Instead
   of partial summation we use `log(p/h) ≤ log p · log(K/h)/log K` (monotonicity of
   `x ↦ 1 − log h/log x`), so `Σ_{M<p≤K} log(p/h) ≤ θ(K)·log(K/h)/log K`.  This needs only
   `θ(K) ≤ (1+o(1))K` and `A log A/log M → c`.  The Mertens-type sum (10) is replaced by the crude
   `#{M<p≤K} ≤ θ(K)/log M`.
2. **Cells.**  `C_M` is defined as `∏ (⌊p/h⌋+1) ≥ ∏ ⌈p/h⌉`; same asymptotics.
3. **`a_p`.**  Defined as `log_p K + 1`, which equals `min{a ≥ 2 : p^a > K}` for primes `p ≤ K`.
4. **`ψ − θ`.**  Mathlib's `ψ(x) − θ(x) ≤ 2√x log x` is used in place of `O(√x)`; still `o(M)`.
5. **Step 3 of Lemma 4.1.**  The prefix extraction is an abstract lemma (`prefix_profile`) proved
   by induction on the total depth, with no ordering of the primes.
6. **Lemma 6.2.**  "Active" indices are those `m` with `(k+2h)/m > M`; the PNT error is applied with
   `y ≥ M/2`.

## File map

| File | Paper |
|---|---|
| `Defs.lean` | (1), (2), (11)–(13), (15)–(16), (22)–(23), (41), (46) |
| `Kummer.lean` | Lemma 2.1, four-range split |
| `Anchor.lean` | Lemma 5.1 |
| `Code.lean` | Lemma 3.2, (45), (49)–(50) |
| `Asymptotics.lean`, `AsymptoticsPNT.lean` | (14) and all `o(·)` bookkeeping |
| `Entropy.lean` | Lemma 3.1 |
| `TailCount.lean`, `TailBound.lean` | Lemma 4.1 |
| `Budget.lean` | Section 6 |
| `Select.lean` | (42)–(43) |
| `Main.lean` | Proposition 7.1, Theorem 1.2 (conditional on `PNTHyp`) |
| `PNT.lean` | `PNTHyp` derived from `PrimeNumberTheoremAnd.MediumPNT` |
| `MainUnconditional.lean` | Theorem 1.2 with no hypothesis |
| `Sanity.lean` | faithfulness checks: `u(n,k)`·(cofactor on primes `> k`) = `C(n,k)`, characterizations of `f(n) > K` and `f(n) = ∞`, and the literal `limsup` form (4): `1/2 ≤ limsup (f(n)·logloglog n/(log n·loglog n))` in `ℝ≥0∞` (`main_theorem_limsup`) |

Status (2026-09-03): see the bottom of this file.

Additional deviation: `D_split` (four-range decomposition) carries the hypothesis `M ≤ K`, which
the paper uses implicitly (`M < K`, (14)).

## Build

```
lake exe cache get
lake build
```

The PrimeNumberTheoremAnd dependency (pinned by commit in `lakefile.toml`) is built from source by
`lake build`; its Mathlib oleans come from the Mathlib cache.


## Status (2026-09-03 20:19 KST)

* `lake build` succeeds (8,696 jobs, verified from a clean `.lake/build`); no `sorry`, `axiom` or `native_decide` in `Erdos684Lean/`.
* Axiom sweep over all 83 public theorems of the project: every one depends only on
  `propext`, `Classical.choice`, `Quot.sound`.
* `#print axioms` for `Erdos684.pntHyp`, `Erdos684.main_theorem_unconditional`,
  `Erdos684.unbounded_unconditional` (and the conditional `Erdos684.main_theorem`):
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* Dependency pins: PrimeNumberTheoremAnd commit `a5154676af9aa3095150ee410cdda80555aa0642`
  (2026-08-30), Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` (v4.32.2).
