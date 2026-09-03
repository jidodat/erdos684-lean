import Erdos684Lean.Defs

/-!
# The Legendre–Kummer carry formula and the threshold criterion (paper Lemma 2.1)

* `Erdos684.carry_iff` — the carry condition in Mathlib's form `p^i ≤ k % p^i + (n-k) % p^i`
  is equivalent to `[n]_{p^i} < [k]_{p^i}` (paper, proof of Lemma 2.1).
* `Erdos684.log_uPart_eq_D` — `log u(n,k) = D_n(k)` (paper (6)).
* `Erdos684.lt_fThr_of_forall` — the threshold criterion: if `u(n,k) ≤ n²` for all `1 ≤ k ≤ K`
  then `f(n) > K` (paper (7)).
* `Erdos684.D_split` — the four-range decomposition (paper Section 6).
-/

open Finset Real
open Nat (primesLE)

namespace Erdos684

/-- The carry condition (paper, proof of Lemma 2.1). -/
theorem carry_iff {p n k i : ℕ} (hkn : k ≤ n) (hp : 0 < p ^ i) :
    p ^ i ≤ k % p ^ i + (n - k) % p ^ i ↔ n % p ^ i < k % p ^ i := by
  have h1 : n % p ^ i = (k % p ^ i + (n - k) % p ^ i) % p ^ i := by
    conv_lhs => rw [← Nat.add_sub_of_le hkn]
    exact Nat.add_mod _ _ _
  have hk := Nat.mod_lt k hp
  have hnk := Nat.mod_lt (n - k) hp
  rw [h1]
  generalize k % p ^ i = d at hk ⊢
  generalize (n - k) % p ^ i = e at hnk ⊢
  constructor
  · intro h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h
    by_contra hc
    push Not at hc
    rw [Nat.mod_eq_of_lt hc] at h
    omega

theorem uPart_pos (n k : ℕ) : 0 < uPart n k := by
  unfold uPart
  exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primesLE hp).pos _

/-- Paper (6): `log u(n,k) = Σ_{p ≤ k} Σ_{a ≥ 1} log p · 1{[n]_{p^a} < [k]_{p^a}}`. -/
theorem log_uPart_eq_D {n k : ℕ} (hkn : k ≤ n) : Real.log (uPart n k) = D n k := by
  unfold uPart D
  push_cast
  rw [Real.log_prod (fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero))]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesLE hp
  rw [Real.log_pow,
    Nat.factorization_choose hpp hkn (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n)),
    Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc := carry_iff hkn (pow_pos hpp.pos a)
  by_cases h : n % p ^ a < k % p ^ a
  · simp [h, hc.mpr h]
  · simp [h, mt hc.mp h]

/-- Paper (7): the threshold criterion. -/
theorem lt_fThr_of_forall {n K : ℕ} (h : ∀ k, 1 ≤ k → k ≤ K → uPart n k ≤ n ^ 2) :
    (K : ℕ∞) < fThr n := by
  unfold fThr
  refine lt_of_lt_of_le (b := ((K + 1 : ℕ) : ℕ∞))
    (by exact_mod_cast Nat.lt_succ_self K) (le_sInf ?_)
  rintro _ ⟨k, ⟨hk1, hkn, hlt⟩, rfl⟩
  refine ENat.coe_le_coe.mpr ?_
  by_contra hc
  push Not at hc
  exact absurd hlt (not_lt.mpr (h k hk1 (by omega)))

/-- The four-range decomposition of the carry sum (paper Section 6). -/
theorem D_split {M K n k : ℕ} (hMK : M ≤ K) (hkK : k ≤ K) :
    D n k = D1 M n k + D2 M n k + D3 M K n k + D4 K n k := by
  simp only [D, D1, D2, D3, D4, Dpart]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun a ha => ?_
  have hp2 := Nat.two_le_of_mem_primesLE hp
  have hpk := Nat.le_of_mem_primesLE hp
  have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
  rcases Nat.eq_or_lt_of_le ha1 with rfl | ha2
  · simp only [pow_one, true_and]
    split_ifs <;> first | omega | simp
  · have hpa : p ≤ p ^ a := le_self_pow (by omega) (by omega)
    split_ifs <;> first | omega | simp

end Erdos684
