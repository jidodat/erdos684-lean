import Erdos684Lean.Defs

/-!
# The product-cell code: discrete facts (paper Section 3 and (45))

* `code_mem_codeSet`, `card_codeSet` — the code takes values in a set of size `CM`.
* `equal_cell` — paper Lemma 3.2: equal cells give `‖tL‖_p < h`.
* `fold` — paper (45): the affine fold `[n]_p = p - 1 - d_p` with `1 ≤ d_p ≤ 2h - 1`.
-/

open Finset

namespace Erdos684

variable (P : Params)

theorem code_mem_codeSet (M j : ℕ) : code P M j ∈ codeSet P M := by
  rw [codeSet, Fintype.mem_piFinset]
  intro p
  have hp : 0 < (p : ℕ) := by
    have hmem : (p : ℕ) ∈ (Nat.primesLE (Kof P M)).filter (fun p => M < p) := p.2
    have := (Finset.mem_filter.mp hmem).2
    omega
  rw [Finset.mem_range, Nat.lt_succ_iff]
  change (j * Lof M % (p : ℕ)) / hof P M ≤ (p : ℕ) / hof P M
  exact Nat.div_le_div_right (Nat.mod_lt _ hp).le

theorem card_codeSet (M : ℕ) : (codeSet P M).card = CM P M := by
  rw [codeSet, Fintype.card_piFinset, CM]
  simp only [Finset.card_range]
  exact Finset.prod_coe_sort (PMK P M) (fun p => p / hof P M + 1)

/-- Paper Lemma 3.2 (equal-cell difference), in `ℕ`-residue form.  For `0 < h`, `2h < p`, if
`i < j` lie in the same cell modulo `p` then the residue of `(j - i) L` lies in
`[0,h) ∪ (p-h, p)`. -/
theorem equal_cell {L p h i j : ℕ} (hh : 0 < h) (hp : 2 * h < p) (hij : i < j)
    (hcell : (i * L % p) / h = (j * L % p) / h) :
    (j - i) * L % p < h ∨ p - h < (j - i) * L % p := by
  have hp0 : 0 < p := by omega
  have hx := Nat.mod_lt (i * L) hp0
  have hy := Nat.mod_lt (j * L) hp0
  have hr := Nat.mod_lt ((j - i) * L) hp0
  -- same cell: the residues differ by less than `h`
  have e1 := Nat.div_add_mod (i * L % p) h
  have e2 := Nat.div_add_mod (j * L % p) h
  have f1 := Nat.mod_lt (i * L % p) hh
  have f2 := Nat.mod_lt (j * L % p) hh
  rw [← hcell] at e2
  -- `(j - i) L + i L = j L`, hence `(r + x) % p = y`
  have hle : i * L ≤ j * L := Nat.mul_le_mul_right L hij.le
  have hsum : (j - i) * L + i * L = j * L := by
    rw [Nat.sub_mul, Nat.sub_add_cancel hle]
  have key : ((j - i) * L % p + i * L % p) % p = j * L % p := by
    rw [← Nat.add_mod, hsum]
  rcases lt_or_ge ((j - i) * L % p + i * L % p) p with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at key
    omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at key
    omega

/-- Paper (45) (the affine fold).  If `‖tL‖_p < h` and `n = tL - h - 1` then
`[n]_p = p - 1 - d` for some `1 ≤ d ≤ 2h - 1`. -/
theorem fold {L p h t : ℕ} (hh : 0 < h) (hp : 2 * h < p) (ht : h + 1 ≤ t * L)
    (hz : t * L % p < h ∨ p - h < t * L % p) :
    ∃ d, 1 ≤ d ∧ d ≤ 2 * h - 1 ∧ (t * L - h - 1) % p = p - 1 - d := by
  have hp0 : 0 < p := by omega
  have hzlt := Nat.mod_lt (t * L) hp0
  obtain ⟨q, hq⟩ : ∃ q, t * L = p * q + t * L % p := ⟨t * L / p, (Nat.div_add_mod _ _).symm⟩
  rcases hz with hlt | hgt
  · -- residue below `h`: borrow one full period
    rcases q with _ | q
    · rw [Nat.mul_zero, Nat.zero_add] at hq
      omega
    · rw [Nat.mul_succ] at hq
      refine ⟨h - t * L % p, by omega, by omega, ?_⟩
      have e2 : t * L - h - 1 = p * q + (p - 1 - (h - t * L % p)) := by omega
      rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · -- residue above `p - h`: no borrow
    refine ⟨p + h - t * L % p, by omega, by omega, ?_⟩
    have e2 : t * L - h - 1 = p * q + (p - 1 - (p + h - t * L % p)) := by omega
    rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- `[n]_q = q - 1 - [h]_q` whenever `q ∣ tL` and `h + 1 ≤ tL` — paper (49). -/
theorem small_residue {L q h t : ℕ} (hq : 0 < q) (hdvd : q ∣ t * L) (ht : h + 1 ≤ t * L) :
    (t * L - h - 1) % q = q - 1 - h % q := by
  obtain ⟨c, hc⟩ := hdvd
  have e := Nat.div_add_mod h q
  have hm := Nat.mod_lt h hq
  -- `c > h / q`, since `q c = tL > h ≥ q (h / q)`
  have hcq : h / q < c := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul_left q hcon
    omega
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + h / q + 1 := ⟨c - h / q - 1, by omega⟩
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hc
  have e2 : t * L - h - 1 = q * c' + (q - 1 - h % q) := by omega
  rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Paper (50): the carry equivalence at levels dividing `L`. -/
theorem carry_identity {L q h t k : ℕ} (hq : 0 < q) (hdvd : q ∣ t * L) (ht : h + 1 ≤ t * L) :
    (t * L - h - 1) % q < k % q ↔ q ≤ h % q + k % q := by
  rw [small_residue hq hdvd ht]
  have := Nat.mod_lt h hq
  have := Nat.mod_lt k hq
  omega

end Erdos684
