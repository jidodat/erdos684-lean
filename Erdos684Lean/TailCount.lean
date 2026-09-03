import Erdos684Lean.Asymptotics

/-!
# The high-power tail, discrete part (paper Lemma 4.1, Steps 1–3)

* `ell_ge_imp` — nestedness (Step 1): `ℓ_p(t) ≥ r ≥ 1` forces `[n_t]_{p^{a_p+r-1}} < K`.
* `Qp` — the reduced modulus `Q_p(r) = p^{a_p + r - 1 - b_p}` (paper (28)).
* `prefix_profile` — the greedy prefix extraction of Step 3 (paper (31)), in the form of an
  abstract lemma about finitely supported profiles.
* `count_profile` — the CRT count (paper (30)):
  `#{1 ≤ t ≤ J : ℓ_p(t) ≥ r_p ∀p} ≤ R(r) (J/Q(r) + 1)`.
-/

open Finset Real
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-- `Q_p(r) = p^{a_p + r - 1 - b_p}` with `b_p = log_p M` — paper (28). -/
noncomputable def Qp (M p r : ℕ) : ℕ := p ^ (aOf P M p + r - 1 - Nat.log p M)

/-- `g_p = p^{b_p} = p^{ν_p(L)}`. -/
noncomputable def gp (M p : ℕ) : ℕ := p ^ Nat.log p M

/-- The support of a profile inside the primes `≤ K`. -/
noncomputable def supp (M : ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  (primesLE (Kof P M)).filter (fun p => 0 < r p)

/-- `R(r) = ∏_{r_p > 0} 2K / g_p` — paper (29). -/
noncomputable def Rr (M : ℕ) (r : ℕ → ℕ) : ℝ := ∏ p ∈ supp P M r, (2 * (Kof P M : ℝ) / gp M p)

/-- `Q(r) = ∏_{r_p > 0} Q_p(r_p)` — paper (29). -/
noncomputable def Qr (M : ℕ) (r : ℕ → ℕ) : ℕ := ∏ p ∈ supp P M r, Qp P M p (r p)

/-- `W(r) = Σ_p r_p log p` — paper (29). -/
noncomputable def Wr (M : ℕ) (r : ℕ → ℕ) : ℝ := ∑ p ∈ primesLE (Kof P M), (r p : ℝ) * Real.log p

/-- The depth event `{1 ≤ t ≤ J : ℓ_p(t) ≥ r_p for every p}`. -/
noncomputable def depthEvent (M : ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  (Icc 1 (Jof P M)).filter (fun t => ∀ p ∈ primesLE (Kof P M), r p ≤ ell P M t p)

/-- `p^{a_p} > K`. -/
theorem Kof_lt_pow_aOf {M p : ℕ} (hp : p.Prime) : Kof P M < p ^ aOf P M p := by
  unfold aOf
  exact Nat.lt_pow_succ_log_self hp.one_lt (Kof P M)

/-- `a_p ≥ 2`. -/
theorem two_le_aOf {M p : ℕ} (hp : p.Prime) (hpK : p ≤ Kof P M) : 2 ≤ aOf P M p := by
  unfold aOf
  have := Nat.log_pos hp.one_lt hpK
  omega

/-- `a_p - 1 = log_p K`. -/
theorem aOf_sub_one (M p : ℕ) : aOf P M p - 1 = Nat.log p (Kof P M) := by
  unfold aOf
  omega

/-- Nestedness (paper Step 1): if `ℓ_p(t) ≥ r ≥ 1` then `[n_t]_{p^{a_p+r-1}} < K`. -/
theorem ell_ge_imp {M t p r : ℕ} (hr : 1 ≤ r) (hℓ : r ≤ ell P M t p) :
    nOf P M t % p ^ (aOf P M p + r - 1) < Kof P M := by
  by_contra hcon
  push Not at hcon
  have hsub : {a ∈ Ico (aOf P M p) (nOf P M t + 1) | nOf P M t % p ^ a < Kof P M} ⊆
      Ico (aOf P M p) (aOf P M p + r - 1) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Ico] at ha
    rw [Finset.mem_Ico]
    refine ⟨ha.1.1, ?_⟩
    by_contra hge
    push Not at hge
    have hdvd : p ^ (aOf P M p + r - 1) ∣ p ^ a := Nat.pow_dvd_pow p hge
    have h1 : nOf P M t % p ^ a % p ^ (aOf P M p + r - 1) = nOf P M t % p ^ (aOf P M p + r - 1) :=
      Nat.mod_mod_of_dvd _ hdvd
    have h2 : nOf P M t % p ^ a % p ^ (aOf P M p + r - 1) ≤ nOf P M t % p ^ a := Nat.mod_le _ _
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  unfold ell at hℓ
  omega

/-- `Z(t) = W(ℓ(t))`. -/
theorem Z_eq_Wr (M t : ℕ) : Z P M t = Wr P M (fun p => ell P M t p) := rfl

/-- The greedy prefix extraction (paper Step 3): from a profile `ℓ` of weight `≥ T > 0` extract a
sub-profile `r ≤ ℓ` with `T ≤ W(r) < T + w_max`, where `w_max` bounds every weight. -/
theorem prefix_profile (s : Finset ℕ) (w : ℕ → ℝ) (wmax : ℝ) (hw : ∀ p ∈ s, 0 < w p ∧ w p ≤ wmax)
    (ℓ : ℕ → ℕ) (T : ℝ) (hT : 0 < T) (hℓ : T ≤ ∑ p ∈ s, (ℓ p : ℝ) * w p) :
    ∃ r : ℕ → ℕ, (∀ p, r p ≤ ℓ p) ∧ (∀ p, p ∉ s → r p = 0) ∧
      T ≤ ∑ p ∈ s, (r p : ℝ) * w p ∧ ∑ p ∈ s, (r p : ℝ) * w p < T + wmax := by
  classical
  suffices H : ∀ N : ℕ, ∀ ℓ : ℕ → ℕ, ∑ p ∈ s, ℓ p = N → T ≤ ∑ p ∈ s, (ℓ p : ℝ) * w p →
      ∃ r : ℕ → ℕ, (∀ p, r p ≤ ℓ p) ∧ (∀ p, p ∉ s → r p = 0) ∧
        T ≤ ∑ p ∈ s, (r p : ℝ) * w p ∧ ∑ p ∈ s, (r p : ℝ) * w p < T + wmax from
    H _ ℓ rfl hℓ
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih ℓ hN hℓ
  by_cases hlt : ∑ p ∈ s, (ℓ p : ℝ) * w p < T + wmax
  · refine ⟨fun p => if p ∈ s then ℓ p else 0, ?_, ?_, ?_, ?_⟩
    · intro p
      dsimp only
      split_ifs <;> omega
    · intro p hp
      simp [hp]
    · exact hℓ.trans_eq (Finset.sum_congr rfl (fun p hp => by simp [hp])).symm
    · exact (Finset.sum_congr rfl (fun p hp => by simp [hp])).trans_lt hlt
  · push Not at hlt
    have hex : ∃ p₀ ∈ s, 0 < ℓ p₀ := by
      by_contra hno
      push Not at hno
      have hzero : ∑ p ∈ s, (ℓ p : ℝ) * w p = 0 :=
        Finset.sum_eq_zero (fun p hp => by simp [Nat.le_zero.mp (hno p hp)])
      linarith
    obtain ⟨p₀, hp₀, hℓp₀⟩ := hex
    obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : ℕ → ℕ, ℓ' = Function.update ℓ p₀ (ℓ p₀ - 1) := ⟨_, rfl⟩
    have hℓ'p₀ : ℓ' p₀ = ℓ p₀ - 1 := by
      rw [hℓ']
      exact Function.update_self _ _ _
    have hℓ'ne : ∀ p, p ≠ p₀ → ℓ' p = ℓ p := by
      intro p hp
      rw [hℓ']
      exact Function.update_of_ne hp _ _
    have hℓ'le : ∀ p, ℓ' p ≤ ℓ p := by
      intro p
      by_cases hp : p = p₀
      · subst hp
        rw [hℓ'p₀]
        omega
      · rw [hℓ'ne p hp]
    have e1 : ∑ p ∈ s, ℓ' p = ℓ' p₀ + ∑ p ∈ s.erase p₀, ℓ' p :=
      (Finset.add_sum_erase s ℓ' hp₀).symm
    have e2 : ∑ p ∈ s, ℓ p = ℓ p₀ + ∑ p ∈ s.erase p₀, ℓ p :=
      (Finset.add_sum_erase s ℓ hp₀).symm
    have e3 : ∑ p ∈ s.erase p₀, ℓ' p = ∑ p ∈ s.erase p₀, ℓ p :=
      Finset.sum_congr rfl (fun p hp => hℓ'ne p (Finset.ne_of_mem_erase hp))
    have hsumN : ∑ p ∈ s, ℓ' p < N := by
      rw [← hN, e1, e2, e3, hℓ'p₀]
      omega
    have f1 : ∑ p ∈ s, (ℓ' p : ℝ) * w p =
        (ℓ' p₀ : ℝ) * w p₀ + ∑ p ∈ s.erase p₀, (ℓ' p : ℝ) * w p :=
      (Finset.add_sum_erase s (fun p => (ℓ' p : ℝ) * w p) hp₀).symm
    have f2 : ∑ p ∈ s, (ℓ p : ℝ) * w p =
        (ℓ p₀ : ℝ) * w p₀ + ∑ p ∈ s.erase p₀, (ℓ p : ℝ) * w p :=
      (Finset.add_sum_erase s (fun p => (ℓ p : ℝ) * w p) hp₀).symm
    have f3 : ∑ p ∈ s.erase p₀, (ℓ' p : ℝ) * w p = ∑ p ∈ s.erase p₀, (ℓ p : ℝ) * w p :=
      Finset.sum_congr rfl (fun p hp => by rw [hℓ'ne p (Finset.ne_of_mem_erase hp)])
    have hsumR : ∑ p ∈ s, (ℓ' p : ℝ) * w p = ∑ p ∈ s, (ℓ p : ℝ) * w p - w p₀ := by
      rw [f1, f2, f3, hℓ'p₀, Nat.cast_pred hℓp₀]
      ring
    have hT' : T ≤ ∑ p ∈ s, (ℓ' p : ℝ) * w p := by
      rw [hsumR]
      have := (hw p₀ hp₀).2
      linarith
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := ih _ hsumN ℓ' rfl hT'
    exact ⟨r, fun p => (hr1 p).trans (hℓ'le p), hr2, hr3, hr4⟩

/-- A set of naturals `≤ N` whose pairwise differences are multiples of `Q > 0` has at most
`N / Q + 1` elements. -/
private theorem card_le_div_add_one_of_dvd_sub {A : Finset ℕ} {Q N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N) (hd : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → Q ∣ b - a) :
    A.card ≤ N / Q + 1 := by
  rcases A.eq_empty_or_nonempty with hA0 | hne
  · simp [hA0]
  have ha₀A : A.min' hne ∈ A := Finset.min'_mem A hne
  have hle : ∀ a ∈ A, A.min' hne ≤ a := fun a ha => Finset.min'_le A a ha
  calc A.card ≤ (Finset.range (N / Q + 1)).card := ?_
    _ = N / Q + 1 := Finset.card_range _
  refine Finset.card_le_card_of_injOn (fun a => (a - A.min' hne) / Q) ?_ ?_
  · intro a ha
    rw [Finset.mem_coe] at ha
    rw [Finset.mem_coe, Finset.mem_range]
    change (a - A.min' hne) / Q < N / Q + 1
    have h1 : (a - A.min' hne) / Q ≤ N / Q :=
      Nat.div_le_div_right (by have := hA a ha; omega)
    omega
  · intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only at hab
    have h1 := Nat.div_mul_cancel (hd _ ha₀A a ha (hle a ha))
    have h2 := Nat.div_mul_cancel (hd _ ha₀A b hb (hle b hb))
    rw [hab] at h1
    have h3 : a - A.min' hne = b - A.min' hne := h1.symm.trans h2
    have := hle a ha
    have := hle b hb
    omega

/-- A product of pairwise coprime naturals, each dividing `n`, divides `n`. -/
private theorem prod_dvd_of_pairwise_coprime {ι : Type*} {s : Finset ι}
    {f : ι → ℕ} {n : ℕ} (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ n) : ∏ i ∈ s, f i ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hdvd a (Finset.mem_insert_self a s)) (ih ?_ ?_)
    · rw [Nat.coprime_prod_right_iff]
      intro j hj
      exact hcop a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    · intro i hi j hj hij
      exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · intro i hi
      exact hdvd i (Finset.mem_insert_of_mem hi)

/-- The CRT count (paper (30)).  Requires `M < K` (so that `g_p ≤ M < K` and
`2K/g_p ≥ K/g_p + 1`), and `h + 1 ≤ L` (so that `n_t` is a genuine subtraction for `t ≥ 1`). -/
theorem count_profile {M : ℕ} (hMK : M < Kof P M) (hhL : hof P M + 1 ≤ Lof M) (r : ℕ → ℕ) :
    ((depthEvent P M r).card : ℝ) ≤ Rr P M r * ((Jof P M : ℝ) / Qr P M r + 1) := by
  classical
  -- basic facts about the support
  have hS_mem : ∀ p ∈ supp P M r, p.Prime ∧ p ≤ Kof P M ∧ 0 < r p := by
    intro p hp
    simp only [supp, Finset.mem_filter, Nat.mem_primesLE] at hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  have hb_lt_a : ∀ p ∈ supp P M r, Nat.log p M < aOf P M p := by
    intro p _
    have := Nat.log_mono_right (b := p) hMK.le
    unfold aOf
    omega
  have hg_pos : ∀ p ∈ supp P M r, 0 < gp M p := fun p hp => pow_pos (hS_mem p hp).1.pos _
  have hg_le : ∀ p ∈ supp P M r, gp M p ≤ Kof P M := by
    intro p _
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · have h1 : gp M p = 1 := by simp [gp, hM0]
      omega
    · exact (Nat.pow_log_le_self p hM0.ne').trans hMK.le
  have hg_dvd : ∀ p ∈ supp P M r, gp M p ∣ Lof M := by
    intro p hp
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · have h1 : gp M p = 1 := by simp [gp, hM0]
      rw [h1]
      exact one_dvd _
    · exact dvd_Lof (hg_pos p hp) (Nat.pow_log_le_self p hM0.ne')
  have hq : ∀ p ∈ supp P M r, p ^ (aOf P M p + r p - 1) = gp M p * Qp P M p (r p) := by
    intro p hp
    have hba := hb_lt_a p hp
    have hrp := (hS_mem p hp).2.2
    unfold gp Qp
    rw [← pow_add]
    congr 1
    omega
  have hgq : ∀ p ∈ supp P M r, gp M p ∣ p ^ (aOf P M p + r p - 1) := by
    intro p hp
    rw [hq p hp]
    exact dvd_mul_right _ _
  have hn : ∀ t, 1 ≤ t → nOf P M t + (hof P M + 1) = t * Lof M := by
    intro t ht
    have := Nat.le_mul_of_pos_left (Lof M) ht
    unfold nOf
    omega
  -- the target set
  obtain ⟨Y, hYdef⟩ : ∃ Y : Finset (∀ p ∈ supp P M r, ℕ), Y = (supp P M r).pi (fun p =>
      ((Finset.range (Kof P M)).filter (fun s => gp M p ∣ hof P M + 1 + s)).image
        (fun s => (hof P M + 1 + s) % p ^ (aOf P M p + r p - 1))) := ⟨_, rfl⟩
  -- the map `t ↦ (tL mod q_p)_p` lands in `Y`
  have hmaps : ∀ t ∈ depthEvent P M r,
      (fun p (_ : p ∈ supp P M r) => t * Lof M % p ^ (aOf P M p + r p - 1)) ∈ Y := by
    intro t ht
    rw [depthEvent, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨⟨ht1, _⟩, hell⟩ := ht
    rw [hYdef, Finset.mem_pi]
    intro p hp
    obtain ⟨hpp, hpK, hrp⟩ := hS_mem p hp
    have hℓ : r p ≤ ell P M t p := hell p (Nat.mem_primesLE.mpr ⟨hpK, hpp⟩)
    have hlt := ell_ge_imp P hrp hℓ
    have htL := hn t ht1
    have hsplit := Nat.div_add_mod (nOf P M t) (p ^ (aOf P M p + r p - 1))
    rw [Finset.mem_image]
    refine ⟨nOf P M t % p ^ (aOf P M p + r p - 1), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, ?_⟩
      have e : t * Lof M = p ^ (aOf P M p + r p - 1) * (nOf P M t / p ^ (aOf P M p + r p - 1))
          + (hof P M + 1 + nOf P M t % p ^ (aOf P M p + r p - 1)) := by omega
      have hgL : gp M p ∣ t * Lof M := dvd_mul_of_dvd_right (hg_dvd p hp) t
      rw [e] at hgL
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left (hgq p hp) _)).mp hgL
    · show (hof P M + 1 + nOf P M t % p ^ (aOf P M p + r p - 1)) % p ^ (aOf P M p + r p - 1)
        = t * Lof M % p ^ (aOf P M p + r p - 1)
      have e : t * Lof M = (hof P M + 1 + nOf P M t % p ^ (aOf P M p + r p - 1))
          + p ^ (aOf P M p + r p - 1) * (nOf P M t / p ^ (aOf P M p + r p - 1)) := by omega
      rw [e, Nat.add_mul_mod_self_left]
  -- fibre bound and the count in `ℕ`
  have hmain : (depthEvent P M r).card ≤ (Jof P M / Qr P M r + 1) * Y.card := by
    refine Finset.card_le_mul_card_image_of_maps_to hmaps _ ?_
    intro y _
    refine card_le_div_add_one_of_dvd_sub ?_ ?_
    · intro t ht
      rw [Finset.mem_filter, depthEvent, Finset.mem_filter, Finset.mem_Icc] at ht
      exact ht.1.1.2
    · intro t ht t' ht' _
      rw [Finset.mem_filter] at ht ht'
      have hcong : ∀ p ∈ supp P M r,
          t * Lof M % p ^ (aOf P M p + r p - 1) = t' * Lof M % p ^ (aOf P M p + r p - 1) := by
        intro p hp
        have e1 := congrFun (congrFun ht.2 p) hp
        have e2 := congrFun (congrFun ht'.2 p) hp
        exact e1.trans e2.symm
      unfold Qr
      refine prod_dvd_of_pairwise_coprime ?_ ?_
      · intro p hp p' hp' hne
        exact Nat.coprime_pow_primes _ _ (hS_mem p hp).1 (hS_mem p' hp').1 hne
      · intro p hp
        obtain ⟨hpp, _, _⟩ := hS_mem p hp
        have h1 : p ^ (aOf P M p + r p - 1) ∣ (t' - t) * Lof M := by
          rw [Nat.sub_mul]
          exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (hcong p hp).symm)
        rw [hq p hp] at h1
        have hL' : Lof M = gp M p * (Lof M / gp M p) := by
          have := Nat.ordProj_mul_ordCompl_eq_self (Lof M) p
          rw [factorization_Lof M hpp] at this
          exact this.symm
        rw [hL', mul_left_comm, Nat.mul_dvd_mul_iff_left (hg_pos p hp)] at h1
        have hcop : Nat.Coprime (Qp P M p (r p)) (Lof M / gp M p) := by
          have := Nat.coprime_ordCompl hpp (Lof_pos M).ne'
          rw [factorization_Lof M hpp] at this
          exact Nat.Coprime.pow_left _ this
        exact hcop.dvd_of_dvd_mul_right h1
  -- the size of the target set
  have hY : Y.card ≤ ∏ p ∈ supp P M r, (Kof P M / gp M p + 1) := by
    rw [hYdef, Finset.card_pi]
    apply Finset.prod_le_prod'
    intro p hp
    refine Finset.card_image_le.trans ?_
    refine (card_le_div_add_one_of_dvd_sub (Q := gp M p) (N := Kof P M - 1) ?_ ?_).trans ?_
    · intro s hs
      rw [Finset.mem_filter, Finset.mem_range] at hs
      omega
    · intro s hs s' hs' _
      rw [Finset.mem_filter] at hs hs'
      have := Nat.dvd_sub hs'.2 hs.2
      rwa [Nat.add_sub_add_left] at this
    · have := Nat.div_le_div_right (c := gp M p) (Nat.sub_le (Kof P M) 1)
      omega
  have hcardℕ : (depthEvent P M r).card ≤
      (Jof P M / Qr P M r + 1) * ∏ p ∈ supp P M r, (Kof P M / gp M p + 1) :=
    hmain.trans (Nat.mul_le_mul_left _ hY)
  -- pass to `ℝ`
  have hR : ((∏ p ∈ supp P M r, (Kof P M / gp M p + 1) : ℕ) : ℝ) ≤ Rr P M r := by
    rw [Nat.cast_prod]
    unfold Rr
    apply Finset.prod_le_prod
    · intro p _
      positivity
    · intro p hp
      have h1 : ((Kof P M / gp M p : ℕ) : ℝ) ≤ (Kof P M : ℝ) / gp M p := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ (Kof P M : ℝ) / gp M p := by
        rw [le_div_iff₀ (by exact_mod_cast hg_pos p hp), one_mul]
        exact_mod_cast hg_le p hp
      have h3 : 2 * (Kof P M : ℝ) / gp M p = (Kof P M : ℝ) / gp M p + (Kof P M : ℝ) / gp M p := by
        ring
      push_cast
      linarith
  have hJQ : ((Jof P M / Qr P M r + 1 : ℕ) : ℝ) ≤ (Jof P M : ℝ) / Qr P M r + 1 := by
    have : ((Jof P M / Qr P M r : ℕ) : ℝ) ≤ (Jof P M : ℝ) / Qr P M r := Nat.cast_div_le
    push_cast
    linarith
  calc ((depthEvent P M r).card : ℝ)
      ≤ ((Jof P M / Qr P M r + 1 : ℕ) : ℝ) *
          ((∏ p ∈ supp P M r, (Kof P M / gp M p + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcardℕ
    _ ≤ ((Jof P M : ℝ) / Qr P M r + 1) * Rr P M r :=
        mul_le_mul hJQ hR (by positivity) (by positivity)
    _ = Rr P M r * ((Jof P M : ℝ) / Qr P M r + 1) := mul_comm _ _

end Erdos684
