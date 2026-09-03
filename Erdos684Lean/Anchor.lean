import Erdos684Lean.Defs

/-!
# The anchored code-fibre lemma (paper Lemma 5.1)

If `Φ : {0,…,J} → Ω` with `|Ω| ≤ C`, and `F` is a set of forbidden positive differences with
`C(|F|+1) < J+1`, then some pair `i < j` has `Φ i = Φ j` and `j - i ∉ F`.
-/

open Finset

namespace Erdos684

/-- Paper Lemma 5.1 (anchored code-fibre avoidance). -/
theorem anchor {α : Type*} (J : ℕ) (Φ : ℕ → α) (Ω : Finset α)
    (hΦ : ∀ j, j ≤ J → Φ j ∈ Ω) (F : Finset ℕ) (hcard : Ω.card * (F.card + 1) < J + 1) :
    ∃ i j, i < j ∧ j ≤ J ∧ Φ i = Φ j ∧ j - i ∉ F := by
  classical
  -- pigeonhole: some fibre of `Φ` over `range (J+1)` has more than `|F| + 1` elements
  have hmaps : ∀ a ∈ range (J + 1), Φ a ∈ Ω := fun a ha =>
    hΦ a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
  have hn : Ω.card * (F.card + 1) < (range (J + 1)).card := by
    rwa [Finset.card_range]
  obtain ⟨y, -, hy⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hn
  set B : Finset ℕ := {x ∈ range (J + 1) | Φ x = y} with hB
  have hmem : ∀ x, x ∈ B ↔ x ≤ J ∧ Φ x = y := by
    intro x
    simp only [hB, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]; omega
  set i₀ := B.min' hBne with hi₀
  have hi₀B : i₀ ∈ B := B.min'_mem hBne
  by_contra hcon
  push Not at hcon
  -- otherwise `j ↦ j - i₀` maps `B.erase i₀` injectively into `F`
  have hmapsF : Set.MapsTo (fun j => j - i₀) (↑(B.erase i₀) : Set ℕ) (↑F : Set ℕ) := by
    intro j hj
    have hj' : j ∈ B.erase i₀ := hj
    have hlt : i₀ < j := Finset.min'_lt_of_mem_erase_min' B hBne hj'
    have hjB := (hmem j).mp (Finset.mem_of_mem_erase hj')
    have hiB := (hmem i₀).mp hi₀B
    exact hcon i₀ j hlt hjB.1 (hiB.2.trans hjB.2.symm)
  have hinj : (↑(B.erase i₀) : Set ℕ).InjOn (fun j => j - i₀) := by
    intro a ha b hb hab
    have ha' : i₀ < a := Finset.min'_lt_of_mem_erase_min' B hBne ha
    have hb' : i₀ < b := Finset.min'_lt_of_mem_erase_min' B hBne hb
    simp only at hab
    omega
  have hle := Finset.card_le_card_of_injOn _ hmapsF hinj
  rw [Finset.card_erase_of_mem hi₀B] at hle
  omega

end Erdos684
