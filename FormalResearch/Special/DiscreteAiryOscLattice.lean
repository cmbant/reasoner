module

public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# Lattice window indices reaching the whole oscillatory side `[c₀ - r, c₀)`

Companion of `dal_lattice_window` (`DiscreteAiryLimitLattice`), whose oscillatory index `J` sits at `X_J ≈ -A₀`.  Here the first
index `J` sits at the *macroscopic* position `q_J ∈ [c₀ - r, c₀ - r + δ³)`.  With `ζ ∈ C¹` on `[c₀ - r, c₀ + r]`,
`ζ(c₀) = 0`, `0 < c₁ ≤ ζ' ≤ c₂`, `h = δ³`, `q_k = q₀ + kh`, `X_k = ζ(q_k)/δ²`: there are `δ₀ > 0` and, for `δ ≤ δ₀`
and every `q₀`, indices `J ≤ m ≤ N` with

* `q_J ∈ [c₀ - r, c₀ - r + δ³)`; all sites `q_k, k ∈ [J, N+1]` in `[c₀ - r, c₀ + r]`; `q_m ∈ [c₀, c₀ + h)`; `q_N ≥ c₀ + r/4`; `q_{N+1} ≤ c₀ + r/2`;
* spacings `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ` on `[J, N]`; `|X_k| ≤ c₂ r δ⁻²` on `[J, N+1]`;
  `0 ≤ X_m ≤ c₂ δ`; `X_N ≥ c₁ r/(4δ²)`.

Proved (ceilings/floors `dal_idx` and the mean value inequalities `dal_zeta_bounds`).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **Lattice window indices with the oscillatory end at distance `r` from the turn.** -/
theorem dao_lattice {ζ : ℝ → ℝ} {c0 r c1 c2 : ℝ} (hr : 0 < r) (hc1 : 0 < c1) (hc12 : c1 ≤ c2)
    (hz0 : ζ c0 = 0)
    (hd : ∀ q ∈ Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧
      (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Icc (c0 - r) (c0 + r)) ∧
      c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧ dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧
      dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
      (∀ k ∈ Finset.Icc J N, c1 * δ ≤ dalX ζ q₀ δ (k + 1) - dalX ζ q₀ δ k ∧
        dalX ζ q₀ δ (k + 1) - dalX ζ q₀ δ k ≤ c2 * δ) ∧
      (∀ k ∈ Finset.Icc J (N + 1), |dalX ζ q₀ δ k| ≤ c2 * r / δ ^ 2) ∧
      0 ≤ dalX ζ q₀ δ m ∧ dalX ζ q₀ δ m ≤ c2 * δ ∧ c1 * (r / 4) / δ ^ 2 ≤ dalX ζ q₀ δ N := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  set δ0 : ℝ := min 1 (r / 8) with hδ0
  have hδ0pos : 0 < δ0 := lt_min one_pos (by positivity)
  refine ⟨δ0, hδ0pos, min_le_left _ _, ?_⟩
  intro δ q₀ hδ hδδ0
  have hδ1 : δ ≤ 1 := hδδ0.trans (min_le_left _ _)
  have hδ8 : δ ≤ r / 8 := hδδ0.trans (min_le_right _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h2 : 0 < δ ^ 2 := by positivity
  have h3δ : δ ^ 3 ≤ δ ^ 2 := by nlinarith
  have h2δ : δ ^ 2 ≤ δ := by nlinarith
  have h38 : δ ^ 3 ≤ r / 8 := by linarith
  have he3 : δ ^ 3 ≤ r := by linarith
  obtain ⟨J, m, N, hJm, hmN, hJ1, hJ2, hm1, hm2, hqN1, hqN⟩ :=
    dal_idx (q₀ := q₀) (c0 := c0) (e := r) hδ h38 he3
  have qmono : ∀ k k' : ℤ, k ≤ k' → q₀ + (k : ℝ) * δ ^ 3 ≤ q₀ + (k' : ℝ) * δ ^ 3 := by
    intro k k' hk
    have : (k : ℝ) ≤ k' := by exact_mod_cast hk
    nlinarith
  have hc0w : c0 ∈ Icc (c0 - r) (c0 + r) := ⟨by linarith, by linarith⟩
  have hwin : ∀ k ∈ Finset.Icc J (N + 1), q₀ + (k : ℝ) * δ ^ 3 ∈ Icc (c0 - r) (c0 + r) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono J k hk.1
    have a2 := qmono k (N + 1) hk.2
    push_cast at a2
    constructor <;> linarith
  have hqJc : q₀ + (J : ℝ) * δ ^ 3 ≤ c0 := by
    have := qmono J m hJm
    linarith
  have zlow : ∀ x ∈ Icc (c0 - r) (c0 + r), c0 ≤ x → c1 * (x - c0) ≤ ζ x ∧ ζ x ≤ c2 * (x - c0) := by
    intro x hx hcx
    have := dal_zeta_bounds hd hc0w hx hcx
    rw [hz0] at this; simpa using this
  have zneg : ∀ x ∈ Icc (c0 - r) (c0 + r), x ≤ c0 → -(c2 * (c0 - x)) ≤ ζ x := by
    intro x hx hxc
    have := (dal_zeta_bounds hd hx hc0w hxc).2
    rw [hz0] at this; nlinarith
  have hXdef : ∀ x : ℝ, (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ x = ζ x / δ ^ 2 := by
    intro x; rw [dal_rpow_cube hδ]; ring
  have hXk : ∀ k : ℤ, dalX ζ q₀ δ k = ζ (q₀ + (k : ℝ) * δ ^ 3) / δ ^ 2 := by
    intro k; unfold dalX dalQ; exact hXdef _
  refine ⟨J, m, N, hJm, hmN, fun k hk => by unfold dalQ; exact hwin k hk, by unfold dalQ; exact hJ1, by unfold dalQ; exact hJ2,
    by unfold dalQ; exact hm1,
    by unfold dalQ; exact hm2, by unfold dalQ; exact hqN, by unfold dalQ; push_cast; exact hqN1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    have hk1w := hwin (k + 1) (by rw [Finset.mem_Icc]; omega)
    have hle : q₀ + (k : ℝ) * δ ^ 3 ≤ q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3 := qmono k (k + 1) (by omega)
    have := dal_zeta_bounds hd hkw hk1w hle
    have hdiff : q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3 - (q₀ + (k : ℝ) * δ ^ 3) = δ ^ 3 := by push_cast; ring
    rw [hdiff] at this
    rw [hXk, hXk, ← sub_div]
    have e3 : δ ^ 3 = δ * δ ^ 2 := by ring
    constructor
    · rw [le_div_iff₀ h2]; have := this.1; rw [e3] at this; linarith
    · rw [div_le_iff₀ h2]; have := this.2; rw [e3] at this; linarith
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    have a1 := qmono J k hk.1
    have a2 := qmono k (N + 1) hk.2
    push_cast at a2
    rw [hXk, abs_div, abs_of_pos h2, div_le_div_iff_of_pos_right h2]
    rcases le_total (q₀ + (k : ℝ) * δ ^ 3) c0 with hk0 | hk0
    · have := zneg _ hkw hk0
      have h6 : c2 * (c0 - (q₀ + (k : ℝ) * δ ^ 3)) ≤ c2 * r :=
        mul_le_mul_of_nonneg_left (by linarith) hc2.le
      rw [abs_le]; constructor
      · linarith
      · have := (dal_zeta_bounds hd hkw hc0w hk0).1
        rw [hz0] at this
        nlinarith [mul_nonneg hc1.le (sub_nonneg.2 hk0)]
    · have := zlow _ hkw hk0
      have h6 : c2 * (q₀ + (k : ℝ) * δ ^ 3 - c0) ≤ c2 * r :=
        mul_le_mul_of_nonneg_left (by linarith) hc2.le
      have h7 : 0 ≤ c1 * (q₀ + (k : ℝ) * δ ^ 3 - c0) := mul_nonneg hc1.le (by linarith)
      rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
  · have hmw := hwin m (by rw [Finset.mem_Icc]; omega)
    have := (zlow _ hmw hm1).1
    have h7 : 0 ≤ c1 * (q₀ + (m : ℝ) * δ ^ 3 - c0) := mul_nonneg hc1.le (by linarith)
    rw [hXk]
    exact div_nonneg (by linarith) h2.le
  · have hmw := hwin m (by rw [Finset.mem_Icc]; omega)
    have := (zlow _ hmw hm1).2
    have h6 : c2 * (q₀ + (m : ℝ) * δ ^ 3 - c0) ≤ c2 * δ ^ 3 :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    rw [hXk, div_le_iff₀ h2]
    have : c2 * δ ^ 3 = c2 * δ * δ ^ 2 := by ring
    linarith
  · have hNw := hwin N (by rw [Finset.mem_Icc]; omega)
    have a1 := qmono m N hmN
    have h1 := (zlow _ hNw (by linarith)).1
    have h6 : c1 * (r / 4) ≤ c1 * (q₀ + (N : ℝ) * δ ^ 3 - c0) :=
      mul_le_mul_of_nonneg_left (by linarith) hc1.le
    rw [hXk]
    exact div_le_div_of_nonneg_right (h6.trans h1) h2.le

/-- info: 'FormalResearch.Special.dao_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_lattice

end FormalResearch.Special
