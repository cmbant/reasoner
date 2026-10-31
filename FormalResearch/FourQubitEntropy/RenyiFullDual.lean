import FormalResearch.FourQubitEntropy.RenyiFullDefs

/-!
# The Lagrangian dual bound and the analytic cubic envelope

Paper E: `lem:fqe-dual` (Lagrangian dual bound), the contact identities (DC), and
`cor:fqe-renyi-high-f` (analytic cubic envelope; its equality case) of `renyi_cubic_bound.tex` and
`renyi_uncapped_covering.tex`.

* `dual_bound`: for `θ = (α, β, γ)` with `γ ≥ 0` and every triple satisfying (QK),
  `Σ_j H_q(λ^{(j)}) ≤ Σ_j Λ_θ(λ^{(j)}) - ℓ_θ(ε, F)`.
* `ell_ge_min_corner`: `ℓ_θ` is concave, so on a rectangle its minimum is at a corner.
* `contact_identity`: `Λ_θ(c₁) + 2 Λ_θ(c₂) - ℓ_θ(0, 1/2) = 5` for every `θ`.
* `cubic_envelope`, `cubic_envelope_le_five_thirds`, `cubic_envelope_eq`: for every triple of
  probability vectors and `q ≥ q_b`, `E_q ≤ 22/9 - 20P/27 - 2F/27`; hence `E_q ≤ 5/3` when
  `20(P-1) + 2F ≥ 1`, with equality only at the cluster triple.

Nothing here is hypothetical: `dual_bound` uses only (QK) for the triple (a hypothesis of the lemma).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-! ### The supporting function and the outer dual -/

/-- `Λ_θ(λ; q) = H_q(λ) + α(p - 1/3) + β(f - 4) - γ(p² - 1/9)`, `f = 17p - 12t`. -/
noncomputable def Lam (q α β γ : ℝ) (l : Fin 4 → ℝ) : ℝ :=
  renyiSpec q l + α * (pur l - 1 / 3) + β * (17 * pur l - 12 * cub l - 4) - γ * (pur l ^ 2 - 1 / 9)

/-- `ℓ_θ(ε, F) = αε + βF - (γ/6)(F² + (17/2)ε + 2ε²)`. -/
noncomputable def ell (α β γ ε F : ℝ) : ℝ :=
  α * ε + β * F - γ / 6 * (F ^ 2 + 17 / 2 * ε + 2 * ε ^ 2)

/-- **`lem:fqe-dual`.** For `γ ≥ 0` and every triple satisfying (QK),
`Σ_j H_q(λ^{(j)}) ≤ Σ_j Λ_θ(λ^{(j)}) - ℓ_θ(ε, F)`. -/
theorem dual_bound {l₂ l₃ l₄ : Fin 4 → ℝ} (hQK : QKTriple l₂ l₃ l₄) (q α β γ : ℝ)
    (hγ : 0 ≤ γ) :
    renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄ ≤
      Lam q α β γ l₂ + Lam q α β γ l₃ + Lam q α β γ l₄
        - ell α β γ (Pm l₂ l₃ l₄ - 1) (Fm l₂ l₃ l₄) := by
  have h := mul_le_mul_of_nonneg_left hQK hγ
  unfold QKTriple Vm Fm Tm Pm at h
  unfold Lam ell Fm Tm Pm
  nlinarith [h]

/-- `ℓ_θ` is concave in `ε` and in `F` for `γ ≥ 0`; a one-variable corner statement:
`g(x) = a x + b - c x²` with `c ≥ 0` satisfies `g x ≥ min (g x₀) (g x₁)` on `[x₀, x₁]`. -/
theorem quad_concave_min {a b c x₀ x₁ x : ℝ} (hc : 0 ≤ c) (h0 : x₀ ≤ x) (h1 : x ≤ x₁) :
    min (a * x₀ + b - c * x₀ ^ 2) (a * x₁ + b - c * x₁ ^ 2) ≤ a * x + b - c * x ^ 2 := by
  rcases eq_or_lt_of_le (h0.trans h1) with he | hlt
  · have : x = x₀ := le_antisymm (he ▸ h1) h0
    subst this
    exact min_le_left _ _
  · -- interpolation
    set s := (x - x₀) / (x₁ - x₀) with hs
    have hd : 0 < x₁ - x₀ := by linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
    have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
    have hx : x = (1 - s) * x₀ + s * x₁ := by
      rw [hs]; field_simp; ring
    set g : ℝ → ℝ := fun y => a * y + b - c * y ^ 2 with hg
    have key : (1 - s) * g x₀ + s * g x₁ ≤ g x := by
      have : g x - ((1 - s) * g x₀ + s * g x₁) = c * s * (1 - s) * (x₁ - x₀) ^ 2 := by
        simp only [hg]; rw [hx]; ring
      have h2 : 0 ≤ c * s * (1 - s) * (x₁ - x₀) ^ 2 := by
        apply mul_nonneg (mul_nonneg (mul_nonneg hc hs0) (by linarith)) (sq_nonneg _)
      linarith
    have hm : min (g x₀) (g x₁) ≤ (1 - s) * g x₀ + s * g x₁ := by
      rcases le_total (g x₀) (g x₁) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    exact hm.trans key

/-- **Corners of a rectangle.** For `γ ≥ 0`, `ℓ_θ(ε, F) ≥` the least of its four corner values on
`[ε₀, ε₁] × [F₀, F₁]`. -/
theorem ell_ge_min_corner {α β γ ε₀ ε₁ F₀ F₁ ε F : ℝ} (hγ : 0 ≤ γ)
    (he0 : ε₀ ≤ ε) (he1 : ε ≤ ε₁) (hF0 : F₀ ≤ F) (hF1 : F ≤ F₁) :
    min (min (ell α β γ ε₀ F₀) (ell α β γ ε₀ F₁)) (min (ell α β γ ε₁ F₀) (ell α β γ ε₁ F₁))
      ≤ ell α β γ ε F := by
  have hc : 0 ≤ γ / 6 := by positivity
  -- concave in F at fixed ε
  have inF : ∀ e : ℝ, min (ell α β γ e F₀) (ell α β γ e F₁) ≤ ell α β γ e F := by
    intro e
    have := quad_concave_min (a := β) (b := α * e - γ / 6 * (17 / 2 * e + 2 * e ^ 2)) hc hF0 hF1
    unfold ell
    convert this using 1 <;> ring_nf
  -- concave in ε at fixed F
  have inE : ∀ f : ℝ, min (ell α β γ ε₀ f) (ell α β γ ε₁ f) ≤ ell α β γ ε f := by
    intro f
    have hc2 : 0 ≤ γ / 6 * 2 := by positivity
    have := quad_concave_min (a := α - γ / 6 * (17 / 2)) (b := β * f - γ / 6 * f ^ 2) hc2 he0 he1
    unfold ell
    convert this using 1 <;> ring_nf
  calc _ ≤ min (ell α β γ ε F₀) (ell α β γ ε F₁) := by
        apply le_min
        · exact (min_le_min (min_le_left _ _) (min_le_left _ _)).trans (inE F₀)
        · exact (min_le_min (min_le_right _ _) (min_le_right _ _)).trans (inE F₁)
    _ ≤ _ := inF ε

/-! ### The contact spectra `c₁`, `c₂` -/

theorem sum_c1_pow (n : ℝ) (hn : 0 < n) : ∑ i, c1 i ^ n = 2 * (1 / 2 : ℝ) ^ n := by
  unfold c1
  simp [Fin.sum_univ_four, Real.zero_rpow hn.ne']
  ring

/-- `H_q(c₁) = 1` for every `q > 0`, `q ≠ 1`. -/
theorem renyiSpec_c1 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) : renyiSpec q c1 = 1 := by
  unfold renyiSpec
  rw [sum_c1_pow q hq0]
  have h2 : 2 * (1 / 2 : ℝ) ^ q = (2 : ℝ) ^ (1 - q) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num)]
    field_simp
  rw [h2, Real.logb_rpow (by norm_num) (by norm_num)]
  have : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  field_simp

/-- `H_q(c₂) = 2` for every `q > 0`, `q ≠ 1`. -/
theorem renyiSpec_c2 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) : renyiSpec q c2 = 2 := by
  have h := renyiSpec_eq_iff (q := q) (l := c2) hq0 hq1
    (by intro i; unfold c2; fin_cases i <;> norm_num)
    (by unfold c2; simp [Fin.sum_univ_four]; norm_num)
  have h4 : Real.logb 2 ((Fintype.card (Fin 4) : ℕ) : ℝ) = 2 := by
    rw [Fintype.card_fin]
    rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)]
  rw [← h4]
  apply h.2
  intro i
  unfold c2
  fin_cases i <;> simp

theorem pur_c1 : pur c1 = 1 / 2 := by
  unfold pur c1; simp [Fin.sum_univ_four]; norm_num

theorem cub_c1 : cub c1 = 1 / 4 := by
  unfold cub c1; simp [Fin.sum_univ_four]; norm_num

theorem pur_c2 : pur c2 = 1 / 4 := by
  unfold pur c2; simp [Fin.sum_univ_four]; norm_num

theorem cub_c2 : cub c2 = 1 / 16 := by
  unfold cub c2; simp [Fin.sum_univ_four]; norm_num

/-- `Λ_θ(c₁) = 1 + α/6 + (3/2)β - (5/36)γ`. -/
theorem Lam_c1 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (α β γ : ℝ) :
    Lam q α β γ c1 = 1 + α / 6 + 3 / 2 * β - 5 / 36 * γ := by
  unfold Lam
  rw [renyiSpec_c1 hq0 hq1, pur_c1, cub_c1]
  ring

/-- `Λ_θ(c₂) = 2 - α/12 - β/2 + (7/144)γ`. -/
theorem Lam_c2 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (α β γ : ℝ) :
    Lam q α β γ c2 = 2 - α / 12 - β / 2 + 7 / 144 * γ := by
  unfold Lam
  rw [renyiSpec_c2 hq0 hq1, pur_c2, cub_c2]
  ring

/-- **Contact identity (DC)**: `Λ_θ(c₁) + 2Λ_θ(c₂) - ℓ_θ(0, 1/2) = 5` for every `θ`. -/
theorem contact_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (α β γ : ℝ) :
    Lam q α β γ c1 + 2 * Lam q α β γ c2 - ell α β γ 0 (1 / 2) = 5 := by
  rw [Lam_c1 hq0 hq1, Lam_c2 hq0 hq1]
  unfold ell
  ring

/-! ### The analytic cubic envelope (`cor:fqe-renyi-high-f`) -/

open FormalResearch.FourQubitEntropy.PaperECritical in
/-- **`cor:fqe-renyi-high-f`, inequality.** For three probability vectors and `q ≥ q_b`,
`3 E_q ≤ 22/3 - 20 P/9 - 2 F/9`, i.e. `E_q ≤ 5/3 - (20/27)(P-1) - (2/27)(F - 1/2)`. -/
theorem cubic_envelope {l₂ l₃ l₄ : Fin 4 → ℝ} (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃)
    (h₄ : IsProb4 l₄) {q : ℝ} (hq : qb ≤ q) :
    Em q l₂ l₃ l₄ ≤ 5 / 3 - 20 / 27 * (Pm l₂ l₃ l₄ - 1) - 2 / 27 * (Fm l₂ l₃ l₄ - 1 / 2) := by
  have c2' := renyi_cubic_bound hq l₂ h₂.1 h₂.2
  have c3' := renyi_cubic_bound hq l₃ h₃.1 h₃.2
  have c4' := renyi_cubic_bound hq l₄ h₄.1 h₄.2
  unfold Em renyiE Fm Tm Pm pur cub
  linarith


/-! ### Equality in the cubic envelope -/

/-- The entropy of a pure, uniform-two or uniform-four spectrum, with its shape. -/
theorem pureOrUniform_values {q : ℝ} (hq : 1 < q) {l : Fin 4 → ℝ}
    (h : PaperECritical.PureOrUniform l) :
    (renyiSpec q l = 0) ∨ (renyiSpec q l = 1 ∧ UniformTwo l) ∨ (renyiSpec q l = 2 ∧ UniformFour l) := by
  have hq0 : 0 < q := by linarith
  rcases h with ⟨i, hi, hj⟩ | ⟨i, j, hij, hi, hj, hk⟩ | hu
  · left
    unfold renyiSpec
    have : ∑ k, l k ^ q = 1 := by
      rw [Finset.sum_eq_single i]
      · rw [hi]; simp
      · intro k _ hki; rw [hj k hki, Real.zero_rpow hq0.ne']
      · simp
    rw [this]; simp
  · right; left
    refine ⟨?_, ⟨i, j, hij, hi, hj, hk⟩⟩
    have : ∑ k, l k ^ q = 2 * (1 / 2 : ℝ) ^ q := by
      rw [PaperECritical.sum_two_support (f := fun k => l k ^ q) hij
        (fun k h1 h2 => by simp only [hk k h1 h2]; exact Real.zero_rpow hq0.ne')]
      simp only [hi, hj]; ring
    unfold renyiSpec
    rw [this]
    have h2 : 2 * (1 / 2 : ℝ) ^ q = (2 : ℝ) ^ (1 - q) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num)]
      field_simp
    rw [h2, Real.logb_rpow (by norm_num) (by norm_num)]
    have : (1 - q) ≠ 0 := by linarith
    field_simp
  · right; right
    have hu' : l = c2 := by funext i; rw [hu i]; unfold c2; fin_cases i <;> simp
    refine ⟨?_, hu⟩
    rw [hu']; exact renyiSpec_c2 hq0 hq.ne'

theorem cluster_of_values {a b c : ℝ} {l₂ l₃ l₄ : Fin 4 → ℝ}
    (h₂ : (a = 0) ∨ (a = 1 ∧ UniformTwo l₂) ∨ (a = 2 ∧ UniformFour l₂))
    (h₃ : (b = 0) ∨ (b = 1 ∧ UniformTwo l₃) ∨ (b = 2 ∧ UniformFour l₃))
    (h₄ : (c = 0) ∨ (c = 1 ∧ UniformTwo l₄) ∨ (c = 2 ∧ UniformFour l₄))
    (hs : a + b + c = 5) : IsClusterTriple l₂ l₃ l₄ := by
  unfold IsClusterTriple
  rcases h₂ with h | ⟨h, u⟩ | ⟨h, u⟩ <;> rcases h₃ with h' | ⟨h', u'⟩ | ⟨h', u'⟩ <;>
    rcases h₄ with h'' | ⟨h'', u''⟩ | ⟨h'', u''⟩ <;>
    first | (exfalso; linarith) | tauto

open FormalResearch.FourQubitEntropy.PaperECritical in
/-- **`cor:fqe-renyi-high-f`, equality.** For `q ≥ q_b` and `20(P-1) + 2F ≥ 1`: `E_q ≤ 5/3`, and
`E_q = 5/3` only at the cluster triple. -/
theorem cubic_envelope_le_five_thirds {l₂ l₃ l₄ : Fin 4 → ℝ} (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃)
    (h₄ : IsProb4 l₄) {q : ℝ} (hq : qb ≤ q)
    (hF : 1 ≤ 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄) :
    Em q l₂ l₃ l₄ ≤ 5 / 3 ∧ (Em q l₂ l₃ l₄ = 5 / 3 → IsClusterTriple l₂ l₃ l₄) := by
  have hmain := cubic_envelope h₂ h₃ h₄ hq
  refine ⟨by linarith, fun heq => ?_⟩
  have hq1 : 1 < q := lt_of_lt_of_le one_lt_qb hq
  have c2' := renyi_cubic_bound hq l₂ h₂.1 h₂.2
  have c3' := renyi_cubic_bound hq l₃ h₃.1 h₃.2
  have c4' := renyi_cubic_bound hq l₄ h₄.1 h₄.2
  have hsum : Em q l₂ l₃ l₄ = (renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄) / 3 := rfl
  -- all three cubic bounds are equalities
  have key : (renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄) =
      (10 / 3 - 6 * ∑ i, l₂ i ^ 2 + 8 / 3 * ∑ i, l₂ i ^ 3) +
      (10 / 3 - 6 * ∑ i, l₃ i ^ 2 + 8 / 3 * ∑ i, l₃ i ^ 3) +
      (10 / 3 - 6 * ∑ i, l₄ i ^ 2 + 8 / 3 * ∑ i, l₄ i ^ 3) := by
    have e : (10 / 3 - 6 * ∑ i, l₂ i ^ 2 + 8 / 3 * ∑ i, l₂ i ^ 3) +
        (10 / 3 - 6 * ∑ i, l₃ i ^ 2 + 8 / 3 * ∑ i, l₃ i ^ 3) +
        (10 / 3 - 6 * ∑ i, l₄ i ^ 2 + 8 / 3 * ∑ i, l₄ i ^ 3) = 5 := by
      unfold Em renyiE Fm Tm Pm pur cub at *
      linarith
    linarith
  have e2 : renyiSpec q l₂ = 10 / 3 - 6 * ∑ i, l₂ i ^ 2 + 8 / 3 * ∑ i, l₂ i ^ 3 := by linarith
  have e3 : renyiSpec q l₃ = 10 / 3 - 6 * ∑ i, l₃ i ^ 2 + 8 / 3 * ∑ i, l₃ i ^ 3 := by linarith
  have e4 : renyiSpec q l₄ = 10 / 3 - 6 * ∑ i, l₄ i ^ 2 + 8 / 3 * ∑ i, l₄ i ^ 3 := by linarith
  have p2 := (renyi_cubic_eq_iff hq l₂ h₂.1 h₂.2).1 e2
  have p3 := (renyi_cubic_eq_iff hq l₃ h₃.1 h₃.2).1 e3
  have p4 := (renyi_cubic_eq_iff hq l₄ h₄.1 h₄.2).1 e4
  refine cluster_of_values (pureOrUniform_values hq1 p2) (pureOrUniform_values hq1 p3)
    (pureOrUniform_values hq1 p4) ?_
  unfold Em renyiE at heq
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
