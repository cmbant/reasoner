module

public import FormalResearch.Special.DiscreteAirySecondTurn
public import FormalResearch.Special.DiscreteAirySecondHahnCoef
public import FormalResearch.Special.DiscreteAirySecondLangerData

/-!
# The second-order Airy bracket for the closed-form Hahn / centred Racah chains (S4)

Instance of `airy2_turn_full` (`DiscreteAirySecondTurn`; P3 `thm:general-rank-airy-second`) for the closed-form coefficient
sequences of P3 `A:1319-1322` (`hrAk`, `hrCk` of `DiscreteAiryLimitHahn`: `A_k = ½ r_k ẽ((kh)²)`, `c_k = τ(x - B_k)`,
`h = δ³`), with the hypotheses of `discrete_airy_hahn_racah` (`Φ(q_*²) = 0`, `1 - τx > 0`, `τ² = 1`, `Pq_*² < 1`, `Qq_*² < 1`,
`q_* > 0`, `P, Q ≥ 0`).  The three ingredients are

1. **the second-order coefficient closeness** (`hs_perturb`, `DiscreteAirySecondHahnCoef`): on the window
   `|A_k - (A + h²A₂)(q_k - h/2)| ≤ E h³` and `|c_k - (2Au + h²c₂)(q_k)| ≤ E h³` (true order `h⁴`), with
   `A = ½ẽ(q²)`, `u = τ(x - β₀q²)/ẽ(q²)`, `A₂ = ½ẽ(q²) c_{ab}/q²` (`hsA2`), `c₂ = -τ[β₀(1/4 - (a²+b²)/2) + ab/q²]` (`hsCq`);
2. **the Langer-form data from `u`** (`langer_hrel_seven`, `DiscreteAirySecondLangerData`): `ζ = langerZeta u q_*`,
   `g = langerAmp u A q_*` with `ζ ∈ C⁷`, `A, g ∈ C⁶`, the amplitude relation and the eikonal `Ch(ζζ'²) = u` on a ball
   `B(q_*, ρ)`, from `u ∈ C^∞` (`hrU_contDiffAt`), `u(q_*) = 1`, `u'(q_*) > 0`;
3. **`airy2_turn_full`**, which constructs `q₁ ∈ C³(B)` (`airy2_q1_exists`; the transport equation for the data `A₂`, `c₂`).

**`hahn_airy2_turn`** (proved).  For `ρ ≤ q_*/4` (the radius of the Langer chart and of the domain window) there is `q₁` with
`a2Res = 0` on `B(q_*, ρ)` and, for `δ ≤ δ₀`, indices `1 ≤ J < N`, `J ≤ m₀ ≤ N` with the lattice window `[q_* - r, q_* + r/2]`,
`r = ρ/2` (`q_J ∈ [q_* - r, q_* - r + h)`, `q_{m₀} ∈ [q_*, q_* + 2h)`, `q_N ≥ q_* + r/4`, `q_{N+1} ≤ q_* + r/2`,
`q_k = (k + ½)h`) such that `DaiFullR` holds for the chain `(hrAk, hrCk)` with `X̂_k = ζ(q_k)/δ² + δ⁴ q₁(q_k)/g(q_k)`,
`g_k = g(q_k)`, at the error rate `δ⁶ = h²` in the Olver weights on the whole window, with the Casoratian `≥ δ/Q'` unchanged:
the exact recessive solution is `g(Ai(X̂) + O(h²) airyWt)`, every solution `Y` with `|Y_N|, |Y_{N+1}| ≤ Y_max` is
`κ g Ai(X̂) + μ g Bi(X̂)` up to `C h² (|κ| airyWt + |μ| airyBiWt)` (`DaiFullR.pointwise`), `|μ| ≤ C_μ Y_max e^{-ξ(X̂_N)}/δ`.
In the paper's notation `B_τ = q₁/g`, `δ⁴ = h^{4/3}`: the bracket is `Ai(t) + h^{4/3} B_τ(q) Ai'(t) + O(h²)`.

**Claim class: proved**; the constants `δ₀, C, Q', C_μ, ξ₀, ρ` depend on `(P, Q, a, b, τ, x, q_*)` only.

**Not formalised.**  (i) The Langer-chart radius `ρ` is existential (as in `discrete_airy_hahn_racah_full`): the window is
`[q_* - ρ/2, q_* + ρ/2]`, not the largest window of smoothness, and `q₁` is local on `B(q_*, ρ)` (a global `q₁` is the nonsingular
transport ODE, not formalised).  (ii) The `κ` normalisation and the second-order phase `ϖ_τ = B_τ(q_*)` / Darboux matching: only
the bracket is formalised, `κ` is not identified (for the actual `3j` chain `κ ≠ 0` is `hahn_chain_kappa`).  (iii) The Racah `q`-`6j`
chain (`η_π ≠ 0`, `δ_fl = -1/12`), half-integer / shifted-lattice and mixed-parity labels, uniformity in `x`, and the hard edges
`x → 0, 1`.  (iv) The sharper `O(h³)` remainder `𝔯_N` of `thm:general-rank-airy`(ii) (the amplitude `p₂` with `2p₂/g + 𝔧 = 0`).
(v) The closed forms `hrAk`, `hrCk` are the recurrence of the chain only through `hahn_class_chain`/`racah_class_chain`; the
bound `(R)` on `Y` is a hypothesis of the pointwise form.
-/

@[expose] public section

open Finset Metric FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Second-order Airy bracket for the closed-form Hahn / centred Racah chains.**  See the module docstring. -/
theorem hahn_airy2_turn {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (ρ : ℝ) (q1 : ℝ → ℝ), 0 < ρ ∧ ρ ≤ qs / 4 ∧ ContDiffOn ℝ 3 q1 (ball qs ρ) ∧
      (∀ q ∈ ball qs ρ, a2Res (langerZeta (hrU P Q τ x) qs) (hrA1 P Q) (hsA2 P Q a b)
        (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 (hsCq P Q a b τ) q = 0) ∧
      ∃ (δ0 C Q' Cmu ξ0 : ℝ), 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < Q' ∧ 0 < Cmu ∧ 0 < ξ0 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m0 N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m0 ∧ m0 ≤ N ∧
          (∀ k ∈ Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ ρ / 2) ∧
          qs - ρ / 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - ρ / 2 + δ ^ 3 ∧
          qs ≤ ((m0 : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m0 : ℝ) + 1 / 2) * δ ^ 3 < qs + 2 * δ ^ 3 ∧
          qs + ρ / 8 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + ρ / 4 ∧
          DaiFullR (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3))
            (fun k => a2Xh (langerZeta (hrU P Q τ x) qs) (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ
              (dalQ (δ ^ 3 / 2) δ k))
            (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) J m0 N δ (δ ^ 6) C Q' Cmu ξ0 := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have hu0 := hrU_turn hint hturn
  have hu1 := hrU_deriv_pos hqs hκ hα hβ hturn
  obtain ⟨U, hUo, hcU, hζU, hAU, hgU, hUp⟩ :=
    langer_hrel_seven (hrU_contDiffAt τ x 7 hint) hu0 hu1 (hrA_contDiffAt 6 hint) (hrA_pos hint)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo qs hcU
  set ρ : ℝ := min ε r0 with hρ
  have hρ0 : 0 < ρ := lt_min hε hr0
  have hρr0 : ρ ≤ r0 := min_le_right _ _
  have hρ4 : ρ ≤ qs / 4 := hρr0.trans hr0q
  have hbU : ball qs ρ ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hεU
  have hbdom : ∀ q ∈ ball qs ρ, q ∈ Set.Icc (qs - r0) (qs + r0) := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hq
    constructor <;> linarith [hq.1, hq.2]
  have hbpos : ∀ q ∈ ball qs ρ, 0 < q := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hq
    linarith [hq.1, hq.2]
  -- regularity of the data on the ball
  have hζ : ContDiffOn ℝ 7 (langerZeta (hrU P Q τ x) qs) (ball qs ρ) := hζU.mono hbU
  have hA : ContDiffOn ℝ 6 (hrA1 P Q) (ball qs ρ) := hAU.mono hbU
  have hg : ContDiffOn ℝ 6 (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) (ball qs ρ) := hgU.mono hbU
  have hetq : ∀ q ∈ ball qs ρ, ∀ n : WithTop ℕ∞, ContDiffAt ℝ n (fun y : ℝ => etilde P Q (y ^ 2)) q := fun q hq n => by
    have hd := hdom q (hbdom q hq)
    exact etilde_contDiffAt n (mul_pos hd.1 hd.2)
  have hA2 : ContDiffOn ℝ 4 (hsA2 P Q a b) (ball qs ρ) := by
    intro q hq
    have h1 := hetq q hq 4
    have h2 : ContDiffAt ℝ 4 (fun y : ℝ => hsCab a b / y ^ 2) q :=
      contDiffAt_const.div (by fun_prop) (pow_ne_zero 2 (hbpos q hq).ne')
    exact ((contDiffAt_const.mul h1).mul h2).contDiffWithinAt
  have hcq : ContDiffOn ℝ 4 (hsCq P Q a b τ) (ball qs ρ) := by
    intro q hq
    have h2 : ContDiffAt ℝ 4 (fun y : ℝ => a * b / y ^ 2) q :=
      contDiffAt_const.div (by fun_prop) (pow_ne_zero 2 (hbpos q hq).ne')
    unfold hsCq
    exact (contDiffAt_const.mul (contDiffAt_const.add h2)).contDiffWithinAt
  have hz0 : langerZeta (hrU P Q τ x) qs qs = 0 := langerZetaOf_zero _ _
  have hzpos : ∀ q ∈ ball qs ρ, 0 < deriv (langerZeta (hrU P Q τ x) qs) q := fun q hq => (hUp q (hbU hq)).2.2.1
  have hApos : ∀ q ∈ ball qs ρ, 0 < hrA1 P Q q := fun q hq => (hUp q (hbU hq)).1
  have hgpos : ∀ q ∈ ball qs ρ, 0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs q := fun q hq => (hUp q (hbU hq)).2.1
  have hrel : ∀ q ∈ ball qs ρ,
      langerAmp (hrU P Q τ x) (hrA1 P Q) qs q ^ 2 * hrA1 P Q q * deriv (langerZeta (hrU P Q τ x) qs) q *
        (2 * deriv langerCosh (langerZeta (hrU P Q τ x) qs q * deriv (langerZeta (hrU P Q τ x) qs) q ^ 2)) = 1 :=
    fun q hq => (hUp q (hbU hq)).2.2.2.1
  have heik : ∀ q ∈ ball qs ρ,
      langerCosh (langerZeta (hrU P Q τ x) qs q * deriv (langerZeta (hrU P Q τ x) qs) q ^ 2) = hrU P Q τ x q :=
    fun q hq => (hUp q (hbU hq)).2.2.2.2
  obtain ⟨q1, hq1c, hq1, hconc⟩ := airy2_turn_full hρ0 hζ hA hA2 hg hcq hz0 hzpos hApos hgpos hrel
    (hsE a b qs) (hsE_nonneg a b qs)
  obtain ⟨δ0', C, Q', Cmu, ξ0, hδ0', hδ01, hQ', hCmu, hξ0, H⟩ := hconc
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨ρ, q1, hρ0, hρ4, hq1c, hq1, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Q', Cmu, ξ0,
    lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hQ', hCmu, hξ0, ?_⟩
  intro δ hδ hδδ0
  have hδ1' : δ ≤ δ0' := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  obtain ⟨J, m0, N, hJN, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : ρ / 2 ≤ qs / 4 := by linarith
  have hrr : ρ / 2 ≤ r0 := by linarith
  obtain ⟨hpa, hpc⟩ := hs_perturb hP hQ a b τ x qs hqs hτ hr4 hrr hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  have hwinb : ∀ k ∈ Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ ball qs ρ := fun k hk => by
    have h1 := hwin k hk
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [h1.1, h1.2]
  refine ⟨J, m0, N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJN, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; linarith, by rw [← e2]; linarith, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    by rw [← e2]; linarith, by
      have := hqN1
      rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by unfold dalQ; push_cast; ring]
      linarith, ?_⟩
  · have h1 := hwin k hk
    rw [e2] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  · refine Hc _ _ hpa ?_
    intro k hk
    have hkw : dalQ (δ ^ 3 / 2) δ k ∈ ball qs ρ := hwinb k (by rw [mem_Icc] at hk ⊢; omega)
    have := hpc k hk
    unfold a2c
    rw [heik _ hkw]
    exact this

/-- info: 'FormalResearch.Special.hahn_airy2_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_airy2_turn

/-- **Composition form.**  Under the hypotheses of `hahn_airy2_turn`, with the same constants, every sequence `Y` satisfying all
rows `k ≥ 1` of the closed-form recurrence `jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y = 0` at a scale `0 < h ≤ δ₀³` with
`|Y_k| ≤ Y_max` is `κ g Ai(X̂) + μ g Bi(X̂)` up to `C h² (|κ| airyWt(X̂) + |μ| airyBiWt(X̂))` on the whole window `[J, N+1]`
(`h = δ³`, `X̂_k = ζ(q_k)/δ² + δ⁴ q₁(q_k)/g(q_k)`, `g_k = g(q_k)`), with `|μ| ≤ C_μ Y_max e^{-ξ(X̂_N)}/δ`.  `κ` is not
identified. -/
theorem hahn_airy2_compose {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (ρ : ℝ) (q1 : ℝ → ℝ), 0 < ρ ∧ ρ ≤ qs / 4 ∧ ContDiffOn ℝ 3 q1 (ball qs ρ) ∧
      ∃ (δ0 C Cmu ξ0 : ℝ), 0 < δ0 ∧ 0 < Cmu ∧ 0 < ξ0 ∧
        ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ J m0 N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m0 ∧ m0 ≤ N ∧
            (∀ k ∈ Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ ρ / 2) ∧
            qs - ρ / 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - ρ / 2 + δ ^ 3 ∧
            qs ≤ ((m0 : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m0 : ℝ) + 1 / 2) * δ ^ 3 < qs + 2 * δ ^ 3 ∧
            qs + ρ / 8 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + ρ / 4 ∧
            ∃ κ μ : ℝ,
              |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (a2Xh (langerZeta (hrU P Q τ x) qs)
                (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ (dalQ (δ ^ 3 / 2) δ N))) / δ ∧
              ∀ k ∈ Icc J (N + 1),
                |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
                    (fun k => a2Xh (langerZeta (hrU P Q τ x) qs) (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ
                      (dalQ (δ ^ 3 / 2) δ k)) k +
                  μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
                    (fun k => a2Xh (langerZeta (hrU P Q τ x) qs) (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ
                      (dalQ (δ ^ 3 / 2) δ k)) k)| ≤
                  C * δ ^ 6 * (|κ| * airyWt (a2Xh (langerZeta (hrU P Q τ x) qs)
                      (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ (dalQ (δ ^ 3 / 2) δ k)) +
                    |μ| * airyBiWt (a2Xh (langerZeta (hrU P Q τ x) qs)
                      (langerAmp (hrU P Q τ x) (hrA1 P Q) qs) q1 δ (dalQ (δ ^ 3 / 2) δ k))) := by
  obtain ⟨ρ, q1, hρ, hρ4, hq1c, -, δ0, C, Q', Cmu, ξ0, hδ0, -, -, hCmu, hξ0, H⟩ :=
    hahn_airy2_turn hP hQ a b τ x qs hqs hτ hκ hα hβ hturn
  refine ⟨ρ, q1, hρ, hρ4, hq1c, δ0, C, Cmu, ξ0, hδ0, hCmu, hξ0, ?_⟩
  intro h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ0', hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m0, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc⟩ := H δ hδ0' hδle
  have hrows' : ∀ k ∈ Icc (J + 1) N,
      jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise Y Ymax hrows' (hbd _) (hbd _)
  exact ⟨δ, hδ0', hδle, hδ3, J, m0, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, κ, μ, hμ, hpt⟩

/-- info: 'FormalResearch.Special.hahn_airy2_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_airy2_compose

end FormalResearch.Special
