module

public import FormalResearch.Special.DiscreteAiryLimitHahnTurn
public import FormalResearch.Special.DiscreteAiryLimit

/-!
# Discrete-to-Airy limit for the closed-form Hahn / centred Racah chains

Instance of `discrete_airy_limit` (P3 `thm:hahnAiryConnection`, `thm:racahAiryConnection`, `thm:general-rank-airy`(i);
the input they cite from Geronimo-Bruno-Van Assche is replaced by the formalised chain M1-M7b).

**Setting.**  `P = σ₁⁻¹ ≥ 0`, `Q = σ₂⁻¹ ≥ 0` (Hahn: `Q = 0`; centred Racah: `P = 1/(4α²)`, `Q = 1/(4β²)`), `β₀ = √(PQ)`,
`h = δ³`, and the closed-form coefficient sequences of P3 `A:1319-1322` (formalised in `Racah/P3JacobiComparison`)

`A_k = ½ r_k ẽ((kh)²)` (`hrAk`),   `c_k = τ(x - B_k)` (`hrCk`),   `B_k = hrB β₀ a b h k`,

with `τ = ±1`, i.e. the (sign-twisted) natural-gauge recurrence `A_{k+1} Y_{k+1} + A_k Y_{k-1} = τ(x - B_k) Y_k`
(`jac (hrAk …) (hrCk …) Y k = 0`; `τ = +1` is `x Y_k = A_{k+1} Y_{k+1} + B_k Y_k + A_k Y_{k-1}`, `τ = -1` is its
`(-1)^k`-twist).  The **simple turn** is `Φ(q_*²) = 0`, `Φ(σ) = τ(x - β₀σ) - ẽ(σ)` (`Phi`), `1 - τx > 0`, with `q_*²` in the
interior of the domain (`P q_*² < 1`, `Q q_*² < 1`): these are exactly the hypotheses of `prop:exact-hyperbolicity`
(`exact_hyperbolicity_hahn_racah`) plus strictness.

**`discrete_airy_hahn_racah`** (proved): for `δ ≤ δ₀` (`h = δ³`, sites `q_k = (k + ½)h`) there are indices
`1 ≤ J ≤ m ≤ N` (`q_J ≈ q_* - O(h^{2/3})`, `q_m ≈ q_*`, `q_{N+1} ≤ q_* + r/2`) such that the conclusion of
`discrete_airy_limit` holds for the closed-form chain with `ψ_k = g(q_k) Ai(h^{-2/3} ζ(q_k))`, `ζ = langerZeta u q_*`,
`g = langerAmp u A q_*` for `A(q) = ½ ẽ(q²)`, `u(q) = τ(x-β₀q²)/ẽ(q²)` (`hrA1`, `hrU`): the exact recessive solution is
`ψ(1 + O(h))` on `X ≥ 0` and `ψ + O(h)` on `X ∈ [-A₀, 0]`; every solution `Y` of the closed-form chain with
`|Y_N|, |Y_{N+1}| ≤ Y_max` is `κ g (Ai + O(h)) + (exponentially small)`.

**Statement caveat.**  The exported statement of `discrete_airy_hahn_racah` (and `_window`) keeps only `1 ≤ J ≤ m ≤ N`
and the localisation `|q_k - q_*| ≤ r` on `[J, N+1]`; the positions `c₀ ≤ q_m < c₀ + h`, `q_J ∈ [c₀ - Dδ², c₀]`, which
`discrete_airy_limit` does provide, are dropped, so as stated the oscillatory window `X ∈ [-A₀, 0]` is not pinned (a
degenerate `J = m = N` is not excluded by the statement; `X_N ≥ ξ₀`-large is).  The proof supplies the intended window.

**Hypotheses of the abstract theorem checked here** (all proved): `A ∈ C²`, `A(q_*) > 0` (`hrA_contDiffAt`, `hrA_pos`),
`u ∈ C³` (`hrU_contDiffAt`), `u(q_*) = 1` (`hrU_turn`), **`u'(q_*) > 0`** (`hrU_deriv_pos`, from `1 - τx > 0` by an
AM-GM identity), and the `O(h²)` perturbation sizes `|A_k - A(q_k - h/2)| ≤ E₁h²`, `|c_k - 2A(q_k)u(q_k)| ≤ ρ₂h²`
(`hr_coef_A`, `hr_coef_C`, from `rr_sub_one_le`, `Bk_close`; `E₁ = 2(a²+b²+1/3)/q_*²`, `ρ₂` the constant of
`exact_hyperbolicity_hahn_racah`).

**Not formalised (obligations left).**
1. *Identification of the closed forms with the actual chains*: that the Wigner `3j` (Hahn) / `6j` (centred Racah)
   symbols in the natural gauge satisfy exactly this recurrence with these `A_k`, `B_k` (`prop:hahn-class`,
   `prop:racah-class`, `A:1319-1322`; the exact-chain algebra is in `Racah/W1*`, `P2*`, but the matching of the
   closed forms is not done).  Here `Y` is any solution of the closed-form recurrence.
2. *The physical (hard-edge) solution and the bound `(R)`*: `|Y_N|, |Y_{N+1}| ≤ Y_max` with `Y_max` polynomial in `1/h`
   is a hypothesis; the backward-ratio monotonicity (`backward_ratio`, `exact_hyperbolicity_hahn_racah`) transports `Y` from the
   hard edge to `N` but the polynomial bound itself (T:889-892, `3j/6j` orthogonality) is not connected.
3. The normalisation `κ` (Darboux/Wigner-`d` matching, T:336, A:925-1054) and `κ ≠ 0`; the parity factor `σ_τ`, the lattice
   quantisation `K_τ ∈ ℤ`, the explicit `varpi^H` of the second-order bracket; the Racah `q`-6j.
4. Uniformity over the compact family of shapes `x` (everything here is for one fixed `(P, Q, a, b, τ, x)`).
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `A_k = ½ r_k ẽ((kh)²)` of `A:1319-1322`. -/
noncomputable def hrAk (P Q a b h : ℝ) (k : ℤ) : ℝ := 1 / 2 * rr a b (k : ℝ) * etilde P Q (((k : ℝ) * h) ^ 2)

/-- `c_k = τ(x - B_k)`, `B_k = hrB β₀ a b h k` (`A:1321`), `β₀ = √(PQ)`. -/
noncomputable def hrCk (P Q τ x a b h : ℝ) (k : ℤ) : ℝ :=
  τ * (x - hrB (Real.sqrt (P * Q)) a b h (k : ℝ))

/-- A window inside the open domain: `1 - Pq² > 0`, `1 - Qq² > 0` on `[q_* - r₀, q_* + r₀]`, `r₀ ≤ q_*/4`. -/
lemma hr_dom {P Q qs : ℝ} (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ qs / 4 ∧ ∀ q ∈ Set.Icc (qs - r0) (qs + r0),
      0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 := by
  have h1 : ContinuousAt (fun q : ℝ => 1 - P * q ^ 2) qs := by fun_prop
  have h2 : ContinuousAt (fun q : ℝ => 1 - Q * q ^ 2) qs := by fun_prop
  have e1 := h1.eventually (lt_mem_nhds hα)
  have e2 := h2.eventually (lt_mem_nhds hβ)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and e2)
  refine ⟨min (ε / 2) (qs / 4), lt_min (by positivity) (by positivity), min_le_right _ _, fun q hq => ?_⟩
  have hq' : q ∈ Metric.ball qs ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have := min_le_left (ε / 2) (qs / 4)
    constructor <;> linarith [hq.1, hq.2]
  exact hεb q hq'

/-- Size of `A_k - A(kh)`. -/
lemma hr_coef_A {P Q a b h k qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hh : 0 < h) (hqs : 0 < qs) (hk : 1 ≤ k)
    (ha : a ^ 2 ≤ k ^ 2) (hb : b ^ 2 ≤ k ^ 2) (hkq : qs ≤ 2 * k * h)
    (hdom : (k * h) ^ 2 ∈ Dom P Q) :
    |1 / 2 * rr a b k * etilde P Q ((k * h) ^ 2) - 1 / 2 * etilde P Q ((k * h) ^ 2)| ≤
      2 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 * h ^ 2 := by
  have hk0 : 0 < k := by linarith
  have h1 := rr_sub_one_le hk ha hb
  have h2 := etilde_le_one hP hQ hdom
  have h3 := etilde_nonneg P Q ((k * h) ^ 2)
  have e : 1 / 2 * rr a b k * etilde P Q ((k * h) ^ 2) - 1 / 2 * etilde P Q ((k * h) ^ 2) =
      1 / 2 * (rr a b k - 1) * etilde P Q ((k * h) ^ 2) := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg h3, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hn : 0 ≤ a ^ 2 + b ^ 2 + 1 / 3 := by positivity
  have hq : 1 ≤ 4 * k ^ 2 * h ^ 2 / qs ^ 2 := by
    rw [one_le_div (by positivity)]
    nlinarith
  have h4 : (a ^ 2 + b ^ 2 + 1 / 3) / k ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 * h ^ 2 := by
    have e2 : 4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 * h ^ 2 =
        (a ^ 2 + b ^ 2 + 1 / 3) / k ^ 2 * (4 * k ^ 2 * h ^ 2 / qs ^ 2) := by
      field_simp
    rw [e2]
    exact le_mul_of_one_le_right (by positivity) hq
  have h5 : |rr a b k - 1| * etilde P Q ((k * h) ^ 2) ≤ |rr a b k - 1| :=
    mul_le_of_le_one_right (abs_nonneg _) h2
  have e3 : 2 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 * h ^ 2 =
      (4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 * h ^ 2) / 2 := by ring
  rw [e3]
  have e4 : 1 / 2 * |rr a b k - 1| * etilde P Q ((k * h) ^ 2) =
      (|rr a b k - 1| * etilde P Q ((k * h) ^ 2)) / 2 := by ring
  rw [e4]
  linarith

/-- Size of `c_k - τ(x - β₀ q_k²)`, `q_k = (k+½)h`. -/
lemma hr_coef_C {P Q a b τ x h k qs : ℝ} (hh : 0 < h) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hk : 1 ≤ k) (hkq : qs ≤ 2 * k * h) :
    |τ * (x - hrB (Real.sqrt (P * Q)) a b h k) - τ * (x - Real.sqrt (P * Q) * ((k + 1 / 2) * h) ^ 2)| ≤
      (Real.sqrt (P * Q) * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2) * h ^ 2 := by
  have hβ : 0 ≤ Real.sqrt (P * Q) := Real.sqrt_nonneg _
  have hB := Bk_close (β₀ := Real.sqrt (P * Q)) (a := a) (b := b) hβ hh hqs hk hkq
  have e : τ * (x - hrB (Real.sqrt (P * Q)) a b h k) - τ * (x - Real.sqrt (P * Q) * ((k + 1 / 2) * h) ^ 2) =
      -τ * (Real.sqrt (P * Q) * h ^ 2 * (1 / 4 - (a ^ 2 + b ^ 2) / 2) + a * b / (k * (k + 1))) := by
    unfold hrB; ring
  have hτa : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith [abs_nonneg τ]
  rw [e, abs_mul, abs_neg, hτa, one_mul]
  exact hB

/-- The perturbation size `E = max(E₁, ρ₂)` of the closed-form coefficients. -/
noncomputable def hrE (P Q a b qs : ℝ) : ℝ :=
  max (2 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2)
    (Real.sqrt (P * Q) * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2)

lemma hrE_nonneg (P Q a b qs : ℝ) : 0 ≤ hrE P Q a b qs :=
  (show 0 ≤ 2 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 by positivity).trans (le_max_left _ _)

/-- The lattice bound `M = max(1, |a|, |b|)`. -/
noncomputable def hrM (a b : ℝ) : ℝ := max 1 (max |a| |b|)

/-- **Closed forms are `O(h²)`-perturbations of the smooth data** (the perturbation hypotheses of
`discrete_airy_limit`): on the window `k ∈ [J+1, N+1]` with `|q_k - q_*| ≤ r ≤ r₀` (`q_k = (k+½)δ³`), `δ³ ≤ 3q_*/(4M)`:
`|A_k - A(q_k - h/2)| ≤ E h²` and `|c_k - 2A(q_k)u(q_k)| ≤ E h²`. -/
lemma hr_perturb {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    {r r0 δ : ℝ} {J N : ℤ} (hr4 : r ≤ qs / 4) (hrr : r ≤ r0)
    (hdom : ∀ q ∈ Set.Icc (qs - r0) (qs + r0), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδM : δ ≤ 3 * qs / (4 * hrM a b))
    (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ Set.Icc (qs - r) (qs + r)) :
    (∀ k ∈ Finset.Icc (J + 1) (N + 1),
      |hrAk P Q a b (δ ^ 3) k - hrA1 P Q (dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2)| ≤ hrE P Q a b qs * δ ^ 6) ∧
    (∀ k ∈ Finset.Icc (J + 1) N,
      |hrCk P Q τ x a b (δ ^ 3) k - 2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k)| ≤
        hrE P Q a b qs * δ ^ 6) := by
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMa : |a| ≤ hrM a b := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : |b| ≤ hrM a b := (le_max_right _ _).trans (le_max_right _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hyw : ∀ k ∈ Finset.Icc (J + 1) (N + 1), qs - r ≤ (k : ℝ) * δ ^ 3 ∧ (k : ℝ) * δ ^ 3 ≤ qs + r := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 := hwin (k - 1) (by rw [Finset.mem_Icc]; omega)
    have h2 := hwin k (by rw [Finset.mem_Icc]; omega)
    have e1 : dalQ (δ ^ 3 / 2) δ (k - 1) = (k : ℝ) * δ ^ 3 - δ ^ 3 / 2 := by unfold dalQ; push_cast; ring
    have e2 : dalQ (δ ^ 3 / 2) δ k = (k : ℝ) * δ ^ 3 + δ ^ 3 / 2 := by unfold dalQ; ring
    rw [e1] at h1; rw [e2] at h2
    constructor <;> linarith [h1.1, h2.2]
  have hkM : ∀ k ∈ Finset.Icc (J + 1) (N + 1), hrM a b ≤ (k : ℝ) := by
    intro k hk
    have := (hyw k hk).1
    have h4 : 3 * qs / 4 ≤ (k : ℝ) * δ ^ 3 := by linarith
    have h5 : δ ^ 3 ≤ 3 * qs / (4 * hrM a b) := h3δ.trans hδM
    rw [le_div_iff₀ (by positivity)] at h5
    by_contra hlt
    push Not at hlt
    nlinarith [mul_lt_mul_of_pos_right hlt h3]
  have hk1 : ∀ k ∈ Finset.Icc (J + 1) (N + 1),
      1 ≤ (k : ℝ) ∧ a ^ 2 ≤ (k : ℝ) ^ 2 ∧ b ^ 2 ≤ (k : ℝ) ^ 2 ∧ qs ≤ 2 * (k : ℝ) * δ ^ 3 ∧
        ((k : ℝ) * δ ^ 3) ^ 2 ∈ Dom P Q := by
    intro k hk
    have hM' := hkM k hk
    have hy := hyw k hk
    have hyd := hdom ((k : ℝ) * δ ^ 3) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine ⟨hM1.trans hM', ?_, ?_, ?_, ⟨by positivity, ?_, ?_⟩⟩
    · have : |a| ≤ (k : ℝ) := hMa.trans hM'
      nlinarith [sq_abs a, abs_nonneg a]
    · have : |b| ≤ (k : ℝ) := hMb.trans hM'
      nlinarith [sq_abs b, abs_nonneg b]
    · nlinarith [hy.1]
    · linarith [hyd.1]
    · linarith [hyd.2]
  have e6 : δ ^ 6 = (δ ^ 3) ^ 2 := by ring
  constructor
  · intro k hk
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk
    have e : dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2 = (k : ℝ) * δ ^ 3 := by unfold dalQ; ring
    rw [e]
    unfold hrAk hrA1
    have := hr_coef_A (P := P) (Q := Q) (a := a) (b := b) hP hQ h3 hqs k1 ka kb kq kd
    refine this.trans ?_
    rw [e6]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro k hk
    have hk' : k ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc] at hk ⊢; omega
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk'
    have hqw := hwin k (by rw [Finset.mem_Icc] at hk ⊢; omega)
    have hqd := hdom (dalQ (δ ^ 3 / 2) δ k) ⟨by linarith [hqw.1], by linarith [hqw.2]⟩
    have e2 : dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
    have hpos : 0 < etilde P Q ((((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) := by
      rw [e2] at hqd
      unfold etilde; exact Real.sqrt_pos.2 (mul_pos hqd.1 hqd.2)
    have e1 : 2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k) =
        τ * (x - Real.sqrt (P * Q) * (((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) := by
      unfold hrA1 hrU
      rw [e2]
      generalize etilde P Q ((((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) = e at hpos ⊢
      field_simp
    rw [e1]
    unfold hrCk
    have := hr_coef_C (P := P) (Q := Q) (a := a) (b := b) (τ := τ) (x := x) (qs := qs) h3 hqs hτ k1 kq
    refine this.trans ?_
    rw [e6]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- `J ≥ 1` for a window with `q_J ≥ 3q_*/4` and `δ³ ≤ q_*/2`. -/
lemma hr_J_pos {qs r δ : ℝ} {J N : ℤ} (hr4 : r ≤ qs / 4) (hδ : 0 < δ) (hδq : δ ^ 3 ≤ qs / 2)
    (hJN : J ≤ N + 1) (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ Set.Icc (qs - r) (qs + r)) :
    1 ≤ J := by
  have h3 : 0 < δ ^ 3 := by positivity
  have h1 := hwin J (by rw [Finset.mem_Icc]; omega)
  have e2 : dalQ (δ ^ 3 / 2) δ J = (J : ℝ) * δ ^ 3 + δ ^ 3 / 2 := by unfold dalQ; ring
  rw [e2] at h1
  have h5 : (1 : ℝ) ≤ J := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_lt_mul_of_pos_right hlt h3, h1.1]
  exact_mod_cast h5

/-- **The discrete-to-Airy limit for the closed-form Hahn / centred Racah chains.**  See the module docstring. -/
theorem discrete_airy_hahn_racah {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cosc ∧
      0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        DalConclusion (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3))
          (turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
          J m N δ C Cosc Ctop W Cmu ξ0 := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hrr0, hδ0', hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_limit (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) hr0 (hrE P Q a b qs) A0
      (hrE_nonneg P Q a b qs) hA0
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cosc, Ctop, W, Cmu, ξ0, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, ?_⟩
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
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM hwin
  refine ⟨J, m, N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJm, hmN, fun k hk => ?_,
    Hc _ _ hpa hpc⟩
  have h1 := hwin k hk
  have e2 : dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_racah

/-- info: 'FormalResearch.Special.hr_coef_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hr_coef_A

end FormalResearch.Special
