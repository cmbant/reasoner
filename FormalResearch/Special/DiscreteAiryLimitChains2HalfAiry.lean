module

public import FormalResearch.Special.DiscreteAiryLimitChains2Twist

/-!
# The discrete-to-Airy limit on the shifted lattice `k ↦ Ŷ_{k+½}` (half-integer chains)

For half-integer data the natural-gauge chain lives on the ranks `L ∈ ℤ + ½`.  Writing `L = k + ½` (`k ∈ ℤ`) the chain
`Y_k = Ŷ_{k+½}` solves the closed-form recurrence with the **shifted** coefficients
`A_k = ½ r_{k+½} ẽ(((k+½)h)²)` (`hrAkH`), `c_k = τ(x - B_{k+½})` (`hrCkH`): the bond between the ranks `L-1, L` sits at `L h =
(k+½)h` and the site of the rank `L` at `(L+½)h = (k+1)h`.  This file proves the discrete-to-Airy limit for the shifted
lattice `q_k = q_0 + k h` with `q_0 = h` (`discrete_airy_limit` is already stated for an arbitrary offset `q_0`; only the
`O(h²)` closeness of the closed forms to `A(q_k - h/2)`, `2A(q_k)u(q_k)` has to be redone for the half-shift).

## Results (proved)

* `hrH_perturb`: for the window `|q_k - q_*| ≤ r`, `q_k = (k+1)δ³`: `|A_k - A(q_k - h/2)| ≤ E h²`,
  `|c_k - 2A(q_k)u(q_k)| ≤ E h²` (same `E = hrE`), from `hr_coef_A`, `hr_coef_C` at the real index `κ = k + ½`.
* `discrete_airy_hahn_racah_half`: the exact analogue of `discrete_airy_hahn_racah` (same simple-turn hypotheses and
  constants) for `hrAkH`, `hrCkH` and sites `(k+1)δ³`.
* `AiryOutHalf`, `airy_chain_compose_half`: the abstract composition (any `Y : ℤ → ℝ` solving all rows `k ≥ 1`).

Claim class: **proved**.  The identification with the actual half-integer `3j`/`6j` chains is in
`DiscreteAiryLimitChains2Half3j` / `…Half6j`.

## Not formalised

`κ`, `κ ≠ 0`, the `Ai/Bi` pair, uniformity over families, other offsets `s ∉ {0, ½}` (not needed).
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The shifted bond coefficient `A_k = ½ r_{k+½} ẽ(((k+½)h)²)` (half-integer ranks `L = k + ½`). -/
noncomputable def hrAkH (P Q a b h : ℝ) (k : ℤ) : ℝ :=
  1 / 2 * rr a b ((k : ℝ) + 1 / 2) * etilde P Q ((((k : ℝ) + 1 / 2) * h) ^ 2)

/-- The shifted diagonal coefficient `c_k = τ(x - B_{k+½})`. -/
noncomputable def hrCkH (P Q τ x a b h : ℝ) (k : ℤ) : ℝ :=
  τ * (x - hrB (Real.sqrt (P * Q)) a b h ((k : ℝ) + 1 / 2))

/-- **The closed forms on the half-shifted lattice are `O(h²)`-perturbations of the smooth data.**  Window
`k ∈ [J+1, N+1]` with `|q_k - q_*| ≤ r ≤ r₀`, `q_k = (k+1)δ³`, `δ³ ≤ 3q_*/(4M)`. -/
lemma hrH_perturb {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    {r r0 δ : ℝ} {J N : ℤ} (hr4 : r ≤ qs / 4) (hrr : r ≤ r0)
    (hdom : ∀ q ∈ Set.Icc (qs - r0) (qs + r0), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδM : δ ≤ 3 * qs / (4 * hrM a b))
    (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3) δ k ∈ Set.Icc (qs - r) (qs + r)) :
    (∀ k ∈ Finset.Icc (J + 1) (N + 1),
      |hrAkH P Q a b (δ ^ 3) k - hrA1 P Q (dalQ (δ ^ 3) δ k - δ ^ 3 / 2)| ≤ hrE P Q a b qs * δ ^ 6) ∧
    (∀ k ∈ Finset.Icc (J + 1) N,
      |hrCkH P Q τ x a b (δ ^ 3) k - 2 * hrA1 P Q (dalQ (δ ^ 3) δ k) * hrU P Q τ x (dalQ (δ ^ 3) δ k)| ≤
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
  have hyw : ∀ k ∈ Finset.Icc (J + 1) (N + 1),
      qs - r ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 ∧ ((k : ℝ) + 1 / 2) * δ ^ 3 ≤ qs + r := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 := hwin (k - 1) (by rw [Finset.mem_Icc]; omega)
    have h2 := hwin k (by rw [Finset.mem_Icc]; omega)
    have e1 : dalQ (δ ^ 3) δ (k - 1) = (k : ℝ) * δ ^ 3 := by unfold dalQ; push_cast; ring
    have e2 : dalQ (δ ^ 3) δ k = ((k : ℝ) + 1) * δ ^ 3 := by unfold dalQ; ring
    rw [e1] at h1; rw [e2] at h2
    constructor <;> nlinarith [h1.1, h2.2]
  have hkM : ∀ k ∈ Finset.Icc (J + 1) (N + 1), hrM a b ≤ (k : ℝ) + 1 / 2 := by
    intro k hk
    have := (hyw k hk).1
    have h4 : 3 * qs / 4 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 := by linarith
    have h5 : δ ^ 3 ≤ 3 * qs / (4 * hrM a b) := h3δ.trans hδM
    rw [le_div_iff₀ (by positivity)] at h5
    by_contra hlt
    push Not at hlt
    nlinarith [mul_lt_mul_of_pos_right hlt h3]
  have hk1 : ∀ k ∈ Finset.Icc (J + 1) (N + 1),
      1 ≤ (k : ℝ) + 1 / 2 ∧ a ^ 2 ≤ ((k : ℝ) + 1 / 2) ^ 2 ∧ b ^ 2 ≤ ((k : ℝ) + 1 / 2) ^ 2 ∧
        qs ≤ 2 * ((k : ℝ) + 1 / 2) * δ ^ 3 ∧ ((((k : ℝ) + 1 / 2)) * δ ^ 3) ^ 2 ∈ Dom P Q := by
    intro k hk
    have hM' := hkM k hk
    have hy := hyw k hk
    have hyd := hdom ((((k : ℝ) + 1 / 2)) * δ ^ 3) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine ⟨hM1.trans hM', ?_, ?_, ?_, ⟨by positivity, ?_, ?_⟩⟩
    · have : |a| ≤ (k : ℝ) + 1 / 2 := hMa.trans hM'
      nlinarith [sq_abs a, abs_nonneg a]
    · have : |b| ≤ (k : ℝ) + 1 / 2 := hMb.trans hM'
      nlinarith [sq_abs b, abs_nonneg b]
    · nlinarith [hy.1]
    · linarith [hyd.1]
    · linarith [hyd.2]
  have e6 : δ ^ 6 = (δ ^ 3) ^ 2 := by ring
  constructor
  · intro k hk
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk
    have e : dalQ (δ ^ 3) δ k - δ ^ 3 / 2 = ((k : ℝ) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
    rw [e]
    unfold hrAkH hrA1
    have := hr_coef_A (P := P) (Q := Q) (a := a) (b := b) hP hQ h3 hqs k1 ka kb kq kd
    refine this.trans ?_
    rw [e6]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro k hk
    have hk' : k ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc] at hk ⊢; omega
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk'
    have hqw := hwin k (by rw [Finset.mem_Icc] at hk ⊢; omega)
    have hqd := hdom (dalQ (δ ^ 3) δ k) ⟨by linarith [hqw.1], by linarith [hqw.2]⟩
    have e2 : dalQ (δ ^ 3) δ k = (((k : ℝ) + 1 / 2) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
    have hpos : 0 < etilde P Q ((((((k : ℝ) + 1 / 2) + 1 / 2)) * δ ^ 3) ^ 2) := by
      rw [e2] at hqd
      unfold etilde; exact Real.sqrt_pos.2 (mul_pos hqd.1 hqd.2)
    have e1 : 2 * hrA1 P Q (dalQ (δ ^ 3) δ k) * hrU P Q τ x (dalQ (δ ^ 3) δ k) =
        τ * (x - Real.sqrt (P * Q) * ((((k : ℝ) + 1 / 2) + 1 / 2) * δ ^ 3) ^ 2) := by
      unfold hrA1 hrU
      rw [e2]
      generalize etilde P Q ((((((k : ℝ) + 1 / 2) + 1 / 2)) * δ ^ 3) ^ 2) = e at hpos ⊢
      field_simp
    rw [e1]
    unfold hrCkH
    have := hr_coef_C (P := P) (Q := Q) (a := a) (b := b) (τ := τ) (x := x) (qs := qs) h3 hqs hτ k1 kq
    refine this.trans ?_
    rw [e6]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- `J ≥ 1` for a window on the half-shifted lattice with `q_J ≥ 3q_*/4` and `δ³ ≤ q_*/2`. -/
lemma hrH_J_pos {qs r δ : ℝ} {J N : ℤ} (hr4 : r ≤ qs / 4) (hδ : 0 < δ) (hδq : δ ^ 3 ≤ qs / 2)
    (hJN : J ≤ N + 1) (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3) δ k ∈ Set.Icc (qs - r) (qs + r)) :
    1 ≤ J := by
  have h3 : 0 < δ ^ 3 := by positivity
  have h1 := hwin J (by rw [Finset.mem_Icc]; omega)
  have e2 : dalQ (δ ^ 3) δ J = ((J : ℝ) + 1) * δ ^ 3 := by unfold dalQ; ring
  rw [e2] at h1
  by_contra hlt
  have hJ0 : J ≤ 0 := by omega
  have hJ0' : (J : ℝ) ≤ 0 := by exact_mod_cast hJ0
  nlinarith [mul_le_mul_of_nonneg_right hJ0' h3.le, h1.1]

/-- **The discrete-to-Airy limit for the closed-form coefficients on the half-shifted lattice** (`hrAkH`, `hrCkH`; sites
`q_k = (k+1)δ³`): the analogue of `discrete_airy_hahn_racah` with the same hypotheses and constants. -/
theorem discrete_airy_hahn_racah_half {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cosc ∧
      0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < D ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1) * δ ^ 3 - qs| ≤ r) ∧
        qs - D * δ ^ 2 ≤ ((J : ℝ) + 1) * δ ^ 3 ∧ ((J : ℝ) + 1) * δ ^ 3 ≤ qs ∧
        qs ≤ ((m : ℝ) + 1) * δ ^ 3 ∧ ((m : ℝ) + 1) * δ ^ 3 < qs + δ ^ 3 ∧
        turnX (hrU P Q τ x) qs (δ ^ 3) δ J ≤ -A0 ∧
        DalConclusion (hrAkH P Q a b (δ ^ 3)) (hrCkH P Q τ x a b (δ ^ 3))
          (turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3) δ) (turnX (hrU P Q τ x) qs (δ ^ 3) δ)
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
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cosc, Ctop, W, Cmu, ξ0, D, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
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
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hXJ, Hc⟩ := H δ (δ ^ 3) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  obtain ⟨hpa, hpc⟩ := hrH_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3) δ k = ((k : ℝ) + 1) * δ ^ 3 := fun k => by unfold dalQ; ring
  refine ⟨J, m, N, hrH_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    hXJ, Hc _ _ hpa hpc⟩
  have h1 := hwin k hk
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- The conclusion of `discrete_airy_hahn_racah_half` for a sequence `Y`, at scale `h = δ³`. -/
def AiryOutHalf (P Q τ x qs : ℝ) (Y : ℤ → ℝ) (Ymax A0 r δ0 C Cosc Ctop W Cmu ξ0 D h : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ Nw ∧
    (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1) * δ ^ 3 - qs| ≤ r) ∧
    qs - D * δ ^ 2 ≤ ((J : ℝ) + 1) * δ ^ 3 ∧ ((J : ℝ) + 1) * δ ^ 3 ≤ qs ∧
    qs ≤ ((m : ℝ) + 1) * δ ^ 3 ∧ ((m : ℝ) + 1) * δ ^ 3 < qs + δ ^ 3 ∧
    turnX (hrU P Q τ x) qs (δ ^ 3) δ J ≤ -A0 ∧
    ξ0 / δ ^ 3 ≤ airyXi (turnX (hrU P Q τ x) qs (δ ^ 3) δ Nw) ∧
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3) δ Nw)) ∧
      (∀ k ∈ Finset.Icc J m, |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3) δ k| ≤
        C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
      (∀ k ∈ Finset.Icc m (Nw + 1), |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3) δ k| ≤
        C * δ ^ 3 * |κ| * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3) δ k +
          Ctop * |μ| / δ / airyWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k))

/-- **Composition lemma, half-shifted lattice.**  Any `Y` solving every row `k ≥ 1` of
`jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y = 0` at a scale `0 < h ≤ δ₀³` and bounded by `Y_max`
satisfies `AiryOutHalf` (constants independent of `Y`, `h`). -/
theorem airy_chain_compose_half {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
        AiryOutHalf P Q τ x qs Y Ymax A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, -, hδ0, -, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah_half hP hQ a b τ x qs hqs hτ hκ hα hβ hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
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
  obtain ⟨J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, Hc⟩ := H δ hδ0' hδle
  obtain ⟨hxi, -, -, -, HY⟩ := Hc
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAkH P Q a b (δ ^ 3)) (hrCkH P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hlow, hup⟩ := HY Y Ymax hrows' (hbd _) (hbd _)
  exact ⟨δ, hδ0', hδle, hδ3, J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, hxi, κ, μ, hμ, hlow, hup⟩

/-- info: 'FormalResearch.Special.hrH_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hrH_perturb

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discrete_airy_hahn_racah_half

/-- info: 'FormalResearch.Special.airy_chain_compose_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_chain_compose_half

end FormalResearch.Special
