module

public import FormalResearch.Special.DiscreteAiryUnifHahnData
public import FormalResearch.Special.DiscreteAiryPhysChains

/-!
# The unified Airy matching for the Hahn `3j` chain, uniform over the shape `x ∈ [x₀, x₁]`

`hahn_chain_airy_full_unif`: fix integers `M, σ` and `0 < x₀ ≤ x₁ < 1`.  There are `r, δ₀, C, Cmu, ξ₀ > 0`, depending only on
`(M, σ, x₀, x₁)`, such that for **every** admissible node `(N, n)` whose abscissa `x_n = xLat M σ N n` lies in `[x₀, x₁]`
(rational nodes, **no parity condition** and no fixed `x`) with `1/N ≤ δ₀³`, `AiryFullAt 1 0 1 x_n √(1-x_n²) M σ Ŷ √N r δ₀ C Cmu ξ₀ (1/N)`
holds: the unified `DaiFull` of the closed-form recurrence plus `Ŷ = κ g Ai + μ g Bi` on the whole window `[q_* - r, q_* + r/2]`, with
`|μ| ≤ Cmu √N e^{-ξ₀ N}/δ`.  Also `τ = -1` (`x_n ∈ [-x₁, -x₀]`).  The key steps are `discrete_airy_full_unif`
(`DiscreteAiryUnifTheorem`, quantitative in the datum bounds) and `hahn_datum_unif` (`DiscreteAiryUnifHahnData`, the Hahn data
`A = ½√(1-q²)`, `u = τx/√(1-q²)` satisfy those bounds uniformly in `τx ∈ [x₀, x₁]`).

**Claim class: proved.**  Not formalised: the value of `κ` and `κ ≠ 0` (for the fixed-`x` chain `κ² δ → 2` is `hahn_chain_kappa_sharp`, `DiscreteAiryKappaSharpFinal`; not uniform in `x`); shapes with `x → 0` or `x → 1` (the hard-edge degeneration; the
constants blow up there); the half-integer and Racah variants.
-/

@[expose] public section

open Set Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Uniform `discrete_airy_hahn_racah_full`** for `P = 1, Q = 0`, with constants uniform over `τ x ∈ [x₀, x₁]`. -/
theorem discrete_airy_hahn_full_unif (a b x0 x1 : ℝ) (hx0 : 0 < x0) (hx01 : x0 ≤ x1) (hx1 : x1 < 1) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ τ x : ℝ, τ ^ 2 = 1 → τ * x ∈ Icc x0 x1 → ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∃ J m N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - x ^ 2)| ≤ r) ∧
        Real.sqrt (1 - x ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
        ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - x ^ 2) - r + δ ^ 3 ∧
        Real.sqrt (1 - x ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
        ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - x ^ 2) + δ ^ 3 ∧
        Real.sqrt (1 - x ^ 2) + r / 4 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧
        ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - x ^ 2) + r / 2 ∧
        DaiFull (hrAk 1 0 a b (δ ^ 3)) (hrCk 1 0 τ x a b (δ ^ 3))
          (turnX (hrU 1 0 τ x) (Real.sqrt (1 - x ^ 2)) (δ ^ 3 / 2) δ)
          (fun k => langerAmp (hrU 1 0 τ x) (hrA1 1 0) (Real.sqrt (1 - x ^ 2)) (dalQ (δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨ρ, Ku, m, aLo, aHi, KA, hρ, hKu, hm, haLo, haLH, hKA, hdat⟩ := hahn_datum_unif hx0 hx01 hx1
  have hx1' : x1 ^ 2 < 1 := by nlinarith
  obtain ⟨cmin, hcmin⟩ : ∃ cmin, cmin = Real.sqrt (1 - x1 ^ 2) := ⟨_, rfl⟩
  have hcminp : 0 < cmin := by rw [hcmin]; exact Real.sqrt_pos.2 (by linarith)
  obtain ⟨E, hEd⟩ : ∃ E, E = (2 * (a ^ 2 + b ^ 2 + 1 / 3) + 4 * |a * b|) / cmin ^ 2 := ⟨_, rfl⟩
  have hE : 0 ≤ E := by rw [hEd]; positivity
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hrρ, hδ0, hδ01, hC, hCmu, hξ0, H⟩ :=
    discrete_airy_full_unif ρ Ku m aLo aHi KA E hρ hKu hm haLo haLH hKA hE
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * cmin / (4 * hrM a b)) (cmin / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨r, min δ0 (min 1 (min (3 * cmin / (4 * hrM a b)) (cmin / 2))), C, Cmu, ξ0, hr, lt_min hδ0 hδip, hC, hCmu,
    hξ0, ?_⟩
  intro τ x hτ hy δ hδ hδδ0
  obtain ⟨hρqs, hdom, hD⟩ := hdat τ x hτ hy
  have hx2 : x ^ 2 = (τ * x) ^ 2 := by rw [mul_pow, hτ, one_mul]
  have hxy0 : x0 ≤ τ * x := hy.1
  have hxy1 : τ * x ≤ x1 := hy.2
  have hqs : cmin ≤ Real.sqrt (1 - x ^ 2) := by
    rw [hcmin]; exact Real.sqrt_le_sqrt (by rw [hx2]; nlinarith only [hxy0, hxy1, hx0])
  have hqsp : 0 < Real.sqrt (1 - x ^ 2) := lt_of_lt_of_le hcminp hqs
  have hδ1' : δ ≤ δ0 := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM' : δ ≤ 3 * cmin / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq' : δ ≤ cmin / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδM : δ ≤ 3 * Real.sqrt (1 - x ^ 2) / (4 * hrM a b) :=
    hδM'.trans (by gcongr)
  have hδq : δ ≤ Real.sqrt (1 - x ^ 2) / 2 := by linarith
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m', N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, Hc⟩ := H hD δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ Real.sqrt (1 - x ^ 2) / 4 := hrρ.trans hρqs
  obtain ⟨hpa, hpc⟩ := hr_perturb (P := 1) (Q := 0) (by norm_num) (by norm_num) a b τ x (Real.sqrt (1 - x ^ 2)) hqsp hτ
    hr4 hrρ hdom hδ hδ1 hδM hwin
  have hEE : hrE 1 0 a b (Real.sqrt (1 - x ^ 2)) ≤ E := by
    have hc2 : cmin ^ 2 ≤ Real.sqrt (1 - x ^ 2) ^ 2 := by gcongr
    have h1 : 2 * (a ^ 2 + b ^ 2 + 1 / 3) / Real.sqrt (1 - x ^ 2) ^ 2 ≤ E := by
      rw [hEd]
      refine div_le_div₀ (by positivity) ?_ (by positivity) hc2
      have := abs_nonneg (a * b); linarith
    have h2 : 4 * |a * b| / Real.sqrt (1 - x ^ 2) ^ 2 ≤ E := by
      rw [hEd]
      refine div_le_div₀ (by positivity) ?_ (by positivity) hc2
      nlinarith [sq_nonneg a, sq_nonneg b]
    unfold hrE
    simp only [mul_zero, Real.sqrt_zero, zero_mul, zero_div, zero_add]
    exact max_le h1 h2
  have hδ6 : 0 ≤ δ ^ 6 := by positivity
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  refine ⟨J, m', N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJN, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    by rw [← e2]; exact hqN, by
      have := hqN1
      rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by unfold dalQ; push_cast; ring]
      exact this,
    Hc _ _ (fun k hk => (hpa k hk).trans (mul_le_mul_of_nonneg_right hEE hδ6))
      (fun k hk => (hpc k hk).trans (mul_le_mul_of_nonneg_right hEE hδ6))⟩
  have h1 := hwin k hk
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- info: 'FormalResearch.Special.discrete_airy_hahn_full_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_full_unif

/-- **Uniform composition lemma** (`airy_full_compose` with constants uniform over `τ x ∈ [x₀, x₁]`). -/
theorem airy_full_compose_unif (a b x0 x1 : ℝ) (hx0 : 0 < x0) (hx01 : x0 ≤ x1) (hx1 : x1 < 1) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ τ x : ℝ, τ ^ 2 = 1 → τ * x ∈ Icc x0 x1 → ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAk 1 0 a b h) (hrCk 1 0 τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
        AiryFullAt 1 0 τ x (Real.sqrt (1 - x ^ 2)) a b Y Ymax r δ0 C Cmu ξ0 h := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ := discrete_airy_hahn_full_unif a b x0 x1 hx0 hx01 hx1
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro τ x hτ hy h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ0', hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc⟩ := H τ x hτ hy δ hδ0' hδle
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) N,
      jac (hrAk 1 0 a b (δ ^ 3)) (hrCk 1 0 τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise Y Ymax hrows' (hbd _) (hbd _)
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans (hbd 0)
  refine ⟨δ, hδ0', hδle, hδ3, J, m, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, hμ, ?_, hpt⟩
  refine hμ.trans ?_
  have hxi := Hc.1
  have : Real.exp (-airyXi (turnX (hrU 1 0 τ x) (Real.sqrt (1 - x ^ 2)) (δ ^ 3 / 2) δ N)) ≤
      Real.exp (-ξ0 / δ ^ 3) := by
    apply Real.exp_le_exp.2
    rw [neg_div]
    exact neg_le_neg hxi
  have : Cmu * Ymax * Real.exp (-airyXi (turnX (hrU 1 0 τ x) (Real.sqrt (1 - x ^ 2)) (δ ^ 3 / 2) δ N)) ≤
      Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
  exact div_le_div_of_nonneg_right this hδ0'.le

/-- info: 'FormalResearch.Special.airy_full_compose_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_full_compose_unif

/-- **The unified Airy matching for the actual `3j` chain, uniform over all lattice nodes with `x_n ∈ [x₀, x₁]`**
(`τ = +1`).  The constants depend only on `(M, σ, x₀, x₁)`; every node `(N, n)` with `x_n ∈ [x₀, x₁]` and `1/N ≤ δ₀³` is
covered (no parity condition, no fixed shape). -/
theorem hahn_chain_airy_full_unif (M σ : ℤ) (x0 x1 : ℝ) (hx0 : 0 < x0) (hx01 : x0 ≤ x1) (hx1 : x1 < 1) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        x0 ≤ (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) → (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) ≤ x1 →
        1 / (N : ℝ) ≤ δ0 ^ 3 →
        AiryFullAt 1 0 1 (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ)
          (Real.sqrt (1 - (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) ^ 2)) (M : ℝ) (σ : ℝ)
          (hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n)) (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ := airy_full_compose_unif (M : ℝ) (σ : ℝ) x0 x1 hx0 hx01 hx1
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro N n hN hn hxa hxb hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine H 1 _ (by norm_num) ⟨by simpa using hxa, by simpa using hxb⟩ (1 / (N : ℝ)) _ _ (by positivity) hNδ
    (fun k hk => hahn_class_chain M σ N _ hN0 k hk) ?_
  intro k
  exact hahn_chain_abs_le M σ N hN n hn k

/-- **The same for `τ = -1`** (`x_n ∈ [-x₁, -x₀]`, the twisted chain `(-1)^k Ŷ_k`). -/
theorem hahn_chain_airy_full_neg_unif (M σ : ℤ) (x0 x1 : ℝ) (hx0 : 0 < x0) (hx01 : x0 ≤ x1) (hx1 : x1 < 1) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        -x1 ≤ (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) → (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) ≤ -x0 →
        1 / (N : ℝ) ≤ δ0 ^ 3 →
        AiryFullAt 1 0 (-1) (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ)
          (Real.sqrt (1 - (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n : ℝ) ^ 2)) (M : ℝ) (σ : ℝ)
          (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) j)
          (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ := airy_full_compose_unif (M : ℝ) (σ : ℝ) x0 x1 hx0 hx01 hx1
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro N n hN hn hxa hxb hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine H (-1) _ (by norm_num) ⟨by linarith, by linarith⟩ (1 / (N : ℝ)) _ _ (by positivity) hNδ
    (fun k hk => hahn_class_chain_neg M σ N _ hN0 k hk) ?_
  intro k
  have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
  rw [abs_mul, h1, one_mul]
  exact hahn_chain_abs_le M σ N hN n hn k

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_unif

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_neg_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_neg_unif

end FormalResearch.Special
