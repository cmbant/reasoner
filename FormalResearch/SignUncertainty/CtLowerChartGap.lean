module

public import FormalResearch.SignUncertainty.CtLowerDefs
public import FormalResearch.SignUncertainty.HankelChartCubic
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible
public import FormalResearch.SignUncertainty.HankelBootAssembly
public import FormalResearch.SignUncertainty.CtCfuData

/-!
# `chart_gap`: the Langer chart inversion at the first Airy node (F1, `thm:ct-lower`)

`constant_terms_lower.tex`: `ct:langer-inv`, `ct:phic-exp`, `ct:five-term-node` and the first step of "Proof of the lower
bound in `thm:ct-lower`(i)".  **Proved** (given `κ_ε < 0`, see `ctChartGap`):

* `ctPsi_taylor`: near `0⁻`, `ctPsi ε` is the smooth `ψ_ε` of `cfu_psi_langer` (unique positive root `τ₀`), with
  `ψ_ε(a) = ψ₀ + γ₀ a + O(a²)`;
* `phi_expansion_core`: the root `φ = φ_c(a₁)` of `û(φ) = a₁` exists in `[-3, -2]` (intermediate value theorem) and
  `φ = a₁ - 2^{-2/3}ψ₀ c^{-1/3} - γ₀ a₁ c⁻¹ + O(c^{-4/3})`;
* `lam_psi0`: `2^{-2/3}ψ₀ = β₁κ_ε`; `five_term_poly`, `five_term_bound`: the exact algebra behind
  `c ξ(φ_c(a₁)) = Δ₅^ε(c) + O(c⁻¹)` (`ctNode_expansion`, with the model `ctChartX` of `cξ` of `hankelXi_expansion`);
* `ctChartGap_eps`, **`ctChartGap`**: for feasible `f` with `M[f] = 1` and `T ≤ Δ₅^ε(c) - K c⁻¹ log c`,
  `ũ(T/c) - φ_c(a₁) ≥ (Kβ₁/2) c^{-4/3} log c` (large `c`).  The point `ũ₁` is produced by
  `hankel_quantC1_of_feasible` (which needs `T < cξ(a₁)`, i.e. `κ_ε < 0` here) and `hankelBoot_uT_range`.

The hypothesis `κ_ε < 0` (`ctKappa ε < 0`, TeX `ct:theta1` numerics: `I₀ ≈ 0.243 < 3 log 2`) is the only input not
proved here.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty
open FormalResearch.CohnElkies FormalResearch.Special
/-- the exact polynomial identity behind the five-term expansion at the node -/
theorem five_term_poly {k β a₁ θ1 θ3 P : ℝ} (hk : k ≠ 0) (hβ : β ≠ 0) (hP : P ≠ 0) :
    let A := -a₁ / β
    let κ := θ1 / P
    let γ0 := -(7 / 25 * θ1 + 12 / P * θ3)
    let φ0 := a₁ - β * κ * k⁻¹ - γ0 * a₁ * (k⁻¹) ^ 3
    (k ^ 3 / P - φ0 * k / β + 9 * P / 25 * (φ0 / β) ^ 2 * k⁻¹) -
      (k ^ 3 / P + A * k + κ + 9 * P / 25 * A ^ 2 * k⁻¹ + A * (θ1 + 12 / P * θ3) * (k⁻¹) ^ 2) =
    (k⁻¹) ^ 3 * (9 * P / (25 * β ^ 2)) *
      ((-(β * κ)) ^ 2 + 2 * a₁ * (-(γ0 * a₁)) * k⁻¹ + 2 * (-(β * κ)) * (-(γ0 * a₁)) * (k⁻¹) ^ 2 +
        (-(γ0 * a₁)) ^ 2 * (k⁻¹) ^ 4) := by
  intro A κ γ0 φ0
  simp only [A, κ, γ0, φ0]
  field_simp
  ring

/-- the five-term approximation at a point `φ` within `K k⁻⁴` of `φ₀`, with a constant independent of `k` -/
theorem five_term_bound {β a₁ θ1 θ3 P K : ℝ} (hβ : 0 < β) (hP : 0 < P) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k φ : ℝ, 1 ≤ k → |φ| ≤ 3 →
    |φ - (a₁ - β * (θ1 / P) * k⁻¹ - (-(7 / 25 * θ1 + 12 / P * θ3)) * a₁ * (k⁻¹) ^ 3)| ≤ K * (k⁻¹) ^ 4 →
    |(k ^ 3 / P - φ * k / β + 9 * P / 25 * (φ / β) ^ 2 * k⁻¹) -
      (k ^ 3 / P + (-a₁ / β) * k + θ1 / P + 9 * P / 25 * (-a₁ / β) ^ 2 * k⁻¹ +
        (-a₁ / β) * (θ1 + 12 / P * θ3) * (k⁻¹) ^ 2)| ≤ C * (k⁻¹) ^ 3 := by
  set γ0 : ℝ := -(7 / 25 * θ1 + 12 / P * θ3) with hγ
  set κ : ℝ := θ1 / P with hκ
  set p : ℝ := -(β * κ) with hp
  set p3 : ℝ := -(γ0 * a₁) with hp3
  set q : ℝ := 9 * P / (25 * β ^ 2) with hq
  have hq0 : 0 ≤ q := by positivity
  refine ⟨K / β + q * K * (6 + K) + q * (p ^ 2 + 2 * |a₁| * |p3| + 2 * |p| * |p3| + p3 ^ 2), by positivity,
    fun k φ hk hφ hφ0 => ?_⟩
  have hk0 : 0 < k := by linarith
  set s : ℝ := k⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hk0
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ hk
  set φ₀ : ℝ := a₁ - β * κ * s - γ0 * a₁ * s ^ 3 with hφ₀
  have hid := five_term_poly (k := k) (β := β) (a₁ := a₁) (θ1 := θ1) (θ3 := θ3) (P := P) hk0.ne' hβ.ne' hP.ne'
  simp only at hid
  have e : (k ^ 3 / P - φ * k / β + 9 * P / 25 * (φ / β) ^ 2 * k⁻¹) -
      (k ^ 3 / P + (-a₁ / β) * k + θ1 / P + 9 * P / 25 * (-a₁ / β) ^ 2 * k⁻¹ +
        (-a₁ / β) * (θ1 + 12 / P * θ3) * (k⁻¹) ^ 2) =
      (-(φ - φ₀) * k / β + q * s * ((φ - φ₀) * (φ + φ₀))) +
        s ^ 3 * q * (p ^ 2 + 2 * a₁ * p3 * s + 2 * p * p3 * s ^ 2 + p3 ^ 2 * s ^ 4) := by
    rw [← hid]
    have hβ' : β ≠ 0 := hβ.ne'
    simp only [hs, hφ₀, hq, hκ, hγ]
    field_simp
    ring
  rw [e]
  have hr : |φ - φ₀| ≤ K * s ^ 4 := hφ0
  clear_value φ₀ s
  clear e hid hφ0 hφ₀
  have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
  have hs4 : s ^ 4 ≤ s ^ 3 := by nlinarith [pow_nonneg hs0.le 3]
  have hs5 : s ^ 5 ≤ s ^ 3 := by nlinarith [pow_nonneg hs0.le 3, pow_nonneg hs0.le 4]
  have hk_s : k * s ^ 4 = s ^ 3 := by
    have : k * s = 1 := by rw [hs]; field_simp
    calc k * s ^ 4 = (k * s) * s ^ 3 := by ring
      _ = s ^ 3 := by rw [this, one_mul]
  -- first part
  have t1 : |-(φ - φ₀) * k / β| ≤ K / β * s ^ 3 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hk0, abs_of_pos hβ]
    rw [div_le_iff₀ hβ]
    calc |φ - φ₀| * k ≤ K * s ^ 4 * k := mul_le_mul_of_nonneg_right hr hk0.le
      _ = K * s ^ 3 := by rw [mul_assoc, mul_comm (s ^ 4) k, hk_s]
      _ = K / β * s ^ 3 * β := by field_simp
  have hsum : |φ + φ₀| ≤ 6 + K := by
    have h1 : φ + φ₀ = 2 * φ - (φ - φ₀) := by ring
    rw [h1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]
    have : K * s ^ 4 ≤ K := by nlinarith [mul_le_mul_of_nonneg_left hs4 hK]
    linarith
  have t2 : |q * s * ((φ - φ₀) * (φ + φ₀))| ≤ q * K * (6 + K) * s ^ 3 := by
    rw [abs_mul (q * s), abs_of_nonneg (by positivity : 0 ≤ q * s), abs_mul (φ - φ₀)]
    have h1 : |φ - φ₀| * |φ + φ₀| ≤ K * s ^ 4 * (6 + K) :=
      mul_le_mul hr hsum (abs_nonneg _) (by positivity)
    calc q * s * (|φ - φ₀| * |φ + φ₀|) ≤ q * s * (K * s ^ 4 * (6 + K)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = q * K * (6 + K) * s ^ 5 := by ring
      _ ≤ q * K * (6 + K) * s ^ 3 := mul_le_mul_of_nonneg_left hs5 (by positivity)
  have t3 : |s ^ 3 * q * (p ^ 2 + 2 * a₁ * p3 * s + 2 * p * p3 * s ^ 2 + p3 ^ 2 * s ^ 4)| ≤
      q * (p ^ 2 + 2 * |a₁| * |p3| + 2 * |p| * |p3| + p3 ^ 2) * s ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 3), abs_of_nonneg hq0]
    have h1 : |p ^ 2 + 2 * a₁ * p3 * s + 2 * p * p3 * s ^ 2 + p3 ^ 2 * s ^ 4| ≤
        p ^ 2 + 2 * |a₁| * |p3| + 2 * |p| * |p3| + p3 ^ 2 := by
      have a1 : |2 * a₁ * p3 * s| ≤ 2 * |a₁| * |p3| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hs0]
        have : 0 ≤ 2 * |a₁| * |p3| := by positivity
        nlinarith
      have a2 : |2 * p * p3 * s ^ 2| ≤ 2 * |p| * |p3| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two, abs_pow, abs_of_pos hs0]
        have : 0 ≤ 2 * |p| * |p3| := by positivity
        have : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
        nlinarith [abs_nonneg p, abs_nonneg p3]
      have a3 : |p3 ^ 2 * s ^ 4| ≤ p3 ^ 2 := by
        rw [abs_mul, abs_pow, abs_pow, abs_of_pos hs0, sq_abs]
        have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le hs1
        nlinarith [sq_nonneg p3]
      calc _ ≤ |p ^ 2| + |2 * a₁ * p3 * s| + |2 * p * p3 * s ^ 2| + |p3 ^ 2 * s ^ 4| := by
            refine (abs_add_le _ _).trans ?_
            refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
            exact add_le_add ((abs_add_le _ _).trans le_rfl) le_rfl
        _ ≤ _ := by rw [abs_pow, sq_abs]; linarith
    calc s ^ 3 * q * |p ^ 2 + 2 * a₁ * p3 * s + 2 * p * p3 * s ^ 2 + p3 ^ 2 * s ^ 4| ≤
        s ^ 3 * q * (p ^ 2 + 2 * |a₁| * |p3| + 2 * |p| * |p3| + p3 ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  refine (abs_add_le _ _).trans ?_
  have t12 := abs_add_le (-(φ - φ₀) * k / β) (q * s * ((φ - φ₀) * (φ + φ₀)))
  linarith only [t1, t2, t3, t12]


set_option maxHeartbeats 1000000 in
/-- Pure-analysis core of the expansion of `φ_c(a₁)`: with `s = c^{-1/3}`, `û(φ) = φ + λ s ψ(μ s² φ)` and
`λ μ = 1`, any root of `û(φ) = a₁` in `[-3, -2]` satisfies `φ = a₁ - λψ₀ s - γ₀ a₁ s³ + O(s⁴)`, and a root exists. -/
lemma phi_expansion_core {ψ : ℝ → ℝ} {ρ C ψ0 γ0 a₁ lam mu : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hlam : 0 < lam) (hmu : 0 < mu) (hlm : lam * mu = 1)
    (hψ : ∀ a, -ρ < a → a < 0 → |ψ a - ψ0 - γ0 * a| ≤ C * a ^ 2)
    (hcont : ContinuousOn ψ (Ioo (-ρ) 0)) (ha₁ : -2.35 < a₁ ∧ a₁ < -2.33) :
    ∃ s₀ K : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      (∃ φ ∈ Icc (-3 : ℝ) (-2), φ + lam * s * ψ (mu * s ^ 2 * φ) = a₁) ∧
      ∀ φ ∈ Icc (-3 : ℝ) (-2), φ + lam * s * ψ (mu * s ^ 2 * φ) = a₁ →
        |φ - (a₁ - lam * ψ0 * s - γ0 * a₁ * s ^ 3)| ≤ K * s ^ 4 := by
  set M : ℝ := |ψ0| + |γ0| * ρ + C * ρ ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨min (ρ / (4 * mu)) (min 1 (1 / (10 * (lam * M + 1)))), lam * (|γ0| * M + 9 * C * mu ^ 2), ?_, ?_⟩
  · have : 0 < lam * M + 1 := by positivity
    positivity
  intro s hs hs0
  have hs1 : s ≤ 1 := hs0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsρ : s ≤ ρ / (4 * mu) := hs0.trans (min_le_left _ _)
  have hsM : s ≤ 1 / (10 * (lam * M + 1)) := hs0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlsM : lam * s * M ≤ 1 / 10 := by
    have h1 : 0 < lam * M + 1 := by positivity
    have : s * (10 * (lam * M + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hsM
    nlinarith [mul_nonneg hlam.le hM0]
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hmus : mu * s ^ 2 * 3 < ρ := by
    have : mu * s ≤ ρ / 4 := by
      rw [le_div_iff₀ (by positivity)] at hsρ; nlinarith
    nlinarith
  -- the point `a_φ ∈ (-ρ, 0)`
  have hmem : ∀ φ ∈ Icc (-3 : ℝ) (-2), -ρ < mu * s ^ 2 * φ ∧ mu * s ^ 2 * φ < 0 := by
    intro φ hφ
    have hp : 0 < mu * s ^ 2 := by positivity
    constructor <;> nlinarith [hφ.1, hφ.2]
  have hψM : ∀ φ ∈ Icc (-3 : ℝ) (-2), |ψ (mu * s ^ 2 * φ)| ≤ M := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := hmem φ hφ
    have h := hψ _ h1 h2
    have hab : |mu * s ^ 2 * φ| ≤ ρ := by rw [abs_le]; constructor <;> linarith
    have e : ψ (mu * s ^ 2 * φ) = ψ0 + γ0 * (mu * s ^ 2 * φ) + (ψ (mu * s ^ 2 * φ) - ψ0 - γ0 * (mu * s ^ 2 * φ)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) h).trans ?_
    rw [abs_mul]
    have h3 : (mu * s ^ 2 * φ) ^ 2 ≤ ρ ^ 2 := by
      have := sq_le_sq' (by linarith [abs_le.1 hab]) (abs_le.1 hab).2
      simpa using this
    nlinarith [abs_nonneg γ0, mul_le_mul_of_nonneg_left hab (abs_nonneg γ0)]
  constructor
  · -- existence by the intermediate value theorem
    have hcg : ContinuousOn (fun φ : ℝ => φ + lam * s * ψ (mu * s ^ 2 * φ)) (Icc (-3 : ℝ) (-2)) := by
      refine continuousOn_id.add (continuousOn_const.mul ?_)
      refine hcont.comp (by fun_prop) (fun φ hφ => ?_)
      exact hmem φ hφ
    have hl : (fun φ : ℝ => φ + lam * s * ψ (mu * s ^ 2 * φ)) (-3) ≤ a₁ := by
      have := hψM (-3) ⟨le_rfl, by norm_num⟩
      have h2 := abs_le.1 this
      simp only
      nlinarith [mul_le_mul_of_nonneg_left h2.2 (by positivity : 0 ≤ lam * s)]
    have hr : a₁ ≤ (fun φ : ℝ => φ + lam * s * ψ (mu * s ^ 2 * φ)) (-2) := by
      have := hψM (-2) ⟨by norm_num, le_rfl⟩
      have h2 := abs_le.1 this
      simp only
      nlinarith [mul_le_mul_of_nonneg_left h2.1 (by positivity : 0 ≤ lam * s)]
    obtain ⟨φ, hφ, hφe⟩ := intermediate_value_Icc (by norm_num : (-3 : ℝ) ≤ -2) hcg ⟨hl, hr⟩
    exact ⟨φ, hφ, hφe⟩
  · intro φ hφ hroot
    obtain ⟨h1, h2⟩ := hmem φ hφ
    have h := hψ _ h1 h2
    have hM' := hψM φ hφ
    have hφa : φ - a₁ = -(lam * s * ψ (mu * s ^ 2 * φ)) := by linarith
    have hφa' : |φ - a₁| ≤ lam * s * M := by
      rw [hφa, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam * s)]
      exact mul_le_mul_of_nonneg_left hM' (by positivity)
    set e : ℝ := ψ (mu * s ^ 2 * φ) - ψ0 - γ0 * (mu * s ^ 2 * φ) with hed
    have he : |e| ≤ 9 * C * mu ^ 2 * s ^ 4 := by
      refine h.trans ?_
      have : (mu * s ^ 2 * φ) ^ 2 = mu ^ 2 * s ^ 4 * φ ^ 2 := by ring
      rw [this]
      have hφ2 : φ ^ 2 ≤ 9 := by nlinarith [hφ.1, hφ.2]
      nlinarith [mul_nonneg hC (mul_nonneg (sq_nonneg mu) (pow_nonneg hs.le 4))]
    have eq : φ - (a₁ - lam * ψ0 * s - γ0 * a₁ * s ^ 3) = -(γ0 * s ^ 3 * (φ - a₁)) - lam * s * e := by
      have hψe : ψ (mu * s ^ 2 * φ) = ψ0 + γ0 * (mu * s ^ 2 * φ) + e := by rw [hed]; ring
      rw [hψe] at hroot
      have h3 : lam * s * (ψ0 + γ0 * (mu * s ^ 2 * φ) + e) = lam * s * ψ0 + γ0 * s ^ 3 * φ + lam * s * e := by
        linear_combination (γ0 * s ^ 3 * φ) * hlm
      rw [h3] at hroot
      linarith
    rw [eq]
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    have n1 : |γ0 * s ^ 3 * (φ - a₁)| ≤ |γ0| * s ^ 3 * (lam * s * M) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.le 3)]
      exact mul_le_mul_of_nonneg_left hφa' (by positivity)
    have n2 : |lam * s * e| ≤ lam * s * (9 * C * mu ^ 2 * s ^ 4) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam * s)]
      exact mul_le_mul_of_nonneg_left he (by positivity)
    have s4 : s ^ 5 ≤ s ^ 4 := by nlinarith [pow_nonneg hs.le 4]
    have : lam * (|γ0| * M + 9 * C * mu ^ 2) * s ^ 4 ≥ |γ0| * s ^ 3 * (lam * s * M) + lam * s * (9 * C * mu ^ 2 * s ^ 4) := by
      have h5 : lam * (9 * C * mu ^ 2) * s ^ 5 ≤ lam * (9 * C * mu ^ 2) * s ^ 4 :=
        mul_le_mul_of_nonneg_left s4 (by positivity)
      have eL : lam * (|γ0| * M + 9 * C * mu ^ 2) * s ^ 4 =
          lam * |γ0| * M * s ^ 4 + lam * (9 * C * mu ^ 2) * s ^ 4 := by ring
      have eR : |γ0| * s ^ 3 * (lam * s * M) + lam * s * (9 * C * mu ^ 2 * s ^ 4) =
          lam * |γ0| * M * s ^ 4 + lam * (9 * C * mu ^ 2) * s ^ 5 := by ring
      rw [eL, eR]; linarith only [h5]
    exact (add_le_add n1 n2).trans this



/-- `ctPsi ε` is the smooth function `ψ_ε` of `cfu_psi_langer` near `0⁻`, with its Taylor data. -/
lemma ctPsi_taylor {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ContinuousOn (ctPsi ε) (Ioo (-ρ) 0) ∧
      ∀ a : ℝ, -ρ < a → a < 0 →
        |ctPsi ε a - (12 / π ^ 2) ^ ((1 : ℝ) / 3) * CtOuter.ctTheta1 ε -
            (-(7 / 25 * CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε)) * a| ≤ C * a ^ 2 := by
  obtain ⟨ρ, τ0, ψ, Ξ, hρ, hψ, hΞ, hmain, hψ0, hψ1, -, -, -, ⟨C, hC⟩⟩ := CtCfu.cfu_psi_langer hε
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ), ContinuousAt ψ a := by
    have h1 : ContDiffAt ℝ 1 ψ 0 := hψ.of_le (by simp)
    have := h1.eventually (by simp)
    filter_upwards [this] with a ha using ha.continuousAt
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp hev
  have hctPsi : ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a = ψ a := by
    intro a ha
    obtain ⟨hpos, hphi, huniq, hψa, -⟩ := hmain a ha
    have hspec : 0 < ctTau0 a ∧ edgePhi (hankelEdgeM (ctTau0 a)) (ctTau0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) :=
      Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧ edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2))
        ⟨τ0 a, hpos, hphi⟩
    have : ctTau0 a = τ0 a := huniq _ hspec.1 hspec.2
    unfold ctPsi
    rw [this, hψa]
  refine ⟨min ρ r, |C|, lt_min hρ hr, abs_nonneg _, ?_, ?_⟩
  · have hsub : Ioo (-(min ρ r)) 0 ⊆ Ioo (-ρ) 0 := fun a ha =>
      ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ha.1, ha.2⟩
    have hc : ContinuousOn ψ (Ioo (-(min ρ r)) 0) := by
      intro a ha
      refine (hrr ?_).continuousWithinAt
      rw [Real.dist_eq, sub_zero]
      have := ha.1
      have h2 := ha.2
      rw [abs_lt]
      constructor
      · have := min_le_right ρ r; linarith
      · linarith [lt_min hρ hr]
    exact hc.congr (fun a ha => hctPsi a (hsub ha))
  · intro a ha1 ha2
    have haρ : -ρ < a := lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ha1
    rw [hctPsi a ⟨haρ, ha2⟩]
    have hab : |a| < ρ := by rw [abs_lt]; exact ⟨haρ, by linarith⟩
    have h := (hC a hab).1
    rw [hψ0, hψ1] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg a)


/-- `2^{-2/3} · ψ₀ = β₁ κ_ε`, i.e. `2^{-2/3}(12/π²)^{1/3} θ₁ = β₁ θ₁/π²` (`ct:psi-coeffs`, `ct:five-term-node`). -/
lemma lam_psi0 (θ1 : ℝ) :
    (2 : ℝ) ^ (-(2 / 3) : ℝ) * ((12 / π ^ 2) ^ ((1 : ℝ) / 3) * θ1) = hankelBeta1 * (θ1 / π ^ 2) := by
  have h := CtCfu.d0_mul_beta
  have hd : (12 / π ^ 2) ^ ((1 : ℝ) / 3) = (CtCfu.d0)⁻¹ := by
    unfold CtCfu.d0; rw [← Real.inv_rpow (by positivity), inv_div]
  have hb : hankelBeta1 = (π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3) := rfl
  have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]
  have hd0 := CtCfu.d0_pos
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  rw [hd, h2, hb]
  generalize (π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3) = B at h ⊢
  generalize (2 : ℝ) ^ ((2 : ℝ) / 3) = t at h hp2 ⊢
  generalize CtCfu.d0 = d at h hd0 ⊢
  have hB : B ≠ 0 := by
    intro hB0; rw [hB0, mul_zero] at h; have : (0 : ℝ) < π ^ 2 := by positivity
    linarith
  have hπ : π ^ 2 ≠ 0 := by positivity
  rw [← h]
  field_simp

/-- The model `c/π² - x c^{1/3}/β₁ + (9π²/25)(x/β₁)² c^{-1/3}` of `c ξ(x)` (`ct:langer-inv`, `x = ũ = -v`). -/
noncomputable def ctChartX (c x : ℝ) : ℝ :=
  c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1 + 9 * π ^ 2 / 25 * (x / hankelBeta1) ^ 2 * c ^ (-(1 / 3) : ℝ)

lemma rpow_third_facts {c : ℝ} (hc : 0 < c) :
    (c ^ (1 / 3 : ℝ)) ^ 3 = c ∧ c ^ (-(1 / 3) : ℝ) = (c ^ (1 / 3 : ℝ))⁻¹ ∧
      c ^ (-(2 / 3) : ℝ) = ((c ^ (1 / 3 : ℝ))⁻¹) ^ 2 ∧ c ^ (-(4 / 3) : ℝ) = ((c ^ (1 / 3 : ℝ))⁻¹) ^ 4 := by
  refine ⟨?_, Real.rpow_neg hc.le _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  · rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg (by positivity)]; norm_num
  · rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg (by positivity)]; norm_num

/-- `ctDelta5` in the variable `k = c^{1/3}`. -/
lemma ctDelta5_eq_k {ε c : ℝ} (hc : 0 < c) :
    ctDelta5 ε c = (c ^ (1 / 3 : ℝ)) ^ 3 / π ^ 2 + (-airyZero 1 / hankelBeta1) * c ^ (1 / 3 : ℝ) +
      CtOuter.ctTheta1 ε / π ^ 2 + 9 * π ^ 2 / 25 * (-airyZero 1 / hankelBeta1) ^ 2 * (c ^ (1 / 3 : ℝ))⁻¹ +
        (-airyZero 1 / hankelBeta1) * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε) *
          ((c ^ (1 / 3 : ℝ))⁻¹) ^ 2 := by
  obtain ⟨h3, h1, h2, -⟩ := rpow_third_facts hc
  have hA : airyOrderCoeff = -airyZero 1 / hankelBeta1 := by
    unfold airyOrderCoeff; rw [abs_of_neg (airyZero_neg 1)]
  unfold ctDelta5 ctKappa ctC1Langer ctD2star
  rw [h3, h1, h2, hA]

lemma ctChartX_eq_k {c x : ℝ} (hc : 0 < c) :
    ctChartX c x = (c ^ (1 / 3 : ℝ)) ^ 3 / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1 +
      9 * π ^ 2 / 25 * (x / hankelBeta1) ^ 2 * (c ^ (1 / 3 : ℝ))⁻¹ := by
  obtain ⟨h3, h1, -, -⟩ := rpow_third_facts hc
  unfold ctChartX; rw [h3, h1]

set_option maxHeartbeats 800000 in
/-- **The node `φ_c(a₁)` and the five-term expansion** (`ct:phic-exp`, `ct:five-term-node`).  For `ε = ±1` there are
`C, c₀` such that for `c ≥ c₀` the equation `û(φ) = a₁` has a solution `φ ∈ [-3, -2]`, and every solution satisfies
`|c ξ-model(φ) - Δ₅^ε(c)| ≤ C c⁻¹` (`ctChartX c φ` is the model of `c ξ(φ)` of `ct:langer-inv`). -/
theorem ctNode_expansion {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C c₀ : ℝ, 3e6 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      (∃ φ ∈ Icc (-3 : ℝ) (-2), ctUhat ε c φ = airyZero 1) ∧
      ∀ φ ∈ Icc (-3 : ℝ) (-2), ctUhat ε c φ = airyZero 1 →
        |ctChartX c φ - ctDelta5 ε c| ≤ C * c⁻¹ := by
  obtain ⟨ρ, C0, hρ, hC0, hcont, htay⟩ := ctPsi_taylor hε
  have hlam : (0 : ℝ) < (2 : ℝ) ^ (-(2 / 3) : ℝ) := by positivity
  have hmu : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have hlm : (2 : ℝ) ^ (-(2 / 3) : ℝ) * (2 : ℝ) ^ ((2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  obtain ⟨s₀, K, hs₀, hcore⟩ := phi_expansion_core hρ hC0 hlam hmu hlm htay hcont (airyZero_one)
  have hev : ∀ᶠ c : ℝ in atTop, c ^ (-(1 / 3) : ℝ) < min s₀ 1 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually (gt_mem_nhds (lt_min hs₀ one_pos))
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp hev
  set β := hankelBeta1 with hβ
  have hβ0 : 0 < β := hankelBeta1_pos
  set a₁ := airyZero 1 with ha₁
  set θ1 := CtOuter.ctTheta1 ε with hθ1
  set θ3 := CtOuter.ctTheta3 ε with hθ3
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  obtain ⟨C5, hC5, hbd⟩ := five_term_bound (β := β) (a₁ := a₁) (θ1 := θ1) (θ3 := θ3) (P := π ^ 2) (K := max K 0)
    hβ0 (by positivity) hK0
  refine ⟨C5, max c₁ 3e6, le_max_right _ _, fun c hc => ?_⟩
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans hc
  have hc3 : 3e6 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hs := hc₁ c hc1
  set s : ℝ := c ^ (-(1 / 3) : ℝ) with hsd
  have hs0 : 0 < s := Real.rpow_pos_of_pos hc0 _
  have hs₀' : s ≤ s₀ := (lt_min_iff.mp hs).1.le
  have hs1 : s ≤ 1 := (lt_min_iff.mp hs).2.le
  obtain ⟨h3, hsk, hs2, hs4⟩ := rpow_third_facts hc0
  set k : ℝ := c ^ (1 / 3 : ℝ) with hk
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Real.one_le_rpow (by linarith) (by norm_num)
  -- `ctUhat` in the variable `s`
  have hU : ∀ u : ℝ, ctUhat ε c u = u + (2 : ℝ) ^ (-(2 / 3) : ℝ) * s *
      ctPsi ε ((2 : ℝ) ^ ((2 : ℝ) / 3) * s ^ 2 * u) := by
    intro u
    have hs2' : c ^ (-(2 / 3) : ℝ) = s ^ 2 := by rw [hs2, ← hsk]
    unfold ctUhat
    rw [hs2']
  obtain ⟨hex, hall⟩ := hcore s hs0 hs₀'
  constructor
  · obtain ⟨φ, hφ, hφe⟩ := hex
    exact ⟨φ, hφ, by rw [hU]; exact hφe⟩
  · intro φ hφ hroot
    rw [hU] at hroot
    have h1 := hall φ hφ hroot
    rw [lam_psi0] at h1
    have hφ3 : |φ| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hφ.1, hφ.2]
    have hsk' : s = k⁻¹ := hsk
    have h2 := hbd k φ hk1 hφ3 (by rw [← hsk']; exact h1.trans (by gcongr; exact le_max_left _ _))
    rw [ctChartX_eq_k hc0, ctDelta5_eq_k hc0]
    have hc_inv : c⁻¹ = (k⁻¹) ^ 3 := by rw [inv_pow, h3]
    rw [hc_inv]
    exact h2

/-- the real-variable inversion step: the slope of the model chart is `≍ k/β`. -/
lemma gap_from_chain {k β q' K L u₁ φ : ℝ} (hk1 : 1 ≤ k) (hβ : 0 < β) (hq' : 0 ≤ q') (hka : 12 * β * q' ≤ k)
    (hK : 0 < K) (hL : 0 ≤ L) (hu : -3 ≤ u₁ ∧ u₁ ≤ 0) (hφ : -3 ≤ φ ∧ φ ≤ -2)
    (H : -(u₁ - φ) * (k / β - q' * k⁻¹ * (u₁ + φ)) ≤ -(3 / 4 * K * ((k⁻¹) ^ 3 * L))) :
    K * β / 2 * ((k⁻¹) ^ 3 * k⁻¹ * L) ≤ u₁ - φ := by
  have hk0 : 0 < k := by linarith
  have hki0 : 0 < k⁻¹ := inv_pos.mpr hk0
  have hqk : 0 ≤ q' * k⁻¹ := by positivity
  have hsum : |u₁ + φ| ≤ 6 := by rw [abs_le]; constructor <;> linarith
  have h2 : 12 * β * q' ≤ k ^ 2 := by nlinarith
  have hσ : q' * k⁻¹ * |u₁ + φ| ≤ k / (2 * β) := by
    have h1 : q' * k⁻¹ * |u₁ + φ| ≤ q' * k⁻¹ * 6 := mul_le_mul_of_nonneg_left hsum hqk
    refine h1.trans ?_
    have : q' * k⁻¹ * 6 = (6 * q') / k := by field_simp
    rw [this, div_le_div_iff₀ hk0 (by positivity)]
    nlinarith
  have hx1 : q' * k⁻¹ * (u₁ + φ) ≤ q' * k⁻¹ * |u₁ + φ| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hqk
  have hx2 : -(q' * k⁻¹ * |u₁ + φ|) ≤ q' * k⁻¹ * (u₁ + φ) := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le (u₁ + φ)) hqk
    rwa [mul_neg] at this
  set σ := k / β - q' * k⁻¹ * (u₁ + φ) with hσd
  have e1 : k / β - k / (2 * β) = k / (2 * β) := by field_simp; ring
  have e2 : k / β + k / (2 * β) = 3 * k / (2 * β) := by field_simp; ring
  have hσlo : k / (2 * β) ≤ σ := by linarith
  have hσhi : σ ≤ 3 * k / (2 * β) := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσlo
  set d := u₁ - φ with hdd
  have hRHS : 0 ≤ 3 / 4 * K * ((k⁻¹) ^ 3 * L) := by positivity
  have hdσ : 3 / 4 * K * ((k⁻¹) ^ 3 * L) ≤ d * σ := by linarith
  have hd0 : 0 ≤ d := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_neg_of_pos hneg hσpos
    linarith
  have hdσ2 : 3 / 4 * K * ((k⁻¹) ^ 3 * L) ≤ d * (3 * k / (2 * β)) :=
    hdσ.trans (mul_le_mul_of_nonneg_left hσhi hd0)
  have hm : 0 < 3 * k / (2 * β) := by positivity
  refine le_of_mul_le_mul_right ?_ hm
  have e3 : K * β / 2 * ((k⁻¹) ^ 3 * k⁻¹ * L) * (3 * k / (2 * β)) = 3 / 4 * K * ((k⁻¹) ^ 3 * L) := by
    have hkne := hk0.ne'
    have hβne := hβ.ne'
    field_simp
    ring
  rw [e3]
  exact hdσ2

lemma ctChartX_sub {c u φ : ℝ} (hc : 0 < c) :
    ctChartX c u - ctChartX c φ = -(u - φ) * (c ^ (1 / 3 : ℝ) / hankelBeta1 -
      9 * π ^ 2 / (25 * hankelBeta1 ^ 2) * (c ^ (1 / 3 : ℝ))⁻¹ * (u + φ)) := by
  have hk0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hkne := hk0.ne'
  have hβne := hankelBeta1_pos.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [ctChartX_eq_k hc, ctChartX_eq_k hc]
  field_simp
  ring

/-- **`chart_gap` for one sign, given `κ_ε < 0`** (`ct:langer-inv` with `ct:five-term-node` and `thm:hankel-one-two`; the
inversion step of the proof of `thm:ct-lower`): if `T ≤ Δ₅^ε(c) - K c⁻¹ log c` for a feasible `f` with `M[f] = 1` then
`ũ(T/c) - φ_c(a₁) ≥ (Kβ₁/2) c^{-4/3} log c`. -/
theorem ctChartGap_eps {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hκ : ctKappa ε < 0) {K : ℝ} (hK : 0 < K) :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T ≤ ctDelta5 ε c - K * (c⁻¹ * Real.log c) →
      K * hankelBeta1 / 2 * (c ^ (-(4 / 3) : ℝ) * Real.log c) ≤ ctGap ε c T := by
  obtain ⟨Cx, hCx⟩ := hankelXi_expansion
  have hCx' : ∀ c : ℝ, 3e6 ≤ c → ∀ x : ℝ, |x| ≤ 3 → |c * hankelXi c x - ctChartX c x| ≤ Cx * c⁻¹ :=
    fun c hc x hx => hCx c hc x hx
  obtain ⟨C5, c5, hc5, hnode⟩ := ctNode_expansion hε
  obtain ⟨c6, hc6, hq⟩ := hankel_quantC1_of_feasible
  have hβ0 : 0 < hankelBeta1 := hankelBeta1_pos
  set β := hankelBeta1 with hβ
  set a₁ := airyZero 1 with ha₁
  set q' : ℝ := 9 * π ^ 2 / (25 * β ^ 2) with hq'
  have hq'0 : 0 ≤ q' := by positivity
  set d₂ : ℝ := (-a₁ / β) * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε) with hd₂
  set κ : ℝ := ctKappa ε with hκd
  set k₀ : ℝ := max (max 1 (12 * β * q')) (2 * (|d₂| + |Cx|) / (-κ)) with hk₀
  set C' : ℝ := C5 + Cx with hC'
  refine ⟨max (max (max c5 c6) 3e6) (max (k₀ ^ 3) (Real.exp (4 * |C'| / K))), ?_⟩
  intro c hc T f hf hM hT
  have hc5' : c5 ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hc6' : c6 ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hc3 : 3e6 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hck : k₀ ^ 3 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hce : Real.exp (4 * |C'| / K) ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith
  obtain ⟨h3, hsk, hs2, hs4⟩ := rpow_third_facts hc0
  set k : ℝ := c ^ (1 / 3 : ℝ) with hk
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hkk₀ : k₀ ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    have hk₀0 : 0 ≤ k₀ := by
      have : (1 : ℝ) ≤ k₀ := (le_max_left _ _).trans (le_max_left _ _)
      linarith
    have := pow_lt_pow_left₀ hlt hk0.le (by norm_num : (3 : ℕ) ≠ 0)
    rw [h3] at this
    linarith
  have hk_a : 12 * β * q' ≤ k := ((le_max_right _ _).trans (le_max_left _ _)).trans hkk₀
  have hk_b : 2 * (|d₂| + |Cx|) / (-κ) ≤ k := (le_max_right _ _).trans hkk₀
  have hlogc : 4 * |C'| / K ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hc0]; exact hce
  have hlog0 : 0 ≤ Real.log c := by
    have : 0 ≤ 4 * |C'| / K := by positivity
    linarith
  have hcinv : c⁻¹ = (k⁻¹) ^ 3 := by rw [inv_pow, h3]
  have hc43 : c ^ (-(4 / 3) : ℝ) = c⁻¹ * k⁻¹ := by
    rw [hs4, hcinv]; ring
  have hki0 : 0 < k⁻¹ := inv_pos.mpr hk0
  -- the node
  obtain ⟨⟨φ₁, hφ₁, hφ₁e⟩, hφall⟩ := hnode c hc5'
  have hφex : ∃ φ ∈ Icc (-3 : ℝ) (-2), ctUhat ε c φ = a₁ := ⟨φ₁, hφ₁, hφ₁e⟩
  have hφspec := Function.invFunOn_pos hφex
  set φ := Function.invFunOn (ctUhat ε c) (Icc (-3 : ℝ) (-2)) a₁ with hφdef
  have hX5 := hφall φ hφspec.1 hφspec.2
  have hφ3 : -3 ≤ φ ∧ φ ≤ -2 := hφspec.1
  have ha₁b := airyZero_one
  -- `T < c ξ(a₁)`
  have hxa := hCx' c hc3 a₁ (by rw [abs_le]; constructor <;> linarith [ha₁b.1, ha₁b.2])
  have hΔ : ctDelta5 ε c - ctChartX c a₁ = κ + d₂ * (k⁻¹) ^ 2 := by
    rw [ctDelta5_eq_k hc0, ctChartX_eq_k hc0]
    simp only [hκd, hd₂, ctKappa]
    ring
  have hkinv_le : (|d₂| + |Cx|) * k⁻¹ ≤ -κ / 2 := by
    have h1 : (|d₂| + |Cx|) ≤ (-κ) * k / 2 := by
      have := hk_b
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    calc (|d₂| + |Cx|) * k⁻¹ ≤ (-κ * k / 2) * k⁻¹ := mul_le_mul_of_nonneg_right h1 hki0.le
      _ = -κ / 2 := by field_simp
  have hki1 : k⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
  have hki2 : (k⁻¹) ^ 2 ≤ k⁻¹ := by
    calc (k⁻¹) ^ 2 = k⁻¹ * k⁻¹ := by ring
      _ ≤ 1 * k⁻¹ := mul_le_mul_of_nonneg_right hki1 hki0.le
      _ = k⁻¹ := one_mul _
  have hki3 : (k⁻¹) ^ 3 ≤ k⁻¹ := by
    calc (k⁻¹) ^ 3 = (k⁻¹) ^ 2 * k⁻¹ := by ring
      _ ≤ 1 * k⁻¹ := mul_le_mul_of_nonneg_right ((hki2.trans hki1)) hki0.le
      _ = k⁻¹ := one_mul _
  have hlt1 : κ + d₂ * (k⁻¹) ^ 2 + Cx * c⁻¹ < 0 := by
    rw [hcinv]
    have a1 : d₂ * (k⁻¹) ^ 2 ≤ |d₂| * k⁻¹ := by
      calc d₂ * (k⁻¹) ^ 2 ≤ |d₂| * (k⁻¹) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |d₂| * k⁻¹ := mul_le_mul_of_nonneg_left hki2 (abs_nonneg _)
    have a2 : Cx * (k⁻¹) ^ 3 ≤ |Cx| * k⁻¹ := by
      calc Cx * (k⁻¹) ^ 3 ≤ |Cx| * (k⁻¹) ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Cx| * k⁻¹ := mul_le_mul_of_nonneg_left hki3 (abs_nonneg _)
    have h7 : (|d₂| + |Cx|) * k⁻¹ = |d₂| * k⁻¹ + |Cx| * k⁻¹ := by ring
    linarith only [hkinv_le, a1, a2, h7, hκ]
  have hKlog : 0 ≤ K * (c⁻¹ * Real.log c) := by positivity
  have hTlt : T < c * hankelXi c a₁ := by
    have h1 := (abs_le.1 hxa).1
    linarith
  obtain ⟨u_T, ha1, hle, hcT, hB2⟩ := hq c ε T f hc6' hf hε hM hTlt
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  have hxiT : hankelXi c u_T = T / c := by rw [eq_div_iff hc0.ne']; linarith [hcT]
  have hexT : ∃ x ∈ Icc (-3 : ℝ) 0, hankelXi c x = T / c := ⟨u_T, ⟨hu3, hu0⟩, hxiT⟩
  have hu₁spec : ctUtilde c T ∈ Icc (-3 : ℝ) 0 ∧ hankelXi c (ctUtilde c T) = T / c := by
    unfold ctUtilde; exact Function.invFunOn_pos hexT
  set u₁ := ctUtilde c T with hu₁d
  have hu₁1 : -3 ≤ u₁ ∧ u₁ ≤ 0 := hu₁spec.1
  have hTe : c * hankelXi c u₁ = T := by rw [hu₁spec.2]; field_simp
  have hxu := hCx' c hc3 u₁ (by rw [abs_le]; constructor <;> linarith [hu₁1.1, hu₁1.2])
  rw [hTe] at hxu
  have hC'le : C' ≤ K * Real.log c / 4 := by
    have h1 : 4 * |C'| / K ≤ Real.log c := hlogc
    rw [div_le_iff₀ hK] at h1
    have := le_abs_self C'
    linarith
  have hcpos : 0 < c⁻¹ := inv_pos.mpr hc0
  have hchain : ctChartX c u₁ - ctChartX c φ ≤ C' * c⁻¹ - K * (c⁻¹ * Real.log c) := by
    have h1 := (abs_le.1 hxu).1
    have h2 := (abs_le.1 hX5).1
    have h4 : ctDelta5 ε c ≤ ctChartX c φ + C5 * c⁻¹ := by linarith
    have h5 : C' * c⁻¹ = C5 * c⁻¹ + Cx * c⁻¹ := by rw [hC']; ring
    linarith
  have hchain2 : ctChartX c u₁ - ctChartX c φ ≤ -(3 / 4 * K * (c⁻¹ * Real.log c)) := by
    have : C' * c⁻¹ ≤ K * Real.log c / 4 * c⁻¹ := mul_le_mul_of_nonneg_right hC'le hcpos.le
    have h6 : K * Real.log c / 4 * c⁻¹ = K * (c⁻¹ * Real.log c) / 4 := by ring
    linarith
  rw [ctChartX_sub hc0] at hchain2
  have hgap := gap_from_chain (k := k) (β := β) (q' := q') (K := K) (L := Real.log c) (u₁ := u₁) (φ := φ)
    hk1 hβ0 hq'0 hk_a hK hlog0 hu₁1 hφ3 (by rw [← hcinv]; exact hchain2)
  have hgapd : ctGap ε c T = u₁ - φ := rfl
  rw [hgapd, hc43]
  have e5 : K * β / 2 * (c⁻¹ * k⁻¹ * Real.log c) = K * β / 2 * ((k⁻¹) ^ 3 * k⁻¹ * Real.log c) := by
    rw [hcinv]
  rw [e5]
  exact hgap

/-- **`chart_gap`** (`ct:langer-inv`, `ct:five-term-node`, `thm:hankel-one-two`): given `κ_ε < 0` for `ε = ±1`, for every
`K > 0` and all large `c`, every feasible `f` with `M[f] = 1` and `T ≤ Δ₅^ε(c) - K c⁻¹ log c` has
`ũ(T/c) - φ_c(a₁) ≥ (Kβ₁/2) c^{-4/3} log c`. -/
theorem ctChartGap (hκ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ctKappa ε < 0) :
    ∀ K : ℝ, 0 < K → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
        T ≤ ctDelta5 ε c - K * (c⁻¹ * Real.log c) →
        K * hankelBeta1 / 2 * (c ^ (-(4 / 3) : ℝ) * Real.log c) ≤ ctGap ε c T := by
  intro K hK
  obtain ⟨c₁, h1⟩ := ctChartGap_eps (Or.inl rfl) (hκ 1 (Or.inl rfl)) hK
  obtain ⟨c₂, h2⟩ := ctChartGap_eps (Or.inr rfl) (hκ (-1) (Or.inr rfl)) hK
  refine ⟨max c₁ c₂, fun c hc ε hε T f hf hM hT => ?_⟩
  rcases hε with rfl | rfl
  · exact h1 c ((le_max_left _ _).trans hc) T f hf hM hT
  · exact h2 c ((le_max_right _ _).trans hc) T f hf hM hT

/-- info: 'FormalResearch.SignUncertainty.ctChartGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctChartGap

/-- info: 'FormalResearch.SignUncertainty.ctNode_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctNode_expansion

end FormalResearch.SignUncertainty
