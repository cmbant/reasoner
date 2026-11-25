module

public import FormalResearch.SignUncertainty.CtCfuInv
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor

/-!
# `ct:cfu` Step 2: the phase shift `ψ_ε(a)` and the Langer chart inversion

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:psi-def`, `ct:langer-inv`, `ct:psi-coeffs` (Lemma `ct:cfu`, Step 2).  **Proved** (smooth, not
analytic: `C^∞` near `a = 0`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

open CtOuter FormalResearch.CohnElkies

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma Xi2_paper : Xi2 / 2 * ((2 : ℝ) ^ ((4 : ℝ) / 3) * ceBeta1 ^ 2) = 9 * π ^ 2 / 25 := by
  have hu : d0 * (2 : ℝ) ^ ((2 : ℝ) / 3) * ceBeta1 = π ^ 2 := d0_mul_beta
  have h4 : (2 : ℝ) ^ ((4 : ℝ) / 3) = ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hd := d0_pos.ne'
  have h2 := d0_pi_sq
  have h6 : π ^ 4 = 144 * d0 ^ 6 := by
    have : π ^ 4 = (π ^ 2) ^ 2 := by ring
    rw [this, h2]; ring
  have e : (2 : ℝ) ^ ((4 : ℝ) / 3) * ceBeta1 ^ 2 = (π ^ 2 / d0) ^ 2 := by
    rw [h4, ← mul_pow, ← hu]
    field_simp
  rw [e, Xi2_eq]
  have hπ : π ^ 2 ≠ 0 := by positivity
  rw [h6, h2]
  field_simp
  ring

lemma deriv_Xi_paper : deriv Xi 0 * ((2 : ℝ) ^ ((2 : ℝ) / 3) * ceBeta1) = -1 := by
  have hu : d0 * (2 : ℝ) ^ ((2 : ℝ) / 3) * ceBeta1 = π ^ 2 := d0_mul_beta
  rw [deriv_Xi_zero]
  have hπ : π ^ 2 ≠ 0 := by positivity
  field_simp
  linarith [hu]

/-- **`ct:cfu` Step 2 (`ct:psi-def`, `ct:psi-coeffs`, `ct:langer-inv` data).**  There are `ρ > 0` and smooth (`C^∞` at `0`) functions
`ψ = ψ_ε`, `Ξ` of the Langer parameter `a`, and `τ₀(a)` for `a ∈ (-ρ, 0)`, such that for `a ∈ (-ρ, 0)`:
`τ₀(a) > 0` is the unique positive solution of `Φ(τ; m(τ)) = (2/3)(-a)^{3/2}` (`Φ = edgePhi`, `m = hankelEdgeM`),
`ψ(a) = θ_ε(τ₀(a))/√(-a)` and `Ξ(a) = exp(m(τ₀(a)))/π²` (`= ξ` with `L = m(τ₀)`); and
`ψ(0) = (12/π²)^{1/3} θ_1^ε`, `ψ'(0) = -(7θ_1^ε/25 + 12θ_3^ε/π²)`, `Ξ(0) = 1/π²`,
`Ξ'(0) · 2^{2/3}β₁ = -1`, `(Ξ''(0)/2) · 2^{4/3}β₁² = 9π²/25` (`β₁ = (π²√3)^{2/3}`), with second- and third-order Taylor bounds. -/
theorem cfu_psi_langer {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (ρ : ℝ) (τ0 ψ Ξ : ℝ → ℝ), 0 < ρ ∧ ContDiffAt ℝ ∞' ψ 0 ∧ ContDiffAt ℝ ∞' Ξ 0 ∧
      (∀ a ∈ Ioo (-ρ) 0, 0 < τ0 a ∧
        edgePhi (hankelEdgeM (τ0 a)) (τ0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) ∧
        (∀ τ : ℝ, 0 < τ → edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → τ = τ0 a) ∧
        ψ a = outerTheta ε (τ0 a) / Real.sqrt (-a) ∧
        Ξ a = Real.exp (hankelEdgeM (τ0 a)) / π ^ 2) ∧
      ψ 0 = (12 / π ^ 2) ^ ((1 : ℝ) / 3) * ctTheta1 ε ∧
      deriv ψ 0 = -(7 / 25 * ctTheta1 ε + 12 / π ^ 2 * ctTheta3 ε) ∧
      Ξ 0 = 1 / π ^ 2 ∧
      deriv Ξ 0 * ((2 : ℝ) ^ ((2 : ℝ) / 3) * ceBeta1) = -1 ∧
      deriv (deriv Ξ) 0 / 2 * ((2 : ℝ) ^ ((4 : ℝ) / 3) * ceBeta1 ^ 2) = 9 * π ^ 2 / 25 ∧
      (∃ C : ℝ, ∀ a : ℝ, |a| < ρ →
        |ψ a - ψ 0 - deriv ψ 0 * a| ≤ C * a ^ 2 ∧
        |Ξ a - Ξ 0 - deriv Ξ 0 * a - deriv (deriv Ξ) 0 / 2 * a ^ 2| ≤ C * |a| ^ 3) := by
  obtain ⟨th, hth, hrel, hth0, hth1⟩ := theta_hat hε
  have hpsi : ContDiffAt ℝ ∞' (psiOf th) 0 := contDiffAt_psiOf hth
  have hXi : ContDiffAt ℝ ∞' Xi 0 := by
    unfold Xi
    have h1 : ContDiffAt ℝ ∞' NF (zA 0) := by
      rw [zA_zero]
      exact (contDiffAt_id.mul contDiffAt_nfun)
    exact (Real.contDiff_exp.contDiffAt.comp 0 (h1.comp 0 contDiffAt_zA)).div_const _
  obtain ⟨ρ1, hρ1, K1, hK1, hT1⟩ := taylor2_of_contDiffAt (hpsi.of_le (by simp))
  obtain ⟨ρ2, hρ2, K2, hK2, hT2⟩ := taylor2_of_contDiffAt (hXi.of_le (by simp))
  -- the good neighbourhood
  have htau : Tendsto tau0 (𝓝 0) (𝓝 0) := by
    have h : Tendsto tau0 (𝓝 0) (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp tendsto_zA
    rwa [Real.sqrt_zero] at h
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ), (zA a ∈ Ioo (-rr) rr ∧ 0 < fF (zA a) ∧ AFp (zA a) ≠ 0) ∧ AF (zA a) = a ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) := by
    filter_upwards [zA_good, AF_zA_eventually] with a h1 h2
    exact ⟨h1, h2, hrel⟩
  have hev2 : ∀ᶠ a in 𝓝 (0 : ℝ), outerTheta ε (tau0 a) = tau0 a * th (tau0 a ^ 2) := htau.eventually hrel
  obtain ⟨ρ3, hρ3, h3⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
  set ρ := min (min ρ1 ρ2) ρ3 with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ1 hρ2) hρ3
  refine ⟨ρ, tau0, psiOf th, Xi, hρ, hpsi, hXi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha3 : dist a 0 < ρ3 := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ha.1, min_le_right (min ρ1 ρ2) ρ3], by linarith [ha.2, hρ3]⟩
    obtain ⟨⟨hg, hr, -⟩, hrel2⟩ := h3 ha3
    obtain ⟨h0, hm, hphi, hsq⟩ := tau0_props ha.2 hr hg
    refine ⟨h0, hphi, ?_, ?_, ?_⟩
    · intro τ hτ hφ
      have hmono := critical_value_strictMonoOn
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hmono (mem_Ici.mpr hτ.le) (mem_Ici.mpr h0.le) hlt
        simp only at this
        linarith
      · have := hmono (mem_Ici.mpr h0.le) (mem_Ici.mpr hτ.le) hgt
        simp only at this
        linarith
    · unfold psiOf
      rw [hrel2, hsq]
      have hz := zA_pos ha.2 hr
      have hτ2 : tau0 a ^ 2 = zA a := Real.sq_sqrt hz.le
      rw [hτ2]
      have hdpos : 0 < dF (zA a) := by
        obtain ⟨-, h2, -⟩ := hg
        unfold dF; positivity
      field_simp
    · unfold Xi; rw [hm]
  · rw [psiOf_zero, hth0]
    have hd := d0_pos
    have e : (12 / π ^ 2) ^ ((1 : ℝ) / 3) = d0⁻¹ := by
      unfold d0; rw [← Real.inv_rpow (by positivity), inv_div]
    rw [e]; field_simp
  · exact psi_coeff hth hth0 hth1
  · exact Xi_zero
  · exact deriv_Xi_paper
  · rw [deriv_deriv_Xi_zero]; exact Xi2_paper
  · refine ⟨K1 * ρ + |deriv (deriv (psiOf th)) 0| / 2 + K2, fun a ha => ?_⟩
    have ha1 : |a| < ρ1 := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_left _ _))
    have ha2 : |a| < ρ2 := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_right _ _))
    have hρ' : 0 ≤ ρ := hρ.le
    have hsq : |a| ^ 3 ≤ ρ * a ^ 2 := by
      have : |a| ^ 3 = |a| * a ^ 2 := by rw [← sq_abs a]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right ha.le (sq_nonneg _)
    have hsq0 : 0 ≤ a ^ 2 := sq_nonneg a
    have hK2a : 0 ≤ K2 * |a| ^ 3 := by positivity
    constructor
    · have h := hT1 a ha1
      have e : psiOf th a - psiOf th 0 - deriv (psiOf th) 0 * a =
          (psiOf th a - psiOf th 0 - deriv (psiOf th) 0 * a - deriv (deriv (psiOf th)) 0 * a ^ 2 / 2) +
            deriv (deriv (psiOf th)) 0 * a ^ 2 / 2 := by ring
      rw [e]
      calc _ ≤ |psiOf th a - psiOf th 0 - deriv (psiOf th) 0 * a - deriv (deriv (psiOf th)) 0 * a ^ 2 / 2| +
            |deriv (deriv (psiOf th)) 0 * a ^ 2 / 2| := abs_add_le _ _
        _ ≤ K1 * |a| ^ 3 + |deriv (deriv (psiOf th)) 0| * a ^ 2 / 2 := by
            refine add_le_add h (le_of_eq ?_)
            rw [abs_div, abs_mul, abs_of_nonneg hsq0, abs_two]
        _ ≤ K1 * (ρ * a ^ 2) + |deriv (deriv (psiOf th)) 0| * a ^ 2 / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hsq hK1) le_rfl
        _ ≤ (K1 * ρ + |deriv (deriv (psiOf th)) 0| / 2 + K2) * a ^ 2 := by
            nlinarith [mul_nonneg hK2 hsq0, abs_nonneg (deriv (deriv (psiOf th)) 0)]
    · have h := hT2 a ha2
      have e : Xi a - Xi 0 - deriv Xi 0 * a - deriv (deriv Xi) 0 / 2 * a ^ 2 =
          Xi a - Xi 0 - deriv Xi 0 * a - deriv (deriv Xi) 0 * a ^ 2 / 2 := by ring
      rw [e]
      refine h.trans ?_
      have : 0 ≤ K1 * ρ + |deriv (deriv (psiOf th)) 0| / 2 := by positivity
      nlinarith [pow_nonneg (abs_nonneg a) 3]

/-- **`ct:langer-inv`** (`constant_terms_lower.tex`): with `a = 2^{2/3} c^{-2/3} ũ`, `ũ = -v`, and `ξ(a) = Ξ(a)`,
`c ξ(-v) = c/π² + (v/β₁) c^{1/3} + (9π²/25)(v/β₁)² c^{-1/3} + O(c^{-1}|v|³)` for `|2^{2/3} c^{-2/3} v| < ρ`;
here `Ξ(a) = exp(m(τ₀(a)))/π²` for `a < 0` (see `cfu_psi_langer`) and `β₁ = (π²√3)^{2/3}`. -/
theorem langer_inv : ∃ (ρ : ℝ) (C : ℝ), 0 < ρ ∧ ∀ c v : ℝ, 0 < c →
    |(2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 : ℝ) / 3) * v| < ρ →
    |c * Xi (-((2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 : ℝ) / 3) * v)) -
        (c / π ^ 2 + v / ceBeta1 * c ^ ((1 : ℝ) / 3) + 9 * π ^ 2 / 25 * (v / ceBeta1) ^ 2 * c ^ (-(1 : ℝ) / 3))|
      ≤ C * c⁻¹ * |v| ^ 3 := by
  have hXi : ContDiffAt ℝ ∞' Xi 0 := by
    unfold Xi
    have h1 : ContDiffAt ℝ ∞' NF (zA 0) := by
      rw [zA_zero]
      exact (contDiffAt_id.mul contDiffAt_nfun)
    exact (Real.contDiff_exp.contDiffAt.comp 0 (h1.comp 0 contDiffAt_zA)).div_const _
  obtain ⟨ρ, hρ, K, hK, hT⟩ := taylor2_of_contDiffAt (hXi.of_le (by simp))
  refine ⟨ρ, 4 * K, hρ, fun c v hc ha => ?_⟩
  -- change of variable `t = c^{1/3}`
  set t : ℝ := c ^ ((1 : ℝ) / 3) with ht
  have htpos : 0 < t := by positivity
  have hct : c = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have hc13 : c ^ (-(1 : ℝ) / 3) = t⁻¹ := by
    rw [neg_div, Real.rpow_neg hc.le]
  have hc23 : c ^ (-(2 : ℝ) / 3) = (t ^ 2)⁻¹ := by
    rw [neg_div, Real.rpow_neg hc.le, ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
  set u : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3) with hu
  have hupos : 0 < u := by positivity
  have hu3 : u ^ 3 = 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hu2 : (2 : ℝ) ^ ((4 : ℝ) / 3) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hβ : 0 < ceBeta1 := ceBeta1_pos
  have hX1 : deriv Xi 0 = -1 / (u * ceBeta1) := by
    have := deriv_Xi_paper
    rw [eq_div_iff (by positivity)]; linarith [this]
  have hX2 : Xi2 / 2 = 9 * π ^ 2 / 25 / (u ^ 2 * ceBeta1 ^ 2) := by
    have := Xi2_paper
    rw [hu2] at this
    rw [eq_div_iff (by positivity)]; linarith [this]
  simp only [deriv_deriv_Xi_zero] at hT
  -- the point `a`
  set a : ℝ := -(u * c ^ (-(2 : ℝ) / 3) * v) with hadef
  have haρ : |a| < ρ := by rw [hadef, abs_neg]; exact ha
  have hR := hT a haρ
  have hae : a = -(u * v / t ^ 2) := by rw [hadef, hc23]; ring
  have hmain : c * Xi a - (c / π ^ 2 + v / ceBeta1 * c ^ ((1 : ℝ) / 3) + 9 * π ^ 2 / 25 * (v / ceBeta1) ^ 2 * c ^ (-(1 : ℝ) / 3)) =
      c * (Xi a - Xi 0 - deriv Xi 0 * a - Xi2 * a ^ 2 / 2) := by
    rw [hc13, ← ht, Xi_zero, hX1, hae]
    have hX2' : Xi2 = 2 * (9 * π ^ 2 / 25 / (u ^ 2 * ceBeta1 ^ 2)) := by linarith [hX2]
    rw [hX2', hct]
    have hπ : π ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hmain, abs_mul, abs_of_pos hc]
  calc c * |Xi a - Xi 0 - deriv Xi 0 * a - Xi2 * a ^ 2 / 2| ≤ c * (K * |a| ^ 3) :=
        mul_le_mul_of_nonneg_left hR hc.le
    _ = 4 * K * c⁻¹ * |v| ^ 3 := by
        rw [hae, abs_neg, abs_div, abs_mul, abs_of_pos hupos, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), hct]
        field_simp
        rw [hu3]; ring

/-- info: 'FormalResearch.SignUncertainty.CtCfu.cfu_psi_langer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cfu_psi_langer

/-- info: 'FormalResearch.SignUncertainty.CtCfu.langer_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_inv

end FormalResearch.SignUncertainty.CtCfu
