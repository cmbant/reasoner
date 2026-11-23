module

public import FormalResearch.SignUncertainty.HankelLocalHolo
public import FormalResearch.SignUncertainty.DeepLobeKernel
public import FormalResearch.SignUncertainty.MellinInversion

/-!
# The analytic tail bound `(T)` and the split of the inversion integral (`gt:7.7p`, Step 0)

On `Re ζ = σ_* = 1/10` the product `K₀(ζ, ξ) W̃_c(ζ)` is bounded by
`B(c,ξ) (11/10 + |τ|)^{1/2} e^{-c a lobeU(τ)}`, `a = 3/280`, `B = 2 e^{5/(12c)} e^{c(4σ_*³/9 + σ_* log π²ξ)}`
(`norm_K0Wt_line_le`; `norm_mellinK0_vert_le`, `hankelWt_norm_le`).  For `c ≥ 5000` this is integrable, and the
part `|τ| ≥ 1/3` is `≤ C e^{-κ' c}` with `κ' > 0` when `|log π²ξ| ≤ 10⁻³` (`hankel_tail_le`).

Lean constants versus the paper: the paper's (T) uses the sharper `Re S̃(1/10 + i/3) + (1/10) log π²ξ < -0.0082`
(exponent `2·10⁻³ c` after the weight), whereas here the existing crude kernel bound
`g(σ) < (4/3)σ²` is used, giving a smaller but positive exponent `κ' ≈ 3·10⁻⁵`.  Only `κ' > 0` is used downstream
(`r_∞ ≤ C c^{1/3} e^{-κ c}`), so no stated result changes.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma lobeU_nonneg (τ : ℝ) : 0 ≤ lobeU τ := by
  unfold lobeU
  have h1 : 0 ≤ (1 / 2 : ℝ) * min (τ ^ 2) 1 := mul_nonneg (by norm_num) (le_min (sq_nonneg _) zero_le_one)
  exact add_nonneg h1 (le_max_left _ _)

lemma lobeU_ge_of_third {τ : ℝ} (hτ : 1 / 3 ≤ |τ|) : 1 / 18 ≤ lobeU τ := by
  unfold lobeU
  have h1 : (1 / 9 : ℝ) ≤ min (τ ^ 2) 1 := by
    refine le_min ?_ (by norm_num)
    have : (1 / 3 : ℝ) ^ 2 ≤ |τ| ^ 2 := pow_le_pow_left₀ (by norm_num) hτ 2
    rw [sq_abs] at this; linarith
  have := le_max_left (0 : ℝ) (Real.log |τ|)
  linarith

lemma exp_neg_lobeU_le {k : ℝ} (hk : 0 ≤ k) (τ : ℝ) :
    Real.exp (-(k * lobeU τ)) ≤ (2 : ℝ) ^ k * (1 + |τ|) ^ (-k) := by
  have h1 : 0 < 1 + |τ| := by positivity
  rcases lt_or_ge |τ| 1 with h | h
  · have hU := lobeU_nonneg τ
    have h2 : Real.exp (-(k * lobeU τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h3 : (1 + |τ|) ^ (-k) * (2 : ℝ) ^ k ≥ 1 := by
      rw [Real.rpow_neg h1.le]
      have : (1 + |τ|) ^ k ≤ (2 : ℝ) ^ k := Real.rpow_le_rpow h1.le (by linarith) hk
      have hp : 0 < (1 + |τ|) ^ k := Real.rpow_pos_of_pos h1 _
      rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ hp]
      linarith
    nlinarith
  · have hpos : 0 < |τ| := by linarith
    have hU : lobeU τ = 1 / 2 + Real.log |τ| := by
      unfold lobeU
      have : min (τ ^ 2) 1 = 1 := by
        apply min_eq_right
        nlinarith [sq_abs τ, abs_nonneg τ]
      rw [this, max_eq_right (Real.log_nonneg h)]; ring
    rw [hU]
    have e1 : Real.exp (-(k * (1 / 2 + Real.log |τ|))) = Real.exp (-(k / 2)) * |τ| ^ (-k) := by
      rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]; congr 1; ring
    rw [e1]
    have h4 : Real.exp (-(k / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h5 : |τ| ^ (-k) ≤ (2 : ℝ) ^ k * (1 + |τ|) ^ (-k) := by
      rw [Real.rpow_neg hpos.le, Real.rpow_neg h1.le]
      have hp1 : 0 < (1 + |τ|) ^ k := Real.rpow_pos_of_pos h1 _
      have hp2 : 0 < |τ| ^ k := Real.rpow_pos_of_pos hpos _
      have : (1 + |τ|) ^ k ≤ (2 : ℝ) ^ k * |τ| ^ k := by
        rw [← Real.mul_rpow (by norm_num) hpos.le]
        exact Real.rpow_le_rpow h1.le (by linarith) hk
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hp2 hp1]
      linarith
    calc Real.exp (-(k / 2)) * |τ| ^ (-k) ≤ 1 * |τ| ^ (-k) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact h5

/-- The product `K₀ W̃_c` on the line `Re ζ = 1/10` is bounded by `B (11/10 + |τ|)^{1/2} e^{-c a lobeU(τ)}`,
`a = 3/280`. -/
lemma norm_K0Wt_line_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {ξ : ℝ} (hξ : 0 < ξ) (τ : ℝ) :
    ‖mellinK0 c (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ξ *
        hankelWt c f (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (1 / (6 * c))) * (11 / 10 + |τ|) ^ (1 / 2 : ℝ) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * (1 / 10) * lobeU τ))) := by
  have hc0 : 0 < c := by linarith
  set ζ : ℂ := ((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hre : ζ.re = 1 / 10 := by simp [hζ]
  have hK := norm_mellinK0_vert_le hc0 hξ (s := 1 / 10) (τ := τ) (by norm_num) (by norm_num)
  have hW := hankelWt_norm_le hc hf hε (ζ := ζ) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [hM, one_mul] at hW
  have hn : ‖1 + ζ‖ ≤ 11 / 10 + |τ| := by
    have : (1 : ℂ) + ζ = ((11 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by rw [hζ]; push_cast; ring
    rw [this]
    calc _ ≤ ‖((11 / 10 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 11 / 10 + |τ| := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
        rw [abs_of_pos (by norm_num)]
  have hW' : ‖hankelWt c f ζ‖ ≤ (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) :=
    hW.trans (by gcongr)
  rw [norm_mul]
  calc ‖mellinK0 c ζ ξ‖ * ‖hankelWt c f ζ‖
      ≤ (2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * (1 / 10) * lobeU τ)))) *
        ((11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c))) := by gcongr
    _ = _ := by ring

/-- Continuity of `τ ↦ K₀ W̃_c` along the line `Re ζ = 1/10`. -/
lemma continuous_K0Wt_line {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {ξ : ℝ}
    (hξ : 0 < ξ) :
    Continuous (fun τ : ℝ => mellinK0 c (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ξ *
        hankelWt c f (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) := by
  set z : ℝ → ℂ := fun τ => ((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hz
  have hzc : Continuous z := by fun_prop
  have hre : ∀ τ, (z τ).re = 1 / 10 := fun τ => by simp [hz]
  have hK : (fun τ : ℝ => mellinK0 c (z τ) ξ) = fun τ =>
      Complex.Gamma ((c : ℂ) * (1 - z τ)) / Complex.Gamma (c : ℂ) *
        ((2 * Real.pi * c * ξ : ℂ) ^ ((c : ℂ) * z τ)) * Complex.exp ((c : ℂ) * hInt (z τ)) := by
    funext τ
    rw [← mellin_strip_kernel_eq hc hξ (ζ := z τ) (by rw [hre]; norm_num) (by rw [hre]; norm_num),
      hInt_eq_stripH (by rw [hre]; norm_num) (by rw [hre]; norm_num)]
  have hG : Continuous (fun τ : ℝ => Complex.Gamma ((c : ℂ) * (1 - z τ))) := by
    refine continuous_iff_continuousAt.2 fun τ => ?_
    have hw : 0 < ((c : ℂ) * (1 - z τ)).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
        zero_mul, sub_zero, hre]
      nlinarith
    have hdiff : DifferentiableAt ℂ Complex.Gamma ((c : ℂ) * (1 - z τ)) := by
      refine Complex.differentiableAt_Gamma _ (fun m hm => ?_)
      rw [hm] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact ContinuousAt.comp (g := Complex.Gamma) (f := fun τ : ℝ => (c : ℂ) * (1 - z τ)) hdiff.continuousAt
      (by fun_prop)
  have hpow : Continuous (fun τ : ℝ => (2 * Real.pi * c * ξ : ℂ) ^ ((c : ℂ) * z τ)) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    have : (0 : ℝ) < 2 * Real.pi * c * ξ := by positivity
    exact_mod_cast this.ne'
  have hH : Continuous (fun τ : ℝ => hInt (z τ)) := by
    refine (differentiableOn_hInt.continuousOn).comp_continuous hzc (fun τ => ?_)
    exact closedStrip_subset ⟨by rw [hre]; norm_num, by rw [hre]; norm_num⟩
  have hKc : Continuous (fun τ : ℝ => mellinK0 c (z τ) ξ) := by
    rw [hK]
    exact ((hG.div_const _).mul hpow).mul (by fun_prop)
  have hopen : ∀ τ, z τ ∈ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := fun τ => ⟨by rw [hre]; norm_num, by rw [hre]; norm_num⟩
  have hWc : Continuous (fun τ : ℝ => hankelWt c f (z τ)) :=
    (hankelWt_differentiableOn hc hf).continuousOn.comp_continuous hzc hopen
  exact hKc.mul hWc

lemma measurable_lobeU : Measurable lobeU := by
  unfold lobeU
  fun_prop

/-- The weight `(11/10 + |τ|)^{1/2} e^{-k lobeU(τ)}` is integrable for `k > 3/2`. -/
lemma integrable_lobe_weight {k : ℝ} (hk : 3 / 2 < k) :
    Integrable (fun τ : ℝ => (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) := by
  have hint : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(k - 1 / 2))) := by
    refine integrable_one_add_norm ?_
    simp only [Module.finrank_self, Nat.cast_one]; linarith
  refine Integrable.mono' (hint.const_mul (11 / 10 * (2 : ℝ) ^ k)) ?_ (Eventually.of_forall fun τ => ?_)
  · have : Measurable (fun τ : ℝ => (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) := by
      have := measurable_lobeU
      fun_prop
    exact this.aestronglyMeasurable
  · have h1 : 0 < 1 + |τ| := by positivity
    have hnn : 0 ≤ (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs]
    have e1 : (11 / 10 + |τ|) ^ (1 / 2 : ℝ) ≤ 11 / 10 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      calc (11 / 10 + |τ|) ^ (1 / 2 : ℝ) ≤ (11 / 10 * (1 + |τ|)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg τ]) (by norm_num)
        _ = (11 / 10) ^ (1 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) h1.le
        _ ≤ 11 / 10 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
            gcongr
            calc (11 / 10 : ℝ) ^ (1 / 2 : ℝ) ≤ (11 / 10 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 11 / 10 := Real.rpow_one _
    have e2 := exp_neg_lobeU_le (k := k) (by linarith) τ
    calc (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))
        ≤ (11 / 10 * (1 + |τ|) ^ (1 / 2 : ℝ)) * ((2 : ℝ) ^ k * (1 + |τ|) ^ (-k)) := by gcongr
      _ = 11 / 10 * (2 : ℝ) ^ k * ((1 + |τ|) ^ (1 / 2 : ℝ) * (1 + |τ|) ^ (-k)) := by ring
      _ = 11 / 10 * (2 : ℝ) ^ k * (1 + ‖τ‖) ^ (-(k - 1 / 2)) := by
          rw [← Real.rpow_add h1, Real.norm_eq_abs]; congr 2; ring

/-- The full-line integrand `K₀ W̃_c` on `Re ζ = 1/10`. -/
noncomputable def hankelK0Wt (c : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (τ : ℝ) : ℂ :=
  mellinK0 c (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ξ *
    hankelWt c f (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)

lemma integrable_hankelK0Wt {c ε : ℝ} (hc : 140 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (hankelK0Wt c f ξ) := by
  have hc0 : 0 < c := by linarith
  have hw := integrable_lobe_weight (k := c * (3 / 280)) (by nlinarith)
  refine Integrable.mono' (hw.const_mul (2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (1 / (6 * c)))) (continuous_K0Wt_line hc0 hf hξ).aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  have := norm_K0Wt_line_le (by linarith : 3 / 2 < c) hf hε hM hξ τ
  refine this.trans (le_of_eq ?_)
  have e : c * (2 * (3 / 56 : ℝ) * (1 / 10) * lobeU τ) = c * (3 / 280) * lobeU τ := by ring
  rw [e]; ring

/-- `ℓ(ξ) = log(π² ξ)` as a complex number. -/
noncomputable def hankelEll (ξ : ℝ) : ℂ := Complex.log (Real.pi ^ 2 * ξ)

/-- The tail piece `∫_{|τ|>1/3} K₀ W̃_c`. -/
noncomputable def hankelTail (c : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ τ in (Icc (-(1 / 3 : ℝ)) (1 / 3))ᶜ, hankelK0Wt c f ξ τ

/-- The `c`-independent weight integral in the tail bound. -/
noncomputable def hankelTailI0 : ℝ :=
  ∫ τ : ℝ, (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-((5000 * (3 / 280) / 32) * lobeU τ))

/-- **Tail bound `(T)`** (with the Lean exponent `1/40000`, see the module docstring). -/
theorem hankel_tail_le {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hL : Real.log (Real.pi ^ 2 * ξ) ≤ 1 / 1000) :
    ‖hankelTail c f ξ‖ ≤ 6 * hankelTailI0 * Real.exp (-(c / 40000)) := by
  have hc0 : 0 < c := by linarith
  set k0 : ℝ := 5000 * (3 / 280) / 32 with hk0
  have hk0' : 3 / 2 < k0 := by rw [hk0]; norm_num
  have hw := integrable_lobe_weight hk0'
  set w : ℝ → ℝ := fun τ => (11 / 10 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k0 * lobeU τ)) with hwdef
  set Cc : ℝ := 2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (1 / (6 * c)) * Real.exp (-(c * (3 / 280) * (31 / 32) / 18)) with hCc
  have hCc_le : Cc ≤ 6 * Real.exp (-(c / 40000)) := by
    have e1 : Real.exp (1 / (4 * c)) * Real.exp (1 / (6 * c)) ≤ 3 := by
      rw [← Real.exp_add]
      have : 1 / (4 * c) + 1 / (6 * c) ≤ 1 := by
        have h1 : 1 / (4 * c) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have h2 : 1 / (6 * c) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
      calc Real.exp (1 / (4 * c) + 1 / (6 * c)) ≤ Real.exp 1 := Real.exp_le_exp.2 this
        _ ≤ 3 := (Real.exp_one_lt_d9.le.trans (by norm_num))
    have e2 : Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (3 / 280) * (31 / 32) / 18)) ≤ Real.exp (-(c / 40000)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : (4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ) - (3 / 280) * (31 / 32) / 18 ≤
          -(1 / 40000) := by
        have := hL; norm_num; linarith
      nlinarith
    calc Cc = 2 * (Real.exp (1 / (4 * c)) * Real.exp (1 / (6 * c))) *
          (Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
            Real.exp (-(c * (3 / 280) * (31 / 32) / 18))) := by rw [hCc]; ring
      _ ≤ 2 * 3 * Real.exp (-(c / 40000)) := by gcongr
      _ = _ := by ring
  have hpt : ∀ τ ∈ (Icc (-(1 / 3 : ℝ)) (1 / 3))ᶜ, ‖hankelK0Wt c f ξ τ‖ ≤ Cc * w τ := by
    intro τ hτ
    have hτ' : 1 / 3 ≤ |τ| := by
      by_contra h
      push Not at h
      exact hτ (abs_le.1 h.le)
    have h1 := norm_K0Wt_line_le (by linarith : 3 / 2 < c) hf hε hM hξ τ
    have hU := lobeU_ge_of_third hτ'
    have hU0 := lobeU_nonneg τ
    have e : Real.exp (-(c * (2 * (3 / 56 : ℝ) * (1 / 10) * lobeU τ))) ≤
        Real.exp (-(c * (3 / 280) * (31 / 32) / 18)) * Real.exp (-(k0 * lobeU τ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : c * (3 / 280) * (31 / 32) / 18 ≤ c * (3 / 280) * (31 / 32) * lobeU τ := by nlinarith
      have h3 : k0 * lobeU τ ≤ c * (3 / 280) / 32 * lobeU τ := by
        apply mul_le_mul_of_nonneg_right _ hU0
        rw [hk0]; nlinarith
      nlinarith
    calc ‖hankelK0Wt c f ξ τ‖ ≤ _ := h1
      _ ≤ (2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * (1 / 10) ^ 3 + (1 / 10) * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (1 / (6 * c))) * (11 / 10 + |τ|) ^ (1 / 2 : ℝ) *
        (Real.exp (-(c * (3 / 280) * (31 / 32) / 18)) * Real.exp (-(k0 * lobeU τ))) := by gcongr
      _ = Cc * w τ := by rw [hCc, hwdef]; ring
  have hCc0 : 0 ≤ Cc := by positivity
  unfold hankelTail
  calc ‖∫ τ in (Icc (-(1 / 3 : ℝ)) (1 / 3))ᶜ, hankelK0Wt c f ξ τ‖
      ≤ ∫ τ in (Icc (-(1 / 3 : ℝ)) (1 / 3))ᶜ, ‖hankelK0Wt c f ξ τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ in (Icc (-(1 / 3 : ℝ)) (1 / 3))ᶜ, Cc * w τ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hw.const_mul Cc).integrableOn) ?_
        exact (ae_restrict_iff' measurableSet_Icc.compl).2 (Eventually.of_forall hpt)
    _ ≤ ∫ τ : ℝ, Cc * w τ := setIntegral_le_integral (hw.const_mul Cc)
          (Eventually.of_forall fun τ => by positivity)
    _ = Cc * hankelTailI0 := by rw [integral_const_mul]; rfl
    _ ≤ 6 * Real.exp (-(c / 40000)) * hankelTailI0 := by
        gcongr
        exact integral_nonneg fun τ => by positivity
    _ = _ := by ring

/-- **Split of the inversion integral** (`gt:7.7p` Step 0): for `c ≥ 5000` and `ξ > 0`,
`(ρ₀ f)(cξ) = (2πξ)^{-1} ((fρ₀)_loc + tail)`, `(fρ₀)_loc = hankelLocal c f (log π²ξ)`. -/
theorem hankel_rho0_split {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {ξ : ℝ} (hξ : 0 < ξ) :
    (((hankelRho0 c (c * ξ) * f (c * ξ) : ℝ)) : ℂ) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) * (hankelLocal c f (hankelEll ξ) + hankelTail c f ξ) := by
  have hc0 : 0 < c := by linarith
  have hinv := hankel_inversion_line (by linarith : 3 / 2 < c) hf hε (σ := 1 / 10) (by norm_num) (by norm_num)
    (by nlinarith) hξ
  rw [hinv]
  congr 1
  have hint := integrable_hankelK0Wt (by linarith : 140 < c) hf hε hM hξ
  have hsplit := integral_add_compl (measurableSet_Icc (a := -(1 / 3 : ℝ)) (b := 1 / 3)) hint
  show ∫ τ : ℝ, hankelK0Wt c f ξ τ = _
  rw [← hsplit]
  congr 1
  unfold hankelLocal
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun τ hτ => ?_)
  have hn : ‖((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 0.35 := by
    have h2 : ‖((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 ≤ 0.35 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, Complex.add_im, Complex.mul_im]
      nlinarith [hτ.1, hτ.2]
    exact le_of_sq_le_sq (by simpa using h2) (by norm_num)
  have hre : 0 < (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re := by simp
  unfold hankelEll hankelK0Wt
  exact (hankelJ_eq_mellinK0 hn hre).symm

/-- info: 'FormalResearch.SignUncertainty.hankel_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_tail_le

/-- info: 'FormalResearch.SignUncertainty.hankel_rho0_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_rho0_split

end FormalResearch.SignUncertainty
