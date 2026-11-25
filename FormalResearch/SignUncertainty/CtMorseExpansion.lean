module

public import FormalResearch.SignUncertainty.CtMorseHadamard

/-!
# Finite real stationary-phase expansion in a Morse coordinate

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:morse-expansion`.  **Proved.**

For `r ≥ 1`, `B ∈ C^{2r}`, `χ ∈ C_c^∞((-a,a))` equal to `1` near `0`, `σ = ±1`, `μ ≥ 1`:
`∫ χ B e^{iσμX²/2} dX = e^{iσπ/4} √(2π/μ) [Σ_{m<r} B^{(2m)}(0)/m! (iσ/(2μ))^m + O_{r,χ,a}(μ^{-r} ‖B‖_{C^{2r}})]`.

Proof by induction on `r`.  With `h = f - f(0)χ` and `g = h/x = ∫₀¹ h'(tx) dt` (`CtMorseHadamard`), integration by parts gives
`W(f) = f(0) W(χ) - (iσμ)⁻¹ W(g')`, and the Taylor coefficients of `g'` at `0` are `f^{(2m+2)}(0)/(2m+2)`, so
`E_r(f) = f(0)(W(χ) - G) - (iσμ)⁻¹ E_{r-1}(g')`, with `W(χ) - G = O(μ^{-N})` (`CtMorseFresnel`); the base case `r = 1` is
`CtMorseKernel` (`W(g') = O(μ^{-1/2})`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtMorse

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The cutoff as a complex-valued function. -/
noncomputable def chic (χ : ℝ → ℝ) (x : ℝ) : ℂ := (χ x : ℂ)

/-- The oscillatory integral `W(f) = ∫ f(x) e^{iλx²/2} dx`. -/
noncomputable def Wint (lam : ℝ) (f : ℝ → ℂ) : ℂ := ∫ x : ℝ, f x * osc lam x

/-- The leading constant `e^{iσπ/4} √(2π/μ)`. -/
noncomputable def Gc (σ μ : ℝ) : ℂ := Complex.exp (σ * (π / 4) * Complex.I) * ((Real.sqrt (2 * π / μ) : ℝ) : ℂ)

/-- The Taylor sum `Σ_{m<r} f^{(2m)}(0)/m! (iσ/(2μ))^m`. -/
noncomputable def Ssum (σ μ : ℝ) (r : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range r, iteratedDeriv (2 * m) f 0 / (m.factorial : ℂ) * (Complex.I * σ / (2 * μ)) ^ m

/-- The error `E_r(f) = W(f) - G · S_r(f)`. -/
noncomputable def Eerr (σ μ : ℝ) (r : ℕ) (f : ℝ → ℂ) : ℂ := Wint (σ * μ) f - Gc σ μ * Ssum σ μ r f

section Chi

variable {χ : ℝ → ℝ} {δ a : ℝ}

lemma contDiff_chic (hχ : ContDiff ℝ ∞' χ) : ContDiff ℝ ∞' (chic χ) :=
  Complex.ofRealCLM.contDiff.comp hχ

lemma supp_chic (h0 : ∀ x, a < |x| → χ x = 0) : Supp a (chic χ) := fun x hx => by simp [chic, h0 x hx]

lemma chic_one (h1 : ∀ x, |x| < δ → χ x = 1) {x : ℝ} (hx : |x| < δ) : chic χ x = 1 := by simp [chic, h1 x hx]

/-- Derivatives of `χ` at `0` of positive order vanish. -/
lemma iteratedDeriv_chic_zero (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1) {j : ℕ} (hj : 1 ≤ j) :
    iteratedDeriv j (chic χ) 0 = 0 := by
  have hev : chic χ =ᶠ[𝓝 (0 : ℝ)] fun _ => (1 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with y hy
    exact chic_one h1 (by simpa [Real.dist_eq] using hy)
  rw [hev.iteratedDeriv_eq j, iteratedDeriv_const]
  have : j ≠ 0 := by omega
  simp [this]

lemma chic_deriv_bound (hχ : ContDiff ℝ ∞' χ) (h0 : ∀ x, a < |x| → χ x = 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ N, ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ C := by
  have hB : ∀ j : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ B := fun j => by
    have hc : Continuous (iteratedDeriv j (chic χ)) :=
      (contDiff_chic hχ).continuous_iteratedDeriv j (by exact_mod_cast le_top)
    exact hc.bounded_above_of_compact_support (((supp_chic h0).iteratedDeriv j).hasCompactSupport)
  choose B hB using hB
  refine ⟨∑ j ∈ Finset.range (N + 1), |B j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun j hj x => ?_⟩
  calc ‖iteratedDeriv j (chic χ) x‖ ≤ B j := hB j x
    _ ≤ |B j| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

end Chi

lemma integrable_Wint {a lam : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : Supp a f) :
    Integrable fun x => f x * osc lam x := by
  refine Continuous.integrable_of_hasCompactSupport (hc.mul (continuous_osc lam)) ?_
  exact (hs.hasCompactSupport).mul_right

lemma hasDerivAt_osc (lam x : ℝ) :
    HasDerivAt (osc lam) (Complex.I * (lam : ℂ) * (x : ℂ) * osc lam x) x := by
  unfold osc
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * (lam : ℂ) * (y : ℂ) ^ 2 / 2)
      (Complex.I * (lam : ℂ) * (2 * (x : ℂ)) / 2) x := by
    have := (((hasDerivAt_id (x : ℂ)).pow 2).const_mul (Complex.I * (lam : ℂ))).div_const 2
    simpa using this.comp_ofReal
  refine h1.cexp.congr_deriv ?_
  ring

section Step

variable {χ : ℝ → ℝ} {δ a : ℝ}

/-- `h = f - f(0) χ`. -/
noncomputable def hfun (χ : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f x - f 0 * chic χ x

lemma iter_hfun (hχ : ContDiff ℝ ∞' χ) {f : ℝ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) {j : ℕ} (hj : j ≤ n) (x : ℝ) :
    iteratedDeriv j (hfun χ f) x = iteratedDeriv j f x - f 0 * iteratedDeriv j (chic χ) x := by
  have e : hfun χ f = f - fun x => f 0 * chic χ x := by funext x; rfl
  have hf' : ContDiffAt ℝ (j : WithTop ℕ∞) f x := (hf.of_le (by exact_mod_cast hj)).contDiffAt
  have hχ' : ContDiffAt ℝ (j : WithTop ℕ∞) (fun x => f 0 * chic χ x) x :=
    contDiffAt_const.mul ((contDiff_chic hχ).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [e, iteratedDeriv_sub hf' hχ', iteratedDeriv_const_mul (f 0) ((contDiff_chic hχ).of_le (by exact_mod_cast le_top)).contDiffAt]

lemma contDiff_hfun (hχ : ContDiff ℝ ∞' χ) {f : ℝ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (hfun χ f) :=
  hf.sub (contDiff_const.mul ((contDiff_chic hχ).of_le (by exact_mod_cast le_top)))

lemma supp_hfun (h0 : ∀ x, a < |x| → χ x = 0) {f : ℝ → ℂ} (hs : Supp a f) : Supp a (hfun χ f) := fun x hx => by
  simp [hfun, hs x hx, supp_chic h0 x hx]

lemma hfun_zero (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1) (f : ℝ → ℂ) : hfun χ f 0 = 0 := by
  simp [hfun, chic_one h1 (by simpa using hδ : |(0 : ℝ)| < δ)]

/-- **Integration by parts**: `W(f) = f(0) W(χ) - (iλ)⁻¹ W(g')` with `g = h/x`. -/
lemma Wint_step (hχ : ContDiff ℝ ∞' χ) (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1)
    (h0 : ∀ x, a < |x| → χ x = 0) (ha : 0 ≤ a) {f : ℝ → ℂ} {n : ℕ} (hn : 2 ≤ n) (hf : ContDiff ℝ n f)
    (hs : Supp a f) {lam : ℝ} (hlam : lam ≠ 0) :
    Wint lam f = f 0 * Wint lam (chic χ) - (1 / (Complex.I * lam)) * Wint lam (deriv (hadG (hfun χ f))) := by
  set h := hfun χ f with hh
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have hhc : ContDiff ℝ (m + 1 + 1 : ℕ) h := contDiff_hfun hχ hf
  have hhs : Supp a h := supp_hfun h0 hs
  have hh0 : h 0 = 0 := hfun_zero hδ h1 f
  have hG : ContDiff ℝ (m + 1 : ℕ) (hadG h) := contDiff_hadG hhc hhs
  have hG1 : ContDiff ℝ 1 (hadG h) := hG.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hGs : Supp a (hadG h) := supp_hadG (hhc.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1 + 1))) hh0 ha hhs
  have hG's : Supp a (deriv (hadG h)) := hGs.deriv
  have hGd : ∀ x, HasDerivAt (hadG h) (deriv (hadG h) x) x := fun x => ((hG1.differentiable (by simp)) x).hasDerivAt
  have hG'c : Continuous (deriv (hadG h)) := by
    have := hG1.continuous_deriv (by simp)
    exact this
  have hGc : Continuous (hadG h) := hG1.continuous
  have hfc : Continuous f := hf.continuous
  -- linearity
  have hfs' : Continuous (chic χ) := (contDiff_chic hχ).continuous
  have hdecomp : Wint lam f = f 0 * Wint lam (chic χ) + Wint lam h := by
    unfold Wint
    have i1 : Integrable fun x => chic χ x * osc lam x := integrable_Wint hfs' (supp_chic h0)
    have i2 : Integrable fun x => h x * osc lam x := integrable_Wint hhc.continuous hhs
    rw [← integral_const_mul, ← integral_add (i1.const_mul _) i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hh, hfun]; ring
  -- integration by parts
  have hF : ∀ x, HasDerivAt (fun y => hadG h y * osc lam y)
      (deriv (hadG h) x * osc lam x + hadG h x * (Complex.I * (lam : ℂ) * (x : ℂ) * osc lam x)) x :=
    fun x => (hGd x).mul (hasDerivAt_osc lam x)
  have i3 : Integrable fun x => deriv (hadG h) x * osc lam x := integrable_Wint hG'c hG's
  have i4 : Integrable fun x => hadG h x * (Complex.I * (lam : ℂ) * (x : ℂ) * osc lam x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := continuous_osc lam
      have := hGc
      fun_prop
    · have : HasCompactSupport (hadG h) := hGs.hasCompactSupport
      exact this.mul_right
  have i5 : Integrable fun x => hadG h x * osc lam x := integrable_Wint hGc hGs
  have h00 := integral_eq_zero_of_hasDerivAt_of_integrable hF (i3.add i4) i5
  rw [integral_add i3 i4] at h00
  have hWh : Wint lam h = ∫ x, hadG h x * ((x : ℂ) * osc lam x) := by
    unfold Wint
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show h x * osc lam x = hadG h x * ((x : ℂ) * osc lam x)
    rw [← mul_hadG (hhc.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1 + 1))) hh0 x]; ring
  have hmid : ∫ x, hadG h x * (Complex.I * (lam : ℂ) * (x : ℂ) * osc lam x) =
      (Complex.I * lam) * ∫ x, hadG h x * ((x : ℂ) * osc lam x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hlamC : (Complex.I * (lam : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hlam)
  rw [hmid] at h00
  have hW' : Wint lam (deriv (hadG h)) = ∫ x, deriv (hadG h) x * osc lam x := rfl
  rw [hdecomp, hWh, hW']
  have : ∫ x, hadG h x * ((x : ℂ) * osc lam x) =
      -(1 / (Complex.I * lam)) * ∫ x, deriv (hadG h) x * osc lam x := by
    have hc : (Complex.I * (lam : ℂ)) * ∫ x, hadG h x * ((x : ℂ) * osc lam x) =
        -∫ x, deriv (hadG h) x * osc lam x := by linear_combination h00
    calc ∫ x, hadG h x * ((x : ℂ) * osc lam x)
        = (Complex.I * (lam : ℂ))⁻¹ * ((Complex.I * (lam : ℂ)) * ∫ x, hadG h x * ((x : ℂ) * osc lam x)) :=
          (inv_mul_cancel_left₀ hlamC _).symm
      _ = _ := by rw [hc]; ring
  rw [this]; ring

/-- Properties of `g' = (hadG h)'` for `f ∈ C^{2(s+1)}`. -/
lemma gprime_props (hχ : ContDiff ℝ ∞' χ) (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1)
    (h0 : ∀ x, a < |x| → χ x = 0) (ha : 0 ≤ a) {f : ℝ → ℂ} {s : ℕ} (hf : ContDiff ℝ (2 * (s + 1) : ℕ) f)
    (hfs : Supp a f) {M Cχ : ℝ} (hM : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j f x‖ ≤ M)
    (hC : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ Cχ) :
    ContDiff ℝ (2 * s : ℕ) (deriv (hadG (hfun χ f))) ∧ Supp a (deriv (hadG (hfun χ f))) ∧
    (∀ j ≤ 2 * s, ∀ x, ‖iteratedDeriv j (deriv (hadG (hfun χ f))) x‖ ≤ M * (1 + Cχ)) ∧
    (∀ j ≤ 2 * s, iteratedDeriv j (deriv (hadG (hfun χ f))) 0 = iteratedDeriv (j + 2) f 0 / ((j : ℂ) + 2)) ∧
    deriv (hadG (hfun χ f)) = tay 1 (iteratedDeriv 2 (hfun χ f)) := by
  set h := hfun χ f with hh
  have hn : 2 * (s + 1) = (2 * s + 1) + 1 := by ring
  have hhc : ContDiff ℝ ((2 * s + 1) + 1 : ℕ) h := by rw [← hn]; exact contDiff_hfun hχ hf
  have hhs : Supp a h := supp_hfun h0 hfs
  have hh0 : h 0 = 0 := hfun_zero hδ h1 f
  have hG : ContDiff ℝ (2 * s + 1 : ℕ) (hadG h) := contDiff_hadG hhc hhs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by omega) 0)
  have hC0 : 0 ≤ Cχ := (norm_nonneg _).trans (hC 0 (by omega) 0)
  have hbd : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j h x‖ ≤ M * (1 + Cχ) := by
    intro j hj x
    rw [hh, iter_hfun hχ hf hj x]
    calc ‖iteratedDeriv j f x - f 0 * iteratedDeriv j (chic χ) x‖
        ≤ ‖iteratedDeriv j f x‖ + ‖f 0‖ * ‖iteratedDeriv j (chic χ) x‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      _ ≤ M + M * Cχ := by
          have hf0 : ‖f 0‖ ≤ M := by simpa using hM 0 (by omega) 0
          exact add_le_add (hM j hj x) (mul_le_mul hf0 (hC j hj x) (norm_nonneg _) hM0)
      _ = M * (1 + Cχ) := by ring
  have hGs : Supp a (hadG h) :=
    supp_hadG (hhc.of_le (by exact_mod_cast (by omega : 1 ≤ (2 * s + 1) + 1))) hh0 ha hhs
  have hg'iter : ∀ j ≤ 2 * s, iteratedDeriv j (deriv (hadG h)) = tay (j + 1) (iteratedDeriv (j + 2) h) := by
    intro j hj
    rw [← iteratedDeriv_succ']
    exact iteratedDeriv_hadG hhc hhs (by omega)
  refine ⟨?_, hGs.deriv, ?_, ?_, ?_⟩
  · have hG' : ContDiff ℝ (((2 * s : ℕ) : WithTop ℕ∞) + 1) (hadG h) := by exact_mod_cast hG
    have := (contDiff_succ_iff_deriv.mp hG').2.2
    exact_mod_cast this
  · intro j hj x
    rw [hg'iter j hj]
    have hc : Continuous (iteratedDeriv (j + 2) h) :=
      hhc.continuous_iteratedDeriv (j + 2) (by exact_mod_cast (by omega : j + 2 ≤ (2 * s + 1) + 1))
    have := norm_tay_le hc (hbd (j + 2) (by omega)) (j + 1) x
    refine this.trans ?_
    have hB : 0 ≤ M * (1 + Cχ) := by positivity
    exact div_le_self hB (by have : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
                             push_cast at this ⊢; linarith)
  · intro j hj
    rw [hg'iter j hj, tay_zero]
    have : iteratedDeriv (j + 2) h 0 = iteratedDeriv (j + 2) f 0 := by
      rw [hh, iter_hfun hχ hf (by omega) 0, iteratedDeriv_chic_zero hδ h1 (by omega), mul_zero, sub_zero]
    rw [this]
    push_cast
    ring_nf
  · rw [← iteratedDeriv_one]
    exact iteratedDeriv_hadG hhc hhs (by omega : 1 + 1 ≤ (2 * s + 1) + 1)

lemma Ssum_step {σ μ : ℝ} (hσ : σ * σ = 1) (hμ : 0 < μ) {f g' : ℝ → ℂ} {s : ℕ}
    (hg : ∀ j ≤ 2 * s, iteratedDeriv j g' 0 = iteratedDeriv (j + 2) f 0 / ((j : ℂ) + 2)) :
    Ssum σ μ (s + 1) f = f 0 + (-(1 / (Complex.I * ((σ * μ : ℝ) : ℂ)))) * Ssum σ μ s g' := by
  unfold Ssum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hσ3 : (σ : ℂ) * σ = 1 := by exact_mod_cast hσ
  have hσ' : (σ : ℂ) ≠ 0 := by
    intro h; rw [h] at hσ3; simp at hσ3
  have hq : (-(1 / (Complex.I * ((σ * μ : ℝ) : ℂ)))) = 2 * (Complex.I * σ / (2 * μ)) := by
    push_cast
    field_simp
    rw [Complex.I_sq]
    linear_combination hσ3
  have hterm : ∀ m ∈ Finset.range s,
      iteratedDeriv (2 * (m + 1)) f 0 / ((m + 1).factorial : ℂ) * (Complex.I * σ / (2 * μ)) ^ (m + 1) =
      (-(1 / (Complex.I * ((σ * μ : ℝ) : ℂ)))) *
        (iteratedDeriv (2 * m) g' 0 / (m.factorial : ℂ) * (Complex.I * σ / (2 * μ)) ^ m) := by
    intro m hm
    have hm' : 2 * m ≤ 2 * s := by have := Finset.mem_range.mp hm; omega
    rw [hg (2 * m) hm', hq, Nat.factorial_succ]
    have e : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [e]
    push_cast
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    have h2 : (2 * (m : ℂ) + 2) ≠ 0 := by
      have : (0 : ℝ) < 2 * m + 2 := by positivity
      exact_mod_cast this.ne'
    have h3 : ((m : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < m + 1 := by positivity
      exact_mod_cast this.ne'
    generalize (Complex.I * σ / (2 * μ)) = q
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [mul_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
  rw [add_comm]

lemma Eerr_step (hχ : ContDiff ℝ ∞' χ) (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1)
    (h0 : ∀ x, a < |x| → χ x = 0) (ha : 0 ≤ a) {f : ℝ → ℂ} {s : ℕ} (hf : ContDiff ℝ (2 * (s + 1) : ℕ) f)
    (hfs : Supp a f) {M Cχ : ℝ} (hM : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j f x‖ ≤ M)
    (hC : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ Cχ) {σ μ : ℝ} (hσ : σ * σ = 1) (hμ : 0 < μ) :
    Eerr σ μ (s + 1) f = f 0 * (Wint (σ * μ) (chic χ) - Gc σ μ) -
      (1 / (Complex.I * ((σ * μ : ℝ) : ℂ))) * Eerr σ μ s (deriv (hadG (hfun χ f))) := by
  have hσ0 : σ * μ ≠ 0 := by
    intro h; rcases mul_eq_zero.mp h with h | h
    · rw [h] at hσ; norm_num at hσ
    · exact hμ.ne' h
  obtain ⟨-, -, -, hP4, -⟩ := gprime_props hχ hδ h1 h0 ha hf hfs hM hC
  have hW := Wint_step hχ hδ h1 h0 ha (by omega : 2 ≤ 2 * (s + 1)) hf hfs hσ0
  have hS := Ssum_step hσ hμ hP4
  unfold Eerr
  rw [hW, hS]
  ring

/-- The one-step bound `‖E_{s+1}(f)‖ ≤ M K/μ^{s+2} + μ⁻¹ ‖E_s(g')‖`. -/
lemma Eerr_split (hχ : ContDiff ℝ ∞' χ) (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1)
    (h0 : ∀ x, a < |x| → χ x = 0) (ha : 0 ≤ a) {f : ℝ → ℂ} {s : ℕ} (hf : ContDiff ℝ (2 * (s + 1) : ℕ) f)
    (hfs : Supp a f) {M Cχ K : ℝ} (hM : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j f x‖ ≤ M)
    (hC : ∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ Cχ) {σ μ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hμ : 0 < μ)
    (hK : ‖Wint (σ * μ) (chic χ) - Gc σ μ‖ ≤ K / μ ^ (s + 2)) :
    ‖Eerr σ μ (s + 1) f‖ ≤ M * (K / μ ^ (s + 2)) + μ⁻¹ * ‖Eerr σ μ s (deriv (hadG (hfun χ f)))‖ := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  rw [Eerr_step hχ hδ h1 h0 ha hf hfs hM hC hσ2 hμ]
  have hlam : ‖(1 : ℂ) / (Complex.I * ((σ * μ : ℝ) : ℂ))‖ = μ⁻¹ := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hμ]
    rcases hσ with h | h <;> subst h <;> simp
  have hf0 : ‖f 0‖ ≤ M := by simpa using hM 0 (by omega) 0
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul hf0 hK (norm_nonneg _) ((norm_nonneg _).trans hf0)
  · rw [norm_mul, hlam]

end Step

lemma arith1 {μ : ℝ} (hμ : 1 ≤ μ) (p : ℕ) (K M : ℝ) (hM : 0 ≤ M) :
    M * (K / μ ^ (p + 1)) ≤ |K| * M / (μ ^ p * Real.sqrt μ) := by
  have hμ0 : 0 < μ := by linarith
  have hsq : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hsq1 : Real.sqrt μ ≤ μ := by
    calc Real.sqrt μ ≤ Real.sqrt μ * Real.sqrt μ := by nlinarith only [Real.one_le_sqrt.mpr hμ, hsq]
      _ = μ := Real.mul_self_sqrt hμ0.le
  have hD : 0 < μ ^ p * Real.sqrt μ := by positivity
  have hle : μ ^ p * Real.sqrt μ ≤ μ ^ (p + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left hsq1 (by positivity)
  calc M * (K / μ ^ (p + 1)) ≤ M * (|K| / μ ^ (p + 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self K) (by positivity)) hM
    _ ≤ M * (|K| / (μ ^ p * Real.sqrt μ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (abs_nonneg K) hD hle) hM
    _ = |K| * M / (μ ^ p * Real.sqrt μ) := by ring

lemma arith2 {μ : ℝ} (hμ : 0 < μ) (p : ℕ) (E : ℝ) :
    μ⁻¹ * (E / (μ ^ p * Real.sqrt μ)) = E / (μ ^ (p + 1) * Real.sqrt μ) := by
  have hsq : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  field_simp
  ring

section Core

variable {χ : ℝ → ℝ} {δ a : ℝ}

/-- **`ct:morse-expansion`, core form** (for `f = χ B` already multiplied by the cutoff): for `r ≥ 1`, `f ∈ C^{2r}`
vanishing for `|x| > a` with `|f^{(j)}| ≤ M` (`j ≤ 2r`), `σ = ±1`, `μ ≥ 1`:
`‖∫ f e^{iσμx²/2} - e^{iσπ/4}√(2π/μ) Σ_{m<r} f^{(2m)}(0)/m! (iσ/(2μ))^m‖ ≤ C M μ^{-r-1/2}`. -/
theorem morse_core (hχ : ContDiff ℝ ∞' χ) (hδ : 0 < δ) (h1 : ∀ x, |x| < δ → χ x = 1)
    (h0 : ∀ x, a < |x| → χ x = 0) (ha : 0 ≤ a) (s : ℕ) :
    ∃ C : ℝ, ∀ {σ μ : ℝ} {f : ℝ → ℂ} {M : ℝ}, (σ = 1 ∨ σ = -1) → 1 ≤ μ → ContDiff ℝ (2 * (s + 1) : ℕ) f →
      Supp a f → (∀ j ≤ 2 * (s + 1), ∀ x, ‖iteratedDeriv j f x‖ ≤ M) →
      ‖Eerr σ μ (s + 1) f‖ ≤ C * M / (μ ^ (s + 1) * Real.sqrt μ) := by
  induction s with
  | zero =>
    obtain ⟨Cχ, hCχ0, hC⟩ := chic_deriv_bound hχ h0 2
    obtain ⟨K, hK⟩ := cutoff_fresnel hδ ha hχ h1 (fun x hx => h0 x hx) (N := 2) (by norm_num)
    refine ⟨|K| + 2 * Real.sqrt 2 * π * (1 + Cχ), fun {σ μ f M} hσ hμ hf hfs hM => ?_⟩
    have hμ0 : 0 < μ := by linarith
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by omega) 0)
    have hKμ : ‖Wint (σ * μ) (chic χ) - Gc σ μ‖ ≤ K / μ ^ (0 + 2) := hK hσ hμ0
    have hsplit := Eerr_split hχ hδ h1 h0 ha hf hfs hM (fun j hj x => hC j (by omega) x) hσ hμ0 hKμ
    obtain ⟨-, -, hP3, -, hP5⟩ := gprime_props hχ hδ h1 h0 ha hf hfs hM (fun j hj x => hC j (by omega) x)
    set h := hfun χ f with hh
    -- the base case: W(g') = O(μ^{-1/2})
    have hhc : ContDiff ℝ 2 h := (contDiff_hfun hχ hf).of_le (by norm_num)
    have hbd2 : ∀ x, ‖iteratedDeriv 2 h x‖ ≤ M * (1 + Cχ) := by
      intro x
      rw [hh, iter_hfun hχ hf (by omega) x]
      calc ‖iteratedDeriv 2 f x - f 0 * iteratedDeriv 2 (chic χ) x‖
          ≤ ‖iteratedDeriv 2 f x‖ + ‖f 0‖ * ‖iteratedDeriv 2 (chic χ) x‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
        _ ≤ M + M * Cχ := by
            have hf0 : ‖f 0‖ ≤ M := by simpa using hM 0 (by omega) 0
            exact add_le_add (hM 2 (by omega) x) (mul_le_mul hf0 (hC 2 (by omega) x) (norm_nonneg _) hM0)
        _ = M * (1 + Cχ) := by ring
    have hkc : Continuous (iteratedDeriv 2 h) := hhc.continuous_iteratedDeriv 2 le_rfl
    have hks : Supp a (iteratedDeriv 2 h) := (supp_hfun h0 hfs).iteratedDeriv 2
    have hki : Integrable (iteratedDeriv 2 h) :=
      hkc.integrable_of_hasCompactSupport hks.hasCompactSupport
    have hσ0 : σ * μ ≠ 0 := by
      rcases hσ with h | h <;> subst h <;> simp [hμ0.ne']
    have hbase := hadamard_bound hkc hki hbd2 hσ0
    have habs : |σ * μ| = μ := by
      rw [abs_mul, abs_of_pos hμ0]; rcases hσ with h | h <;> subst h <;> simp
    rw [habs] at hbase
    have hE0 : Eerr σ μ 0 (deriv (hadG h)) = Wint (σ * μ) (deriv (hadG h)) := by
      simp [Eerr, Ssum]
    have hW : ‖Wint (σ * μ) (deriv (hadG h))‖ ≤ 2 * Real.sqrt 2 * π * (M * (1 + Cχ)) / Real.sqrt μ := by
      have : Wint (σ * μ) (deriv (hadG h)) =
          ∫ X : ℝ, (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) * iteratedDeriv 2 h (t * X)) * osc (σ * μ) X := by
        unfold Wint
        rw [hP5]
        simp [tay]
      rw [this]; exact hbase
    rw [hE0] at hsplit
    have h1' := arith1 hμ 1 K M hM0
    have h2' := arith2 hμ0 0 (2 * Real.sqrt 2 * π * (M * (1 + Cχ)))
    have hW' : μ⁻¹ * ‖Wint (σ * μ) (deriv (hadG h))‖ ≤ μ⁻¹ * (2 * Real.sqrt 2 * π * (M * (1 + Cχ)) / (μ ^ 0 * Real.sqrt μ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using hW
    have hfin : (|K| + 2 * Real.sqrt 2 * π * (1 + Cχ)) * M / (μ ^ (0 + 1) * Real.sqrt μ) =
        |K| * M / (μ ^ 1 * Real.sqrt μ) + 2 * Real.sqrt 2 * π * (M * (1 + Cχ)) / (μ ^ (0 + 1) * Real.sqrt μ) := by
      ring
    calc ‖Eerr σ μ (0 + 1) f‖ ≤ M * (K / μ ^ (0 + 2)) + μ⁻¹ * ‖Wint (σ * μ) (deriv (hadG h))‖ := hsplit
      _ ≤ |K| * M / (μ ^ 1 * Real.sqrt μ) + μ⁻¹ * (2 * Real.sqrt 2 * π * (M * (1 + Cχ)) / (μ ^ 0 * Real.sqrt μ)) :=
          add_le_add h1' hW'
      _ = _ := by rw [h2']; exact hfin.symm
  | succ s ih =>
    obtain ⟨Cs, hCs⟩ := ih
    obtain ⟨Cχ, hCχ0, hC⟩ := chic_deriv_bound hχ h0 (2 * (s + 1 + 1))
    obtain ⟨K, hK⟩ := cutoff_fresnel hδ ha hχ h1 (fun x hx => h0 x hx) (N := s + 1 + 2) (by omega)
    refine ⟨|K| + |Cs| * (1 + Cχ), fun {σ μ f M} hσ hμ hf hfs hM => ?_⟩
    have hμ0 : 0 < μ := by linarith
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by omega) 0)
    have hKμ : ‖Wint (σ * μ) (chic χ) - Gc σ μ‖ ≤ K / μ ^ (s + 1 + 2) := hK hσ hμ0
    have hsplit := Eerr_split hχ hδ h1 h0 ha hf hfs hM (fun j hj x => hC j hj x) hσ hμ0 hKμ
    obtain ⟨hP1, hP2, hP3, -, -⟩ := gprime_props hχ hδ h1 h0 ha hf hfs hM (fun j hj x => hC j hj x)
    have hIH := hCs (σ := σ) (μ := μ) (f := deriv (hadG (hfun χ f))) (M := M * (1 + Cχ)) hσ hμ hP1 hP2 hP3
    have h1' := arith1 hμ (s + 2) K M hM0
    have h2' := arith2 hμ0 (s + 1) (|Cs| * (M * (1 + Cχ)))
    have hIH' : μ⁻¹ * ‖Eerr σ μ (s + 1) (deriv (hadG (hfun χ f)))‖ ≤
        μ⁻¹ * (|Cs| * (M * (1 + Cχ)) / (μ ^ (s + 1) * Real.sqrt μ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine hIH.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ M * (1 + Cχ) := by positivity
      exact mul_le_mul_of_nonneg_right (le_abs_self Cs) this
    have hfin : (|K| + |Cs| * (1 + Cχ)) * M / (μ ^ (s + 1 + 1) * Real.sqrt μ) =
        |K| * M / (μ ^ (s + 2) * Real.sqrt μ) + |Cs| * (M * (1 + Cχ)) / (μ ^ (s + 1 + 1) * Real.sqrt μ) := by
      ring
    calc ‖Eerr σ μ (s + 1 + 1) f‖ ≤ M * (K / μ ^ (s + 1 + 2)) + μ⁻¹ * ‖Eerr σ μ (s + 1) (deriv (hadG (hfun χ f)))‖ := hsplit
      _ ≤ |K| * M / (μ ^ (s + 2) * Real.sqrt μ) + μ⁻¹ * (|Cs| * (M * (1 + Cχ)) / (μ ^ (s + 1) * Real.sqrt μ)) :=
          add_le_add h1' hIH'
      _ = _ := by rw [h2']; exact hfin.symm

/-- info: 'FormalResearch.SignUncertainty.CtMorse.morse_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms morse_core

/-- The cut-off amplitude `f = χ B` is `C^{2r}`, vanishes for `|x| > a`, and has derivatives bounded by `2^{2r} Cχ M`. -/
lemma cutoff_amp (ha : 0 < a) (hχ : ContDiff ℝ ∞' χ) (hχs : tsupport χ ⊆ Ioo (-a) a) {B : ℝ → ℂ} {n : ℕ}
    (hB : ContDiffOn ℝ n B (Ioo (-a) a)) {M Cχ : ℝ} (hM : ∀ j ≤ n, ∀ x ∈ Ioo (-a) a, ‖iteratedDeriv j B x‖ ≤ M)
    (hC : ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (chic χ) x‖ ≤ Cχ) :
    ContDiff ℝ n (fun x => chic χ x * B x) ∧ Supp a (fun x => chic χ x * B x) ∧
    ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (fun x => chic χ x * B x) x‖ ≤ 2 ^ n * Cχ * M := by
  have hevz : ∀ x, x ∉ Ioo (-a) a → (fun y => chic χ y * B y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro x hx
    have hx' : x ∉ tsupport χ := fun h => hx (hχs h)
    have := (notMem_tsupport_iff_eventuallyEq).mp hx'
    filter_upwards [this] with y hy
    simp [chic, hy]
  have hsupp : Supp a (fun x => chic χ x * B x) := by
    intro x hx
    have : x ∉ Ioo (-a) a := fun h => by
      have := abs_lt.mpr ⟨h.1, h.2⟩; linarith
    have hx' : x ∉ tsupport χ := fun h => this (hχs h)
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx'
    simp [chic, hχx]
  refine ⟨?_, hsupp, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ioo (-a) a
    · exact ((contDiff_chic hχ).of_le (by exact_mod_cast le_top)).contDiffAt.mul
        (hB.contDiffAt (Ioo_mem_nhds hx.1 hx.2))
    · exact contDiffAt_const.congr_of_eventuallyEq (hevz x hx)
  · intro j hj x
    by_cases hx : x ∈ Ioo (-a) a
    · have hf1 : ContDiffAt ℝ (j : WithTop ℕ∞) (chic χ) x :=
        ((contDiff_chic hχ).of_le (by exact_mod_cast le_top)).contDiffAt
      have hf2 : ContDiffAt ℝ (j : WithTop ℕ∞) B x :=
        (hB.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).of_le (by exact_mod_cast hj)
      have := iteratedDeriv_fun_mul hf1 hf2
      rw [this]
      calc ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i (chic χ) x * iteratedDeriv (j - i) B x‖
          ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i (chic χ) x * iteratedDeriv (j - i) B x‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Cχ * M) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            have h1 := hC i (hi'.trans hj) x
            have h2 := hM (j - i) ((Nat.sub_le _ _).trans hj) x hx
            calc (j.choose i : ℝ) * ‖iteratedDeriv i (chic χ) x‖ * ‖iteratedDeriv (j - i) B x‖
                ≤ (j.choose i : ℝ) * Cχ * M := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
                    (by have : 0 ≤ Cχ := (norm_nonneg _).trans (hC 0 (by omega) x)
                        positivity)
              _ = (j.choose i : ℝ) * (Cχ * M) := by ring
        _ = 2 ^ j * (Cχ * M) := by
            rw [← Finset.sum_mul]
            congr 1
            exact_mod_cast Nat.sum_range_choose j
        _ ≤ 2 ^ n * Cχ * M := by
            have hC0 : 0 ≤ Cχ := (norm_nonneg _).trans (hC 0 (by omega) x)
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by omega) x hx)
            have : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
            have : 0 ≤ Cχ * M := by positivity
            nlinarith only [this, ‹(2 : ℝ) ^ j ≤ 2 ^ n›]
    · rw [(hevz x hx).iteratedDeriv_eq j, iteratedDeriv_const]
      have hC0 : 0 ≤ Cχ := (norm_nonneg _).trans (hC 0 (by omega) x)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by omega) 0 ⟨by linarith, by linarith⟩)
      have : 0 ≤ 2 ^ n * Cχ * M := by positivity
      split_ifs <;> simpa using this

end Core

/-- **`ct:morse-expansion`** (`constant_terms_lower.tex`, Lemma "Finite real stationary-phase expansion in a Morse coordinate").
Let `r ≥ 1`, `a > 0`, `χ ∈ C_c^∞((-a,a))` real, equal to `1` near `0`, and `B` of class `C^{2r}` on `(-a,a)` with
`|B^{(j)}| ≤ M` there (`j ≤ 2r`).  Then for either sign `σ = ±1` and every `μ ≥ 1`,
`∫ χ B e^{iσμX²/2} dX = e^{iσπ/4} √(2π/μ) [Σ_{m<r} B^{(2m)}(0)/m! (iσ/(2μ))^m + R]` with `‖R‖ ≤ C M μ^{-r}`,
where `C` depends only on `r, χ, a` (uniform in `B`, `σ`, `μ`). -/
theorem morse_expansion {a : ℝ} (ha : 0 < a) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞' χ) (hχs : tsupport χ ⊆ Ioo (-a) a)
    (hχ1 : ∀ᶠ x in 𝓝 (0 : ℝ), χ x = 1) {r : ℕ} (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ {σ μ : ℝ} {B : ℝ → ℂ} {M : ℝ}, (σ = 1 ∨ σ = -1) → 1 ≤ μ →
      ContDiffOn ℝ (2 * r : ℕ) B (Ioo (-a) a) →
      (∀ j ≤ 2 * r, ∀ x ∈ Ioo (-a) a, ‖iteratedDeriv j B x‖ ≤ M) →
      ∃ R : ℂ, (∫ x : ℝ, (χ x : ℂ) * B x * Complex.exp (Complex.I * ((σ * μ : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2)) =
          Complex.exp (σ * (π / 4) * Complex.I) * ((Real.sqrt (2 * π / μ) : ℝ) : ℂ) *
            ((∑ m ∈ Finset.range r, iteratedDeriv (2 * m) B 0 / (m.factorial : ℂ) *
                (Complex.I * σ / (2 * μ)) ^ m) + R) ∧
          ‖R‖ ≤ C * M / μ ^ r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨δ, hδ, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < δ → χ x = 1 := by
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hχ1
    exact ⟨ε, hε, fun x hx => h (by simpa [Real.dist_eq] using hx)⟩
  have h0 : ∀ x, a < |x| → χ x = 0 := by
    intro x hx
    have : x ∉ tsupport χ := fun h => by
      have := abs_lt.mpr (hχs h)
      linarith
    exact image_eq_zero_of_notMem_tsupport this
  obtain ⟨C0, hC0⟩ := morse_core hχ hδ hδ1 h0 ha.le s
  obtain ⟨Cχ, hCχ0, hC⟩ := chic_deriv_bound hχ h0 (2 * (s + 1))
  refine ⟨(C0 * (2 ^ (2 * (s + 1)) * Cχ)) / Real.sqrt (2 * π), fun {σ μ B M} hσ hμ hB hM => ?_⟩
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hfc, hfs, hfb⟩ := cutoff_amp ha hχ hχs hB hM hC
  set f : ℝ → ℂ := fun x => chic χ x * B x with hf
  have hE := hC0 (σ := σ) (μ := μ) (f := f) (M := 2 ^ (2 * (s + 1)) * Cχ * M) hσ hμ hfc hfs hfb
  -- Taylor coefficients agree
  have hfB : f =ᶠ[𝓝 (0 : ℝ)] B := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with y hy
    simp [hf, chic_one hδ1 (by simpa [Real.dist_eq] using hy)]
  have hS : Ssum σ μ (s + 1) f = ∑ m ∈ Finset.range (s + 1), iteratedDeriv (2 * m) B 0 / (m.factorial : ℂ) *
      (Complex.I * σ / (2 * μ)) ^ m := by
    unfold Ssum
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hfB.iteratedDeriv_eq (2 * m)]
  have hW : Wint (σ * μ) f = ∫ x : ℝ, (χ x : ℂ) * B x * Complex.exp (Complex.I * ((σ * μ : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2) := by
    unfold Wint osc
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [hf, chic]
  have hG : Gc σ μ ≠ 0 := by
    unfold Gc
    refine mul_ne_zero (Complex.exp_ne_zero _) ?_
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hGn : ‖Gc σ μ‖ = Real.sqrt (2 * π / μ) := by
    unfold Gc
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have : ‖Complex.exp (σ * (π / 4) * Complex.I)‖ = 1 := by
      have : (σ : ℂ) * (π / 4) * Complex.I = Complex.I * ((σ * π / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact norm_cexp_I_mul _
    rw [this, one_mul]
  refine ⟨Eerr σ μ (s + 1) f / Gc σ μ, ?_, ?_⟩
  · rw [hS.symm, ← hW]
    show Wint (σ * μ) f = Gc σ μ * (Ssum σ μ (s + 1) f + Eerr σ μ (s + 1) f / Gc σ μ)
    have h1 : Gc σ μ * (Eerr σ μ (s + 1) f / Gc σ μ) = Eerr σ μ (s + 1) f := mul_div_cancel₀ _ hG
    rw [mul_add, h1]
    unfold Eerr
    ring
  · rw [norm_div, hGn]
    have hsq : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
    have hsq2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    have hprod : Real.sqrt μ * Real.sqrt (2 * π / μ) = Real.sqrt (2 * π) := by
      rw [← Real.sqrt_mul hμ0.le]; congr 1; field_simp
    have hpos : 0 < Real.sqrt (2 * π / μ) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hpos]
    calc ‖Eerr σ μ (s + 1) f‖ ≤ C0 * (2 ^ (2 * (s + 1)) * Cχ * M) / (μ ^ (s + 1) * Real.sqrt μ) := hE
      _ = (C0 * (2 ^ (2 * (s + 1)) * Cχ) / Real.sqrt (2 * π) * M / μ ^ (s + 1)) * Real.sqrt (2 * π / μ) := by
          rw [← hprod]
          field_simp

/-- info: 'FormalResearch.SignUncertainty.CtMorse.morse_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms morse_expansion

end FormalResearch.SignUncertainty.CtMorse
