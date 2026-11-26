module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpTheta
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpSeparation
public import FormalResearch.ModularBootstrap.Mixtures.CommonSource

/-!
# The hypothesis structure of `pmix:smooth` and the Cardy weight against the tip-normalised comb weight

`positive_mixtures.tex`, Lemma PM.6 (`pmix:smooth`), hypotheses (i)-(ii).  `SmoothWeight w` is a family of weights
`V c' t` (`V c'` the weight at `a = c'/12`, weight `w`) with

* (i) a smooth positive amplitude: the real Cardy asymptote
  `|V(c'x²/3)/((2x)^{w-1} as(c'L(x))) - A(x)| ≤ K/c'` on the Langer window `x ∈ [ξ_*/2, ξ_* + 1/2]`, with `A(ξ_*) > 0`
  and `A ≥ 0`, Lipschitz on the window, so that `q(x) = (2x)^{w-1} A(x)/(1 - e^{-4πx})²` is smooth and positive at `ξ_*`
  (the paper writes the asymptote multiplicatively, `V = q V_Vir (1 + O(1/n))`; the additive form is equivalent since
  `q` and `V_Vir/as` are bounded above and below on the window);
* (ii) the far-band bound `CardyFarBoundP (w - 1) V (ξ_* + 1/2)` (`K_2 = w - 1`);
* `V ≥ 0`, continuity of `V c'`, and the domination `V ≤ C_d K_a` (used only to integrate `h V`; it holds for every
  Cardy weight, with `C_d = ‖λ‖_TV` for a source).

`theta_boundS` is `theta_boundW` (`RampedBumpTheta`, the weight of the Cardy ratio against the comb weight) with the
amplitude `Q(e^{-4πx})` of a product replaced by the amplitude `A` of the structure.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.Special

/-- **The hypotheses of `pmix:smooth`** (see the module docstring) for a weight family `V c' t` at weight `w`. -/
structure SmoothWeight (w : ℕ) (hw : 1 ≤ w) where
  V : ℝ → ℝ → ℝ
  A : ℝ → ℝ
  c₀ : ℝ
  K : ℝ
  hK : 0 ≤ K
  L : ℝ
  hL : 0 ≤ L
  Cd : ℝ
  hCd : 0 ≤ Cd
  nonneg : ∀ {c' t : ℝ}, c₀ ≤ c' → 0 ≤ t → 0 ≤ V c' t
  cont : ∀ {c' : ℝ}, c₀ ≤ c' → Continuous (V c')
  dom : ∀ {c' t : ℝ}, c₀ ≤ c' → 0 ≤ t → V c' t ≤ Cd * kernelK w (c' / 12) t
  asymp : ∀ {c' x : ℝ}, c₀ ≤ c' → x ∈ langerX (1 / 2) →
    |V c' (c' * x ^ 2 / 3) / ((2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) - A x| ≤ K / c'
  A_pos : 0 < A xiStar
  A_nonneg : ∀ x ∈ langerX (1 / 2), 0 ≤ A x
  A_lip : ∀ x ∈ langerX (1 / 2), |A x - A xiStar| ≤ L * |x - xiStar|
  far : CardyFarBoundP (w - 1) V (xiStar + 1 / 2)

namespace SmoothWeight

variable {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw)

/-- The scale `q = (2ξ_*)^{w-1} A(ξ_*)/(1 - e^{-4πξ_*})²` (`= qProb prob` for `A = Q(e^{-4πx})`). -/
noncomputable def q : ℝ :=
  (2 * xiStar) ^ (w - 1) * W.A xiStar / (1 - Real.exp (-(4 * π * xiStar))) ^ 2

lemma q_pos : 0 < W.q := by
  have h1 := one_sub_exp_xiStar_pos
  have h2 := W.A_pos
  have h3 := xiStar_pos
  unfold q
  positivity

/-- `A ≤ A(ξ_*) + L (1/2 + ξ_*)` on the window. -/
lemma A_le {x : ℝ} (hx : x ∈ langerX (1 / 2)) : W.A x ≤ W.A xiStar + W.L * (1 / 2 + xiStar) := by
  have h1 := (abs_le.1 (W.A_lip x hx)).2
  have hd : |x - xiStar| ≤ 1 / 2 + xiStar := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, xiStar_pos]
  nlinarith only [h1, mul_le_mul_of_nonneg_left hd W.hL]

/-- `x ↦ (2x)^{w-1} A(x)` is Lipschitz on the window, around `ξ_*`. -/
lemma fS_lipschitz : ∃ L' : ℝ, 0 ≤ L' ∧ ∀ x ∈ langerX (1 / 2),
    |(2 * x) ^ (w - 1) * W.A x - (2 * xiStar) ^ (w - 1) * W.A xiStar| ≤ L' * |x - xiStar| := by
  have hxs := xiStar_pos
  set p : ℕ := w - 1 with hp
  set M : ℝ := 2 * (xiStar + 1 / 2) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  set CA : ℝ := W.A xiStar + W.L * (1 / 2 + xiStar) with hCA
  have hCA0 : 0 ≤ CA := by
    rw [hCA]; exact add_nonneg W.A_pos.le (mul_nonneg W.hL (by positivity))
  refine ⟨2 * p * M ^ (p - 1) * CA + (2 * xiStar) ^ p * W.L,
    add_nonneg (mul_nonneg (by positivity) hCA0) (mul_nonneg (by positivity) W.hL), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hAx0 := W.A_nonneg x hx
  have hAx1 := W.A_le hx
  have hpow : |(2 * x) ^ p - (2 * xiStar) ^ p| ≤ |2 * x - 2 * xiStar| * p * M ^ (p - 1) := by
    refine (abs_pow_sub_pow_le (2 * x) (2 * xiStar) p).trans ?_
    have hmax : max |2 * x| |2 * xiStar| ≤ M := by
      refine max_le ?_ ?_
      · rw [abs_of_pos (by linarith)]; rw [hM]; linarith [hx.2]
      · rw [abs_of_pos (by linarith)]; rw [hM]; linarith
    have := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax (p - 1)
    gcongr
  set Ax := W.A x
  set As := W.A xiStar
  have e : (2 * x) ^ p * Ax - (2 * xiStar) ^ p * As =
      ((2 * x) ^ p - (2 * xiStar) ^ p) * Ax + (2 * xiStar) ^ p * (Ax - As) := by ring
  rw [e]
  have h2 : |2 * x - 2 * xiStar| = 2 * |x - xiStar| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hP0 : 0 ≤ (2 * xiStar) ^ p := by positivity
  have hlip := W.A_lip x hx
  calc |((2 * x) ^ p - (2 * xiStar) ^ p) * Ax + (2 * xiStar) ^ p * (Ax - As)|
      ≤ |((2 * x) ^ p - (2 * xiStar) ^ p) * Ax| + |(2 * xiStar) ^ p * (Ax - As)| := abs_add_le _ _
    _ ≤ |(2 * x) ^ p - (2 * xiStar) ^ p| * CA + (2 * xiStar) ^ p * (W.L * |x - xiStar|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hAx0]
        gcongr
    _ ≤ _ := by
        rw [h2] at hpow
        nlinarith only [mul_le_mul_of_nonneg_right hpow hCA0, abs_nonneg (x - xiStar), hP0, hCA0]

end SmoothWeight

/-- The bound on `Θ / q`, `Θ = M_wt(x) · B_c/E(x)`, and `(Θ / q) (e^δ - 1)`, for a Cardy ratio `B_c` within `K/c'` of
`(2x)^{w-1} A(x)`; `q = W.q = (2ξ_*)^{w-1} A(ξ_*)/(1 - e^{-4πξ_*})²`.  (`theta_boundW` with the amplitude of the
structure.) -/
theorem theta_boundS {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (K Ca : ℝ) (hK : 0 < K) (hCa : 0 < Ca) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ᶠ c' : ℝ in atTop, ∀ x ∈ langerX (1 / 2), ∀ Bc δ : ℝ, 0 ≤ Bc →
      |Bc - (2 * x) ^ (w - 1) * W.A x| ≤ K / c' → 0 ≤ δ →
      δ ≤ Ca * c' ^ (-(2 / 3 : ℝ)) → δ ≤ 1 / 2 →
      |mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / W.q - 1| +
        mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / W.q * (Real.exp δ - 1) ≤
        c1 * lambdaComb c' * |langerTau x / lambdaComb c'| + c2 * c' ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨CM, hCM, hMw⟩ := mwt_sub_one_le
  obtain ⟨cτ, hcτ, hτ⟩ := abs_sub_xiStar_le_tau
  have hxs := xiStar_pos
  have hpi := Real.pi_pos
  have hq := W.q_pos
  have hEm := Emin_pos
  have hEsp : 0 < (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    have := one_sub_exp_xiStar_pos; positivity
  have hQs : (2 * xiStar) ^ (w - 1) * W.A xiStar =
      W.q * (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    unfold SmoothWeight.q
    exact (div_mul_cancel₀ _ hEsp.ne').symm
  set q : ℝ := W.q with hqdef
  set Es : ℝ := (1 - Real.exp (-(4 * π * xiStar))) ^ 2 with hEs
  set Qs : ℝ := (2 * xiStar) ^ (w - 1) * W.A xiStar with hQsdef
  obtain ⟨Lq, hLq0, hLip⟩ := W.fS_lipschitz
  set C0 : ℝ := (Lq + 8 * π * q) / (Emin * q) with hC0
  have hC0p : 0 < C0 := by rw [hC0]; positivity
  set R : ℝ := 2 + C0 * (1 / 2 + xiStar) with hR
  have hRp : 0 < R := by rw [hR]; positivity
  set Mmax : ℝ := 1 + CM * (1 / 2 + xiStar) with hMmax
  set K1 : ℝ := K / (Emin * q) with hK1
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  refine ⟨(CM * R + C0) / cτ, K1 + 2 * Mmax * R * Ca, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 K1)] with c' hc'
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hc'0 : 0 < c' := by linarith
  have hlam : 0 < lambdaComb c' := lamPos hc'0
  intro x hx Bc δ hBc0 hBc hδ0 hδCa hδ12
  have hx0 : 0 < x := by linarith [hx.1]
  have hxξ : xiStar / 2 ≤ x := hx.1
  set Ex : ℝ := (1 - Real.exp (-(4 * π * x))) ^ 2 with hEx
  have hExm : Emin ≤ Ex := Emin_le hxξ
  have hExp : 0 < Ex := hEm.trans_le hExm
  set ρ : ℝ := Bc / (Ex * q) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hBc0 (by positivity)
  have hΘ : mwt x * (Bc / Ex) / q = mwt x * ρ := by rw [hρ]; field_simp
  rw [hΘ]
  have hd : |x - xiStar| ≤ 1 / 2 + xiStar := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  -- distance bounds
  have hQ1 : |((2 * x) ^ (w - 1) * W.A x) - Qs| ≤ Lq * |x - xiStar| :=
    hLip x hx
  have hE1 := abs_E_sub_le hx0
  rw [← hEx, ← hEs] at hE1
  have hnum : |Bc - Ex * q| ≤ K / c' + (Lq + 8 * π * q) * |x - xiStar| := by
    have e : Bc - Ex * q = (Bc - ((2 * x) ^ (w - 1) * W.A x)) +
        (((2 * x) ^ (w - 1) * W.A x) - Qs) + q * (Es - Ex) := by
      rw [hQs]; ring
    rw [e]
    have h3 : |q * (Es - Ex)| ≤ q * (8 * π * |x - xiStar|) := by
      rw [abs_mul, abs_of_pos hq, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hE1 hq.le
    calc _ ≤ |Bc - ((2 * x) ^ (w - 1) * W.A x)| +
          |((2 * x) ^ (w - 1) * W.A x) - Qs| + |q * (Es - Ex)| := abs_add_three _ _ _
      _ ≤ K / c' + Lq * |x - xiStar| + q * (8 * π * |x - xiStar|) := by linarith
      _ = _ := by ring
  have hρ1 : |ρ - 1| ≤ K / c' / (Emin * q) + C0 * |x - xiStar| := by
    have : ρ - 1 = (Bc - Ex * q) / (Ex * q) := by rw [hρ]; field_simp
    rw [this, abs_div, abs_of_pos (by positivity : 0 < Ex * q)]
    have hden : Emin * q ≤ Ex * q := mul_le_mul_of_nonneg_right hExm hq.le
    calc |Bc - Ex * q| / (Ex * q) ≤ (K / c' + (Lq + 8 * π * q) * |x - xiStar|) / (Ex * q) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (K / c' + (Lq + 8 * π * q) * |x - xiStar|) / (Emin * q) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by rw [hC0]; field_simp
  have hε1 : K / c' / (Emin * q) ≤ 1 := by
    have : K1 ≤ c' := (le_max_right _ _).trans hc'
    rw [div_le_one (by positivity), div_le_iff₀ hc'0]
    rw [hK1, div_le_iff₀ (by positivity)] at this
    linarith
  have hρ2 : ρ ≤ R := by
    have h1 := (abs_le.1 hρ1).2
    have h2 : C0 * |x - xiStar| ≤ C0 * (1 / 2 + xiStar) := mul_le_mul_of_nonneg_left hd hC0p.le
    rw [hR]; linarith
  have hM1 : |mwt x - 1| ≤ CM * |x - xiStar| := hMw x hx
  have hMle : mwt x ≤ Mmax := by
    have := (abs_le.1 hM1).2
    have h3 : CM * |x - xiStar| ≤ CM * (1 / 2 + xiStar) := mul_le_mul_of_nonneg_left hd hCM.le
    rw [hMmax]; linarith
  have hM0 : 0 ≤ mwt x := by
    unfold mwt
    have := mUnn_pos hx0
    have := mUnn_pos hxs
    have := deriv_langerTau_pos hx0
    positivity
  have hσ : |x - xiStar| ≤ lambdaComb c' * |langerTau x / lambdaComb c'| / cτ := by
    have h := hτ x hxξ
    have : lambdaComb c' * |langerTau x / lambdaComb c'| = |langerTau x| := by
      rw [abs_div, abs_of_pos hlam]; field_simp
    rw [this, le_div_iff₀ hcτ]
    linarith
  have hexp : Real.exp δ - 1 ≤ 2 * δ := by
    have := exp_le_one_add_two_mul hδ0 hδ12
    linarith
  have hT1 : |mwt x * ρ - 1| ≤ |mwt x - 1| * ρ + |ρ - 1| := by
    have : mwt x * ρ - 1 = (mwt x - 1) * ρ + (ρ - 1) := by ring
    rw [this]
    calc |(mwt x - 1) * ρ + (ρ - 1)| ≤ |(mwt x - 1) * ρ| + |ρ - 1| := abs_add_le _ _
      _ = |mwt x - 1| * ρ + |ρ - 1| := by rw [abs_mul, abs_of_nonneg hρ0]
  have hA : |mwt x - 1| * ρ ≤ R * (CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ)) := by
    have h1 : |mwt x - 1| ≤ CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) :=
      hM1.trans (mul_le_mul_of_nonneg_left hσ hCM.le)
    have h2 := mul_le_mul h1 hρ2 hρ0 (by positivity)
    linarith
  have hB : mwt x * ρ * (Real.exp δ - 1) ≤ Mmax * R * (2 * (Ca * c' ^ (-(2 / 3 : ℝ)))) := by
    have h0 : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
    have h1 : mwt x * ρ ≤ Mmax * R := mul_le_mul hMle hρ2 hρ0 (hM0.trans hMle)
    calc mwt x * ρ * (Real.exp δ - 1) ≤ (Mmax * R) * (2 * (Ca * c' ^ (-(2 / 3 : ℝ)))) :=
          mul_le_mul h1 (hexp.trans (by linarith)) h0 (mul_nonneg (hM0.trans hMle) hRp.le)
      _ = _ := by ring
  have hC : K / c' / (Emin * q) ≤ K1 * c' ^ (-(2 / 3 : ℝ)) := by
    have : c'⁻¹ ≤ c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hc'1 (by norm_num)
    calc K / c' / (Emin * q) = K1 * c'⁻¹ := by rw [hK1]; field_simp
      _ ≤ K1 * c' ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left this (by positivity)
  have hCd : C0 * |x - xiStar| ≤ C0 * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) :=
    mul_le_mul_of_nonneg_left hσ hC0p.le
  have hfin : R * (CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ)) +
      C0 * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) =
      (CM * R + C0) / cτ * lambdaComb c' * |langerTau x / lambdaComb c'| := by ring
  linarith [hT1, hA, hB, hρ1, hC, hCd, hfin]


/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theta_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_boundW

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theta_boundS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_boundS

end FormalResearch.ModularBootstrap.Mixtures
