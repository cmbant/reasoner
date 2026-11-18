module

public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder

/-!
# Paper J, Layer 2: the window mass (`lem:tha-M`, `PropThaM`, plan item L2.C4)

Source: app_thmA "Window mass", lemma `lem:tha-M` (steps 1-3 of its proof).  Frozen statement: `PropThaM`
(`TheoremA/Statements.lean`).  Notation: `y = kappaBal(a) U(a,.)` (the normalised pair `ut`), `A = max(-a,0)`,
`I = [5/4 sqrt A, 7/4 sqrt A]`, `q(z) = -(z^2/4 + a)` (`= A - z^2/4` on `I`), `s_A = sqrt A + l_A/4`.

## The chain of lemmas (status)

* **(W0) envelope-Wronskian** (paper Step 1(i), Lemma (3)).  From the unit Wronskian `wronsk` and the envelopes of
  `env_well` on `0 <= z <= 2 sqrt(-a)` (where `Ewell = 1`): `sqrt(k2) / (2 CPC^2) <= k2 y^2 + y'^2` and
  `|y y'| <= CPC^2` (`wm_pointwise`, `wm_env_pointwise`).  **Proved.**
* **(V) virial identity** (paper eq:tha-virial).  `2 int_I q y^2 = int_I (y'^2 + q y^2) - [y y']`, from `ode_U`
  (`y'' = (z^2/4+a) y`).  (`wm_virial`.)  **Proved.**
* **(M1i) continuous mass, large A** (paper Step 1(i)).  For `A >= A_0 = max(27, 128 CPC^4/sqrt 15)`:
  `int_I y^2 >= sqrt 15/(128 CPC^2)`.  Uses `k2 = q` on `I` (cube-root bound, `A >= 27`).  (`wm_mass_region`.)
  **Proved.**
* **(M1ii) compactness in a, a in [-A_0, 0]** (paper Step 1(ii)).  `F(a) = int_{s_A}^{s_A + l_*} utilde(a,Z)^2 dZ`
  is continuous (joint smoothness of `U` in `(a,z)`, continuity of `s_A`, of `kappaBal` (`Gamma` continuous and
  positive on `(0, inf)`)) and positive (`U(a,.)` cannot vanish on an interval, else `wronsk` fails there), so
  `min F > 0` on the compact range.  **Open** (needs parametric-integral continuity and `Gamma` continuity in Lean).
* **(M1iii) 0 < a <= a_+** (paper Step 1(iii)).  The same with the barrier normalisation `kappaBal U`; the
  interval `[1/4, 1]` (`A = 0`, `rho = 1`).  **Open** (as M1ii).
* **(M2) lattice transfer on Omega_s** (paper Step 2).  If `int_s^rho y^2 >= c_1` then
  `sum_{Omega_s} y(Z_n)^2 Delta_n >= c_1/2` for small `h`: the Riemann error is at most `d_+ sqrt h` times the
  integral of `|(y^2)'| <= 2 C^2` on the region.  **Open**: the monotone Riemann lemma of `WindowEnvelopes` does not
  apply (`y^2` is not monotone on the window); a derivative-bound Riemann lemma is needed.
* **(M3) the two-site Casoratian** (paper Step 3, `mu~ > delta`).  `|W(phi^(1), phi^(2))| = h^{1/2}|F_cas| >= h^{1/2}/2`
  (`cas_lb` and the Casoratian identity of the engine), then the site bound and `int_J M^2 >= 1/2`.  **Open**: the
  Casoratian identity and the bound on the window sites are engine statements not yet in Lean.
* **(C) corrector step** (paper eq:tha-corrstep).  `|phi^(1)_n - A^[m] y(Z_n)| <= C h M` and `g_- / 2 <= A^[m] <= 2 g_+`.
  **Open**: see the insufficiency note below.

## Insufficiency of the frozen third conjunct (the minimal correction)

`phi_eq_dot` (`TheoremA/SoftTransfer.lean`): `phi h 0 2 k = dot (vrow (AA 2) (BB 2) (u_k) h) (wf 2 0 (u_k) h)`, i.e.
`phi = AA_2 * wf_2^0 + h BB_2 * wf_2^1`.  By `wf2_eq`, `wf_2^0 = pcMinus_0 = kappaBal U(a,-Z)` on the window rows, and
`h BB_2 * wf_2^1 = O(sqrt h)`.  So `phi/kappaBal = AA_2 U(a,-Z_n) + O(sqrt h)`, and the third conjunct of `PropThaM`
needs a *positive lower bound on `AA_2` at the window rows*.  The frozen fields give `cas_lb`, `A_bd`, `B_bd` (`PreValid`)
and do not give a lower bound on `AA_2`; the paper's `g_- / 2 <= A^[m]` (app_thmA Step 3) is not a frozen field.
Minimal correction: a chart field `corrPC_lb` stating `c_A <= (chain).AA 2 (u_k) h` on the window rows (analogous to
`collar_lbW`), or the derivation of that bound from `cas_lb` (not checked here).  The first two conjuncts (with the
uncorrected `U`) do not use `AA` and need only (M1)-(M2).

Axiom pins are at the end of the file.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Real intervalIntegral
open FormalResearch.JacobiEigenvectors.Charts

section Virial

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma wm_slice_smooth (hf : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : ContDiff ℝ ⊤ (U a) := by
  have h := hf.smooth_U.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ⊤ (fun w : ℝ => (a, w)))
  exact h

lemma wm_deriv_smooth (hf : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) :
    ContDiff ℝ ⊤ (deriv (U a)) :=
  (wm_slice_smooth hf a).deriv'

/-- the virial identity for the Weber solution `U(a, .)`, `U'' = (z^2/4 + a) U`:
`2 int_alpha^beta q (kappa U)^2 = int_alpha^beta (E) - [(kappa U)(kappa U')]`, `q = -(z^2/4+a)`, `E = (kappa U')^2 + q (kappa U)^2`. -/
lemma wm_virial (hf : ParabolicCylinderFacts U V cPC CPC) (a κ α β : ℝ) :
    2 * ∫ z in α..β, (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2 =
      (∫ z in α..β, ((κ * deriv (U a) z) ^ 2 + (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2))
        - ((κ * U a β) * (κ * deriv (U a) β) - (κ * U a α) * (κ * deriv (U a) α)) := by
  have hU : Continuous (U a) := (wm_slice_smooth hf a).continuous
  have hU' : Continuous (deriv (U a)) := (wm_deriv_smooth hf a).continuous
  have hd : ∀ z, HasDerivAt (U a) (deriv (U a) z) z := fun z =>
    ((wm_slice_smooth hf a).differentiable (by simp) z).hasDerivAt
  have hd' : ∀ z, HasDerivAt (deriv (U a)) (deriv (deriv (U a)) z) z := fun z =>
    ((wm_deriv_smooth hf a).differentiable (by simp) z).hasDerivAt
  have hF : ∀ z ∈ Set.uIcc α β, HasDerivAt (fun w => (κ * U a w) * (κ * deriv (U a) w))
      ((κ * deriv (U a) z) ^ 2 + (z ^ 2 / 4 + a) * (κ * U a z) ^ 2) z := by
    intro z _
    have h1 : HasDerivAt (fun w => κ * U a w) (κ * deriv (U a) z) z := (hd z).const_mul κ
    have h2 : HasDerivAt (fun w => κ * deriv (U a) w) (κ * deriv (deriv (U a)) z) z :=
      (hd' z).const_mul κ
    have h3 := h1.mul h2
    convert h3 using 1
    rw [hf.ode_U a z]
    ring
  have hG : Continuous (fun z => (κ * deriv (U a) z) ^ 2 + (z ^ 2 / 4 + a) * (κ * U a z) ^ 2) := by
    fun_prop
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hG.intervalIntegrable _ _)
  have hQ : Continuous (fun z => (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2) := by fun_prop
  have hsplit : (∫ z in α..β, ((κ * deriv (U a) z) ^ 2 + (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2)) =
      (∫ z in α..β, ((κ * deriv (U a) z) ^ 2 + (z ^ 2 / 4 + a) * (κ * U a z) ^ 2)) +
        2 * ∫ z in α..β, (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2 := by
    have e1 : (fun z => (κ * deriv (U a) z) ^ 2 + (-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2) =
        fun z => ((κ * deriv (U a) z) ^ 2 + (z ^ 2 / 4 + a) * (κ * U a z) ^ 2) +
          2 * ((-(z ^ 2 / 4 + a)) * (κ * U a z) ^ 2) := by
      funext z; ring
    rw [e1, intervalIntegral.integral_add (hG.intervalIntegrable _ _) ((hQ.intervalIntegrable _ _).const_mul 2),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hFT]
  ring

lemma wm_kappa_pos {a : ℝ} (ha : a ≤ 0) : 0 < kappaBal a := by
  unfold kappaBal
  rw [if_pos ha]
  apply Real.rpow_pos_of_pos
  apply Real.Gamma_pos_of_pos
  linarith

lemma wm_k2_ge_one (a z : ℝ) : 1 ≤ k2 a z := by
  unfold k2
  refine le_trans ?_ (le_max_right _ _)
  exact Real.one_le_rpow (le_max_right _ _) (by norm_num)

lemma wm_mbal_sq_sqrt (a z : ℝ) : Mbal a z ^ 2 * Real.sqrt (k2 a z) = 1 := by
  have hk : 0 < k2 a z := lt_of_lt_of_le one_pos (wm_k2_ge_one a z)
  unfold Mbal
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, Real.sqrt_eq_rpow, ← Real.rpow_add hk]
  norm_num

/-- the envelope-Wronskian lower bound (Step 1(i), Lemma (3) of app_thmA): `K P^2 + P'^2 >= sqrt K / (2 C^2)`,
and `|P P'| <= C^2`, from the unit Wronskian `P Q' - P' Q = 1` and the two envelopes `P^2 + P'^2/K <= (C M)^2`, `Q^2 + Q'^2/K <= (C M)^2`,
`M^2 sqrt K = 1`. -/
lemma wm_pointwise (P P' Q Q' K M C : ℝ) (hK : 0 < K) (hC : 0 < C) (hM : 0 ≤ M)
    (hMK : M ^ 2 * Real.sqrt K = 1) (hW : P * Q' - P' * Q = 1)
    (hPe : P ^ 2 + P' ^ 2 / K ≤ (C * M) ^ 2) (hQe : Q ^ 2 + Q' ^ 2 / K ≤ (C * M) ^ 2) :
    Real.sqrt K / (2 * C ^ 2) ≤ K * P ^ 2 + P' ^ 2 ∧ |P * P'| ≤ C ^ 2 := by
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hKs : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hCM : 0 ≤ C * M := mul_nonneg hC.le hM
  have hQ'sq : Q' ^ 2 ≤ K * (C * M) ^ 2 := by
    have h1 : Q' ^ 2 / K ≤ (C * M) ^ 2 := by linarith [sq_nonneg Q]
    have h2 := (div_le_iff₀ hK).mp h1
    linarith [mul_comm ((C * M) ^ 2) K]
  have hP'sq : P' ^ 2 ≤ K * (C * M) ^ 2 := by
    have h1 : P' ^ 2 / K ≤ (C * M) ^ 2 := by linarith [sq_nonneg P]
    have h2 := (div_le_iff₀ hK).mp h1
    linarith [mul_comm ((C * M) ^ 2) K]
  have hQ'abs : |Q'| ≤ Real.sqrt K * (C * M) := by
    rw [← sq_le_sq₀ (abs_nonneg _) (mul_nonneg hsK.le hCM), sq_abs, mul_pow, hKs]
    exact hQ'sq
  have hQabs : |Q| ≤ C * M := by
    rw [← sq_le_sq₀ (abs_nonneg _) hCM, sq_abs]
    have : 0 ≤ Q' ^ 2 / K := div_nonneg (sq_nonneg _) hK.le
    linarith
  have hW' : 1 ≤ C * M * (Real.sqrt K * |P| + |P'|) := by
    have h1 : P * Q' - P' * Q ≤ |P| * |Q'| + |P'| * |Q| := by
      nlinarith [abs_mul P Q', abs_mul P' Q, le_abs_self (P * Q'), neg_le_abs (P' * Q)]
    have h2 : |P| * |Q'| ≤ |P| * (Real.sqrt K * (C * M)) :=
      mul_le_mul_of_nonneg_left hQ'abs (abs_nonneg _)
    have h3 : |P'| * |Q| ≤ |P'| * (C * M) := mul_le_mul_of_nonneg_left hQabs (abs_nonneg _)
    nlinarith [h1, h2, h3, hW]
  have hS : 0 ≤ Real.sqrt K * |P| + |P'| := by positivity
  have hS2 : (Real.sqrt K * |P| + |P'|) ^ 2 ≤ 2 * (K * P ^ 2 + P' ^ 2) := by
    have e : (Real.sqrt K * |P|) ^ 2 = K * P ^ 2 := by rw [mul_pow, sq_abs, hKs]
    nlinarith [sq_nonneg (Real.sqrt K * |P| - |P'|), sq_abs P']
  have h2 : 1 ≤ 2 * C ^ 2 * M ^ 2 * (K * P ^ 2 + P' ^ 2) := by
    have hC2 : 0 ≤ C ^ 2 * M ^ 2 := by positivity
    have hX : 1 ≤ (C * M * (Real.sqrt K * |P| + |P'|)) ^ 2 := by nlinarith
    have e : (C * M * (Real.sqrt K * |P| + |P'|)) ^ 2 =
        C ^ 2 * M ^ 2 * (Real.sqrt K * |P| + |P'|) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hS2 hC2]
  have h3 : Real.sqrt K ≤ 2 * C ^ 2 * (K * P ^ 2 + P' ^ 2) := by
    have e : Real.sqrt K * (2 * C ^ 2 * M ^ 2 * (K * P ^ 2 + P' ^ 2)) =
        2 * C ^ 2 * (K * P ^ 2 + P' ^ 2) := by
      linear_combination (2 * C ^ 2 * (K * P ^ 2 + P' ^ 2)) * hMK
    calc Real.sqrt K = Real.sqrt K * 1 := (mul_one _).symm
      _ ≤ Real.sqrt K * (2 * C ^ 2 * M ^ 2 * (K * P ^ 2 + P' ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hsK.le
      _ = 2 * C ^ 2 * (K * P ^ 2 + P' ^ 2) := e
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · have hP2 : P ^ 2 ≤ (C * M) ^ 2 := by
      have := div_nonneg (sq_nonneg P') hK.le
      linarith
    have hM4K : (M ^ 2) ^ 2 * K = 1 := by
      have h2' : (M ^ 2 * Real.sqrt K) ^ 2 = 1 := by rw [hMK]; norm_num
      rw [mul_pow, hKs] at h2'
      exact h2'
    have hPP : (P * P') ^ 2 ≤ (C ^ 2) ^ 2 := by
      rw [mul_pow]
      have hmul : P ^ 2 * P' ^ 2 ≤ (C * M) ^ 2 * (K * (C * M) ^ 2) :=
        mul_le_mul hP2 hP'sq (sq_nonneg _) (by positivity)
      have e : (C * M) ^ 2 * (K * (C * M) ^ 2) = (C ^ 2) ^ 2 * ((M ^ 2) ^ 2 * K) := by ring
      rw [e, hM4K, mul_one] at hmul
      exact hmul
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by rw [sq_abs]; exact hPP)

/-- the pointwise envelope bound of the normalised pair on `0 <= z <= 2 sqrt(-a)` (where `Ewell = 1`). -/
lemma wm_env_pointwise (hf : ParabolicCylinderFacts U V cPC CPC) (a z : ℝ) (ha : a ≤ 0) (hz0 : 0 ≤ z)
    (hzI : z ≤ 2 * Real.sqrt (-a)) :
    Real.sqrt (k2 a z) / (2 * CPC ^ 2) ≤ (kappaBal a * deriv (U a) z) ^ 2 + k2 a z * (kappaBal a * U a z) ^ 2 ∧
      |(kappaBal a * U a z) * (kappaBal a * deriv (U a) z)| ≤ CPC ^ 2 := by
  have hC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hκ : 0 < kappaBal a := wm_kappa_pos ha
  have hK : 0 < k2 a z := lt_of_lt_of_le one_pos (wm_k2_ge_one a z)
  have hM : 0 ≤ Mbal a z := Real.rpow_nonneg hK.le _
  have hEw : Ewell a z = 1 := by
    unfold Ewell
    have hn : ¬ (2 * Real.sqrt |a| < z) := by
      rw [abs_of_nonpos ha, not_lt]
      linarith
    rw [if_neg hn]
  obtain ⟨envU, envV⟩ := hf.env_well a ha z hz0
  rw [hEw] at envU envV
  have hPe : (kappaBal a * U a z) ^ 2 + (kappaBal a * deriv (U a) z) ^ 2 / k2 a z ≤
      (CPC * Mbal a z) ^ 2 := by
    have h := (Real.sqrt_le_iff.mp envU).2
    simpa [ut, mul_one] using h
  have hQe : (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z) ^ 2 +
      (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) ^ 2 / k2 a z ≤ (CPC * Mbal a z) ^ 2 := by
    have h := (Real.sqrt_le_iff.mp envV).2
    simpa [vt, inv_one, mul_one] using h
  have hW : (kappaBal a * U a z) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) -
      (kappaBal a * deriv (U a) z) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z) = 1 := by
    have hwr := hf.wronsk a z
    have e : (kappaBal a * U a z) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) -
        (kappaBal a * deriv (U a) z) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z) =
        Real.sqrt (Real.pi / 2) * (U a z * deriv (V a) z - deriv (U a) z * V a z) := by
      field_simp
    rw [e, hwr, ← Real.sqrt_mul (by positivity)]
    have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  have key := wm_pointwise (kappaBal a * U a z) (kappaBal a * deriv (U a) z)
    (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z)
    (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) (k2 a z) (Mbal a z) CPC hK hC hM
    (wm_mbal_sq_sqrt a z) hW hPe hQe
  refine ⟨?_, key.2⟩
  have := key.1
  linarith [this]

end Virial

section Region

lemma wm_cbrt_le (A : ℝ) (hA : 27 ≤ A) : A ^ ((1 : ℝ) / 3) ≤ 15 * A / 64 := by
  obtain ⟨t, ht⟩ : ∃ t, t = A ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  rw [← ht]
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg (by linarith) _
  have ht3 : t ^ 3 = A := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have ht3' : 3 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg ht0 ht0, mul_nonneg (mul_nonneg ht0 ht0) (sub_nonneg.2 h.le)]
  rw [← ht3]
  have h15 : 0 ≤ 15 * t ^ 2 - 64 := by nlinarith
  nlinarith [mul_nonneg ht0 h15]

/-- **Step 1(i) of lem:tha-M (continuous mass, large `A`)**: for `a <= -A_0`, with `A = -a`, the
window `I = [5/4 sqrt A, 7/4 sqrt A]` carries `int_I (kappa U)^2 >= sqrt 15 / (128 CPC^2)`. -/
lemma wm_mass_region (hf : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (hA : 27 ≤ -a)
    (hC : 128 * CPC ^ 4 ≤ Real.sqrt 15 * (-a)) :
    Real.sqrt 15 / (128 * CPC ^ 2) ≤
      ∫ z in (5 / 4 * Real.sqrt (-a))..(7 / 4 * Real.sqrt (-a)), (kappaBal a * U a z) ^ 2 := by
  have hCpos : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have ha : a ≤ 0 := by linarith
  have hA0 : 0 < -a := by linarith
  have hs2 : Real.sqrt (-a) ^ 2 = -a := Real.sq_sqrt hA0.le
  have hs0 : 0 < Real.sqrt (-a) := Real.sqrt_pos.mpr hA0
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (-a) := ⟨_, rfl⟩
  rw [← hs] at hs2 hs0 ⊢
  have hαβ : 5 / 4 * s ≤ 7 / 4 * s := by linarith
  have hI : ∀ z ∈ Set.uIcc (5 / 4 * s) (7 / 4 * s), 5 / 4 * s ≤ z ∧ z ≤ 7 / 4 * s := fun z hz => by
    rw [Set.uIcc_of_le hαβ] at hz
    exact hz
  have hq : ∀ z ∈ Set.uIcc (5 / 4 * s) (7 / 4 * s),
      15 * (-a) / 64 ≤ -(z ^ 2 / 4 + a) ∧ -(z ^ 2 / 4 + a) ≤ -a := by
    intro z hz
    obtain ⟨h1, h2⟩ := hI z hz
    have hz0 : 0 ≤ z := by linarith
    have z2a : (5 / 4 * s) ^ 2 ≤ z ^ 2 := by nlinarith
    have z2b : z ^ 2 ≤ (7 / 4 * s) ^ 2 := by nlinarith
    have e1 : (5 / 4 * s) ^ 2 = 25 / 16 * (-a) := by rw [← hs2]; ring
    have e2 : (7 / 4 * s) ^ 2 = 49 / 16 * (-a) := by rw [← hs2]; ring
    constructor <;> linarith
  have hk2 : ∀ z ∈ Set.uIcc (5 / 4 * s) (7 / 4 * s), k2 a z = -(z ^ 2 / 4 + a) := by
    intro z hz
    obtain ⟨hq1, hq2⟩ := hq z hz
    unfold k2
    have habs1 : |z ^ 2 / 4 + a| = -(z ^ 2 / 4 + a) := abs_of_nonpos (by linarith)
    have habs2 : |a| = -a := abs_of_nonpos ha
    have hm : max |a| 1 = -a := by
      rw [habs2]
      exact max_eq_left (by linarith)
    rw [habs1, hm]
    exact max_eq_left (by have := wm_cbrt_le (-a) hA; linarith)
  have hsq15 : Real.sqrt (15 * (-a) / 64) = Real.sqrt 15 * s / 8 := by
    have e : 15 * (-a) / 64 = (Real.sqrt 15 * s / 8) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), hs2]
      ring
    rw [e]
    exact Real.sqrt_sq (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs0.le) (by norm_num))
  have hEc : Continuous (fun z => (kappaBal a * deriv (U a) z) ^ 2 +
      (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2) := by
    have hU : Continuous (U a) := (wm_slice_smooth hf a).continuous
    have hU' : Continuous (deriv (U a)) := (wm_deriv_smooth hf a).continuous
    fun_prop
  have hE : ∀ z ∈ Set.uIcc (5 / 4 * s) (7 / 4 * s),
      Real.sqrt (15 * (-a) / 64) / (2 * CPC ^ 2) ≤ (kappaBal a * deriv (U a) z) ^ 2 +
        (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2 := by
    intro z hz
    obtain ⟨hq1, -⟩ := hq z hz
    obtain ⟨h1, h2⟩ := hI z hz
    have hz0 : 0 ≤ z := by linarith
    have hzI : z ≤ 2 * Real.sqrt (-a) := by rw [← hs]; linarith
    obtain ⟨hb1, -⟩ := wm_env_pointwise hf a z ha hz0 hzI
    rw [hk2 z hz] at hb1
    have hmono : Real.sqrt (15 * (-a) / 64) / (2 * CPC ^ 2) ≤
        Real.sqrt (-(z ^ 2 / 4 + a)) / (2 * CPC ^ 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr (Real.sqrt_le_sqrt hq1)
    linarith
  have hEint : (7 / 4 * s - 5 / 4 * s) * (Real.sqrt (15 * (-a) / 64) / (2 * CPC ^ 2)) ≤
      ∫ z in (5 / 4 * s)..(7 / 4 * s), ((kappaBal a * deriv (U a) z) ^ 2 +
        (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2) := by
    have := intervalIntegral.integral_mono_on hαβ
      ((continuous_const).intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (hEc.intervalIntegrable _ _) (fun z hz => hE z (by rw [Set.uIcc_of_le hαβ]; exact hz))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have hV := wm_virial hf a (kappaBal a) (5 / 4 * s) (7 / 4 * s)
  have hbd : |(kappaBal a * U a (7 / 4 * s)) * (kappaBal a * deriv (U a) (7 / 4 * s)) -
      (kappaBal a * U a (5 / 4 * s)) * (kappaBal a * deriv (U a) (5 / 4 * s))| ≤ 2 * CPC ^ 2 := by
    have hb : ∀ z, 5 / 4 * s ≤ z → z ≤ 7 / 4 * s →
        |(kappaBal a * U a z) * (kappaBal a * deriv (U a) z)| ≤ CPC ^ 2 := by
      intro z h1 h2
      exact (wm_env_pointwise hf a z ha (by linarith) (by rw [← hs]; linarith)).2
    have b1 := hb (7 / 4 * s) hαβ le_rfl
    have b2 := hb (5 / 4 * s) le_rfl hαβ
    have := abs_sub ((kappaBal a * U a (7 / 4 * s)) * (kappaBal a * deriv (U a) (7 / 4 * s)))
      ((kappaBal a * U a (5 / 4 * s)) * (kappaBal a * deriv (U a) (5 / 4 * s)))
    linarith
  have hqJ : ∫ z in (5 / 4 * s)..(7 / 4 * s), (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2 ≤
      (-a) * ∫ z in (5 / 4 * s)..(7 / 4 * s), (kappaBal a * U a z) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    have hqc : Continuous (fun z : ℝ => (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2) := by
      have hU : Continuous (U a) := (wm_slice_smooth hf a).continuous
      fun_prop
    have hpc : Continuous (fun z : ℝ => (kappaBal a * U a z) ^ 2) := by
      have hU : Continuous (U a) := (wm_slice_smooth hf a).continuous
      fun_prop
    refine intervalIntegral.integral_mono_on hαβ (hqc.intervalIntegrable _ _)
      ((hpc.const_mul (-a)).intervalIntegrable _ _) (fun z hz => ?_)
    obtain ⟨hq1, hq2⟩ := hq z (by rw [Set.uIcc_of_le hαβ]; exact hz)
    have hp : 0 ≤ (kappaBal a * U a z) ^ 2 := sq_nonneg _
    nlinarith
  have hC2 : 0 < CPC ^ 2 := by positivity
  have hsE : (7 / 4 * s - 5 / 4 * s) * (Real.sqrt (15 * (-a) / 64) / (2 * CPC ^ 2)) =
      Real.sqrt 15 * (-a) / (32 * CPC ^ 2) := by
    rw [hsq15]
    have : (7 / 4 * s - 5 / 4 * s) * (Real.sqrt 15 * s / 8 / (2 * CPC ^ 2)) =
        Real.sqrt 15 * s ^ 2 / (32 * CPC ^ 2) := by
      field_simp
      ring
    rw [this, hs2]
  have key2 : 2 * (-a) * (Real.sqrt 15 / (128 * CPC ^ 2)) ≤
      Real.sqrt 15 * (-a) / (32 * CPC ^ 2) - 2 * CPC ^ 2 := by
    have e : Real.sqrt 15 * (-a) / (32 * CPC ^ 2) - 2 * CPC ^ 2 -
        2 * (-a) * (Real.sqrt 15 / (128 * CPC ^ 2)) =
        (Real.sqrt 15 * (-a) - 128 * CPC ^ 4) / (64 * CPC ^ 2) := by
      field_simp
      ring
    have : 0 ≤ (Real.sqrt 15 * (-a) - 128 * CPC ^ 4) / (64 * CPC ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have h1 : Real.sqrt 15 * (-a) / (32 * CPC ^ 2) - 2 * CPC ^ 2 ≤
      2 * ∫ z in (5 / 4 * s)..(7 / 4 * s), (-(z ^ 2 / 4 + a)) * (kappaBal a * U a z) ^ 2 := by
    rw [hV]
    rw [hsE] at hEint
    linarith [le_trans (le_abs_self _) hbd]
  have hfin : 2 * (-a) * (Real.sqrt 15 / (128 * CPC ^ 2)) ≤
      2 * (-a) * ∫ z in (5 / 4 * s)..(7 / 4 * s), (kappaBal a * U a z) ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_left hfin (by linarith)

end Region

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_virial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_virial

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_pointwise

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_env_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_env_pointwise

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_mass_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_mass_region

end FormalResearch.JacobiEigenvectors.TheoremA

end

end
