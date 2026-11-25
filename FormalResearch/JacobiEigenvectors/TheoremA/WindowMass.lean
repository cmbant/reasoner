module

public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowEnvelopes

/-!
# Paper J, Layer 2: the window mass (`lem:tha-M`, `PropThaM`, plan item L2.C4)

Source: app_thmA "Window mass", lemma `lem:tha-M` (steps 1-3 of its proof).  Frozen statement: `PropThaM`
(`TheoremA/Statements.lean`).  Notation: `y = kappaBal(a) U(a,.)` (the normalised pair `ut`), `A = max(-a,0)`,
`I = [5/4 sqrt A, 7/4 sqrt A]`, `q(z) = -(z^2/4 + a)` (`= A - z^2/4` on `I`), `s_A = sqrt A + l_A/4`.

## The chain of lemmas (status; the assembly `propThaM_of_facts` is in `WindowMass2.lean`)

* **(W0) envelope-Wronskian** (paper Step 1(i), Lemma (3)): `wm_pointwise`, `wm_env_pointwise`.  Proved.
* **(V) virial identity** (paper eq:tha-virial): `wm_virial`.  Proved.
* **(M1i) continuous mass, large A** (paper Step 1(i)): `wm_mass_region`.  Proved.
* **(M1ii), (M1iii) compactness** (paper Step 1(ii), (iii)): `wm_c1`.  There is `c_1 > 0` with
  `int_s^rho (kappaBal U)^2 >= c_1` for all `a <= a_+` and `|s| <= s_A`.  Proved: large `A` by `wm_mass_region`, the
  compact range `[-A_0, 0]` by continuity of the parametric integral (`pc.cont_U` gives joint continuity of `U`,
  `Gamma` is continuous and positive on `(0, inf)`; the discontinuity of `kappaBal` at `a = 0` is handled by the two
  continuous branches `wmK1`, `wmK2`) and positivity (`U(a, .)` cannot vanish on an interval by `wronsk`), and `0 < a <= a_+`
  likewise.  No extra chart fact is needed.
* **(M2) lattice transfer** (paper Step 2): `WmBlock`, `wm_lower_U`, `wm_lower_L`, `wm_count` (lattice facts), used in
  `WindowMass2.lean`.  Proved, with a derivative-bound (Lipschitz) Riemann estimate instead of the paper's monotone one.
* **(M3), (C)** (two-site Casoratian and corrector step): `WindowMass2.lean`.  Proved.

## Differences from the paper

* The paper's monotone-Riemann transfer is replaced by a Lipschitz estimate (`|(y^2)'| <= 2 C_1^2`, from `env_well`
  through `winCB`), because `y^2` is not monotone on the window (`wm_lower_U`, `wm_lower_L`).
* The paper's corrector bounds `g_- / 2 <= A^[m] <= 2 g_+` and `|B^[m]| <= C_B` (lem:cha-PCcoord) are not derivable from
  the frozen chart fields (`cas_lb`, `A_bd`, `B_bd`: `Fcas` involves the free `pp`/`PiM`, and `B_bd` is weighted by the free
  `rho`).  The upper bound `|A| <= K_A` is `A_bd`; the lower bound and the bound on `B` are the new chart fields
  `gm`, `CBc` (`consts_pos4`, `corr_PC`, `Charts/SoftParabolicCylinder.lean`): confirmed and refined finding F-PW6 (both the
  lower bound on `AA` and the bound on `BB` are needed, on the rows of the PC patch with `|u_k - u_c| <= 2 eta`).
* **Finding (frozen `PropThaM` is not provable as stated).**  `PropThaM` quantifies over arbitrary `U V` with no premise on
  them (unlike `PropThaWin`, which has `cPC CPC` and `ParabolicCylinderFacts U V cPC CPC` inside the statement), so e.g.
  `U = 0` would make all three conjuncts false.  Minimal correction in `TheoremA/Statements.lean`: give `PropThaM` the
  parameters `(cPC CPC : ℝ)` and the premise `ParabolicCylinderFacts U V cPC CPC` after `intro`, as in `PropThaWin`.  Here the
  theorem `propThaM_of_facts` takes `pc : ParabolicCylinderFacts U V cPC CPC` as a hypothesis and concludes `PropThaM`
  (which then holds for every such `U`, `V`); the frozen file is not edited.

## Not formalised

Nothing of the lemma.  The chart field `corr_PC` (paper: lem:cha-PCcoord) is a hypothesis of the chart, not proved here.

Axiom pins are at the end of each file.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Real intervalIntegral
open FormalResearch.JacobiEigenvectors.Charts
open FormalResearch.JacobiEigenvectors.Engine (cas)

section Virial

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma wm_slice_smooth (hf : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : ContDiff ℝ ⊤ (U a) := by
  exact hf.slice_U a

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
  rw [ite_eq_left ha]
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
    rw [ite_eq_right hn]
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
    push Not at h
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


section Compact

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma wm_gamma_cont : Continuous (fun a : ℝ => Real.Gamma (1 / 2 + |a|)) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have hne : ∀ m : ℕ, (1 / 2 + |a|) ≠ -(m : ℝ) := fun m h => by
    have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h2 := abs_nonneg a
    linarith
  exact (Real.differentiableAt_Gamma hne).continuousAt.comp (f := fun a : ℝ => 1 / 2 + |a|)
    (by fun_prop)

lemma wm_gamma_pos (a : ℝ) : 0 < Real.Gamma (1 / 2 + |a|) :=
  Real.Gamma_pos_of_pos (by have := abs_nonneg a; linarith)

/-- `kappaBal` on `a <= 0`, as a globally continuous function. -/
def wmK1 (a : ℝ) : ℝ := (Real.Gamma (1 / 2 + |a|)) ^ (-(1 : ℝ) / 2)

/-- `kappaBal` on `a > 0`, as a globally continuous function. -/
def wmK2 (a : ℝ) : ℝ := (2 * Real.pi) ^ (-(1 : ℝ) / 4) * Real.sqrt (Real.Gamma (1 / 2 + |a|))

lemma wmK1_cont : Continuous wmK1 := by
  unfold wmK1
  exact wm_gamma_cont.rpow_const (fun a => Or.inl (wm_gamma_pos a).ne')

lemma wmK2_cont : Continuous wmK2 := by
  unfold wmK2
  exact continuous_const.mul (Real.continuous_sqrt.comp wm_gamma_cont)

lemma wmK1_pos (a : ℝ) : 0 < wmK1 a := Real.rpow_pos_of_pos (wm_gamma_pos a) _

lemma wmK2_pos (a : ℝ) : 0 < wmK2 a := by
  unfold wmK2
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.sqrt_pos.mpr (wm_gamma_pos a))

lemma wm_kappa_eq1 {a : ℝ} (ha : a ≤ 0) : kappaBal a = wmK1 a := by
  unfold kappaBal wmK1
  rw [ite_eq_left ha, abs_of_nonpos ha]
  congr 2

lemma wm_kappa_eq2 {a : ℝ} (ha : 0 < a) : kappaBal a = wmK2 a := by
  unfold kappaBal wmK2
  rw [ite_eq_right (not_le.mpr ha), abs_of_pos ha]

/-- the window integrand `(kappa U(a, c + t))^2` is not a.e. zero on `(0, l)`: `U(a,.)` and `U'(a,.)` cannot vanish at a common point (Wronskian). -/
lemma wm_not_zero (hf : ParabolicCylinderFacts U V cPC CPC) (a c l : ℝ) (hl : 0 < l) :
    ∃ t ∈ Set.Ioo (0 : ℝ) l, U a (c + t) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : U a (c + l / 2) = 0 := hcon (l / 2) ⟨by linarith, by linarith⟩
  have hder : deriv (U a) (c + l / 2) = 0 := by
    have hm : Set.Ioo c (c + l) ∈ nhds (c + l / 2) := Ioo_mem_nhds (by linarith) (by linarith)
    have : (U a) =ᶠ[nhds (c + l / 2)] fun _ => (0 : ℝ) := by
      filter_upwards [hm] with z hz
      have := hcon (z - c) ⟨by linarith [hz.1], by linarith [hz.2]⟩
      simpa using this
    rw [this.deriv_eq]
    simp
  have hw := hf.wronsk a (c + l / 2)
  rw [h0, hder] at hw
  have hpos : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have : Real.sqrt (2 / Real.pi) = 0 := by rw [← hw]; ring
  linarith

lemma wm_param_pos (hf : ParabolicCylinderFacts U V cPC CPC) (κ : ℝ) (hκ : κ ≠ 0) (a c l : ℝ) (hl : 0 < l) :
    0 < ∫ t in (0 : ℝ)..l, (κ * U a (c + t)) ^ 2 := by
  obtain ⟨t1, ht1, hne⟩ := wm_not_zero hf a c l hl
  have hU : Continuous (U a) := (wm_slice_smooth hf a).continuous
  have hcont : Continuous (fun t : ℝ => (κ * U a (c + t)) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun t => sq_nonneg _)
    (hcont.intervalIntegrable _ _)]
  refine ⟨hl, ?_⟩
  have hopen : IsOpen (Function.support (fun t : ℝ => (κ * U a (c + t)) ^ 2) ∩ Set.Ioo 0 l) :=
    hcont.isOpen_support.inter isOpen_Ioo
  have hmem : t1 ∈ Function.support (fun t : ℝ => (κ * U a (c + t)) ^ 2) ∩ Set.Ioo 0 l := by
    refine ⟨?_, ht1⟩
    simp only [Function.mem_support]
    exact pow_ne_zero 2 (mul_ne_zero hκ hne)
  have hpos := hopen.measure_pos MeasureTheory.volume ⟨t1, hmem⟩
  exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Ioc_self))

lemma wm_param_cont (hf : ParabolicCylinderFacts U V cPC CPC) (κ c : ℝ → ℝ) (hκ : Continuous κ) (hc : Continuous c)
    (l : ℝ) : Continuous (fun a : ℝ => ∫ t in (0 : ℝ)..l, (κ a * U a (c a + t)) ^ 2) := by
  have hU := hf.cont_U
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun a t => (κ a * U a (c a + t)) ^ 2) ?_ 0 l
  have h1 : Continuous (fun p : ℝ × ℝ => U p.1 (c p.1 + p.2)) :=
    hU.comp (continuous_fst.prodMk ((hc.comp continuous_fst).add continuous_snd))
  exact ((hκ.comp continuous_fst).mul h1).pow 2

lemma wm_min_pos {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {F : ℝ → ℝ} (hF : Continuous F)
    (hpos : ∀ a ∈ K, 0 < F a) : ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, m ≤ F a := by
  obtain ⟨a0, ha0, hmin⟩ := hK.exists_isMinOn hne hF.continuousOn
  exact ⟨F a0, hpos a0 ha0, fun a ha => hmin ha⟩

/-- the cut `s_A` as a function of `a`. -/
def wmCut (a : ℝ) : ℝ := Real.sqrt (max (-a) 0) + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) / 4

/-- the window end `rho(a) = 2 sqrt A + l_A`. -/
def wmRho (a : ℝ) : ℝ := 2 * Real.sqrt (max (-a) 0) + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)

lemma wmCut_cont : Continuous wmCut := by
  unfold wmCut
  have h1 : Continuous (fun a : ℝ => max (-a) 0) := by fun_prop
  have h2 : Continuous (fun a : ℝ => (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) :=
    (continuous_const.add h1).rpow_const (fun a => Or.inl (by have := le_max_right (-a) 0; linarith : (1 + max (-a) 0) ≠ 0))
  exact (Real.continuous_sqrt.comp h1).add (h2.div_const 4)

lemma wm_ell_le_one (a : ℝ) : (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) ≤ 1 := by
  have h := le_max_right (-a) 0
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

lemma wm_ell_pos (a : ℝ) : 0 < (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) :=
  Real.rpow_pos_of_pos (by have := le_max_right (-a) 0; linarith) _

lemma wm_rho_sub_cut (a : ℝ) : wmRho a - wmCut a = Real.sqrt (max (-a) 0) + 3 / 4 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := by
  unfold wmRho wmCut; ring

/-- **Step 1 of lem:tha-M (continuous mass)**: there is `c_1 > 0` (depending on `a_+`, `C_PC` and `U`) with
`int_s^rho (kappa U(a,z))^2 dz >= c_1` for every `a <= a_+` and every cut `|s| <= s_A`. -/
lemma wm_c1 (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ a : ℝ, a ≤ aplus → ∀ s : ℝ, |s| ≤ wmCut a →
      c1 ≤ ∫ z in s..(wmRho a), (kappaBal a * U a z) ^ 2 := by
  have hC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hU : ∀ a, Continuous (U a) := fun a => (wm_slice_smooth hf a).continuous
  have hnn : ∀ a, ∀ κ : ℝ, ∀ x y : ℝ, IntervalIntegrable (fun z => (κ * U a z) ^ 2) MeasureTheory.volume x y :=
    fun a κ x y => (by have := hU a; fun_prop : Continuous fun z => (κ * U a z) ^ 2).intervalIntegrable _ _
  set A0 : ℝ := max 27 (128 * CPC ^ 4 / Real.sqrt 15) with hA0
  have hA0_27 : 27 ≤ A0 := le_max_left _ _
  have hs15 : 0 < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  set lstar : ℝ := 3 / 4 * (1 + A0) ^ (-(1 : ℝ) / 6) with hlstar
  have hlstar_pos : 0 < lstar := by
    rw [hlstar]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
  -- case 2: -A0 <= a <= 0
  obtain ⟨F2, hF2pos, hF2⟩ : ∃ m : ℝ, 0 < m ∧ ∀ a ∈ Set.Icc (-A0) 0,
      m ≤ ∫ t in (0 : ℝ)..lstar, (wmK1 a * U a (wmCut a + t)) ^ 2 :=
    wm_min_pos (isCompact_Icc) ⟨0, by simp; linarith⟩
      (wm_param_cont hf wmK1 wmCut wmK1_cont wmCut_cont lstar)
      (fun a _ => wm_param_pos hf _ (wmK1_pos a).ne' a _ _ hlstar_pos)
  -- case 3: 0 < a <= a_+
  obtain ⟨F3, hF3pos, hF3⟩ : ∃ m : ℝ, 0 < m ∧ ∀ a ∈ Set.Icc 0 (max aplus 0),
      m ≤ ∫ t in (0 : ℝ)..(3 / 4), (wmK2 a * U a ((1 / 4 : ℝ) + t)) ^ 2 :=
    wm_min_pos (isCompact_Icc) ⟨0, by simp⟩
      (wm_param_cont hf wmK2 (fun _ => (1 / 4 : ℝ)) wmK2_cont continuous_const (3 / 4))
      (fun a _ => wm_param_pos hf _ (wmK2_pos a).ne' a _ _ (by norm_num))
  refine ⟨min (Real.sqrt 15 / (128 * CPC ^ 2)) (min F2 F3), lt_min (by positivity) (lt_min hF2pos hF3pos), ?_⟩
  intro a ha s hs
  have hsc : s ≤ wmCut a := le_trans (le_abs_self s) hs
  rcases le_or_gt a (-A0) with hlarge | hnot
  · -- large `A`
    have hA : 27 ≤ -a := by linarith
    have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
    have hC4 : 128 * CPC ^ 4 ≤ Real.sqrt 15 * (-a) := by
      have h1 : 128 * CPC ^ 4 / Real.sqrt 15 ≤ -a := le_trans (le_max_right _ _) (by linarith)
      have h1' := (div_le_iff₀ hs15).mp h1
      linarith
    have hmass := wm_mass_region hf a hA hC4
    have hs1 : 1 ≤ Real.sqrt (-a) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    have hell := wm_ell_le_one a
    have hell0 := wm_ell_pos a
    unfold wmCut at hsc
    rw [hmax] at hsc hell hell0
    have hI1 : s ≤ 5 / 4 * Real.sqrt (-a) := by linarith
    have hI2 : 7 / 4 * Real.sqrt (-a) ≤ wmRho a := by
      unfold wmRho; rw [hmax]; linarith
    have hI3 : 5 / 4 * Real.sqrt (-a) ≤ 7 / 4 * Real.sqrt (-a) := by linarith
    refine le_trans (min_le_left _ _) (le_trans hmass ?_)
    exact intervalIntegral.integral_mono_interval hI1 hI3 hI2
      (Filter.Eventually.of_forall fun z => sq_nonneg _) (hnn a _ _ _)
  · rcases le_or_gt a 0 with hmid | hpos
    · -- compact range `[-A0, 0]`
      have hmem : a ∈ Set.Icc (-A0) 0 := ⟨le_of_lt hnot, hmid⟩
      have h2 := hF2 a hmem
      rw [wm_kappa_eq1 hmid]
      have hshift : (∫ t in (0 : ℝ)..lstar, (wmK1 a * U a (wmCut a + t)) ^ 2) =
          ∫ z in (wmCut a)..(wmCut a + lstar), (wmK1 a * U a z) ^ 2 := by
        have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := lstar)
          (fun z => (wmK1 a * U a z) ^ 2) (wmCut a)
        simpa using this
      have hbd : wmCut a + lstar ≤ wmRho a := by
        have hA : max (-a) 0 ≤ A0 := max_le (by linarith) (by linarith)
        have hmono : (1 + A0) ^ (-(1 : ℝ) / 6) ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) :=
          Real.rpow_le_rpow_of_nonpos (by have := le_max_right (-a) 0; linarith) (by linarith) (by norm_num)
        have h3 := wm_rho_sub_cut a
        have h4 := Real.sqrt_nonneg (max (-a) 0)
        rw [hlstar]
        linarith
      have hmono := intervalIntegral.integral_mono_interval hsc (by linarith : wmCut a ≤ wmCut a + lstar) hbd
        (Filter.Eventually.of_forall fun z => sq_nonneg _) (hnn a (wmK1 a) _ _)
      refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_trans ?_ hmono))
      rw [← hshift]; exact h2
    · -- `0 < a <= a_+`
      have hmem : a ∈ Set.Icc 0 (max aplus 0) := ⟨hpos.le, le_trans ha (le_max_left _ _)⟩
      have h3 := hF3 a hmem
      rw [wm_kappa_eq2 hpos]
      have hmax : max (-a) 0 = 0 := max_eq_right (by linarith)
      have hcut : wmCut a = 1 / 4 := by
        unfold wmCut; rw [hmax]; norm_num
      have hrho : wmRho a = 1 := by
        unfold wmRho; rw [hmax]; norm_num
      have hshift : (∫ t in (0 : ℝ)..(3 / 4), (wmK2 a * U a ((1 / 4 : ℝ) + t)) ^ 2) =
          ∫ z in (1 / 4 : ℝ)..(1 / 4 + 3 / 4), (wmK2 a * U a z) ^ 2 := by
        have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 3 / 4)
          (fun z => (wmK2 a * U a z) ^ 2) (1 / 4 : ℝ)
        simpa using this
      rw [hrho]
      rw [hcut] at hsc
      have hmono := intervalIntegral.integral_mono_interval hsc (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4 + 3 / 4)
        (by norm_num : (1 / 4 : ℝ) + 3 / 4 ≤ 1)
        (Filter.Eventually.of_forall fun z => sq_nonneg _) (hnn a (wmK2 a) _ _)
      refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans ?_ hmono))
      rw [← hshift]; exact h3

end Compact


section Lattice

/-! ### Abstract lattice lemmas (Step 2 and Step 3 of lem:tha-M): a monotone block of rows `Z na < ... < Z nb` with gaps at most `δ` -/

lemma wm_chain {Z : ℤ → ℝ} {na nb : ℤ} {ε δ : ℝ}
    (hsp : ∀ n, na ≤ n → n < nb → ε ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ δ) :
    ∀ n m : ℤ, na ≤ n → n ≤ m → m ≤ nb →
      ((m - n : ℤ) : ℝ) * ε ≤ Z m - Z n ∧ Z m - Z n ≤ ((m - n : ℤ) : ℝ) * δ := by
  intro n m hn hnm hm
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ m - n by omega)
  have key : ∀ k : ℕ, n + (k : ℤ) ≤ nb →
      (k : ℝ) * ε ≤ Z (n + k) - Z n ∧ Z (n + k) - Z n ≤ (k : ℝ) * δ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by push_cast at hk; omega)
      have h2 := hsp (n + (k : ℤ)) (by omega) (by push_cast at hk; omega)
      have e : n + ((k + 1 : ℕ) : ℤ) = n + (k : ℤ) + 1 := by push_cast; ring
      rw [e]
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have e : m = n + (k : ℤ) := by omega
  subst e
  simpa using key k (by omega)

lemma wm_cross {Z : ℤ → ℝ} {na nb : ℤ} (hab : na ≤ nb) (t : ℝ) (h1 : Z na ≤ t) (h2 : t < Z nb) :
    ∃ k, na ≤ k ∧ k < nb ∧ Z k ≤ t ∧ t < Z (k + 1) := by
  have hlt : na < nb := by
    by_contra hc
    have : na = nb := by omega
    subst this
    linarith
  have hne : ((Finset.Ico na nb).filter (fun n => Z n ≤ t)).Nonempty :=
    ⟨na, by simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨le_rfl, hlt⟩, h1⟩⟩
  set k := ((Finset.Ico na nb).filter (fun n => Z n ≤ t)).max' hne with hk
  have hkmem := Finset.max'_mem _ hne
  rw [← hk] at hkmem
  simp only [Finset.mem_filter, Finset.mem_Ico] at hkmem
  refine ⟨k, hkmem.1.1, hkmem.1.2, hkmem.2, ?_⟩
  by_contra hc
  push Not at hc
  by_cases hk1 : k + 1 < nb
  · have hmem : k + 1 ∈ (Finset.Ico na nb).filter (fun n => Z n ≤ t) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, hk1⟩, hc⟩
    have := Finset.le_max' _ _ hmem
    rw [← hk] at this
    omega
  · have : k + 1 = nb := by omega
    rw [this] at hc
    linarith

lemma wm_cells (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (z : ℕ → ℝ) (δ D : ℝ) (K : ℕ)
    (hz : ∀ i, i ≤ K → z i ≤ z (i + 1) ∧ z (i + 1) - z i ≤ δ ∧
      ∀ x ∈ Set.Icc (z i) (z (i + 1)), g x ≤ g (z i) + D * δ) :
    ∫ x in (z 0)..(z (K + 1)), g x ≤
      δ * ∑ i ∈ Finset.range (K + 1), g (z i) + D * δ * (z (K + 1) - z 0) := by
  have cell : ∀ i, i ≤ K → ∫ x in (z i)..(z (i + 1)), g x ≤ δ * g (z i) + D * δ * (z (i + 1) - z i) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hz i hi
    have hle := intervalIntegral.integral_mono_on h1 (hint _ _)
      ((continuous_const (y := g (z i) + D * δ)).intervalIntegrable (μ := MeasureTheory.volume) _ _) h3
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    nlinarith [mul_le_mul_of_nonneg_left h2 (hg0 (z i))]
  induction K with
  | zero =>
    have := cell 0 le_rfl
    simpa using this
  | succ K ih =>
    have ih' := ih (fun i hi => hz i (by omega)) (fun i hi => cell i (by omega))
    have hc := cell (K + 1) le_rfl
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hint (z 0) (z (K + 1))) (hint (z (K + 1)) (z (K + 1 + 1)))
    rw [Finset.sum_range_succ]
    nlinarith [ih', hc, hadj]

lemma wm_cells_int (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (Z : ℤ → ℝ) (k0 k1 : ℤ) (hk : k0 ≤ k1) (δ D : ℝ)
    (hz : ∀ n, k0 ≤ n → n ≤ k1 → Z n ≤ Z (n + 1) ∧ Z (n + 1) - Z n ≤ δ ∧
      ∀ x ∈ Set.Icc (Z n) (Z (n + 1)), g x ≤ g (Z n) + D * δ) :
    ∫ x in (Z k0)..(Z (k1 + 1)), g x ≤
      δ * ∑ n ∈ Finset.Icc k0 k1, g (Z n) + D * δ * (Z (k1 + 1) - Z k0) := by
  obtain ⟨K, hK⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k1 - k0 by omega)
  have hk1 : k1 = k0 + (K : ℤ) := by omega
  subst hk1
  have h := wm_cells g hg0 hint (fun i : ℕ => Z (k0 + (i : ℤ))) δ D K (by
    intro i hi
    have e : k0 + ((i + 1 : ℕ) : ℤ) = k0 + (i : ℤ) + 1 := by push_cast; ring
    simp only [e]
    exact hz (k0 + (i : ℤ)) (by omega) (by omega))
  have e1 : k0 + ((K + 1 : ℕ) : ℤ) = k0 + (K : ℤ) + 1 := by push_cast; ring
  simp only [Nat.cast_zero, add_zero, e1] at h
  rw [sum_Icc_range (fun n => g (Z n)) k0 K]
  exact h

lemma wm_int_le (g : ℝ → ℝ) (B a b : ℝ) (hab : a ≤ b)
    (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (hg : ∀ x ∈ Set.Icc a b, g x ≤ B) : ∫ x in a..b, g x ≤ B * (b - a) := by
  have := intervalIntegral.integral_mono_on hab (hint a b)
    ((continuous_const (y := B)).intervalIntegrable (μ := MeasureTheory.volume) _ _) hg
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

/-- the block data used by both lower-sum lemmas. -/
structure WmBlock (Z : ℤ → ℝ) (na nb : ℤ) (ρ δ : ℝ) : Prop where
  nab : na ≤ nb
  sp : ∀ n, na ≤ n → n < nb → 0 < Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ δ
  rng : ∀ n, na ≤ n → n ≤ nb → -ρ ≤ Z n ∧ Z n ≤ ρ
  low : Z na < -ρ + δ
  up : ρ - δ < Z nb

lemma WmBlock.mono {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ : ℝ} (hB : WmBlock Z na nb ρ δ) {n m : ℤ} (hn : na ≤ n) (hnm : n ≤ m)
    (hm : m ≤ nb) : Z n ≤ Z m := by
  have := (wm_chain (ε := 0) (fun n h1 h2 => ⟨(hB.sp n h1 h2).1.le, (hB.sp n h1 h2).2⟩)) n m hn hnm hm
  simpa using this.1

lemma WmBlock.cell {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ : ℝ} (hB : WmBlock Z na nb ρ δ) {g : ℝ → ℝ} {D : ℝ}
    (hLip : ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ → g x ≤ g y + D * δ)
    {n : ℤ} (hn : na ≤ n) (hn' : n < nb) :
    Z n ≤ Z (n + 1) ∧ Z (n + 1) - Z n ≤ δ ∧ ∀ x ∈ Set.Icc (Z n) (Z (n + 1)), g x ≤ g (Z n) + D * δ := by
  obtain ⟨h1, h2⟩ := hB.sp n hn hn'
  refine ⟨by linarith, h2, fun x hx => ?_⟩
  have r1 := hB.rng n hn hn'.le
  have r2 := hB.rng (n + 1) (by omega) (by omega)
  exact hLip x ⟨by linarith [hx.1], by linarith [hx.2]⟩ (Z n) ⟨r1.1, r1.2⟩ hx.1 (by linarith [hx.2])

/-- Lower sum over the rows right of the cut `t`: `int_t^rho g <= delta sum_{Z_n > t} g(Z_n) + 2 D delta rho + 2 B delta`. -/
lemma wm_lower_U {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ : ℝ} (hB : WmBlock Z na nb ρ δ) (hδ : 0 < δ)
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    {B D : ℝ} (hD : 0 ≤ D) (hgB : ∀ x ∈ Set.Icc (-ρ) ρ, g x ≤ B)
    (hLip : ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ → g x ≤ g y + D * δ)
    {t : ℝ} (ht1 : -ρ + δ ≤ t) (ht2 : t + 2 * δ < ρ) :
    (∫ x in t..ρ, g x) ≤
      δ * ∑ n ∈ (Finset.Icc na nb).filter (fun n => t < Z n), g (Z n) + 2 * D * δ * ρ + 2 * B * δ := by
  have hB0 : 0 ≤ B := le_trans (hg0 0) (hgB 0 ⟨by linarith, by linarith⟩)
  have hna : Z na ≤ t := by linarith [hB.low]
  have hnb : t < Z nb := by linarith [hB.up]
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := wm_cross (Z := Z) (na := na) (nb := nb) hB.nab t hna hnb
  have hstep := (hB.sp k hk1 hk2).2
  have hk5 : k + 1 < nb := by
    by_contra hc
    have : k + 1 = nb := by omega
    rw [this] at hk4
    have hup := hB.up
    have : Z nb ≤ Z k + δ := by
      have := (hB.sp k hk1 hk2).2
      rw [show k + 1 = nb from by omega] at this
      linarith
    linarith
  have hcell := wm_cells_int g hg0 hint Z (k + 1) (nb - 1) (by omega) δ D (fun n h1 h2 =>
    hB.cell hLip (by omega) (by omega))
  have e1 : nb - 1 + 1 = nb := by ring
  rw [e1] at hcell
  have r_k1 := hB.rng (k + 1) (by omega) (by omega)
  have r_nb := hB.rng nb hB.nab le_rfl
  have hZk1 : t < Z (k + 1) := hk4
  have int1 : ∫ x in t..(Z (k + 1)), g x ≤ B * δ := by
    have := wm_int_le g B t (Z (k + 1)) hZk1.le hint (fun x hx => hgB x ⟨by linarith [hx.1], by linarith [hx.2, r_k1.2]⟩)
    nlinarith [mul_le_mul_of_nonneg_left (show Z (k + 1) - t ≤ δ by linarith) hB0]
  have int3 : ∫ x in (Z nb)..ρ, g x ≤ B * δ := by
    have := wm_int_le g B (Z nb) ρ r_nb.2 hint (fun x hx => hgB x ⟨by linarith [hx.1, r_nb.1], hx.2⟩)
    nlinarith [mul_le_mul_of_nonneg_left (show ρ - Z nb ≤ δ by linarith [hB.up]) hB0]
  have hsplit : (∫ x in t..ρ, g x) = (∫ x in t..(Z (k + 1)), g x) + (∫ x in (Z (k + 1))..(Z nb), g x) +
      ∫ x in (Z nb)..ρ, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hsub : ∑ n ∈ Finset.Icc (k + 1) (nb - 1), g (Z n) ≤
      ∑ n ∈ (Finset.Icc na nb).filter (fun n => t < Z n), g (Z n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hg0 _)
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_filter] at hn ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have := hB.mono (by omega : na ≤ k + 1) (by omega : k + 1 ≤ n) (by omega : n ≤ nb)
    linarith
  have hrange : Z nb - Z (k + 1) ≤ 2 * ρ := by linarith [r_nb.2, r_k1.1]
  have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc (k + 1) (nb - 1), g (Z n) :=
    Finset.sum_nonneg (fun n _ => hg0 _)
  nlinarith [mul_le_mul_of_nonneg_left hrange (mul_nonneg hD hδ.le), mul_le_mul_of_nonneg_left hsub hδ.le]

/-- Lower sum over the rows left of the cut `t`: `int_{-rho}^t g <= delta sum_{Z_n <= t} g(Z_n) + 2 D delta rho + B delta`. -/
lemma wm_lower_L {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ : ℝ} (hB : WmBlock Z na nb ρ δ) (hδ : 0 < δ)
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    {B D : ℝ} (hD : 0 ≤ D) (hgB : ∀ x ∈ Set.Icc (-ρ) ρ, g x ≤ B)
    (hLip : ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ → g x ≤ g y + D * δ)
    {t : ℝ} (ht1 : -ρ + δ ≤ t) (ht2 : t < ρ - δ) :
    (∫ x in (-ρ)..t, g x) ≤
      δ * ∑ n ∈ (Finset.Icc na nb).filter (fun n => Z n ≤ t), g (Z n) + 2 * D * δ * ρ + B * δ := by
  have hB0 : 0 ≤ B := le_trans (hg0 0) (hgB 0 ⟨by linarith, by linarith⟩)
  have hna : Z na ≤ t := by linarith [hB.low]
  have hnb : t < Z nb := by linarith [hB.up]
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := wm_cross (Z := Z) (na := na) (nb := nb) hB.nab t hna hnb
  have hcell := wm_cells_int g hg0 hint Z na k hk1 δ D (fun n h1 h2 =>
    hB.cell hLip h1 (by omega))
  have r_na := hB.rng na le_rfl hB.nab
  have r_k1 := hB.rng (k + 1) (by omega) (by omega)
  have int1 : ∫ x in (-ρ)..(Z na), g x ≤ B * δ := by
    have := wm_int_le g B (-ρ) (Z na) r_na.1 hint (fun x hx => hgB x ⟨hx.1, by linarith [hx.2, r_na.2]⟩)
    nlinarith [mul_le_mul_of_nonneg_left (show Z na - -ρ ≤ δ by linarith [hB.low]) hB0]
  have int2 : ∫ x in (Z na)..t, g x ≤ ∫ x in (Z na)..(Z (k + 1)), g x :=
    intervalIntegral.integral_mono_interval le_rfl hna hk4.le (Filter.Eventually.of_forall hg0) (hint _ _)
  have hsplit : (∫ x in (-ρ)..t, g x) = (∫ x in (-ρ)..(Z na), g x) + ∫ x in (Z na)..t, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hsub : ∑ n ∈ Finset.Icc na k, g (Z n) ≤
      ∑ n ∈ (Finset.Icc na nb).filter (fun n => Z n ≤ t), g (Z n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hg0 _)
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_filter] at hn ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have := hB.mono (by omega : na ≤ n) (by omega : n ≤ k) (by omega : k ≤ nb)
    linarith
  have hrange : Z (k + 1) - Z na ≤ 2 * ρ := by linarith [r_na.1, r_k1.2]
  nlinarith [mul_le_mul_of_nonneg_left hrange (mul_nonneg hD hδ.le), mul_le_mul_of_nonneg_left hsub hδ.le]

/-- Rows in a window `(α, β]` and their number (`(K+2) δ > β - α`). -/
lemma wm_count {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ : ℝ} (hB : WmBlock Z na nb ρ δ) (hδ : 0 < δ) {α β : ℝ}
    (hαβ : α + 2 * δ ≤ β) (hα : Z na ≤ α) (hβ : β < Z nb) :
    ∃ k0 : ℤ, ∃ K : ℕ, na ≤ k0 ∧ k0 + (K : ℤ) + 1 ≤ nb ∧
      (∀ i : ℕ, i ≤ K → α < Z (k0 + i) ∧ Z (k0 + i) ≤ β) ∧ β - α < ((K : ℝ) + 2) * δ := by
  have hαnb : α < Z nb := by linarith
  obtain ⟨ka, ha1, ha2, ha3, ha4⟩ := wm_cross (Z := Z) (na := na) (nb := nb) hB.nab α hα hαnb
  obtain ⟨kb, hb1, hb2, hb3, hb4⟩ := wm_cross (Z := Z) (na := na) (nb := nb) hB.nab β (by linarith) hβ
  have hstepa := (hB.sp ka ha1 ha2).2
  have hkab : ka + 1 ≤ kb := by
    by_contra hc
    have hle : kb + 1 ≤ ka + 1 := by omega
    have := hB.mono (by omega : na ≤ kb + 1) hle (by omega : ka + 1 ≤ nb)
    linarith
  obtain ⟨K, hK⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ kb - (ka + 1) by omega)
  have hkb : kb = ka + 1 + (K : ℤ) := by omega
  refine ⟨ka + 1, K, by omega, by omega, ?_, ?_⟩
  · intro i hi
    constructor
    · have := hB.mono (by omega : na ≤ ka + 1) (by omega : ka + 1 ≤ ka + 1 + (i : ℤ)) (by omega : ka + 1 + (i : ℤ) ≤ nb)
      linarith
    · have := hB.mono (by omega : na ≤ ka + 1 + (i : ℤ)) (by omega : ka + 1 + (i : ℤ) ≤ kb) (by omega : kb ≤ nb)
      linarith
  · have hch := wm_chain (ε := 0) (fun n h1 h2 => ⟨(hB.sp n h1 h2).1.le, (hB.sp n h1 h2).2⟩) (ka + 1) kb
      (by omega) (by omega) (by omega)
    have hstepb := (hB.sp kb hb1 hb2).2
    have e : ((kb - (ka + 1) : ℤ) : ℝ) = (K : ℝ) := by rw [hK]; simp
    rw [e] at hch
    linarith [hch.2]

/-- the pair-sum lemma: `c_3 M_n^2 <= phi_n^2 + phi_{n+1}^2` on `K+1` consecutive rows and the mass of those rows give the sum of `phi^2` over any set containing them. -/
lemma wm_pair_sum (φ M : ℤ → ℝ) (S : Finset ℤ) (k0 : ℤ) (K : ℕ) (c3 c4 mm : ℝ) (hc3 : 0 ≤ c3)
    (hS : ∀ i : ℕ, i ≤ K + 1 → k0 + (i : ℤ) ∈ S)
    (hpair : ∀ i : ℕ, i ≤ K → c3 * M (k0 + i) ^ 2 ≤ φ (k0 + i) ^ 2 + φ (k0 + i + 1) ^ 2)
    (hmass : c4 * mm ≤ ∑ i ∈ Finset.range (K + 1), M (k0 + i) ^ 2) :
    c3 * c4 * mm / 2 ≤ ∑ n ∈ S, φ n ^ 2 := by
  have h1 : ∑ i ∈ Finset.range (K + 1), φ (k0 + i) ^ 2 ≤ ∑ n ∈ S, φ n ^ 2 := by
    have hinj : Set.InjOn (fun i : ℕ => k0 + (i : ℤ)) (Finset.range (K + 1) : Set ℕ) := by
      intro x _ y _ hxy
      simpa using hxy
    rw [← Finset.sum_image (f := fun n => φ n ^ 2) (g := fun i : ℕ => k0 + (i : ℤ)) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact hS i (by simp at hi; omega)
  have h2 : ∑ i ∈ Finset.range (K + 1), φ (k0 + i + 1) ^ 2 ≤ ∑ n ∈ S, φ n ^ 2 := by
    have hinj : Set.InjOn (fun i : ℕ => k0 + (i : ℤ) + 1) (Finset.range (K + 1) : Set ℕ) := by
      intro x _ y _ hxy
      simpa using hxy
    rw [← Finset.sum_image (f := fun n => φ n ^ 2) (g := fun i : ℕ => k0 + (i : ℤ) + 1) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have := hS (i + 1) (by simp at hi; omega)
    simpa [add_assoc] using this
  have h3 : c3 * ∑ i ∈ Finset.range (K + 1), M (k0 + i) ^ 2 ≤
      ∑ i ∈ Finset.range (K + 1), (φ (k0 + i) ^ 2 + φ (k0 + i + 1) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hpair i (by simp at hi; omega))
  rw [Finset.sum_add_distrib] at h3
  nlinarith [mul_le_mul_of_nonneg_left hmass hc3]

/-- the two-site Casoratian inequality. -/
lemma wm_cas_two (φ ψ A : ℤ → ℝ) (n : ℤ) (c0 CA T : ℝ) (hc0 : 0 < c0) (hA0 : 0 ≤ A n) (hA : A n ≤ CA)
    (hT0 : 0 ≤ T) (hψ0 : |ψ n| ≤ T) (hψ1 : |ψ (n + 1)| ≤ T) (hcas : c0 ≤ |cas A φ ψ n|) :
    c0 ^ 2 ≤ 2 * (CA * T) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := by
  have h1 : |cas A φ ψ n| ≤ A n * (|φ (n + 1)| * |ψ n| + |φ n| * |ψ (n + 1)|) := by
    unfold cas
    rw [abs_mul, abs_of_nonneg hA0]
    apply mul_le_mul_of_nonneg_left _ hA0
    calc |φ (n + 1) * ψ n - φ n * ψ (n + 1)| ≤ |φ (n + 1) * ψ n| + |φ n * ψ (n + 1)| := abs_sub _ _
      _ = |φ (n + 1)| * |ψ n| + |φ n| * |ψ (n + 1)| := by rw [abs_mul, abs_mul]
  have h2 : |φ (n + 1)| * |ψ n| + |φ n| * |ψ (n + 1)| ≤ T * (|φ n| + |φ (n + 1)|) := by
    nlinarith [mul_le_mul_of_nonneg_left hψ0 (abs_nonneg (φ (n + 1))),
      mul_le_mul_of_nonneg_left hψ1 (abs_nonneg (φ n))]
  have hCA0 : 0 ≤ CA := le_trans hA0 hA
  have h3 : c0 ≤ CA * (T * (|φ n| + |φ (n + 1)|)) := by
    calc c0 ≤ |cas A φ ψ n| := hcas
      _ ≤ A n * (|φ (n + 1)| * |ψ n| + |φ n| * |ψ (n + 1)|) := h1
      _ ≤ A n * (T * (|φ n| + |φ (n + 1)|)) := mul_le_mul_of_nonneg_left h2 hA0
      _ ≤ CA * (T * (|φ n| + |φ (n + 1)|)) :=
          mul_le_mul_of_nonneg_right hA (mul_nonneg hT0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  have h4 : c0 ^ 2 ≤ (CA * T) ^ 2 * (|φ n| + |φ (n + 1)|) ^ 2 := by
    have e : CA * (T * (|φ n| + |φ (n + 1)|)) = (CA * T) * (|φ n| + |φ (n + 1)|) := by ring
    rw [e] at h3
    calc c0 ^ 2 ≤ ((CA * T) * (|φ n| + |φ (n + 1)|)) ^ 2 := pow_le_pow_left₀ hc0.le h3 2
      _ = (CA * T) ^ 2 * (|φ n| + |φ (n + 1)|) ^ 2 := by ring
  have h5 : (|φ n| + |φ (n + 1)|) ^ 2 ≤ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := by
    nlinarith [sq_nonneg (|φ n| - |φ (n + 1)|), sq_abs (φ n), sq_abs (φ (n + 1))]
  calc c0 ^ 2 ≤ (CA * T) ^ 2 * (|φ n| + |φ (n + 1)|) ^ 2 := h4
    _ ≤ (CA * T) ^ 2 * (2 * (φ n ^ 2 + φ (n + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    _ = 2 * (CA * T) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := by ring

end Lattice

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

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_c1

end FormalResearch.JacobiEigenvectors.TheoremA

end

end
