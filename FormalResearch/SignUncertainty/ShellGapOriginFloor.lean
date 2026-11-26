module

public import FormalResearch.SignUncertainty.ShellGapExtract
public import FormalResearch.SignUncertainty.OneProfileEnvelope

/-!
# The origin floor `eq:ce-origin-floor` (Corollary `cor:ce-projection-mass`, `ce_projection_mass.tex`)

Source: `CFT/sign_uncertainty/paper/ce_projection_mass.tex`, `cor:ce-projection-mass` and its proof, on top of
`thm:ce-physical-profile` / `thm:ce-shell-gap`.

In the normalisation `M[f_c] = 1`, `f_c = ĥ_c - h_c`, every sequence has a subsequence with profile limits
`P_∞, Q_∞` of `p_c, q_c`; with `S = P_∞ + Q_∞` (the limit of `Ψ_{ĥ_c}/M[f_c]`) the paper proves
`liminf h_c(0)/M[f_c] ≥ sup_{y>0} ℒ_y(2 Q_∞)`.

* `airyLaplace_re_le_l1` (`gt:3.1`): `ℒ_y(F) ≤ ‖F‖₁` for `F ∈ 𝒢` and `y ≥ 0`, from the sharp `H^∞` bound
  `airyFtilde_norm_le` at `ζ = i y`.
* `integral_le_add_of_locunif`: the Fatou step `‖S‖₁ ≤ liminf ‖Φ_n‖₁` for `0 ≤ Φ_n → S` locally uniformly.
* `HankelOriginFloor D` and `hankelOriginFloor_proved`: the statement in Hankel form and its proof from the
  exposed extraction `hankelShellGap_sub`, the origin mass identity `M[ĥ_k] = h_k(0)` and the Laplace constraint
  of the limit.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- `gt:3.1` in the form used by `eq:ce-origin-floor`: for `F ∈ 𝒢` and `y ≥ 0`,
`ℒ_y(F) = e^{-y³/12} ∫ F e^{yu} du ≤ ‖F‖₁`. -/
theorem airyLaplace_re_le_l1 {F : ℂ → ℂ} (hF : InAiryClass F) {y : ℝ} (hy : 0 ≤ y) :
    airyLaplace (fun u => (F (u : ℂ)).re) y ≤ ∫ u : ℝ, ‖F (u : ℂ)‖ := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hIm⟩ := hF
  have hG : AiryClassG F := by
    refine ⟨hd, hi, C, ⌈ν⌉₊, hC, fun z => (hb z).trans ?_⟩
    have : (1 + ‖z‖) ^ ν ≤ (1 + ‖z‖) ^ (⌈ν⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (Nat.le_ceil ν)
    rw [Real.rpow_natCast] at this
    gcongr
    exact airyEnv_pos z |>.le
  have hnorm := airyFtilde_norm_le hG (ζ := (y : ℂ) * I) (by simpa using hy)
  have hk := airyPhiK_pos
  have e1 : ∀ u : ℝ, cexp (-(I * ((y : ℂ) * I) * (u : ℂ))) = ((Real.exp (y * u) : ℝ) : ℂ) := fun u => by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (-(y : ℂ) * u) * Complex.I_sq
  have e2 : cexp (-(I * ((y : ℂ) * I) ^ 3 / 12)) = ((Real.exp (-(y ^ 3) / 12) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (-(y : ℂ) ^ 3 / 12 * (I ^ 2 - 1)) * Complex.I_sq
  have hF' : airyFtilde F ((y : ℂ) * I) =
      ((airyPhiK * Real.exp (-(y ^ 3) / 12) : ℝ) : ℂ) *
        ∫ u : ℝ, F (u : ℂ) * ((Real.exp (y * u) : ℝ) : ℂ) := by
    unfold airyFtilde airyFhat
    simp_rw [e1, e2]
    push_cast
    ring
  have hFr : ∀ u : ℝ, F (u : ℂ) * ((Real.exp (y * u) : ℝ) : ℂ) =
      (((F (u : ℂ)).re * Real.exp (y * u) : ℝ) : ℂ) := fun u => by
    have h1 : F (u : ℂ) = (((F (u : ℂ)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hIm u)
    conv_lhs => rw [h1]
    push_cast
    rfl
  simp_rw [hFr, integral_complex_ofReal] at hF'
  rw [hF', norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (mul_pos hk (Real.exp_pos _))] at hnorm
  have hle : Real.exp (-(y ^ 3) / 12) * |∫ u : ℝ, (F (u : ℂ)).re * Real.exp (y * u)| ≤
      ∫ u : ℝ, ‖F (u : ℂ)‖ := by
    have := hnorm
    nlinarith [this]
  unfold airyLaplace
  exact (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le).trans hle

lemma tlu_const_mul {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (a : ℝ)
    (h : TendstoLocallyUniformlyOn F f atTop univ) :
    TendstoLocallyUniformlyOn (fun n u => a * F n u) (fun u => a * f u) atTop univ := by
  have := (uniformContinuous_id.const_smul a).comp_tendstoLocallyUniformlyOn h
  simpa [Function.comp_def] using this

/-- The Fatou step: if `0 ≤ Φ_n → S` locally uniformly, with `S` integrable and `Φ_n`
integrable, then for every `ε > 0` eventually `∫ S ≤ (∫ Φ_n) + ε`. -/
theorem integral_le_add_of_locunif {Φ : ℕ → ℝ → ℝ} {S : ℝ → ℝ} (hSi : Integrable S)
    (hΦi : ∀ n, Integrable (Φ n)) (hΦnn : ∀ n u, 0 ≤ Φ n u)
    (hloc : TendstoLocallyUniformlyOn Φ S atTop univ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∫ u, S u ≤ (∫ u, Φ n u) + ε := by
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := fun m n hmn =>
    Icc_subset_Icc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
  have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.2 ⟨n, abs_le.mp hn⟩
  have ht := tendsto_setIntegral_of_monotone (μ := volume) (f := S)
    (fun n => measurableSet_Icc) hmono (by rw [hU]; exact hSi.integrableOn)
  rw [hU, Measure.restrict_univ] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))).exists
  have hab : -(m : ℝ) ≤ m := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hUn : TendstoUniformlyOn Φ S atTop (Icc (-(m : ℝ)) m) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      (hloc.mono (subset_univ _))
  have hlim := setIntegral_Icc_tendsto_unif hab hUn (Eventually.of_forall fun n => (hΦi n).integrableOn)
    hSi.integrableOn
  filter_upwards [hlim.eventually (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))] with n hn
  have h3 : ∫ u in Icc (-(m : ℝ)) m, Φ n u ≤ ∫ u, Φ n u :=
    setIntegral_le_integral (hΦi n) (Eventually.of_forall fun u => hΦnn n u)
  have h4 : ∫ u, S u < (∫ u in Icc (-(m : ℝ)) m, S u) + ε / 2 := by linarith [hm]
  have h5 : (∫ u in Icc (-(m : ℝ)) m, S u) < (∫ u in Icc (-(m : ℝ)) m, Φ n u) + ε / 2 := by linarith [hn]
  linarith [h3, h4, h5]

/-- If `a ≤ r_n + ε` eventually for every `ε > 0`, then `a ≤ liminf r_n` (in `EReal`). -/
theorem coe_le_liminf_of_forall_add {r : ℕ → ℝ} {a : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a ≤ r n + ε) :
    ((a : ℝ) : EReal) ≤ liminf (fun n => ((r n : ℝ) : EReal)) atTop := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hba : b < a := EReal.coe_lt_coe_iff.1 hb2
  have hfreq := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hb1
  have hev := h ((a - b) / 2) (by linarith)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  have := EReal.coe_lt_coe_iff.1 hn1
  linarith

/-- **`eq:ce-origin-floor`** (`ce_projection_mass.tex`, `cor:ce-projection-mass`; Hankel form). Dimensions
`d_k ≥ 2`, `c_k = d_k/2`; the hypotheses are those of `HankelShellGapLimit` (offsets `o(c^{1/3})`, Hankel
Cohn–Elkies profiles `h_k = G k`, `h_k ≤ 0` at the prescribed shells, thresholds
`T_k ≤ c/π² - (u_*/β₁)c^{1/3} + o(c^{1/3})`). With `f_k = ĥ_k - h_k` (`ĥ_k = 𝓗 G_k`), `M[·] = hankelMass` and
`Ψ = hankelWindowProfile`, there are a subsequence `K` and limits `S = P` and `Q` (`= Q_∞`) such that, in the
normalisation `M[f] = 1`: `Ψ_{ĥ}/M[f] → S` and `Ψ_f/M[f] → 2 Q_∞` locally uniformly; `(S, Q_∞)` satisfy the
system `eq:ce-laplace-constraint` (`TwoProfileFeasibleWitness`, with `H = S - 2 Q_∞`); `h_k(0)/M[f_k]` is bounded;
and along the subsequence
`liminf h_c(0)/M[f_c] ≥ sup_{y>0} ℒ_y(2 Q_∞)` (`eq:ce-origin-floor`, in `EReal`). -/
def HankelOriginFloor (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ,
    (∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) →
    ∀ (u_star : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop → (∀ k, 2 ≤ dk k) →
      ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ (G : ℕ → ℝ → ℝ) (T : ℕ → ℝ), (∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k)) →
          (∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
            G k (shellSite t (r t) (dk k)) ≤ 0) →
          (∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          ∃ (K : ℕ → ℕ) (S Q : ℂ → ℂ), StrictMono K ∧ TwoProfileFeasibleWitness D u_star S Q ∧
            TendstoLocallyUniformlyOn
              (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
                  (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
                hankelMass ((dk (K n) : ℝ) / 2)
                  (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ))
              (fun u => (S (u : ℂ)).re) atTop univ ∧
            TendstoLocallyUniformlyOn
              (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
                  (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) u /
                hankelMass ((dk (K n) : ℝ) / 2)
                  (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ))
              (fun u => ((2 : ℂ) * Q (u : ℂ)).re) atTop univ ∧
            (∃ B : ℝ, ∀ k, G k 0 / hankelMass ((dk k : ℝ) / 2)
              (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ) ≤ B) ∧
            (⨆ (y : ℝ) (_ : 0 < y), ((airyLaplace (fun u => ((2 : ℂ) * Q (u : ℂ)).re) y : ℝ) : EReal)) ≤
              liminf (fun n => ((G (K n) 0 / hankelMass ((dk (K n) : ℝ) / 2)
                (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) : ℝ) : EReal))
                atTop

/-- **`eq:ce-origin-floor`**, proved (see `HankelOriginFloor`): `ℒ_y(2Q_∞) = ℒ_y(S) - ℒ_y(H) ≤ ℒ_y(S) ≤ ‖S‖₁`
(`gt:3.1`, `airyLaplace_re_le_l1`) and `‖S‖₁ ≤ liminf M[ĥ_k]/M[f_k] = liminf h_k(0)/M[f_k]` (Fatou, positivity
of `ĥ`, `M[ĥ_k] = h_k(0)`). -/
theorem hankelOriginFloor_proved (D : ShellHBData) : HankelOriginFloor D := by
  have Hrc := radial_compactness
  intro r hr u_star dk hdk h2 ε hε G T hP hshell hT
  obtain ⟨K, Fp, Fq, hK, hFp, hFq, hlocp, hlocq, hw⟩ :=
    hankelShellGap_sub D r hr u_star dk hdk h2 ε hε G T hP hshell hT
  have hcpos : ∀ k, 0 < (dk k : ℝ) / 2 := fun k => by
    have : (2 : ℝ) ≤ dk k := by exact_mod_cast h2 k
    positivity
  have hμpos : ∀ k, 0 < hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) := fun k =>
    hankelMass_pos_of_continuousOn (hcpos k) ((hP k).minus (h2 k)).cont ((hP k).minus (h2 k)).int
      ((hP k).minus_ne_zero (h2 k))
  -- `f = 2 q`, `ĥ = p + q`
  have hfq : ∀ k, (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ) =
      fun Δ => (2 : ℝ) * hankelMinus ((dk k : ℝ) / 2) (G k) Δ := fun k => by
    funext Δ; unfold hankelMinus; ring
  have hhat : ∀ k, besselHankelTransform ((dk k : ℝ) / 2) (G k) =
      fun Δ => hankelPlus ((dk k : ℝ) / 2) (G k) Δ + hankelMinus ((dk k : ℝ) / 2) (G k) Δ := fun k => by
    funext Δ; unfold hankelPlus hankelMinus; ring
  have hMf : ∀ k, hankelMass ((dk k : ℝ) / 2)
      (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ) =
      2 * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) := fun k => by
    rw [hfq k, hankelMass_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hMfpos : ∀ k, 0 < hankelMass ((dk k : ℝ) / 2)
      (fun Δ => besselHankelTransform ((dk k : ℝ) / 2) (G k) Δ - G k Δ) := fun k => by
    rw [hMf k]; exact mul_pos two_pos (hμpos k)
  set P : ℂ → ℂ := fun z => ((1 / 2 : ℝ) : ℂ) * (Fp z + Fq z) with hPdef
  set Q : ℂ → ℂ := fun z => ((1 / 2 : ℝ) : ℂ) * Fq z with hQdef
  have hPcl : InAiryClass P := (hFp.add hFq).smul (1 / 2)
  have hQcl : InAiryClass Q := hFq.smul (1 / 2)
  obtain ⟨-, -, hPnn, -, -, -, -, -, hlap⟩ := id hw
  have hμ0 : ∀ k, hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) ≠ 0 :=
    fun k => (hμpos k).ne'
  -- the profile of `ĥ`
  have hΦ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
          (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
        hankelMass ((dk (K n) : ℝ) / 2)
          (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ))
      (fun u => (P (u : ℂ)).re) atTop univ := by
    have hsum := tlu_const_mul (1 / 2 : ℝ) (hlocp.add hlocq)
    refine (hsum.congr (fun n u _ => ?_)).congr_right (fun u _ => ?_)
    · simp only [Pi.add_apply]
      rw [hMf (K n), hhat (K n), hankelWindowProfile_add]
      have := hμ0 (K n)
      field_simp
    · simp [hPdef, Complex.mul_re]
  have hΨ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
          (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) u /
        hankelMass ((dk (K n) : ℝ) / 2)
          (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ))
      (fun u => ((2 : ℂ) * Q (u : ℂ)).re) atTop univ := by
    refine (hlocq.congr (fun n u _ => ?_)).congr_right (fun u _ => ?_)
    · rw [hMf (K n), hfq (K n), hankelWindowProfile_smul]
      have := hμ0 (K n)
      field_simp
    · simp [hQdef]
  have hint : ∀ n, ∫ u, hankelWindowProfile ((dk (K n) : ℝ) / 2)
        (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
      hankelMass ((dk (K n) : ℝ) / 2)
        (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) =
      G (K n) 0 / hankelMass ((dk (K n) : ℝ) / 2)
        (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) := fun n => by
    rw [integral_div, integral_hankelWindowProfile (hcpos (K n)), (hP (K n)).integral_hat_eq (h2 (K n))]
  refine ⟨K, P, Q, hK, hw, hΦ, hΨ, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hankelShell_mass_ratio_bdd Hrc hdk h2 hε hP hT
    refine ⟨(|C| + 1) / 2, fun k => ?_⟩
    rw [div_le_iff₀ (hMfpos k), hMf k]
    have h1 := (hP k).origin_le_mass (h2 k)
    have h2' := hC k
    have h3 : C * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) ≤
        |C| * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (hμpos k).le
    have e : (|C| + 1) / 2 * (2 * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k))) =
        |C| * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) +
          hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) := by ring
    linarith
  · refine iSup₂_le fun y hy => ?_
    refine coe_le_liminf_of_forall_add fun ε' hε' => ?_
    -- `ℒ_y(2Q) ≤ ℒ_y(S)`
    have hi1 := hPcl.integrable_exp_nonneg hy.le
    have hi2 : Integrable (fun u : ℝ => ((2 : ℂ) * Q (u : ℂ)).re * Real.exp (y * u)) :=
      ((hQcl.integrable_exp_nonneg hy.le).const_mul 2).congr
        (Eventually.of_forall fun u => by simp [Complex.mul_re]; ring)
    have hl := hlap y hy.le
    have hsplit : ∫ u : ℝ, (P (u : ℂ) - 2 * Q (u : ℂ)).re * Real.exp (y * u) =
        (∫ u : ℝ, (P (u : ℂ)).re * Real.exp (y * u)) -
          ∫ u : ℝ, ((2 : ℂ) * Q (u : ℂ)).re * Real.exp (y * u) := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [Complex.sub_re]
      ring
    have hL1 : airyLaplace (fun u => ((2 : ℂ) * Q (u : ℂ)).re) y ≤
        airyLaplace (fun u => (P (u : ℂ)).re) y := by
      unfold airyLaplace
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      linarith
    have hL2 := airyLaplace_re_le_l1 hPcl hy.le
    have hnorm : ∫ u : ℝ, ‖P (u : ℂ)‖ = ∫ u : ℝ, (P (u : ℂ)).re := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show ‖P (u : ℂ)‖ = (P (u : ℂ)).re
      rw [← Complex.abs_re_eq_norm.mpr (hPcl.2.2.2 u), abs_of_nonneg (hPnn u)]
    have hSi : Integrable fun u : ℝ => (P (u : ℂ)).re := by simpa using hPcl.2.1.re
    have hΦi : ∀ n, Integrable (fun u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
        (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
      hankelMass ((dk (K n) : ℝ) / 2)
        (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ)) := fun n =>
      ((integrable_hankelWindowProfile_iff (hcpos (K n)) _).2 (hP (K n)).int_hat).div_const _
    have hΦnn : ∀ n u, 0 ≤ hankelWindowProfile ((dk (K n) : ℝ) / 2)
        (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
      hankelMass ((dk (K n) : ℝ) / 2)
        (fun Δ => besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n)) Δ - G (K n) Δ) := fun n u =>
      div_nonneg (hankelWindowProfile_nonneg_of (hcpos (K n))
        (fun hpos => (hP (K n)).nonneg_hat _ hpos.le)) (hMfpos (K n)).le
    filter_upwards [integral_le_add_of_locunif hSi hΦi hΦnn hΦ hε'] with n hn
    rw [hint n] at hn
    linarith

/-- info: 'FormalResearch.SignUncertainty.airyLaplace_re_le_l1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLaplace_re_le_l1

/-- info: 'FormalResearch.SignUncertainty.hankelOriginFloor_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelOriginFloor_proved

end FormalResearch.SignUncertainty
