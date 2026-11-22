module

public import FormalResearch.Special.AiryThm47Exist
public import FormalResearch.Special.AiryThm47Zeros
public import FormalResearch.Special.AiryCftSignEqualityMain
public import FormalResearch.SignUncertainty.ClarkTwoNode

/-!
# Hermite–Biehler Equality Characterization and Two-Node `L¹` Norm (`clark_airy.tex`, Lemma H.2a)

Source: `CFT/common/clark_airy.tex`, **Lemma H.2a** (`lem:hb-uniqueness`) and eq. `(eq:hb-two-node-norm)`.

* `hbTopZeros`, `hbMinZero`, `hbExtremal`, `hbExtremal_spec`: canonical top-zero set `S`, terminal
  node `t_m = min S`, and Hermite–Biehler extremal `G_N(u) = N(u)^2 / ∏_{t ∈ S}(t - u)` via
  `at47_top_zeros_min` and `at47_existence`.
* `hb_uniqueness`, `hbExtremal_uniqueness`: if `H ∈ 𝒢` has `∫ H ≥ 0`, `H(t_j) ≤ 0` for `t_j ∈ S \ {t_m}`,
  and `H(u) ≤ 0` for `u ≤ t_m`, then `H = -b G_N` with `b ≥ 0`; if `H ≢ 0`, then `b = ‖H‖₁ / ‖G_N‖₁ > 0`
  and `H'(t_j) ≠ 0` for every `t_j ∈ S`.
* `hb_two_node_l1_norm`, `hb_two_node_l1_norm_pair`, `clarkExtremal_l1_norm`: for `m = 2`,
  `∫_ℝ |G_N| = 2 ∫_{t₂}^{t₁} (-G_N)` (`eq:hb-two-node-norm`).
* `airy_m1_uniqueness`: the `(P, Q) = (1, 0)` (`m = 1`, `N = Ai`, `G_Ai = airyExtremal`) case of Lemma H.2a.
* `hb_derivAiry_two_node_witness`: concrete non-vacuous `(P, Q) = (0, 1)` (`N = Ai'`, `m = 2`) witness.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Part 1: Shared helper lemmas -/

private lemma eq_of_mul_at47_pr_eq {S : Finset ℝ} {f g : ℂ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z : ℂ, f z * at47_pr S z = g z * at47_pr S z) (z : ℂ) : f z = g z := by
  have hfin : {w : ℂ | at47_pr S w = 0}.Finite := by
    refine (S.finite_toSet.image (fun t : ℝ => (t : ℂ))).subset fun w hw => ?_
    unfold at47_pr at hw
    obtain ⟨t, ht, h0⟩ := Finset.prod_eq_zero_iff.mp hw
    exact ⟨t, ht, (sub_eq_zero.mp h0).symm⟩
  have hdense : Dense {w : ℂ | at47_pr S w = 0}ᶜ := hfin.countable.dense_compl ℂ
  have hext := Continuous.ext_on hdense hf hg fun w hw => mul_right_cancel₀ hw (hfg w)
  exact congrFun hext z

private lemma integral_norm_pos_of_continuous_ne_zero {f : ℂ → ℂ}
    (hc : Continuous (fun x : ℝ => f (x : ℂ)))
    (hi : Integrable (fun x : ℝ => f (x : ℂ)))
    (hne : ∃ x₀ : ℝ, f (x₀ : ℂ) ≠ 0) :
    0 < ∫ x : ℝ, ‖f (x : ℂ)‖ := by
  obtain ⟨x₀, hx₀⟩ := hne
  let g : ℝ → ℝ := fun x => ‖f (x : ℂ)‖
  have hg_cont : Continuous g := hc.norm
  have hg_int : Integrable g := hi.norm
  have hg₀_pos : 0 < g x₀ := norm_pos_iff.mpr hx₀
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hg_cont.continuousAt (g x₀ / 2) (by positivity)
  have h_sub : Ioo (x₀ - δ) (x₀ + δ) ⊆ Metric.ball x₀ δ := by
    rw [Real.ball_eq_Ioo]
  have h_low : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), g x₀ / 2 ≤ g x := by
    intro x hx
    have hdist : dist (g x) (g x₀) < g x₀ / 2 := hδ (Metric.mem_ball.mp (h_sub hx))
    rw [Real.dist_eq, abs_lt] at hdist
    linarith
  have h_ball_pos : 0 < ∫ x in Ioo (x₀ - δ) (x₀ + δ), g x := by
    have hconst_int : IntegrableOn (fun _ : ℝ => g x₀ / 2) (Ioo (x₀ - δ) (x₀ + δ)) :=
      continuousOn_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hg_on : IntegrableOn g (Ioo (x₀ - δ) (x₀ + δ)) := hg_int.integrableOn
    have hmono := setIntegral_mono_on hconst_int hg_on measurableSet_Ioo h_low
    have hval : ∫ _x in Ioo (x₀ - δ) (x₀ + δ), (g x₀ / 2 : ℝ) = (2 * δ) * (g x₀ / 2) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hprod_pos : 0 < (2 * δ) * (g x₀ / 2) := by positivity
    linarith
  have h_le_tot : ∫ x in Ioo (x₀ - δ) (x₀ + δ), g x ≤ ∫ x : ℝ, g x :=
    setIntegral_le_integral hg_int (Eventually.of_forall fun x => norm_nonneg _)
  linarith

private lemma at47_extremal_deriv_ne_zero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)
    (S : Finset ℝ) (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0) {G_N : ℂ → ℂ}
    (hGd : Differentiable ℂ G_N)
    (hGeq : ∀ z : ℂ, G_N z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2)
    {t : ℝ} (ht : t ∈ S) :
    G_N (t : ℂ) = 0 ∧ deriv G_N (t : ℂ) ≠ 0 := by
  have hNd := differentiable_airyPQN P Q
  have hε : (((-1 : ℝ) ^ S.card : ℝ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero _ (by norm_num)
  have hprt : at47_pr S (t : ℂ) = 0 := at47_pr_eq_zero ht
  have heq_fn : (fun z => G_N z * at47_pr S z) =
      fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2 := funext hGeq
  have hGt : G_N (t : ℂ) = 0 := by
    have hd1 : deriv (fun z => G_N z * at47_pr S z) (t : ℂ) =
        deriv G_N (t : ℂ) * at47_pr S (t : ℂ) + G_N (t : ℂ) * deriv (at47_pr S) (t : ℂ) :=
      ((hGd _).hasDerivAt.mul ((at47_pr_differentiable S _).hasDerivAt)).deriv
    have hsq : deriv (fun z => airyPQN P Q z ^ 2) (t : ℂ) = 0 := by
      have hd_sq : HasDerivAt (fun z => airyPQN P Q z ^ 2)
          (2 * airyPQN P Q (t : ℂ) ^ (2 - 1) * deriv (airyPQN P Q) (t : ℂ)) (t : ℂ) :=
        (hNd (t : ℂ)).hasDerivAt.pow 2
      rw [hd_sq.deriv, hSz t ht]
      simp
    have hd2 : deriv (fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) (t : ℂ) = 0 := by
      have hd_sq_diff : Differentiable ℂ (fun z => airyPQN P Q z ^ 2) := by fun_prop
      have hd_cm : HasDerivAt (fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2)
          ((((-1 : ℝ) ^ S.card : ℝ) : ℂ) * deriv (fun z => airyPQN P Q z ^ 2) (t : ℂ)) (t : ℂ) :=
        (hd_sq_diff (t : ℂ)).hasDerivAt.const_mul _
      rw [hd_cm.deriv, hsq, mul_zero]
    rw [heq_fn, hd2, hprt, mul_zero, zero_add] at hd1
    exact (mul_eq_zero.mp hd1.symm).resolve_right (at47_pr_deriv_ne_zero ht)
  refine ⟨hGt, fun hG't => ?_⟩
  have h1 := at47_deriv2_mul_zero hGd (at47_pr_differentiable S) hGt hG't hprt
  have hd_sq : Differentiable ℂ (fun z => airyPQN P Q z ^ 2) := by fun_prop
  have e2 : deriv (fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) =
      fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * deriv (fun z => airyPQN P Q z ^ 2) z := by
    funext z; exact (((hd_sq z).hasDerivAt.const_mul _).deriv)
  have h_cm2 : deriv (fun z => (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * deriv (fun z => airyPQN P Q z ^ 2) z)
      (t : ℂ) = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * deriv (deriv (fun z => airyPQN P Q z ^ 2)) (t : ℂ) :=
    (((hd_sq.deriv (t : ℂ)).hasDerivAt.const_mul _).deriv)
  rw [heq_fn, e2, h_cm2, at47_deriv2_sq hNd (hSz t ht)] at h1
  have hN'ne : deriv (airyPQN P Q) (t : ℂ) ≠ 0 := by
    rw [deriv_airyPQN]; exact airyPQ_simple_of_HB hHB hQ _ (hSz t ht)
  have h2 : (2 : ℂ) * deriv (airyPQN P Q) (t : ℂ) ^ 2 = 0 :=
    (mul_eq_zero.mp h1).resolve_left hε
  rcases mul_eq_zero.mp h2 with h20 | hN20
  · norm_num at h20
  · exact hN'ne (pow_eq_zero_iff two_ne_zero |>.mp hN20)

/-! ### Part 2: Canonical Hermite–Biehler top zeros and extremal -/

/-- Canonical set `S` of the `m = at47_m P Q` largest zeros of `N = P Ai + Q Ai'`. -/
noncomputable def hbTopZeros {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) : Finset ℝ :=
  (at47_top_zeros_min hHB hQ).choose

/-- Terminal node `t_m = min S` of the `m = at47_m P Q` largest zeros of `N`. -/
noncomputable def hbMinZero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) : ℝ :=
  (at47_top_zeros_min hHB hQ).choose_spec.choose

/-- Specification of `hbTopZeros` and `hbMinZero` from `at47_top_zeros_min`. -/
theorem hbTopZeros_spec {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    (hbTopZeros hHB hQ).card = at47_m P Q ∧
      (∀ t ∈ hbTopZeros hHB hQ, airyPQN P Q (t : ℂ) = 0) ∧
      (∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ hbTopZeros hHB hQ → ∀ t ∈ hbTopZeros hHB hQ, x < t) ∧
      hbMinZero hHB hQ ∈ hbTopZeros hHB hQ ∧
      ∀ t ∈ hbTopZeros hHB hQ, hbMinZero hHB hQ ≤ t :=
  (at47_top_zeros_min hHB hQ).choose_spec.choose_spec

/-- Canonical Hermite–Biehler extremal `G_N(u) = N(u)^2 / ∏_{t ∈ S}(t - u)`. -/
noncomputable def hbExtremal {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) : ℂ → ℂ :=
  let hs := hbTopZeros_spec hHB hQ
  (at47_existence hHB hQ (hbTopZeros hHB hQ) hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2).choose

/-- Admissibility and defining equation of `hbExtremal` from `at47_existence`. -/
theorem hbExtremal_spec {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    let S := hbTopZeros hHB hQ
    let tm := hbMinZero hHB hQ
    let G_N := hbExtremal hHB hQ
    Differentiable ℂ G_N ∧
      (∀ z : ℂ, G_N z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) ∧
      Integrable (fun x : ℝ => G_N (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖G_N u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (G_N (x : ℂ)).im = 0) ∧
      (∀ x : ℝ, x ≤ tm → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ t ∈ S, G_N (t : ℂ) = 0) ∧
      (∫ x : ℝ, G_N (x : ℂ)) = 0 ∧
      ∃ x : ℝ, G_N (x : ℂ) ≠ 0 := by
  let hs := hbTopZeros_spec hHB hQ
  exact (at47_existence hHB hQ (hbTopZeros hHB hQ) hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2).choose_spec

/-! ### Part 3: Lemma H.2a — Hermite–Biehler uniqueness (`lem:hb-uniqueness`) -/

/-- **Lemma H.2a (`lem:hb-uniqueness`)**: equality for polynomial Hermite–Biehler data `(P, Q)`, `Q ≠ 0`.
If `H ∈ 𝒢` satisfies `∫ H ≥ 0`, `H(t) ≤ 0` on `S \ {t_m}`, and `H(u) ≤ 0` for `u ≤ t_m`, then
`H = -b G_N` for some `b ≥ 0`. If `H ≢ 0`, then `b = ‖H‖₁ / ‖G_N‖₁ > 0` and `H'(t) ≠ 0` for all `t ∈ S`. -/
theorem hb_uniqueness {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (S : Finset ℝ)
    (hcard : S.card = at47_m P Q) (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0)
    (hS_top : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t)
    {tm : ℝ} (htm : tm ∈ S) (hmin : ∀ t ∈ S, tm ≤ t)
    {G_N : ℂ → ℂ} (hGd : Differentiable ℂ G_N)
    (hGeq : ∀ z : ℂ, G_N z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2)
    {H : ℂ → ℂ} (hHd : Differentiable ℂ H) (hHi : Integrable (fun x : ℝ => H (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hHb : ∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hHreal : ∀ x : ℝ, (H (x : ℂ)).im = 0) (hHint : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re)
    (hHS : ∀ t ∈ S, t ≠ tm → (H (t : ℂ)).re ≤ 0)
    (hHneg : ∀ x : ℝ, x ≤ tm → (H (x : ℂ)).re ≤ 0) :
    ∃ b : ℝ, 0 ≤ b ∧ (∀ z : ℂ, H z = -((b : ℂ) * G_N z)) ∧
      ((∃ z : ℂ, H z ≠ 0) →
        0 < b ∧
        0 < ∫ x : ℝ, ‖G_N (x : ℂ)‖ ∧
        b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖G_N (x : ℂ)‖) ∧
        ∀ t ∈ S, deriv H (t : ℂ) ≠ 0) := by
  have hf_int : (∫ x : ℝ, -H (x : ℂ)).re ≤ 0 := by
    rw [integral_neg, Complex.neg_re]
    linarith
  have hfS : ∀ t ∈ S, 0 ≤ (-H (t : ℂ)).re := by
    intro t ht
    rw [Complex.neg_re]
    by_cases htm_eq : t = tm
    · subst htm_eq; linarith [hHneg t le_rfl]
    · linarith [hHS t ht htm_eq]
  obtain ⟨b, hb_nn, hbf, -⟩ := at47_uniqueness hHB hQ S hcard hSz hS_top htm hmin le_rfl
    hHd.neg hHi.neg hC (fun u => by simpa using hHb u)
    (fun x => by simp [hHreal x]) hf_int hfS (fun x hx => by simp [hHneg x hx])
  have hH_eq : ∀ z : ℂ, H z = -((b : ℂ) * G_N z) := by
    have hneg_eq : ∀ z : ℂ, (-H) z = ((b : ℂ) * G_N z) := by
      refine eq_of_mul_at47_pr_eq (S := S) hHd.neg.continuous (continuous_const.mul hGd.continuous) fun z => ?_
      calc (-H z) * at47_pr S z
          = ((b * (-1) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2 := hbf z
        _ = (b : ℂ) * ((((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) := by
            push_cast; ring
        _ = (b : ℂ) * (G_N z * at47_pr S z) := by rw [← hGeq z]
        _ = ((b : ℂ) * G_N z) * at47_pr S z := by ring
    intro z
    have hz := hneg_eq z
    dsimp at hz
    linear_combination -hz
  refine ⟨b, hb_nn, hH_eq, fun ⟨z₀, hz₀⟩ => ?_⟩
  have hb_pos : 0 < b := by
    refine lt_of_le_of_ne hb_nn fun hb0 => hz₀ ?_
    rw [hH_eq z₀, ← hb0]
    simp
  obtain ⟨F, hFd, hFeq, hFi, _, _, _, _, _, ⟨x₁, hx₁⟩⟩ :=
    at47_existence hHB hQ S hcard hSz htm hmin
  have hGF : ∀ z : ℂ, G_N z = F z :=
    eq_of_mul_at47_pr_eq (S := S) hGd.continuous hFd.continuous fun z => by rw [hGeq z, hFeq z]
  have hGi : Integrable (fun x : ℝ => G_N (x : ℂ)) :=
    hFi.congr (Eventually.of_forall fun x => (hGF (x : ℂ)).symm)
  have hGne : ∃ x : ℝ, G_N (x : ℂ) ≠ 0 := ⟨x₁, by rw [hGF]; exact hx₁⟩
  have hG_l1_pos : 0 < ∫ x : ℝ, ‖G_N (x : ℂ)‖ :=
    integral_norm_pos_of_continuous_ne_zero (hGd.continuous.comp Complex.continuous_ofReal) hGi hGne
  have hH_l1_eq : ∫ x : ℝ, ‖H (x : ℂ)‖ = b * ∫ x : ℝ, ‖G_N (x : ℂ)‖ := by
    have hpt : (fun x : ℝ => ‖H (x : ℂ)‖) = fun x : ℝ => b * ‖G_N (x : ℂ)‖ := by
      funext x
      rw [hH_eq (x : ℂ), norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb_pos]
    rw [hpt, integral_const_mul]
  have hb_ratio : b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖G_N (x : ℂ)‖) :=
    eq_div_of_mul_eq hG_l1_pos.ne' hH_l1_eq.symm
  have hH_deriv : ∀ t ∈ S, deriv H (t : ℂ) ≠ 0 := by
    intro t ht
    have hG'ne := (at47_extremal_deriv_ne_zero hHB hQ S hSz hGd hGeq ht).2
    have heq_fn : H = fun z => -((b : ℂ) * G_N z) := funext hH_eq
    have hd : deriv (fun z => -((b : ℂ) * G_N z)) (t : ℂ) = -((b : ℂ) * deriv G_N (t : ℂ)) :=
      (((hGd (t : ℂ)).hasDerivAt.const_mul (b : ℂ)).neg).deriv
    rw [heq_fn, hd]
    exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb_pos.ne') hG'ne)
  exact ⟨hb_pos, hG_l1_pos, hb_ratio, hH_deriv⟩

/-- Bundled form of `hb_uniqueness` using the canonical `hbTopZeros`, `hbMinZero`, and `hbExtremal`. -/
theorem hbExtremal_uniqueness {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)
    {H : ℂ → ℂ} (hHd : Differentiable ℂ H) (hHi : Integrable (fun x : ℝ => H (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hHb : ∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hHreal : ∀ x : ℝ, (H (x : ℂ)).im = 0) (hHint : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re)
    (hHS : ∀ t ∈ hbTopZeros hHB hQ, t ≠ hbMinZero hHB hQ → (H (t : ℂ)).re ≤ 0)
    (hHneg : ∀ x : ℝ, x ≤ hbMinZero hHB hQ → (H (x : ℂ)).re ≤ 0) :
    ∃ b : ℝ, 0 ≤ b ∧ (∀ z : ℂ, H z = -((b : ℂ) * hbExtremal hHB hQ z)) ∧
      ((∃ z : ℂ, H z ≠ 0) →
        0 < b ∧
        0 < ∫ x : ℝ, ‖hbExtremal hHB hQ (x : ℂ)‖ ∧
        b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖hbExtremal hHB hQ (x : ℂ)‖) ∧
        ∀ t ∈ hbTopZeros hHB hQ, deriv H (t : ℂ) ≠ 0) := by
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  exact hb_uniqueness hHB hQ (hbTopZeros hHB hQ) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
    hG.1 hG.2.1 hHd hHi hC hHb hHreal hHint hHS hHneg

/-! ### Part 4: Two-node `L¹` norm identity (`eq:hb-two-node-norm`) -/

/-- **Equation `(eq:hb-two-node-norm)`**: when `m = 2` (`S = {t₁, t₂}` with `t₂ < t₁`),
`G_N` is real on `ℝ` with `∫_ℝ G_N = 0`, `G_N ≥ 0` off `(t₂, t₁)`, `G_N ≤ 0` on `(t₂, t₁)`, and
`∫ x : ℝ, ‖G_N (x : ℂ)‖ = 2 * ∫ x in Set.Ioo t₂ t₁, -(G_N (x : ℂ)).re`. -/
theorem hb_two_node_l1_norm {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)
    (S : Finset ℝ) {t₁ t₂ : ℝ} (ht : t₂ < t₁) (hm : at47_m P Q = 2) (hS : S = {t₁, t₂})
    (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0)
    {G_N : ℂ → ℂ} (hGd : Differentiable ℂ G_N)
    (hGeq : ∀ z : ℂ, G_N z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) :
    (∫ x : ℝ, G_N (x : ℂ)).re = 0 ∧
      (∀ x : ℝ, x ≤ t₂ → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₁ ≤ x → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₂ < x → x < t₁ → (G_N (x : ℂ)).re ≤ 0) ∧
      ∫ x : ℝ, ‖G_N (x : ℂ)‖ = 2 * ∫ x in Set.Ioo t₂ t₁, -(G_N (x : ℂ)).re := by
  have ht12 : t₁ ≠ t₂ := ht.ne'
  have hcard : S.card = at47_m P Q := by
    rw [hS, Finset.card_pair ht12, hm]
  have ht2S : t₂ ∈ S := by rw [hS]; simp
  have ht1S : t₁ ∈ S := by rw [hS]; simp
  have hmin : ∀ t ∈ S, t₂ ≤ t := by
    intro t htm
    rw [hS, Finset.mem_insert, Finset.mem_singleton] at htm
    rcases htm with rfl | rfl
    · exact ht.le
    · exact le_rfl
  obtain ⟨F, hFd, hFeq, hFi, _, hFreal, hFneg, hFS, hFint, _⟩ :=
    at47_existence hHB hQ S hcard hSz ht2S hmin
  have hGF : ∀ z : ℂ, G_N z = F z :=
    eq_of_mul_at47_pr_eq (S := S) hGd.continuous hFd.continuous fun z => by rw [hGeq z, hFeq z]
  have hGi : Integrable (fun x : ℝ => G_N (x : ℂ)) :=
    hFi.congr (Eventually.of_forall fun x => (hGF (x : ℂ)).symm)
  have hGint : (∫ x : ℝ, G_N (x : ℂ)) = 0 := by
    have hcongr : (fun x : ℝ => G_N (x : ℂ)) = fun x : ℝ => F (x : ℂ) := funext fun x => hGF (x : ℂ)
    rw [hcongr, hFint]
  have hGreal : ∀ x : ℝ, (G_N (x : ℂ)).im = 0 := fun x => by rw [hGF]; exact hFreal x
  have hGS : ∀ t ∈ S, G_N (t : ℂ) = 0 := fun t htm => by rw [hGF]; exact hFS t htm
  have hGneg_band : ∀ x : ℝ, x ≤ t₂ → 0 ≤ (G_N (x : ℂ)).re := fun x hx => by
    rw [hGF]; exact hFneg x hx
  have hG_prod : ∀ x : ℝ, ∏ t ∈ S, (x - t) = (x - t₁) * (x - t₂) := fun x => by
    rw [hS, Finset.prod_pair ht12]
  have hG_re_off : ∀ {x : ℝ}, x ∉ S →
      (G_N (x : ℂ)).re = at47_Nf P Q x ^ 2 / ((x - t₁) * (x - t₂)) := by
    intro x hxS
    rw [at47_F_real_formula hGeq hxS, Complex.ofReal_re, hG_prod x, hS, Finset.card_pair ht12]
    norm_num
  have hGpos_above : ∀ x : ℝ, t₁ ≤ x → 0 ≤ (G_N (x : ℂ)).re := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hlt
    · rw [hGS _ ht1S]; simp
    · have hxS : x ∉ S := by
        rw [hS, Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hlt.ne', (ht.trans hlt).ne'⟩
      rw [hG_re_off hxS]
      have hden : 0 < (x - t₁) * (x - t₂) := mul_pos (by linarith) (by linarith)
      exact div_nonneg (sq_nonneg _) hden.le
  have hGnonpos_mid : ∀ x : ℝ, t₂ < x → x < t₁ → (G_N (x : ℂ)).re ≤ 0 := by
    intro x hx2 hx1
    have hxS : x ∉ S := by
      rw [hS, Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hx1.ne, hx2.ne'⟩
    rw [hG_re_off hxS]
    have hden : (x - t₁) * (x - t₂) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hden.le
  let g : ℝ → ℝ := fun x => (G_N (x : ℂ)).re
  have hg_int : Integrable g := hGi.re
  have hg_int_zero : ∫ x : ℝ, g x = 0 := by
    have hre : ∫ x : ℝ, g x = (∫ x : ℝ, G_N (x : ℂ)).re := integral_re hGi
    rw [hre, hGint, Complex.zero_re]
  have hnorm_eq : (fun x : ℝ => ‖G_N (x : ℂ)‖) = fun x : ℝ => |g x| := by
    funext x
    have hx : G_N (x : ℂ) = ((g x : ℝ) : ℂ) := Complex.ext rfl (hGreal x)
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
  have hind_eq : (fun x : ℝ => |g x| - g x) =
      Set.indicator (Set.Ioo t₂ t₁) (fun x => 2 * (-g x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioo t₂ t₁
    · rw [Set.indicator_of_mem hx, abs_of_nonpos (hGnonpos_mid x hx.1 hx.2)]
      ring
    · rw [Set.indicator_of_notMem hx]
      have hnonneg : 0 ≤ g x := by
        rcases le_or_gt x t₂ with hle | hgt
        · exact hGneg_band x hle
        · have ht1_le : t₁ ≤ x := by
            by_contra hlt
            exact hx ⟨hgt, not_le.mp hlt⟩
          exact hGpos_above x ht1_le
      rw [abs_of_nonneg hnonneg, sub_self]
  have hl1 : ∫ x : ℝ, ‖G_N (x : ℂ)‖ = 2 * ∫ x in Set.Ioo t₂ t₁, -(G_N (x : ℂ)).re := by
    calc ∫ x : ℝ, ‖G_N (x : ℂ)‖
        = ∫ x : ℝ, |g x| := by rw [hnorm_eq]
      _ = (∫ x : ℝ, |g x|) - ∫ x : ℝ, g x := by rw [hg_int_zero, sub_zero]
      _ = ∫ x : ℝ, (|g x| - g x) := (integral_sub hg_int.abs hg_int).symm
      _ = ∫ x : ℝ, Set.indicator (Set.Ioo t₂ t₁) (fun x => 2 * (-g x)) x := by rw [hind_eq]
      _ = ∫ x in Set.Ioo t₂ t₁, 2 * (-g x) := integral_indicator measurableSet_Ioo
      _ = 2 * ∫ x in Set.Ioo t₂ t₁, -g x := integral_const_mul 2 _
  refine ⟨by rw [hGint, Complex.zero_re], hGneg_band, hGpos_above, hGnonpos_mid, hl1⟩

/-- Pair-product form of `hb_two_node_l1_norm` without `at47_pr`: for `m = 2`, `t₂ < t₁`,
and `G_N(z) (z - t₁)(z - t₂) = N(z)^2`. -/
theorem hb_two_node_l1_norm_pair {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)
    {t₁ t₂ : ℝ} (ht : t₂ < t₁) (hm : at47_m P Q = 2)
    (hzt₁ : airyPQN P Q (t₁ : ℂ) = 0) (hzt₂ : airyPQN P Q (t₂ : ℂ) = 0)
    {G_N : ℂ → ℂ} (hGd : Differentiable ℂ G_N)
    (hGeq : ∀ z : ℂ, G_N z * ((z - (t₁ : ℂ)) * (z - (t₂ : ℂ))) = airyPQN P Q z ^ 2) :
    (∫ x : ℝ, G_N (x : ℂ)).re = 0 ∧
      (∀ x : ℝ, x ≤ t₂ → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₁ ≤ x → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₂ < x → x < t₁ → (G_N (x : ℂ)).re ≤ 0) ∧
      ∫ x : ℝ, ‖G_N (x : ℂ)‖ = 2 * ∫ x in Set.Ioo t₂ t₁, -(G_N (x : ℂ)).re := by
  let S : Finset ℝ := {t₁, t₂}
  have hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0 := by
    intro t htm
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at htm
    rcases htm with rfl | rfl
    · exact hzt₁
    · exact hzt₂
  have hGeq' : ∀ z : ℂ, G_N z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2 := by
    intro z
    have hcard : S.card = 2 := Finset.card_pair ht.ne'
    have hpr : at47_pr S z = (z - (t₁ : ℂ)) * (z - (t₂ : ℂ)) := by
      unfold at47_pr; rw [Finset.prod_pair ht.ne']
    rw [hpr, hcard]
    simpa using hGeq z
  exact hb_two_node_l1_norm hHB hQ S ht hm rfl hSz hGd hGeq'

/-- Equation `(eq:hb-two-node-norm)` specialized to the Clark two-node extremal `clarkExtremal α`. -/
theorem clarkExtremal_l1_norm {α : ℝ} (hα : Real.sin α ≠ 0) :
    ∫ x : ℝ, ‖clarkExtremal α (x : ℂ)‖ =
      2 * ∫ x in Set.Ioo (clarkNode α 2) (clarkNode α 1), -(clarkExtremal α (x : ℂ)).re := by
  have hQ : Polynomial.C (-Real.sin α) ≠ 0 := by
    simpa using neg_ne_zero.mpr hα
  have hHB : AiryPQHB (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) :=
    airyPQHB_C _ _ (Or.inr (neg_ne_zero.mpr hα))
  have hm : at47_m (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) = 2 := by
    simp [at47_m]
  have hN_eq : ∀ z : ℂ, airyPQN (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) z = psiClark α z :=
    fun z => by rw [airyPQ_C_N, ← psiClark_eq_airyNC]
  have hzt1 : airyPQN (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) (clarkNode α 1 : ℂ) = 0 := by
    rw [hN_eq]; exact clarkNode_zero hα le_rfl
  have hzt2 : airyPQN (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) (clarkNode α 2 : ℂ) = 0 := by
    rw [hN_eq]; exact clarkNode_zero hα (by norm_num)
  have hGeq : ∀ z : ℂ, clarkExtremal α z * ((z - (clarkNode α 1 : ℂ)) * (z - (clarkNode α 2 : ℂ))) =
      airyPQN (Polynomial.C (Real.cos α)) (Polynomial.C (-Real.sin α)) z ^ 2 := fun z => by
    rw [hN_eq]; exact clarkExtremal_mul_denom hα z
  exact (hb_two_node_l1_norm_pair hHB hQ (clarkNode_two_lt_one α) hm hzt1 hzt2
    (differentiable_clarkExtremal α) hGeq).2.2.2.2

/-! ### Part 5: Lemma H.2a (`m = 1` Airy case `(P, Q) = (1, 0)`) -/

/-- **Lemma H.2a (`lem:hb-uniqueness`) for `(P, Q) = (1, 0)` (`m = 1`, `N = Ai`, `G_Ai = airyExtremal`)**:
if `H ∈ 𝒢` satisfies `∫ H ≥ 0` and `H(u) ≤ 0` for `u ≤ a₁`, then `H = -b G_Ai` (`G_Ai(u) = Ai(u)²/(a₁ - u)`)
for some `b ≥ 0`. If `H ≢ 0`, then `b = ‖H‖₁ / ‖G_Ai‖₁ > 0` and `H'(a₁) ≠ 0`. -/
theorem airy_m1_uniqueness {H : ℂ → ℂ}
    (hHd : Differentiable ℂ H) (hHi : Integrable (fun x : ℝ => H (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hHb : ∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hHreal : ∀ x : ℝ, (H (x : ℂ)).im = 0) (hHint : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re)
    (hHneg : ∀ x : ℝ, x ≤ airyZero 1 → (H (x : ℂ)).re ≤ 0) :
    ∃ b : ℝ, 0 ≤ b ∧ (∀ z : ℂ, H z = -((b : ℂ) * airyExtremal z)) ∧
      (∀ u : ℂ, u ≠ (airyZero 1 : ℂ) →
        H u = -((b : ℂ) * (airyAiC u ^ 2 / ((airyZero 1 : ℂ) - u)))) ∧
      ((∃ z : ℂ, H z ≠ 0) →
        0 < b ∧
        0 < ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖ ∧
        b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖airyExtremal (x : ℂ)‖) ∧
        deriv H (airyZero 1 : ℂ) ≠ 0) := by
  by_cases hne : ∃ z : ℂ, H z ≠ 0
  · have hf_int : (∫ x : ℝ, (-H (x : ℂ)).re) ≤ 0 := by
      have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hHi
      simp_rw [Complex.neg_re]
      rw [integral_neg, hre]
      linarith
    have hf_ne : ∃ z : ℂ, (-H) z ≠ 0 := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨z, neg_ne_zero.mpr hz⟩
    obtain ⟨c, hc_neg, hfc, -⟩ := airy_sign_equality hHd.neg hHi.neg hC
      (fun u => by simpa using hHb u) (fun x => by simp [hHreal x])
      (fun x hx => by simp [hHneg x hx]) hf_int hf_ne
    set b : ℝ := -c
    have hb_pos : 0 < b := by linarith
    have hH_eq : ∀ z : ℂ, H z = -((b : ℂ) * airyExtremal z) := by
      intro z
      have hz := hfc z
      dsimp at hz
      have hbc : ((-c : ℝ) : ℂ) = (b : ℂ) := rfl
      rw [hbc] at hz
      linear_combination -hz
    have hH_formula : ∀ u : ℂ, u ≠ (airyZero 1 : ℂ) →
        H u = -((b : ℂ) * (airyAiC u ^ 2 / ((airyZero 1 : ℂ) - u))) := by
      intro u hu
      rw [hH_eq u, airyExtremal_eq hu]
      have hne_sub : (airyZero 1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr hu.symm
      have hne_sub' : u - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hu
      congr 1
      field_simp
      ring
    have hE_ne_real : ∃ x₀ : ℝ, airyExtremal (x₀ : ℂ) ≠ 0 := by
      obtain ⟨x₀, _, hx₀_pos⟩ := airyExtremal_pos_mid
      exact ⟨x₀, fun h0 => by rw [h0, Complex.zero_re] at hx₀_pos; exact lt_irrefl 0 hx₀_pos⟩
    have hE_l1_pos : 0 < ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖ :=
      integral_norm_pos_of_continuous_ne_zero
        (differentiable_airyExtremal.continuous.comp Complex.continuous_ofReal)
        airyExtremal_integrable hE_ne_real
    have hH_l1_eq : ∫ x : ℝ, ‖H (x : ℂ)‖ = b * ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖ := by
      have hpt : (fun x : ℝ => ‖H (x : ℂ)‖) = fun x : ℝ => b * ‖airyExtremal (x : ℂ)‖ := by
        funext x
        rw [hH_eq (x : ℂ), norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb_pos]
      rw [hpt, integral_const_mul]
    have hb_ratio : b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖airyExtremal (x : ℂ)‖) :=
      eq_div_of_mul_eq hE_l1_pos.ne' hH_l1_eq.symm
    have hE_deriv : deriv airyExtremal (airyZero 1 : ℂ) = -(deriv airyAiC (airyZero 1 : ℂ)) ^ 2 := by
      have hd_ds : Differentiable ℂ (dslope airyAiC (airyZero 1 : ℂ)) :=
        EntireDiv.differentiable_dslope_entire differentiable_airyAiC _
      have hd_mul : HasDerivAt (fun u : ℂ => airyAiC u * dslope airyAiC (airyZero 1 : ℂ) u)
          (deriv airyAiC (airyZero 1 : ℂ) * dslope airyAiC (airyZero 1 : ℂ) (airyZero 1 : ℂ) +
            airyAiC (airyZero 1 : ℂ) * deriv (dslope airyAiC (airyZero 1 : ℂ)) (airyZero 1 : ℂ))
          (airyZero 1 : ℂ) :=
        (differentiable_airyAiC _).hasDerivAt.mul (hd_ds _).hasDerivAt
      have hd_ext : HasDerivAt airyExtremal
          (-(deriv airyAiC (airyZero 1 : ℂ) * dslope airyAiC (airyZero 1 : ℂ) (airyZero 1 : ℂ) +
            airyAiC (airyZero 1 : ℂ) * deriv (dslope airyAiC (airyZero 1 : ℂ)) (airyZero 1 : ℂ)))
          (airyZero 1 : ℂ) := hd_mul.neg
      rw [hd_ext.deriv, airyAiC_airyZero, dslope_same, zero_mul, add_zero, sq]
    have hH_deriv : deriv H (airyZero 1 : ℂ) ≠ 0 := by
      have heq_fn : H = fun z => -((b : ℂ) * airyExtremal z) := funext hH_eq
      have hd_H : deriv (fun z => -((b : ℂ) * airyExtremal z)) (airyZero 1 : ℂ) =
          -((b : ℂ) * deriv airyExtremal (airyZero 1 : ℂ)) :=
        (((differentiable_airyExtremal _).hasDerivAt.const_mul (b : ℂ)).neg).deriv
      rw [heq_fn, hd_H, hE_deriv]
      have hAi'_ne : deriv airyAiC (airyZero 1 : ℂ) ≠ 0 := airyZero_deriv_ne_zero 1
      exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb_pos.ne')
        (neg_ne_zero.mpr (pow_ne_zero 2 hAi'_ne)))
    exact ⟨b, hb_pos.le, hH_eq, hH_formula, fun _ => ⟨hb_pos, hE_l1_pos, hb_ratio, hH_deriv⟩⟩
  · push Not at hne
    refine ⟨0, le_rfl, fun z => by simp [hne z], fun u _ => by simp [hne u], fun h => absurd h ?_⟩
    push Not; exact hne

/-! ### Part 6: Concrete non-vacuous witness `(P, Q) = (0, 1)` (`N = Ai'`, `m = 2`) -/

/-- Non-vacuous witness: `(P, Q) = (0, 1)` (`N = Ai'`, `m = 2`) satisfies all hypotheses of
`hb_uniqueness` and `hb_two_node_l1_norm` (with `H = -hbExtremal`, `b = 1`). -/
theorem hb_derivAiry_two_node_witness :
    ∃ (S : Finset ℝ) (t₁ t₂ : ℝ) (G_N : ℂ → ℂ),
      t₂ < t₁ ∧ S = {t₁, t₂} ∧
      (∀ z : ℂ, G_N z * ((z - (t₁ : ℂ)) * (z - (t₂ : ℂ))) = deriv airyAiC z ^ 2) ∧
      (∫ x : ℝ, G_N (x : ℂ)).re = 0 ∧
      (∀ x : ℝ, x ≤ t₂ → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₁ ≤ x → 0 ≤ (G_N (x : ℂ)).re) ∧
      (∀ x : ℝ, t₂ < x → x < t₁ → (G_N (x : ℂ)).re ≤ 0) ∧
      ∫ x : ℝ, ‖G_N (x : ℂ)‖ = 2 * ∫ x in Set.Ioo t₂ t₁, -(G_N (x : ℂ)).re ∧
      ∀ t ∈ S, deriv G_N (t : ℂ) ≠ 0 := by
  have hHB : AiryPQHB (0 : ℝ[X]) (Polynomial.C 1) := by
    simpa using airyPQHB_C 0 1 (Or.inr one_ne_zero)
  have hQ : Polynomial.C (1 : ℝ) ≠ 0 := by simp
  have hm : at47_m (0 : ℝ[X]) (Polynomial.C 1) = 2 := by simp [at47_m]
  let S := hbTopZeros hHB hQ
  let t₂ := hbMinZero hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hcard2 : S.card = 2 := hs.1.trans hm
  have ht₂S : t₂ ∈ S := hs.2.2.2.1
  have herase_card : (S.erase t₂).card = 1 := by
    rw [Finset.card_erase_of_mem ht₂S, hcard2]
  obtain ⟨t₁, ht₁_eq⟩ := Finset.card_eq_one.mp herase_card
  have ht₁_erase : t₁ ∈ S.erase t₂ := by rw [ht₁_eq]; exact Finset.mem_singleton_self t₁
  have ht₁₂ : t₁ ≠ t₂ := (Finset.mem_erase.mp ht₁_erase).1
  have ht₁S : t₁ ∈ S := (Finset.mem_erase.mp ht₁_erase).2
  have ht : t₂ < t₁ := lt_of_le_of_ne (hs.2.2.2.2 t₁ ht₁S) ht₁₂.symm
  have hS_pair : S = {t₁, t₂} := by
    rw [← Finset.insert_erase ht₂S, ht₁_eq, Finset.pair_comm]
  rcases hbExtremal_spec hHB hQ with
    ⟨hGd, hGeq, hGi, ⟨C, ν, hC, hGb⟩, hGreal, hGneg, hGS, hGint, ⟨x₀, hx₀⟩⟩
  have hN_eq : ∀ z : ℂ, airyPQN (0 : ℝ[X]) (Polynomial.C 1) z = deriv airyAiC z := fun z => by
    unfold airyPQN
    rw [airyPQc_zero, airyPQc_C]
    simp
  have hGeq_pair : ∀ z : ℂ,
      hbExtremal hHB hQ z * ((z - (t₁ : ℂ)) * (z - (t₂ : ℂ))) = deriv airyAiC z ^ 2 := fun z => by
    have hpr : at47_pr S z = (z - (t₁ : ℂ)) * (z - (t₂ : ℂ)) := by
      unfold at47_pr; rw [hS_pair, Finset.prod_pair ht₁₂]
    have h := hGeq z
    change hbExtremal hHB hQ z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN 0 (Polynomial.C 1) z ^ 2 at h
    rw [hpr, hcard2, hN_eq z] at h
    simpa using h
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb_two_node_l1_norm hHB hQ S ht hm hS_pair hs.2.1 hGd hGeq
  have hH_uniq := hbExtremal_uniqueness hHB hQ (H := fun z => -hbExtremal hHB hQ z)
    hGd.neg hGi.neg hC (fun u => by simpa using hGb u)
    (fun x => neg_eq_zero.mpr (hGreal x))
    (by rw [integral_neg, Complex.neg_re, h0, neg_zero])
    (fun t htS _ => by rw [Complex.neg_re, hGS t htS]; simp)
    (fun x hx => by rw [Complex.neg_re]; linarith [hGneg x hx])
  obtain ⟨b, _, _, hb_nonzero⟩ := hH_uniq
  have hne : ∃ z : ℂ, (-hbExtremal hHB hQ) z ≠ 0 := ⟨(x₀ : ℂ), neg_ne_zero.mpr hx₀⟩
  have hH_deriv := (hb_nonzero hne).2.2.2
  have hG_deriv : ∀ t ∈ S, deriv (hbExtremal hHB hQ) (t : ℂ) ≠ 0 := by
    intro t htS h0'
    apply hH_deriv t htS
    have hd_neg : deriv (fun z => -hbExtremal hHB hQ z) (t : ℂ) = -deriv (hbExtremal hHB hQ) (t : ℂ) :=
      ((hGd (t : ℂ)).hasDerivAt.neg).deriv
    rw [hd_neg, h0', neg_zero]
  exact ⟨S, t₁, t₂, hbExtremal hHB hQ, ht, hS_pair, hGeq_pair, h0, h1, h2, h3, h4, hG_deriv⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.SignUncertainty.hbExtremal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hbExtremal_spec

/-- info: 'FormalResearch.SignUncertainty.hb_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hb_uniqueness

/-- info: 'FormalResearch.SignUncertainty.hbExtremal_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hbExtremal_uniqueness

/-- info: 'FormalResearch.SignUncertainty.hb_two_node_l1_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hb_two_node_l1_norm

/-- info: 'FormalResearch.SignUncertainty.clarkExtremal_l1_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkExtremal_l1_norm

/-- info: 'FormalResearch.SignUncertainty.airy_m1_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_m1_uniqueness

/-- info: 'FormalResearch.SignUncertainty.hb_derivAiry_two_node_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hb_derivAiry_two_node_witness

end FormalResearch.SignUncertainty
