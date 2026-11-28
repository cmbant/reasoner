module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeBase
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart

/-!
# Analytic Virasoro Edge CFU Map `virV`, `virXPrime`, and `virMGeo` (`cts:cauchy-dual` Step 4)

Constructs the complex Virasoro Chester--Friedman--Ursell biholomorphism `v = virV s a`,
parameter `virXPrime a`, and geometric amplitude `virMGeo s a` on a fixed polydisc around `(0, 0)`:

* `virRf`, `virVf`, `virZf`, `virUf`, `virTf`: solutions to the divided-difference and CFU
  equations via `CtChart.scalar_ift_conj`, proving `virPhiDualC (virTf (s, β)) (virXPrimeOfBeta β) =
  virAC β * s + s^3 / 3`.
* `virBetaOfA`, `virV s a`, `virU q a`, `virXPrime a`: jointly holomorphic, odd in `s`,
  conjugation-symmetric, satisfying `virPhiDualC (virV s a) (virXPrime a) = a * s + s^3 / 3` and
  matching `virXPrime a = √(3 virasoroDeltaChart c' ũ / c')` for real `a = 2^{2/3} c'^{-2/3} ũ`.
* `virMGeo s a`: even-in-`s` holomorphic geometric amplitude equal to `1` on `s^2 + a = 0` and
  matching `√(2π/3) √(edgeF'(virV s a)/s) ∂_s virV (1 - e^{-4π edgeF(virV)})^2 / (1 - e^{-4π x'})^2`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.SignUncertainty.CtChart

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 1. Divided-difference equation `virRf`, `virVf`, `virZf`, `virTf` -/

def virHf (q : ℂ × ℂ) : ℂ :=
  -∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * virPC2 (q.2 + (t : ℂ) * (q.1 - q.2))

lemma contDiffAt_virHf : ContDiffAt ℂ ∞' virHf (0, 0) := by
  unfold virHf
  refine ContDiffAt.neg ?_
  refine contDiffAt_segInt (F := fun (q : ℂ × ℂ) w => (1 - w) * virPC2 (q.2 + w * (q.1 - q.2))) ?_
  intro t _
  have h : ContDiffAt ℂ ∞' virPC2 ((fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)) ((0, 0), (t : ℂ))) := by
    simpa using contDiffAt_virPC2
  have h2 : ContDiffAt ℂ ∞' (fun p : (ℂ × ℂ) × ℂ => virPC2 (p.1.2 + p.2 * (p.1.1 - p.1.2))) ((0, 0), (t : ℂ)) :=
    ContDiffAt.comp (g := virPC2) (f := fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)) ((0, 0), (t : ℂ)) h
      (by fun_prop : ContDiff ℂ ∞' fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)).contDiffAt
  exact (contDiff_const.sub contDiff_snd).contDiffAt.mul h2

lemma virPC2_conj : ∀ᶠ z in 𝓝 (0 : ℂ), virPC2 (starRingEnd ℂ z) = starRingEnd ℂ (virPC2 z) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (virPC_conj.and analyticAt_virPC.eventually_analyticAt)
  have hPC_d : ∀ w ∈ ball (0 : ℂ) r, virPC (starRingEnd ℂ w) = starRingEnd ℂ (virPC w) :=
    fun w hw => (hball w hw).1
  have h1 : ∀ w ∈ ball (0 : ℂ) r, deriv virPC (starRingEnd ℂ w) = starRingEnd ℂ (deriv virPC w) := by
    intro w hw
    have hd : HasDerivAt virPC (deriv virPC w) w := (hball w hw).2.differentiableAt.hasDerivAt
    have hev : (fun u => starRingEnd ℂ (virPC (starRingEnd ℂ u))) =ᶠ[𝓝 (starRingEnd ℂ w)] virPC := by
      filter_upwards [isOpen_ball.mem_nhds (by simpa using hw : starRingEnd ℂ w ∈ ball (0 : ℂ) r)] with u hu
      have hu' : starRingEnd ℂ u ∈ ball (0 : ℂ) r := by simpa using hu
      have hcc := hPC_d _ hu'
      rw [Complex.conj_conj] at hcc
      rw [hcc]
    rw [← (Filter.EventuallyEq.deriv_eq hev)]
    exact (hasDerivAt_conj_conj hd).deriv
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  unfold virPC2
  have hd : HasDerivAt (deriv virPC) (deriv (deriv virPC) z) z :=
    (hball z hz).2.deriv.differentiableAt.hasDerivAt
  have hev : (fun u => starRingEnd ℂ (deriv virPC (starRingEnd ℂ u))) =ᶠ[𝓝 (starRingEnd ℂ z)] deriv virPC := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hz : starRingEnd ℂ z ∈ ball (0 : ℂ) r)] with u hu
    have hu' : starRingEnd ℂ u ∈ ball (0 : ℂ) r := by simpa using hu
    have hcc := h1 _ hu'
    rw [Complex.conj_conj] at hcc
    rw [hcc]
  rw [← (Filter.EventuallyEq.deriv_eq hev)]
  exact (hasDerivAt_conj_conj hd).deriv

lemma virHf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virHf (conj2 q) = starRingEnd ℂ (virHf q) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp virPC2_conj
  have hcont : ContinuousAt (fun p : (ℂ × ℂ) × ℝ => p.1.2 + (p.2 : ℂ) * (p.1.1 - p.1.2)) ((0, 0), 0) := by fun_prop
  -- Simply on a small ball `ball (0, 0) (r / 3)`: `‖q.2 + t * (q.1 - q.2)‖ < r`
  have h1 : ∀ᶠ q : ℂ × ℂ in 𝓝 (0, 0), ‖q.1‖ < r / 3 ∧ ‖q.2‖ < r / 3 := by
    have a1 : ∀ᶠ q : ℂ × ℂ in 𝓝 (0, 0), q.1 ∈ ball (0 : ℂ) (r / 3) :=
      continuous_fst.continuousAt.eventually (Metric.ball_mem_nhds 0 (by positivity))
    have a2 : ∀ᶠ q : ℂ × ℂ in 𝓝 (0, 0), q.2 ∈ ball (0 : ℂ) (r / 3) :=
      continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds 0 (by positivity))
    exact (a1.and a2).mono fun _ h => ⟨by simpa using h.1, by simpa using h.2⟩
  filter_upwards [h1] with q ⟨hq1, hq2⟩
  unfold virHf
  rw [map_neg, ← intInt_conj]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have hmem : q.2 + (t : ℂ) * (q.1 - q.2) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    calc ‖q.2 + (t : ℂ) * (q.1 - q.2)‖
        ≤ ‖q.2‖ + ‖(t : ℂ)‖ * (‖q.1‖ + ‖q.2‖) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖q.2‖ + 1 * (‖q.1‖ + ‖q.2‖) := by
          gcongr; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
      _ < r := by linarith
  have e : (conj2 q).2 + (t : ℂ) * ((conj2 q).1 - (conj2 q).2) =
      starRingEnd ℂ (q.2 + (t : ℂ) * (q.1 - q.2)) := by simp [conj2]
  rw [e, hball _ hmem]
  simp

lemma virHf_taylor : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)),
    (q.1 - q.2) ^ 2 * virHf q = -(virPC q.1 - virPC q.2 - deriv virPC q.2 * (q.1 - q.2)) := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp analyticAt_virPC.eventually_analyticAt
  have h1 : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), q.1 ∈ ball (0 : ℂ) r ∧ q.2 ∈ ball (0 : ℂ) r :=
    (continuous_fst.continuousAt.eventually (Metric.ball_mem_nhds _ hr)).and
      (continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds _ hr))
  filter_upwards [h1] with q ⟨hz, hβ⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, q.2 + (t : ℂ) * (q.1 - q.2) ∈ ball (0 : ℂ) r := fun t ht => by
    have hc := (convex_ball (0 : ℂ) r) hβ hz (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
    convert hc using 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hHf : virHf q = -∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * virPC2 (q.2 + (t : ℂ) * (q.1 - q.2)) := rfl
  have hT := taylor2_seg (p := virPC) (p1 := deriv virPC) (p2 := virPC2) (z := q.1) (β := q.2)
    (fun t ht => (hb _ (hseg t ht)).differentiableAt.hasDerivAt)
    (fun t ht => (hb _ (hseg t ht)).deriv.differentiableAt.hasDerivAt)
    (fun t ht => by
      have h2 : ContinuousAt virPC2 ((fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) t) :=
        (hb _ (hseg t ht)).deriv.deriv.continuousAt
      have h3 : ContinuousAt (fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) t := by fun_prop
      exact (ContinuousAt.comp (g := virPC2) (f := fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) h2 h3).continuousWithinAt)
  rw [hHf, mul_neg, ← hT]

/-- `d² R + d z R² + (1/3) z (z - β) R³ + H(z; β) = 0`. -/
def virG1 (p : ℂ × (ℂ × ℂ)) : ℂ :=
  virDC p.2.2 ^ 2 * p.1 + virDC p.2.2 * p.2.1 * p.1 ^ 2 +
    (1 / 3 : ℂ) * p.2.1 * (p.2.1 - p.2.2) * p.1 ^ 3 + virHf p.2

def virR0 : ℂ := -virHf (0, 0) / ((virD0 : ℝ) : ℂ) ^ 2

private lemma virG1_base : virG1 (virR0, (0, 0)) = 0 := by
  unfold virG1 virR0
  simp only [virDC_zero]
  have := virD0C_ne
  field_simp; ring

private lemma contDiffAt_virG1 : ContDiffAt ℂ ∞' virG1 (virR0, (0, 0)) := by
  unfold virG1
  have hd : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => virDC p.2.2) (virR0, (0, 0)) :=
    ContDiffAt.comp (g := virDC) (f := fun p : ℂ × (ℂ × ℂ) => p.2.2) (virR0, (0, 0))
      (by simpa using contDiffAt_virDC) (contDiff_snd.comp contDiff_snd).contDiffAt
  have hH : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => virHf p.2) (virR0, (0, 0)) :=
    ContDiffAt.comp (g := virHf) (f := fun p : ℂ × (ℂ × ℂ) => p.2) (virR0, (0, 0))
      (by simpa using contDiffAt_virHf) contDiff_snd.contDiffAt
  have hR : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.1) := contDiff_fst
  have hz : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.2.1) := contDiff_fst.comp contDiff_snd
  have hb : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.2.2) := contDiff_snd.comp contDiff_snd
  exact ((((hd.pow 2).mul hR.contDiffAt).add ((hd.mul hz.contDiffAt).mul (hR.contDiffAt.pow 2))).add
    (((contDiffAt_const.mul hz.contDiffAt).mul (hz.sub hb).contDiffAt).mul (hR.contDiffAt.pow 3))).add hH

private lemma hasDerivAt_virG1_base : HasDerivAt (fun R : ℂ => virG1 (R, (0, 0))) (((virD0 : ℝ) : ℂ) ^ 2) virR0 := by
  have h : (fun R : ℂ => virG1 (R, (0, 0))) = fun R => ((virD0 : ℝ) : ℂ) ^ 2 * R + virHf (0, 0) := by
    funext R; simp [virG1, virDC_zero]
  rw [h]
  exact ((hasDerivAt_id virR0).const_mul _).add_const _ |>.congr_deriv (by simp)

private lemma conj_virR0 : starRingEnd ℂ virR0 = virR0 := by
  have h0 : starRingEnd ℂ (virHf (0, 0)) = virHf (0, 0) := by
    have := virHf_conj.self_of_nhds
    simpa [conj2] using this.symm
  unfold virR0
  rw [map_div₀, map_neg, h0, map_pow, Complex.conj_ofReal]

lemma exists_virRf : ∃ R : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' R (0, 0) ∧ R (0, 0) = virR0 ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virG1 (R q, q) = 0) ∧
    ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), R (conj2 q) = starRingEnd ℂ (R q) := by
  have hsym : ∀ᶠ p in 𝓝 (virR0, ((0 : ℂ), (0 : ℂ))),
      virG1 (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (virG1 p) := by
    have hb : Tendsto (fun p : ℂ × (ℂ × ℂ) => p.2.2) (𝓝 (virR0, ((0 : ℂ), (0 : ℂ)))) (𝓝 0) :=
      (continuous_snd.comp continuous_snd).continuousAt.tendsto
    have hq : Tendsto (fun p : ℂ × (ℂ × ℂ) => p.2) (𝓝 (virR0, ((0 : ℂ), (0 : ℂ)))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      continuous_snd.continuousAt.tendsto
    filter_upwards [hb.eventually virDC_conj, hq.eventually virHf_conj] with p hp hH
    unfold virG1
    simp only [conj2] at hH hp ⊢
    simp only [map_add, map_mul, map_pow, map_sub, hp, hH]
    have h3 : starRingEnd ℂ (1 / 3 : ℂ) = 1 / 3 := by rw [map_div₀, map_one, map_ofNat]
    rw [h3]
  obtain ⟨ξ, h1, h2, h3, -, h5⟩ := scalar_ift_conj (g := virG1) (x0 := virR0) (q0 := ((0 : ℂ), (0 : ℂ)))
    (g1 := ((virD0 : ℝ) : ℂ) ^ 2) contDiffAt_virG1 virG1_base hasDerivAt_virG1_base
    (pow_ne_zero 2 virD0C_ne) conj_virR0 (by simp [conj2]) hsym
  exact ⟨ξ, h1, h2, h3, h5⟩

def virRf : ℂ × ℂ → ℂ := Classical.choose exists_virRf

lemma contDiffAt_virRf : ContDiffAt ℂ ∞' virRf (0, 0) := (Classical.choose_spec exists_virRf).1
lemma virRf_eq : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virG1 (virRf q, q) = 0 := (Classical.choose_spec exists_virRf).2.2.1
lemma virRf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virRf (conj2 q) = starRingEnd ℂ (virRf q) :=
  (Classical.choose_spec exists_virRf).2.2.2

def virVf (q : ℂ × ℂ) : ℂ := virDC q.2 + (q.1 - q.2) * virRf q

lemma contDiffAt_virVf : ContDiffAt ℂ ∞' virVf (0, 0) := by
  unfold virVf
  have hd : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => virDC q.2) (0, 0) :=
    ContDiffAt.comp (g := virDC) (f := fun q : ℂ × ℂ => q.2) (0, 0)
      (by simpa using contDiffAt_virDC) contDiff_snd.contDiffAt
  exact hd.add ((contDiff_fst.sub contDiff_snd).contDiffAt.mul contDiffAt_virRf)

lemma virVf_zero : virVf (0, 0) = ((virD0 : ℝ) : ℂ) := by simp [virVf, virDC_zero]
lemma virVf_diag (β : ℂ) : virVf (β, β) = virDC β := by simp [virVf]

lemma virVf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virVf (conj2 q) = starRingEnd ℂ (virVf q) := by
  have hb : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [virRf_conj, hb.eventually virDC_conj] with q hq hd
  unfold virVf
  simp only [conj2, map_add, map_mul, map_sub, hd]
  have hq' : virRf (starRingEnd ℂ q.1, starRingEnd ℂ q.2) = starRingEnd ℂ (virRf q) := hq
  rw [hq']

theorem vir_key_identity : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)),
    virLC q.2 - virPC q.1 = -virAC q.2 * virVf q - q.1 * virVf q ^ 3 / 3 := by
  have hb : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [virRf_eq, virHf_taylor, hb.eventually virDC_cube, hb.eventually deriv_virPC_eq] with q hE1 hE2 hE3 hE4
  obtain ⟨z, β⟩ := q
  simp only at hE3 hE4 hE2 ⊢
  unfold virG1 at hE1
  simp only at hE1
  unfold virVf virLC virAC
  simp only
  unfold virFC at hE3
  have hp : virPC β = β * virNtC β := rfl
  rw [hE4] at hE2
  rw [hp] at hE2
  linear_combination ((z - β) ^ 2) * hE1 - hE2 + (z / 3 - β) * hE3

/-- Scalar equation `z virVf(z; β)² - y = 0`. -/
def virG2 (p : ℂ × (ℂ × ℂ)) : ℂ := p.1 * virVf (p.1, p.2.2) ^ 2 - p.2.1

private lemma virG2_base : virG2 (0, (0, 0)) = 0 := by simp [virG2]

private lemma contDiffAt_virG2 : ContDiffAt ℂ ∞' virG2 (0, (0, 0)) := by
  unfold virG2
  have hV : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => virVf (p.1, p.2.2)) (0, (0, 0)) :=
    ContDiffAt.comp (g := virVf) (f := fun p : ℂ × (ℂ × ℂ) => (p.1, p.2.2)) (0, (0, 0))
      (by simpa using contDiffAt_virVf) (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffAt
  exact (contDiff_fst.contDiffAt.mul (hV.pow 2)).sub (contDiff_fst.comp contDiff_snd).contDiffAt

private lemma hasDerivAt_virG2_base : HasDerivAt (fun z : ℂ => virG2 (z, (0, 0))) (((virD0 : ℝ) : ℂ) ^ 2) 0 := by
  have hW : ContDiffAt ℂ ∞' (fun z : ℂ => virVf (z, 0)) 0 :=
    ContDiffAt.comp (g := virVf) (f := fun z : ℂ => (z, (0 : ℂ))) 0
      (by simpa using contDiffAt_virVf) (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd := (hW.differentiableAt (by simp)).hasDerivAt.pow 2
  have h := (hasDerivAt_id' (0 : ℂ)).mul hd
  have e : (fun z : ℂ => virG2 (z, (0, 0))) = fun z => z * virVf (z, 0) ^ 2 := by
    funext z; simp [virG2]
  rw [e]
  refine h.congr_deriv ?_
  simp [virVf_zero]

lemma exists_virZf : ∃ Z : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' Z (0, 0) ∧ Z (0, 0) = 0 ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virG2 (Z q, q) = 0) ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Z (conj2 q) = starRingEnd ℂ (Z q)) ∧
    ∀ᶠ β in 𝓝 (0 : ℂ), Z (virDC β ^ 2 * β, β) = β := by
  have hsym : ∀ᶠ p in 𝓝 ((0 : ℂ), ((0 : ℂ), (0 : ℂ))),
      virG2 (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (virG2 p) := by
    have ht : Tendsto (fun p : ℂ × (ℂ × ℂ) => (p.1, p.2.2)) (𝓝 ((0 : ℂ), ((0 : ℂ), (0 : ℂ)))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousAt.tendsto
    filter_upwards [ht.eventually virVf_conj] with p hp
    unfold virG2
    have hp' : virVf (starRingEnd ℂ p.1, starRingEnd ℂ p.2.2) = starRingEnd ℂ (virVf (p.1, p.2.2)) := hp
    simp only [conj2, map_sub, map_mul, map_pow, hp']
  obtain ⟨ξ, h1, h2, h3, ⟨U, hU, V, hV, huniq⟩, h5⟩ := scalar_ift_conj (g := virG2) (x0 := 0) (q0 := ((0 : ℂ), (0 : ℂ)))
    (g1 := ((virD0 : ℝ) : ℂ) ^ 2) contDiffAt_virG2 virG2_base hasDerivAt_virG2_base
    (pow_ne_zero 2 virD0C_ne) (by simp) (by simp [conj2]) hsym
  refine ⟨ξ, h1, h2, h3, h5, ?_⟩
  have hq : Tendsto (fun β : ℂ => (virDC β ^ 2 * β, β)) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have hc : ContinuousAt virDC 0 := contDiffAt_virDC.continuousAt
    have hca : ContinuousAt (fun β : ℂ => (virDC β ^ 2 * β, β)) 0 := ((hc.pow 2).mul continuousAt_id).prodMk continuousAt_id
    simpa [virDC_zero] using hca.tendsto
  filter_upwards [hq.eventually hV, hU] with β hβV hβU
  have hz : virG2 (β, (virDC β ^ 2 * β, β)) = 0 := by
    unfold virG2; simp only [virVf_diag]; ring
  exact (huniq _ hβV β hβU hz).symm

def virZf : ℂ × ℂ → ℂ := Classical.choose exists_virZf

lemma contDiffAt_virZf : ContDiffAt ℂ ∞' virZf (0, 0) := (Classical.choose_spec exists_virZf).1
lemma virZf_zero : virZf (0, 0) = 0 := (Classical.choose_spec exists_virZf).2.1
lemma virZf_eq : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virZf q * virVf (virZf q, q.2) ^ 2 = q.1 := by
  filter_upwards [(Classical.choose_spec exists_virZf).2.2.1] with q hq
  have hq' : virZf q * virVf (virZf q, q.2) ^ 2 - q.1 = 0 := hq
  linear_combination hq'
lemma virZf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virZf (conj2 q) = starRingEnd ℂ (virZf q) :=
  (Classical.choose_spec exists_virZf).2.2.2.1
lemma vir_saddle_Z : ∀ᶠ β in 𝓝 (0 : ℂ), virZf (virDC β ^ 2 * β, β) = β :=
  (Classical.choose_spec exists_virZf).2.2.2.2

def virUf (q : ℂ × ℂ) : ℂ := 1 / virVf (virZf q, q.2)
def virTf (p : ℂ × ℂ) : ℂ := p.1 * virUf (p.1 ^ 2, p.2)

lemma contDiffAt_virVZ : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => virVf (virZf q, q.2)) (0, 0) := by
  have h := contDiffAt_virZf
  have hV : ContDiffAt ℂ ∞' virVf (virZf (0, 0), (0, 0).2) := by simpa [virZf_zero] using contDiffAt_virVf
  exact ContDiffAt.comp (g := virVf) (f := fun q : ℂ × ℂ => (virZf q, q.2)) (0, 0) hV (h.prodMk contDiff_snd.contDiffAt)

lemma contDiffAt_virUf : ContDiffAt ℂ ∞' virUf (0, 0) := by
  unfold virUf
  exact contDiffAt_const.div contDiffAt_virVZ (by simp [virZf_zero, virVf_zero, virD0_pos.ne'])

lemma contDiffAt_virTf : ContDiffAt ℂ ∞' virTf (0, 0) := by
  unfold virTf
  have hU : ContDiffAt ℂ ∞' virUf ((fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0)) := by simpa using contDiffAt_virUf
  exact contDiff_fst.contDiffAt.mul
    (ContDiffAt.comp (g := virUf) (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) hU
      ((contDiff_fst.pow 2).prodMk contDiff_snd).contDiffAt)

lemma virUf_zero : virUf (0, 0) = 1 / ((virD0 : ℝ) : ℂ) := by
  unfold virUf; simp [virZf_zero, virVf_zero]

lemma virUf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virUf (conj2 q) = starRingEnd ℂ (virUf q) := by
  have hq : Tendsto (fun q : ℂ × ℂ => (virZf q, q.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have h1 := contDiffAt_virZf.continuousAt.tendsto
    rw [virZf_zero] at h1
    exact h1.prodMk_nhds continuous_snd.continuousAt.tendsto
  filter_upwards [virZf_conj, hq.eventually virVf_conj] with q h1 h2
  unfold virUf
  simp only [conj2] at h1 ⊢
  rw [map_div₀, map_one]
  have : virVf (virZf (starRingEnd ℂ q.1, starRingEnd ℂ q.2), starRingEnd ℂ q.2) =
      starRingEnd ℂ (virVf (virZf q, q.2)) := by
    rw [h1]; exact h2
  rw [this]

lemma virTf_conj : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), virTf (conj2 p) = starRingEnd ℂ (virTf p) := by
  have hsq : Tendsto (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have : ContinuousAt (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) :=
      (continuous_fst.pow 2).continuousAt.prodMk continuous_snd.continuousAt
    simpa using this.tendsto
  filter_upwards [hsq.eventually virUf_conj] with p hp
  unfold virTf
  simp only [conj2] at hp ⊢
  rw [map_mul]
  have : virUf ((starRingEnd ℂ p.1) ^ 2, starRingEnd ℂ p.2) = starRingEnd ℂ (virUf (p.1 ^ 2, p.2)) := by
    simpa [conj2, map_pow] using hp
  rw [this]

lemma vir_chart_identity_beta : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    virPhiDualC (virTf p) (virXPrimeOfBeta p.2) = virAC p.2 * p.1 + p.1 ^ 3 / 3 := by
  have hsq : Tendsto (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have : ContinuousAt (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) :=
      (continuous_fst.pow 2).continuousAt.prodMk continuous_snd.continuousAt
    simpa using this.tendsto
  have hzq : Tendsto (fun p : ℂ × ℂ => (virZf (p.1 ^ 2, p.2), p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have h1 := contDiffAt_virZf.continuousAt.tendsto
    rw [virZf_zero] at h1
    exact (h1.comp hsq).prodMk_nhds continuous_snd.continuousAt.tendsto
  have hVf_ne : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virVf (virZf q, q.2) ≠ 0 :=
    contDiffAt_virVZ.continuousAt.eventually_ne (by simp [virZf_zero, virVf_zero, virD0_pos.ne'])
  have hT0 : Tendsto virTf (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
    have := contDiffAt_virTf.continuousAt.tendsto
    have h0 : virTf (0, 0) = 0 := by simp [virTf]
    rwa [h0] at this
  have hsub := virEdgeFC_sub_xiStar_eq
  have hphi_mul := virPhi0C_eq_mul_virPC
  -- Note `virXPrimeOfBeta β = xiStar + β * virF1 β`, so `(4π/3)(virXPrimeOfBeta β - xiStar) = β * virNC β = virLC β`
  filter_upwards [hsq.eventually virZf_eq, hzq.eventually vir_key_identity, hsq.eventually hVf_ne,
    hT0.eventually hphi_mul] with p h1 h2 h3 h4
  obtain ⟨s, β⟩ := p
  simp only at h1 h2 h3 h4
  set z := virZf (s ^ 2, β) with hz
  set V := virVf (z, β) with hV
  have hTU : virTf (s, β) = s / V := by
    unfold virTf virUf; simp only; rw [← hz, ← hV]; ring
  have hT2 : (s / V) ^ 2 = z := by field_simp [h3]; linear_combination -h1
  have hphi_dual : virPhiDualC (virTf (s, β)) (virXPrimeOfBeta β) =
      -(virTf (s, β) * (virLC β - virPC (virTf (s, β) ^ 2))) := by
    unfold virPhiDualC virLC virNC virXPrimeOfBeta
    rw [h4]
    push_cast; ring
  rw [hphi_dual, hTU, hT2]
  simp only at h2 ⊢
  rw [h2]
  field_simp [h3]
  linear_combination s * h1

/-! ### 2. Invert `virAC` (`β = virBetaOfA a`) and define `virV`, `virU`, `virXPrime`, `virMGeo` -/

lemma contDiffAt_virAC : ContDiffAt ℂ ∞' virAC 0 := by
  unfold virAC
  exact (contDiffAt_virDC.pow 2).neg.mul contDiffAt_id

lemma hasDerivAt_virAC_zero : HasDerivAt virAC (-((virD0 : ℝ) : ℂ) ^ 2) 0 := by
  have hd : HasDerivAt (fun β : ℂ => -(virDC β) ^ 2) _ 0 :=
    ((contDiffAt_virDC.differentiableAt (by simp)).hasDerivAt.pow 2).neg
  have hmul := hd.mul (hasDerivAt_id (0 : ℂ))
  refine hmul.congr_deriv ?_
  simp [virDC_zero]

lemma virAC_zero : virAC 0 = 0 := by simp [virAC]

lemma exists_virBetaOfA : ∃ g : ℂ → ℂ, ContDiffAt ℂ ∞' g 0 ∧ g 0 = 0 ∧
    (∀ᶠ a in 𝓝 (0 : ℂ), virAC (g a) = a) ∧
    ∀ᶠ a in 𝓝 (0 : ℂ), g (starRingEnd ℂ a) = starRingEnd ℂ (g a) := by
  let F : ℂ × (ℂ × ℂ) → ℂ := fun p => virAC p.1 - p.2.1
  have hF_cd : ContDiffAt ℂ ∞' F (0, (0, 0)) :=
    (ContDiffAt.comp (g := virAC) (f := fun p : ℂ × (ℂ × ℂ) => p.1) (0, (0, 0))
      (by simpa using contDiffAt_virAC) contDiff_fst.contDiffAt).sub
      (contDiff_fst.comp contDiff_snd).contDiffAt
  have hF_0 : F (0, (0, 0)) = 0 := by simp [F, virAC_zero]
  have hF_d : HasDerivAt (fun x : ℂ => F (x, (0, 0))) (-((virD0 : ℝ) : ℂ) ^ 2) 0 := by
    have h1 : (fun x : ℂ => F (x, (0, 0))) = virAC := by ext x; simp [F]
    rw [h1]; exact hasDerivAt_virAC_zero
  have hF_ne : -((virD0 : ℝ) : ℂ) ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 virD0C_ne)
  have hsym : ∀ᶠ p in 𝓝 ((0 : ℂ), ((0 : ℂ), (0 : ℂ))),
      F (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (F p) := by
    have h1 : Tendsto (fun p : ℂ × (ℂ × ℂ) => p.1) (𝓝 (0, (0, 0))) (𝓝 0) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [h1.eventually virDC_conj] with p hp
    unfold F virAC
    simp only [conj2, map_sub, map_mul, map_neg, map_pow, hp]
  obtain ⟨ξ, h1, h2, h3, -, h5⟩ := scalar_ift_conj hF_cd hF_0 hF_d hF_ne (by simp) (by simp [conj2]) hsym
  let g : ℂ → ℂ := fun a => ξ (a, 0)
  have hg_cd : ContDiffAt ℂ ∞' g 0 :=
    ContDiffAt.comp (g := ξ) (f := fun a : ℂ => (a, (0 : ℂ))) 0 (by simpa using h1)
      (contDiff_id.prodMk contDiff_const).contDiffAt
  have hg_0 : g 0 = 0 := h2
  have hqa : Tendsto (fun a : ℂ => (a, (0 : ℂ))) (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  refine ⟨g, hg_cd, hg_0, ?_, ?_⟩
  · filter_upwards [hqa.eventually h3] with a ha
    have h0 : virAC (ξ (a, 0)) - a = 0 := ha
    exact sub_eq_zero.mp h0
  · filter_upwards [hqa.eventually h5] with a ha
    dsimp [g]
    have hc2 : (starRingEnd ℂ a, (0 : ℂ)) = conj2 (a, 0) := by simp [conj2]
    rw [hc2, ha]

def virBetaOfA : ℂ → ℂ := Classical.choose exists_virBetaOfA

lemma contDiffAt_virBetaOfA : ContDiffAt ℂ ∞' virBetaOfA 0 := (Classical.choose_spec exists_virBetaOfA).1
lemma virBetaOfA_zero : virBetaOfA 0 = 0 := (Classical.choose_spec exists_virBetaOfA).2.1
lemma virAC_virBetaOfA : ∀ᶠ a in 𝓝 (0 : ℂ), virAC (virBetaOfA a) = a := (Classical.choose_spec exists_virBetaOfA).2.2.1
lemma virBetaOfA_conj : ∀ᶠ a in 𝓝 (0 : ℂ), virBetaOfA (starRingEnd ℂ a) = starRingEnd ℂ (virBetaOfA a) :=
  (Classical.choose_spec exists_virBetaOfA).2.2.2

/-- Analytic CFU coordinate `v = virV s a = s * virU (s^2) a`. -/
def virV (s a : ℂ) : ℂ := virTf (s, virBetaOfA a)
/-- Even factor `U_V(q, a) = virUf(q, virBetaOfA a)`. -/
def virU (q a : ℂ) : ℂ := virUf (q, virBetaOfA a)
/-- Analytic saddle frequency `x'(a) = xiStar + β(a) virF1(β(a))`. -/
def virXPrime (a : ℂ) : ℂ := virXPrimeOfBeta (virBetaOfA a)

lemma virV_eq_mul_virU (s a : ℂ) : virV s a = s * virU (s ^ 2) a := rfl
lemma virV_neg (s a : ℂ) : virV (-s) a = -virV s a := by
  unfold virV virTf; simp

lemma contDiffAt_virV : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virV p.1 p.2) (0, 0) := by
  have h1 : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => (p.1, virBetaOfA p.2)) (0, 0) :=
    contDiff_fst.contDiffAt.prodMk (ContDiffAt.comp (g := virBetaOfA) (f := fun p : ℂ × ℂ => p.2) (0, 0)
      (by simpa using contDiffAt_virBetaOfA) contDiff_snd.contDiffAt)
  have hT : ContDiffAt ℂ ∞' virTf ((0 : ℂ), virBetaOfA 0) := by simpa [virBetaOfA_zero] using contDiffAt_virTf
  exact hT.comp (0, 0) h1

lemma contDiffAt_virU : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virU p.1 p.2) (0, 0) := by
  have h1 : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => (p.1, virBetaOfA p.2)) (0, 0) :=
    contDiff_fst.contDiffAt.prodMk (ContDiffAt.comp (g := virBetaOfA) (f := fun p : ℂ × ℂ => p.2) (0, 0)
      (by simpa using contDiffAt_virBetaOfA) contDiff_snd.contDiffAt)
  have hU : ContDiffAt ℂ ∞' virUf ((0 : ℂ), virBetaOfA 0) := by simpa [virBetaOfA_zero] using contDiffAt_virUf
  exact hU.comp (0, 0) h1

lemma contDiffAt_virXPrime : ContDiffAt ℂ ∞' virXPrime 0 := by
  unfold virXPrime virXPrimeOfBeta
  have hF : ContDiffAt ℂ ∞' virF1 (virBetaOfA 0) := by simpa [virBetaOfA_zero] using contDiffAt_virF1
  exact contDiffAt_const.add (contDiffAt_virBetaOfA.mul (hF.comp 0 contDiffAt_virBetaOfA))

lemma virV_zero_zero : virV 0 0 = 0 := by simp [virV, virTf]
lemma virU_zero_zero : virU 0 0 = 1 / ((virD0 : ℝ) : ℂ) := by
  unfold virU; rw [virBetaOfA_zero]; exact virUf_zero
lemma virXPrime_zero : virXPrime 0 = (xiStar : ℂ) := by
  unfold virXPrime virXPrimeOfBeta; rw [virBetaOfA_zero]; simp

lemma virU_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), virU (starRingEnd ℂ q.1) (starRingEnd ℂ q.2) = starRingEnd ℂ (virU q.1 q.2) := by
  have h1 : Tendsto (fun q : ℂ × ℂ => (q.1, virBetaOfA q.2)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    have hb := contDiffAt_virBetaOfA.continuousAt.tendsto
    rw [virBetaOfA_zero] at hb
    exact continuous_fst.continuousAt.tendsto.prodMk_nhds (hb.comp continuous_snd.continuousAt.tendsto)
  have h2 : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [h1.eventually virUf_conj, h2.eventually virBetaOfA_conj] with q hU hb
  unfold virU
  have hU' := hU
  simp only [conj2] at hU'
  rw [hb, hU']

lemma virV_conj : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), virV (starRingEnd ℂ p.1) (starRingEnd ℂ p.2) = starRingEnd ℂ (virV p.1 p.2) := by
  have h1 : Tendsto (fun p : ℂ × ℂ => (p.1, virBetaOfA p.2)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    have hb := contDiffAt_virBetaOfA.continuousAt.tendsto
    rw [virBetaOfA_zero] at hb
    exact continuous_fst.continuousAt.tendsto.prodMk_nhds (hb.comp continuous_snd.continuousAt.tendsto)
  have h2 : Tendsto (fun p : ℂ × ℂ => p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [h1.eventually virTf_conj, h2.eventually virBetaOfA_conj] with p hT hb
  unfold virV
  have hT' := hT
  simp only [conj2] at hT'
  rw [hb, hT']

lemma virXPrime_conj : ∀ᶠ a in 𝓝 (0 : ℂ), virXPrime (starRingEnd ℂ a) = starRingEnd ℂ (virXPrime a) := by
  have hb := contDiffAt_virBetaOfA.continuousAt.tendsto
  rw [virBetaOfA_zero] at hb
  filter_upwards [virBetaOfA_conj, hb.eventually virF1_conj] with a ha hf
  unfold virXPrime virXPrimeOfBeta
  rw [ha, hf, map_add, map_mul, Complex.conj_ofReal]

lemma virPhiDualC_virV_eq : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    virPhiDualC (virV p.1 p.2) (virXPrime p.2) = p.2 * p.1 + p.1 ^ 3 / 3 := by
  have h1 : Tendsto (fun p : ℂ × ℂ => (p.1, virBetaOfA p.2)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    have hb := contDiffAt_virBetaOfA.continuousAt.tendsto
    rw [virBetaOfA_zero] at hb
    exact continuous_fst.continuousAt.tendsto.prodMk_nhds (hb.comp continuous_snd.continuousAt.tendsto)
  have h2 : Tendsto (fun p : ℂ × ℂ => p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [h1.eventually vir_chart_identity_beta, h2.eventually virAC_virBetaOfA] with p hp ha
  unfold virV virXPrime
  rw [hp, ha]

lemma virV_saddle_real : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ),
    let β := (virBetaOfA (a : ℂ)).re
    (a < 0 → 0 < β ∧ virV (√(-a) : ℂ) (a : ℂ) = (√β : ℂ) ∧
      virEdgeFC (√β : ℂ) = virXPrime (a : ℂ) ∧
      tauPhase (virXPrime (a : ℂ)).re = -a / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)) := by
  have hrB : ∀ᶠ a : ℝ in 𝓝 0, (virBetaOfA (a : ℂ)).im = 0 ∧
      virBetaOfA (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    have hta : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝 0) (𝓝 0) :=
      (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
    have htb : Tendsto (fun a : ℝ => virBetaOfA (a : ℂ)) (𝓝 0) (𝓝 0) := by
      have := contDiffAt_virBetaOfA.continuousAt.tendsto
      rw [virBetaOfA_zero] at this
      exact this.comp hta
    filter_upwards [hta.eventually virBetaOfA_conj, htb.eventually (Metric.ball_mem_nhds 0 one_pos)] with a hc hm
    rw [Complex.conj_ofReal] at hc
    exact ⟨Complex.conj_eq_iff_im.mp hc.symm, hm⟩
  have hrD : ∀ᶠ a : ℝ in 𝓝 0, 0 < (virDC (virBetaOfA (a : ℂ))).re ∧
      (virDC (virBetaOfA (a : ℂ))).im = 0 := by
    have hta : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝 0) (𝓝 0) :=
      (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
    have htb : Tendsto (fun a : ℝ => virBetaOfA (a : ℂ)) (𝓝 0) (𝓝 0) := by
      have := contDiffAt_virBetaOfA.continuousAt.tendsto
      rw [virBetaOfA_zero] at this
      exact this.comp hta
    have htd : Tendsto (fun a : ℝ => virDC (virBetaOfA (a : ℂ))) (𝓝 0) (𝓝 ((virD0 : ℝ) : ℂ)) := by
      have := contDiffAt_virDC.continuousAt.tendsto
      rw [virDC_zero] at this
      exact this.comp htb
    have hre_set : {z : ℂ | 0 < z.re} ∈ 𝓝 ((virD0 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [virD0_pos])
    filter_upwards [hta.eventually virBetaOfA_conj, htb.eventually virDC_conj, htd.eventually hre_set] with a hc hd hre
    rw [Complex.conj_ofReal] at hc
    have hbc : starRingEnd ℂ (virBetaOfA (a : ℂ)) = virBetaOfA (a : ℂ) := hc.symm
    rw [hbc] at hd
    exact ⟨hre, Complex.conj_eq_iff_im.mp hd.symm⟩
  have hta : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝 0) (𝓝 0) :=
    (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
  have htb : Tendsto (fun a : ℝ => virBetaOfA (a : ℂ)) (𝓝 0) (𝓝 0) := by
    have := contDiffAt_virBetaOfA.continuousAt.tendsto
    rw [virBetaOfA_zero] at this
    exact this.comp hta
  have hts : Tendsto (fun a : ℝ => (√(max (-a) 0) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous fun a : ℝ => (√(max (-a) 0) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_neg.max continuous_const).sqrt)
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have htsβ : Tendsto (fun a : ℝ => (√(max (virBetaOfA (a : ℂ)).re 0) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcr : ContinuousAt (fun a : ℝ => (virBetaOfA (a : ℂ)).re) (0 : ℝ) :=
      Complex.continuous_re.continuousAt.comp
        (contDiffAt_virBetaOfA.continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))) Complex.ofReal_zero)
    have hcm : ContinuousAt (fun a : ℝ => (√(max (virBetaOfA (a : ℂ)).re 0) : ℂ)) (0 : ℝ) :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuous_sqrt.continuousAt.comp (hcr.max continuousAt_const))
    simpa [virBetaOfA_zero] using hcm.tendsto
  have hpair : Tendsto (fun a : ℝ => ((√(max (-a) 0) : ℂ), (a : ℂ))) (𝓝 0) (𝓝 (0, 0)) :=
    hts.prodMk_nhds hta
  filter_upwards [hrB, hrD, hta.eventually virAC_virBetaOfA, htb.eventually vir_saddle_Z,
    htsβ.eventually virEdgeFC_sub_xiStar_eq,
    hta.eventually virXPrime_conj, hpair.eventually virPhiDualC_virV_eq] with a hB hD ha_ac hz_sad hsβ_sub hx_conj hphi_v
  intro β ha_neg
  have hB_c : virBetaOfA (a : ℂ) = (β : ℂ) := Complex.ext rfl hB.1
  have hD_re_pos : 0 < (virDC (β : ℂ)).re := by rw [← hB_c]; exact hD.1
  have hD_c : virDC (β : ℂ) = (((virDC (β : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (by rw [← hB_c]; exact hD.2)
  set d := (virDC (β : ℂ)).re
  have h_ac_r : -d ^ 2 * β = a := by
    have h1 := ha_ac
    rw [hB_c] at h1
    unfold virAC at h1
    rw [hD_c] at h1
    have h2 : (-((d : ℂ) ^ 2) * (β : ℂ)).re = (a : ℂ).re := congrArg Complex.re h1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_re] at h2
    exact h2
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hD_re_pos
  have hneg_mul : -d ^ 2 * β = -(d ^ 2 * β) := by ring
  have hβ_pos : 0 < β := pos_of_mul_pos_right (by linarith only [h_ac_r, hneg_mul, ha_neg] : 0 < d ^ 2 * β) hd2.le
  have h_sq_eq : ((-a : ℝ) : ℂ) = virDC (β : ℂ) ^ 2 * (β : ℂ) := by
    rw [hD_c]
    exact_mod_cast (by linarith only [h_ac_r, hneg_mul] : -a = d ^ 2 * β)
  have hZ_val : virZf (((-a : ℝ) : ℂ), (β : ℂ)) = (β : ℂ) := by
    rw [h_sq_eq]; simpa [hB_c] using hz_sad
  have hsqrt_a : ((√(-a) : ℂ)) ^ 2 = ((-a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
  have hV_val : virV (√(-a) : ℂ) (a : ℂ) = (√β : ℂ) := by
    unfold virV virTf virUf
    rw [hB_c, hsqrt_a, hZ_val, virVf_diag, hD_c]
    have hβ_sq : -a = d ^ 2 * β := by linarith [h_ac_r]
    rw [hβ_sq, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hD_re_pos.le]
    push_cast
    have hd_ne : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD_re_pos.ne'
    field_simp [hd_ne]
  have hedge_val : virEdgeFC (√β : ℂ) = virXPrime (a : ℂ) := by
    have hmax : max (virBetaOfA (a : ℂ)).re 0 = β := max_eq_left hβ_pos.le
    have hs_eq := hsβ_sub
    rw [hmax] at hs_eq
    have hs2 : ((√β : ℂ) ^ 2) = (β : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hβ_pos.le]
    rw [hs2] at hs_eq
    unfold virXPrime virXPrimeOfBeta
    rw [hB_c]
    linear_combination hs_eq
  refine ⟨hβ_pos, hV_val, hedge_val, ?_⟩
  have hx'_eq : (virXPrime (a : ℂ)).re = edgeF (√β) := by
    rw [← hedge_val, virEdgeFC_ofReal, Complex.ofReal_re]
  have hphi_real_eq : phiDual (√β) (virXPrime (a : ℂ)).re = -(2 / 3 : ℝ) * (-a) ^ (3 / 2 : ℝ) := by
    have hx_im : (virXPrime (a : ℂ)).im = 0 := by
      have hc := hx_conj
      rw [Complex.conj_ofReal] at hc
      exact Complex.conj_eq_iff_im.mp hc.symm
    have hx_c : virXPrime (a : ℂ) = (((virXPrime (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hx_im
    have hp := hphi_v
    rw [max_eq_left (by linarith : 0 ≤ -a)] at hp
    rw [hV_val, hx_c, virPhiDualC_ofReal] at hp
    have hre_eq := congrArg Complex.re hp
    simp only [Complex.ofReal_re] at hre_eq
    have hs3 : √(-a) ^ 3 = (-a) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((-a) ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul (by linarith)]
      norm_num
    have h1 : (a : ℂ) * (√(-a) : ℂ) + (√(-a) : ℂ) ^ 3 / 3 =
        ((a * √(-a) + √(-a) ^ 3 / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.ofReal_re] at hre_eq
    have h2 : a * √(-a) = -((-a) * √(-a)) := by ring
    have h3 : (-a) * √(-a) = (-a) ^ (3 / 2 : ℝ) := by
      calc (-a) * √(-a) = √((-a) ^ 2) * √(-a) := by rw [Real.sqrt_sq (by linarith)]
        _ = √((-a) ^ 3) := by rw [← Real.sqrt_mul (sq_nonneg _)]; ring_nf
        _ = (-a) ^ (3 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (-a) 3, ← Real.rpow_mul (by linarith)]; norm_num
    linarith only [hre_eq, h2, h3, hs3]
  have hpl := phiDual_eq (x' := (virXPrime (a : ℂ)).re) (Real.sqrt_nonneg β)
  rw [← hx'_eq, sub_self, mul_zero, zero_mul, zero_sub] at hpl
  have hcum : cumulN (virXPrime (a : ℂ)).re = (-a) ^ (3 / 2 : ℝ) / (3 * π) := by
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    have hmul : 2 * π * cumulN (virXPrime (a : ℂ)).re = 2 / 3 * (-a) ^ (3 / 2 : ℝ) := by
      linarith only [hphi_real_eq, hpl]
    field_simp [hpi]
    linarith only [hmul]
  unfold tauPhase
  rw [hcum]
  have hkt : (3 * π * kTip) = 2 * betaTip ^ (3 / 2 : ℝ) := by
    have hb := four_thirds_betaTip_rpow
    have hkt' : KTip = 2 * π * kTip := rfl
    linarith only [hb, hkt']
  have hbase : (-a) ^ (3 / 2 : ℝ) / (3 * π) / kTip = (-a) ^ (3 / 2 : ℝ) / (2 * betaTip ^ (3 / 2 : ℝ)) := by
    rw [div_div, hkt]
  have hden_pos : 0 ≤ 2 * betaTip ^ (3 / 2 : ℝ) := by
    have hb0 := betaTip_pos
    positivity
  rw [hbase, Real.div_rpow (Real.rpow_nonneg (by linarith) _) hden_pos,
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg betaTip_pos.le _),
    ← Real.rpow_mul (by linarith : 0 ≤ -a), ← Real.rpow_mul betaTip_pos.le]
  norm_num

/-! ### 3. Analytic match `virXPrime a^2 / 3 = virasoroXiInf (2^{-2/3} a)` and `virMGeo` -/

lemma virXPrime_eq_virasoroXiInf :
    ∀ᶠ a in 𝓝 (0 : ℂ), virXPrime a ^ 2 / 3 = virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * a) := by
  have han_l : AnalyticAt ℂ (fun a => virXPrime a ^ 2 / 3) 0 :=
    ((analyticAt_of_cd contDiffAt_virXPrime).pow 2).div analyticAt_const (by norm_num)
  have h2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have han_r : AnalyticAt ℂ (fun a => virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * a)) 0 := by
    have hx := langerCore.hxiInf_an 0 (mem_ball_self virasoroRUInf_pos)
    have hm : AnalyticAt ℂ (fun a : ℂ => (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * a) 0 :=
      analyticAt_const.mul analyticAt_id
    exact AnalyticAt.comp (by simpa using hx) hm
  obtain ⟨r1, hr1, h1⟩ := Metric.eventually_nhds_iff_ball.mp han_l.eventually_analyticAt
  obtain ⟨r2, hr2, h2⟩ := Metric.eventually_nhds_iff_ball.mp han_r.eventually_analyticAt
  obtain ⟨r3, hr3, h3⟩ := Metric.eventually_nhds_iff_ball.mp virV_saddle_real
  obtain ⟨r4, hr4, h4⟩ := Metric.eventually_nhds_iff_ball.mp virXPrime_conj
  let r : ℝ := min (min r1 r2) (min r3 (min r4
    (min (chartParams.δ_band * (2 : ℝ) ^ (2 / 3 : ℝ) / 2)
      (min (virasoroBV ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ)) (virasoroRUInf * (2 : ℝ) ^ (2 / 3 : ℝ) / 2)))))
  have hr : 0 < r := lt_min (lt_min hr1 hr2) (lt_min hr3 (lt_min hr4 (lt_min
    (by have := chartParams.hδ_band_pos; positivity)
    (lt_min (by have := virasoroBV_pos; positivity) (by have := virasoroRUInf_pos; positivity)))))
  have heq_neg : ∀ a : ℝ, -r < a → a < 0 →
      virXPrime (a : ℂ) ^ 2 / 3 = virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * (a : ℂ)) := by
    intro a har ha0
    have ha_pos_neg : -a < r := neg_lt.mp har
    have ha3 : a ∈ ball (0 : ℝ) r3 := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_neg ha0]
      exact ha_pos_neg.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨hβ_pos, -, hedge, htau_vir⟩ := h3 a ha3 ha0
    have ha4 : (a : ℂ) ∈ ball (0 : ℂ) r4 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha0]
      exact ha_pos_neg.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hx_im : (virXPrime (a : ℂ)).im = 0 := by
      have hc := h4 _ ha4
      rw [Complex.conj_ofReal] at hc
      exact Complex.conj_eq_iff_im.mp hc.symm
    have hx_re_gt : xiStar < (virXPrime (a : ℂ)).re := by
      rw [← hedge, virEdgeFC_ofReal, Complex.ofReal_re, ← edgeF_zero]
      exact edgeF_strictMonoOn le_rfl (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hβ_pos)
    set ut : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * a with hut_def
    have h2_inv : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add zero_lt_two]; norm_num
    have hut_neg : ut < 0 := mul_neg_of_pos_of_neg h2neg_pos ha0
    have h_neg_ut_band : -ut ≤ chartParams.δ_band := by
      have h1 : -a < chartParams.δ_band * (2 : ℝ) ^ (2 / 3 : ℝ) / 2 :=
        ha_pos_neg.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      have h2 := mul_lt_mul_of_pos_left h1 h2neg_pos
      have h_eq : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (chartParams.δ_band * (2 : ℝ) ^ (2 / 3 : ℝ) / 2) =
          chartParams.δ_band / 2 := by
        calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (chartParams.δ_band * (2 : ℝ) ^ (2 / 3 : ℝ) / 2)
            = chartParams.δ_band * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) / 2 := by ring
          _ = chartParams.δ_band / 2 := by rw [h2_inv, mul_one]
      rw [h_eq] at h2
      have hδ0 := chartParams.hδ_band_pos
      linarith [show -ut = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (-a) by rw [hut_def]; ring]
    have hut_band : -(chartParams.δ_band * (1 : ℝ) ^ (2 / 3 : ℝ)) ≤ ut := by
      simp only [Real.one_rpow, mul_one]; linarith
    have hut_bv : -ut < virasoroBV ^ 2 := by
      have h1 : -a < virasoroBV ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ) :=
        ha_pos_neg.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
      have h2 := mul_lt_mul_of_pos_left h1 h2neg_pos
      have h_eq : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (virasoroBV ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ)) = virasoroBV ^ 2 := by
        calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (virasoroBV ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ))
            = virasoroBV ^ 2 * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) := by ring
          _ = virasoroBV ^ 2 := by rw [h2_inv, mul_one]
      rw [h_eq] at h2
      linarith [show -ut = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (-a) by rw [hut_def]; ring]
    have hut_ruinf : |ut| < virasoroRUInf := by
      rw [abs_of_neg hut_neg]
      have h1 : -a < virasoroRUInf * (2 : ℝ) ^ (2 / 3 : ℝ) / 2 :=
        ha_pos_neg.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
      have h2 := mul_lt_mul_of_pos_left h1 h2neg_pos
      have h_eq : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (virasoroRUInf * (2 : ℝ) ^ (2 / 3 : ℝ) / 2) = virasoroRUInf / 2 := by
        calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (virasoroRUInf * (2 : ℝ) ^ (2 / 3 : ℝ) / 2)
            = virasoroRUInf * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) / 2 := by ring
          _ = virasoroRUInf / 2 := by rw [h2_inv, mul_one]
      rw [h_eq] at h2
      have := virasoroRUInf_pos
      linarith [show -ut = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (-a) by rw [hut_def]; ring]
    have hut_mem : ut ∈ Icc (-(virasoroAC 1 ^ 2)) (virasoroAC 1 ^ 2) := by
      have hAC1 : virasoroAC 1 ^ 2 = 2 * virasoroBV ^ 2 := by simpa using virasoroAC_sq 1 zero_le_one
      rw [hAC1]; constructor <;> nlinarith [sq_nonneg virasoroBV]
    have h0_mem : (0 : ℝ) ∈ Icc (-(virasoroAC 1 ^ 2)) (virasoroAC 1 ^ 2) :=
      ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩
    have hΔ_gt : xiBar < virasoroDeltaChart 1 ut := by
      rw [← mul_one xiBar, ← virasoroDeltaChart_zero (c' := 1)]
      exact virasoroDeltaChart_strictAnti zero_lt_one hut_mem h0_mem hut_neg
    have hxb_pos : 0 < xiBar := by unfold xiBar; positivity [xiStar_pos]
    have hroot_gt : xiStar < √(3 * virasoroDeltaChart 1 ut / 1) := by
      rw [div_one, Real.lt_sqrt xiStar_pos.le]
      have hxb : xiBar = xiStar ^ 2 / 3 := rfl
      linarith
    have htau_chart : tauPhase (√(3 * virasoroDeltaChart 1 ut / 1)) =
        -a / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) := by
      rw [chartParams.hband zero_lt_one hut_band hut_neg, Real.one_rpow, mul_one]
      have h_eq : -ut = -a / (2 : ℝ) ^ (2 / 3 : ℝ) := by
        rw [hut_def, neg_mul_eq_mul_neg, div_eq_mul_inv, Real.rpow_neg zero_le_two]
        ring
      rw [h_eq, div_div]
    have hx_eq_root : (virXPrime (a : ℂ)).re = √(3 * virasoroDeltaChart 1 ut / 1) :=
      tauPhase_strictMonoOn.injOn (Set.mem_Ici.mpr hx_re_gt.le) (Set.mem_Ici.mpr hroot_gt.le)
        (htau_vir.trans htau_chart.symm)
    have hξ_c_eq : virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * (a : ℂ)) = virasoroXiInf (ut : ℂ) := by
      congr 1; rw [hut_def]; push_cast; ring
    have hξ_im : (virasoroXiInf (ut : ℂ)).im = 0 := virasoroXiInf_ofReal_im hut_ruinf
    have hΔ_eq : virasoroDeltaChart 1 ut = (virasoroXiInf (ut : ℂ)).re := by
      unfold virasoroDeltaChart virasoroXiChartC
      simp only [Real.one_rpow, Complex.ofReal_one, mul_one, one_mul]
    have hsq_re : (virXPrime (a : ℂ)).re ^ 2 / 3 = (virasoroXiInf (ut : ℂ)).re := by
      rw [hx_eq_root, div_one, Real.sq_sqrt (by linarith [hΔ_gt, hxb_pos]), hΔ_eq]
      ring
    have hx_c : virXPrime (a : ℂ) = (((virXPrime (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hx_im
    have hξ_c : virasoroXiInf (ut : ℂ) = (((virasoroXiInf (ut : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hξ_im
    rw [hξ_c_eq, hx_c, hξ_c, ← Complex.ofReal_pow,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, hsq_re]
  have hr_1 : r ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr_2 : r ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have han1 : AnalyticOnNhd ℂ (fun a => virXPrime a ^ 2 / 3) (ball 0 r) :=
    fun w hw => h1 w (ball_subset_ball hr_1 hw)
  have han2 : AnalyticOnNhd ℂ (fun a => virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * a)) (ball 0 r) :=
    fun w hw => h2 w (ball_subset_ball hr_2 hw)
  have heq : EqOn (fun a => virXPrime a ^ 2 / 3)
      (fun a => virasoroXiInf (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * a)) (ball 0 r) := by
    refine han1.eqOn_of_preconnected_of_frequently_eq han2 (convex_ball _ _).isPreconnected
      (mem_ball_self hr) ?_
    rw [frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0V, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    set t : ℝ := -min (δ / 2) (r / 2)
    have ht_neg : t < 0 := neg_lt_zero.mpr (lt_min (half_pos hδ_pos) (half_pos hr))
    have ht_gt : -r < t := by
      have : min (δ / 2) (r / 2) < r := (min_le_right _ _).trans_lt (half_lt_self hr)
      linarith
    refine ⟨(t : ℂ), hVU ⟨hδball ?_, by simp [ht_neg.ne]⟩, heq_neg t ht_gt ht_neg⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht_neg]
    dsimp only [t]
    rw [neg_neg]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
  filter_upwards [Metric.ball_mem_nhds 0 hr] with a ha
  exact heq ha

/-- Analytic even quotient `F'(z) / z` filled at `z = 0` by `π / √2`. -/
def virEdgeG' (z : ℂ) : ℂ :=
  dslope virEdgeFC' 0 z

lemma hasDerivAt_virEdgeFC'_zero : HasDerivAt virEdgeFC' ((π / √2 : ℝ) : ℂ) 0 := by
  have h1 : |((0 : ℂ)).im| < 1 / 2 := by simp
  have hsq_at : 1 + Complex.cosh ((π : ℂ) * 0) ^ 2 = (2 : ℂ) := by norm_num
  have hlin : HasDerivAt (fun z : ℂ => (π : ℂ) * z) (π : ℂ) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)
    exact h.congr_deriv (mul_one _)
  have hsh : HasDerivAt (fun z : ℂ => Complex.sinh ((π : ℂ) * z)) (π : ℂ) 0 := by
    have h := (Complex.hasDerivAt_sinh ((π : ℂ) * 0)).comp 0 hlin
    exact h.congr_deriv (by simp)
  have hdiff_den : DifferentiableAt ℂ (fun z : ℂ => (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) 0 := by
    have hch : DifferentiableAt ℂ (fun z : ℂ => Complex.cosh ((π : ℂ) * z)) 0 := by fun_prop
    exact ((differentiableAt_const _).add (hch.pow 2)).cpow_const (one_add_cosh_pi_sq_slit h1)
  have hden0 : (1 + Complex.cosh ((π : ℂ) * 0) ^ 2) ^ (1 / 2 : ℂ) = ((√2 : ℝ) : ℂ) := by
    rw [hsq_at, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  have hden_ne : (1 + Complex.cosh ((π : ℂ) * 0) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [hden0]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  refine (hsh.div hdiff_den.hasDerivAt hden_ne).congr_deriv ?_
  rw [hden0, mul_zero, Complex.sinh_zero, zero_mul, sub_zero]
  have h2c : ((√2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast
  field_simp [h2c]

lemma virEdgeG'_zero : virEdgeG' 0 = ((π / √2 : ℝ) : ℂ) := by
  unfold virEdgeG'
  rw [dslope_same, hasDerivAt_virEdgeFC'_zero.deriv]

lemma virEdgeG'_mul (z : ℂ) : z * virEdgeG' z = virEdgeFC' z := by
  unfold virEdgeG'
  have h := sub_smul_dslope virEdgeFC' 0 z
  simpa [virEdgeFC'_zero] using h

lemma differentiableOn_virEdgeG' : DifferentiableOn ℂ virEdgeG' {z : ℂ | |z.im| < 1 / 2} :=
  (Complex.differentiableOn_dslope (isOpen_virStrip.mem_nhds (by simp))).mpr differentiableOn_virEdgeFC'

lemma analyticOnNhd_virEdgeG' : AnalyticOnNhd ℂ virEdgeG' {z : ℂ | |z.im| < 1 / 2} :=
  differentiableOn_virEdgeG'.analyticOnNhd isOpen_virStrip

lemma virEdgeG'_neg {z : ℂ} : virEdgeG' (-z) = virEdgeG' z := by
  by_cases hz : z = 0
  · subst hz; simp
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    unfold virEdgeG'
    rw [dslope_of_ne _ hnz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      virEdgeFC'_zero, sub_zero, sub_zero]
    have hodd : virEdgeFC' (-z) = -virEdgeFC' z := by
      unfold virEdgeFC'
      rw [mul_neg, Complex.sinh_neg, Complex.cosh_neg]; ring
    rw [hodd]; ring

lemma virEdgeG'_conj {z : ℂ} (hz : |z.im| < 1 / 2) :
    virEdgeG' (starRingEnd ℂ z) = starRingEnd ℂ (virEdgeG' z) := by
  by_cases hz0 : z = 0
  · subst hz0; simp [virEdgeG'_zero]
  · have hsz0 : starRingEnd ℂ z ≠ 0 := by
      intro h; apply hz0; simpa using congrArg (starRingEnd ℂ) h
    unfold virEdgeG'
    rw [dslope_of_ne _ hsz0, dslope_of_ne _ hz0, slope_def_field, slope_def_field,
      virEdgeFC'_zero, sub_zero, sub_zero, map_div₀]
    have hsq : 1 + Complex.cosh ((π : ℂ) * z) ^ 2 ∈ Complex.slitPlane := one_add_cosh_pi_sq_slit hz
    have hc_arg : Complex.cosh ((π : ℂ) * starRingEnd ℂ z) = starRingEnd ℂ (Complex.cosh ((π : ℂ) * z)) := by
      rw [show (π : ℂ) * starRingEnd ℂ z = starRingEnd ℂ ((π : ℂ) * z) by simp, Complex.cosh_conj]
    have hs_arg : Complex.sinh ((π : ℂ) * starRingEnd ℂ z) = starRingEnd ℂ (Complex.sinh ((π : ℂ) * z)) := by
      rw [show (π : ℂ) * starRingEnd ℂ z = starRingEnd ℂ ((π : ℂ) * z) by simp, Complex.sinh_conj]
    have h1c : 1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ z) ^ 2 =
        starRingEnd ℂ (1 + Complex.cosh ((π : ℂ) * z) ^ 2) := by
      rw [hc_arg]; simp
    have hs_c : (1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ z) ^ 2) ^ (1 / 2 : ℂ) =
        starRingEnd ℂ ((1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) := by
      have hc := Complex.cpow_conj (1 + Complex.cosh ((π : ℂ) * z) ^ 2) (1 / 2 : ℂ)
        (Complex.mem_slitPlane_iff_arg.mp hsq).1
      have h12 : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [map_div₀, map_one, map_ofNat]
      rw [h12] at hc
      rw [h1c, hc, Complex.conj_conj]
    have hfc : virEdgeFC' (starRingEnd ℂ z) = starRingEnd ℂ (virEdgeFC' z) := by
      unfold virEdgeFC'; rw [hs_arg, hs_c, map_div₀]
    rw [hfc, sub_zero, sub_zero]

/-- Squared geometric Jacobian before taking the principal square root. -/
def virMSq (s a : ℂ) : ℂ :=
  ((2 * π / 3 : ℝ) : ℂ) * virEdgeG' (virV s a) * virU (s ^ 2) a *
    (deriv (fun σ => virV σ a) s) ^ 2

/-- Holomorphic Virasoro geometric amplitude, equal to `1` on the saddle locus `s^2 + a = 0`. -/
def virMGeo (s a : ℂ) : ℂ :=
  (virMSq s a) ^ (1 / 2 : ℂ) *
    ((1 - Complex.exp (-(4 * π : ℂ) * virEdgeFC (virV s a))) /
      (1 - Complex.exp (-(4 * π : ℂ) * virXPrime a))) ^ 2

lemma contDiffAt2_virV : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
    ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) p := by
  have h2 : ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) ((0 : ℂ), (0 : ℂ)) :=
    contDiffAt_virV.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞')
  exact h2.eventually (by simp : (2 : WithTop ℕ∞) ≠ ∞')

lemma contDiffAt2_virV_slice {s a : ℂ} (hcd : ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) (s, a)) :
    ContDiffAt ℂ 2 (fun σ : ℂ => virV σ a) s :=
  ContDiffAt.comp (g := fun q : ℂ × ℂ => virV q.1 q.2) (f := fun σ : ℂ => (σ, a)) s hcd
    (contDiff_id.prodMk contDiff_const).contDiffAt

lemma contDiffAt_virDerivS :
    ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => deriv (fun σ => virV σ p.2) p.1) (0, 0) := by
  have hv : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virV p.1 p.2) (0, 0) := contDiffAt_virV
  have hf : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => fderiv ℂ (fun q : ℂ × ℂ => virV q.1 q.2) p ((1 : ℂ), (0 : ℂ))) (0, 0) :=
    (hv.fderiv_right (by simp : ∞' + 1 ≤ ∞')).clm_apply contDiffAt_const
  refine hf.congr_of_eventuallyEq ?_
  filter_upwards [contDiffAt2_virV] with p hp
  have hd : DifferentiableAt ℂ (fun q : ℂ × ℂ => virV q.1 q.2) p := hp.differentiableAt (by simp)
  have hL : HasDerivAt (fun σ : ℂ => virV σ p.2) (fderiv ℂ (fun q : ℂ × ℂ => virV q.1 q.2) p (1, 0)) p.1 := by
    have hinc : HasDerivAt (fun σ : ℂ => (σ, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hd.hasFDerivAt.comp_hasDerivAt p.1 hinc : HasDerivAt ((fun q : ℂ × ℂ => virV q.1 q.2) ∘ fun σ => (σ, p.2)) _ p.1)
  exact hL.deriv

lemma contDiffAt_virMSq : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virMSq p.1 p.2) (0, 0) := by
  unfold virMSq
  have hg' : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virEdgeG' (virV p.1 p.2)) (0, 0) := by
    have han : ContDiffAt ℂ ∞' virEdgeG' (virV 0 0) := by
      rw [virV_zero_zero]
      exact (analyticOnNhd_virEdgeG' 0 (by simp)).contDiffAt
    exact han.comp (0, 0) contDiffAt_virV
  have hu : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virU (p.1 ^ 2) p.2) (0, 0) := by
    have hp : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) ((0 : ℂ), (0 : ℂ)) :=
      ((contDiff_fst : ContDiff ℂ ∞' (fun p : ℂ × ℂ => p.1)).pow 2).prodMk contDiff_snd |>.contDiffAt
    have hu0 : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => virU q.1 q.2) ((0 : ℂ) ^ 2, (0 : ℂ)) := by
      simpa using contDiffAt_virU
    exact ContDiffAt.comp ((0 : ℂ), (0 : ℂ)) (g := fun q : ℂ × ℂ => virU q.1 q.2)
      (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) hu0 hp
  exact (((contDiffAt_const.mul hg').mul hu).mul (contDiffAt_virDerivS.pow 2))

lemma virDerivS_zero_zero : deriv (fun σ => virV σ 0) 0 = 1 / ((virD0 : ℝ) : ℂ) := by
  have hd_u : DifferentiableAt ℂ (fun σ : ℂ => virU (σ ^ 2) 0) 0 := by
    have hp : ContDiffAt ℂ ∞' (fun σ : ℂ => (σ ^ 2, (0 : ℂ))) (0 : ℂ) :=
      ((contDiff_id : ContDiff ℂ ∞' (fun σ : ℂ => σ)).pow 2).prodMk contDiff_const |>.contDiffAt
    have hu0 : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => virU q.1 q.2) ((0 : ℂ) ^ 2, (0 : ℂ)) := by
      simpa using contDiffAt_virU
    exact (ContDiffAt.comp (0 : ℂ) (g := fun q : ℂ × ℂ => virU q.1 q.2)
      (f := fun σ : ℂ => (σ ^ 2, (0 : ℂ))) hu0 hp).differentiableAt (by simp)
  have hd : HasDerivAt (fun σ : ℂ => σ * virU (σ ^ 2) 0) (1 * virU (0 ^ 2) 0 + 0 * deriv (fun σ => virU (σ ^ 2) 0) 0) 0 :=
    (hasDerivAt_id 0).mul hd_u.hasDerivAt
  have heq : (fun σ : ℂ => virV σ 0) = fun σ : ℂ => σ * virU (σ ^ 2) 0 := rfl
  rw [heq, hd.deriv, one_mul, zero_mul, add_zero, zero_pow two_ne_zero]
  exact virU_zero_zero

lemma virMSq_zero_zero : virMSq 0 0 = 1 := by
  unfold virMSq
  rw [virV_zero_zero, virEdgeG'_zero, zero_pow two_ne_zero, virU_zero_zero, virDerivS_zero_zero]
  have h1 : (((2 * π / 3 : ℝ) : ℂ) * ((π / √2 : ℝ) : ℂ)) * (1 / ((virD0 : ℝ) : ℂ)) *
      (1 / ((virD0 : ℝ) : ℂ)) ^ 2 =
      ((2 * π ^ 2 / (3 * √2) : ℝ) : ℂ) / ((virD0 : ℝ) : ℂ) ^ 3 := by
    push_cast; ring
  have hne : (2 * π ^ 2 / (3 * √2) : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  rw [h1, virD0C_cube, div_self (Complex.ofReal_ne_zero.mpr hne)]

lemma virExpDen_zero_ne : 1 - Complex.exp (-(4 * π : ℂ) * virXPrime 0) ≠ 0 := by
  rw [virXPrime_zero, sub_ne_zero]
  have hneg : -4 * π * xiStar < 0 := by
    have h1 : 0 < 4 * π * xiStar := by have := Real.pi_pos; have := xiStar_pos; positivity
    linarith
  have hlt : Real.exp (-4 * π * xiStar) < 1 := Real.exp_lt_one_iff.mpr hneg
  intro h
  have hre := congrArg Complex.re h
  rw [show -(4 * π : ℂ) * (xiStar : ℂ) = (((-4 * π * xiStar : ℝ) : ℂ)) by push_cast; ring,
    ← Complex.ofReal_exp, Complex.ofReal_re, Complex.one_re] at hre
  linarith

lemma contDiffAt_virMGeo : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virMGeo p.1 p.2) (0, 0) := by
  unfold virMGeo
  have hmsq : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => (virMSq p.1 p.2) ^ (1 / 2 : ℂ)) (0, 0) := by
    have hsp : virMSq 0 0 ∈ Complex.slitPlane := by rw [virMSq_zero_zero]; exact Complex.one_mem_slitPlane
    have hcp : ContDiffAt ℂ ∞' (fun z : ℂ => z ^ (1 / 2 : ℂ)) (virMSq 0 0) :=
      (analyticAt_id.cpow analyticAt_const hsp).contDiffAt
    exact hcp.comp (0, 0) contDiffAt_virMSq
  have hedge_f : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virEdgeFC (virV p.1 p.2)) (0, 0) := by
    have h0 : ContDiffAt ℂ ∞' virEdgeFC (virV 0 0) := by
      rw [virV_zero_zero]
      exact (analyticOnNhd_virEdgeFC 0 (by simp)).contDiffAt
    exact h0.comp (0, 0) contDiffAt_virV
  have hnum : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => 1 - Complex.exp (-(4 * π : ℂ) * virEdgeFC (virV p.1 p.2))) (0, 0) := by
    have hce : ContDiffAt ℂ ∞' Complex.exp (-(4 * π : ℂ) * virEdgeFC (virV 0 0)) := Complex.contDiff_exp.contDiffAt
    exact contDiffAt_const.sub (hce.comp (0, 0) (contDiffAt_const.mul hedge_f))
  have hx_p : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virXPrime p.2) (0, 0) :=
    ContDiffAt.comp (g := virXPrime) (f := fun p : ℂ × ℂ => p.2) (0, 0)
      (by simpa using contDiffAt_virXPrime) contDiff_snd.contDiffAt
  have hden : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => 1 - Complex.exp (-(4 * π : ℂ) * virXPrime p.2)) (0, 0) := by
    have hce : ContDiffAt ℂ ∞' Complex.exp (-(4 * π : ℂ) * virXPrime 0) := Complex.contDiff_exp.contDiffAt
    exact contDiffAt_const.sub (hce.comp (0, 0) (contDiffAt_const.mul hx_p))
  exact hmsq.mul ((hnum.div hden virExpDen_zero_ne).pow 2)

lemma virMGeo_zero_zero : virMGeo 0 0 = 1 := by
  unfold virMGeo
  rw [virMSq_zero_zero, Complex.one_cpow, virV_zero_zero, virEdgeFC_zero, virXPrime_zero,
    div_self (by simpa [virXPrime_zero] using virExpDen_zero_ne), one_pow, mul_one]

lemma virMGeo_neg : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), virMGeo (-p.1) p.2 = virMGeo p.1 p.2 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp contDiffAt2_virV
  filter_upwards [Metric.ball_mem_nhds ((0 : ℂ), (0 : ℂ)) hr] with p hp
  have hneg_ball : (-p.1, p.2) ∈ ball ((0 : ℂ), (0 : ℂ)) r := by
    rw [Metric.mem_ball] at hp ⊢
    simpa [Prod.dist_eq, dist_zero_right] using hp
  have hd_eq : deriv (fun σ => virV σ p.2) (-p.1) = deriv (fun σ => virV σ p.2) p.1 := by
    have hd_pos : DifferentiableAt ℂ (fun σ => virV σ p.2) p.1 :=
      (contDiffAt2_virV_slice (hball p hp)).differentiableAt (by simp)
    have hcomp : (fun σ => virV (-σ) p.2) = fun σ => -virV σ p.2 := by ext σ; exact virV_neg σ p.2
    have hl : HasDerivAt (fun σ => virV (-σ) p.2) (deriv (fun σ => virV σ p.2) (-p.1) * (-1)) p.1 := by
      have hd_neg : DifferentiableAt ℂ (fun σ => virV σ p.2) (-p.1) :=
        (contDiffAt2_virV_slice (hball (-p.1, p.2) hneg_ball)).differentiableAt (by simp)
      exact hd_neg.hasDerivAt.comp p.1 (hasDerivAt_neg p.1)
    have hr_d : HasDerivAt (fun σ => -virV σ p.2) (-(deriv (fun σ => virV σ p.2) p.1)) p.1 :=
      hd_pos.hasDerivAt.neg
    rw [hcomp] at hl
    have he := hl.unique hr_d
    linear_combination -he
  unfold virMGeo virMSq
  rw [virV_neg, virEdgeG'_neg, neg_sq, hd_eq, virEdgeFC_neg]

lemma virMGeo_conj : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
    virMGeo (starRingEnd ℂ p.1) (starRingEnd ℂ p.2) = starRingEnd ℂ (virMGeo p.1 p.2) := by
  have hmsq_slit : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), virMSq p.1 p.2 ∈ Complex.slitPlane := by
    have hc := contDiffAt_virMSq.continuousAt
    have h1 : virMSq 0 0 ∈ Complex.slitPlane := by rw [virMSq_zero_zero]; exact Complex.one_mem_slitPlane
    exact hc.eventually (Complex.isOpen_slitPlane.mem_nhds h1)
  have hv_strip : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), |(virV p.1 p.2).im| < 1 / 2 := by
    have hc : ContinuousAt (fun p : ℂ × ℂ => |(virV p.1 p.2).im|) (0, 0) :=
      continuous_abs.continuousAt.comp (Complex.continuous_im.continuousAt.comp contDiffAt_virV.continuousAt)
    exact hc.eventually (isOpen_Iio.mem_nhds (by simp [virV_zero_zero]))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (virV_conj.and contDiffAt2_virV)
  have hv_pair : Tendsto (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (((continuous_fst.pow 2).prodMk continuous_snd).continuousAt (x := ((0 : ℂ), (0 : ℂ)))).tendsto.trans
      (by simp)
  have hderiv_conj : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      deriv (fun σ => virV σ (starRingEnd ℂ p.2)) (starRingEnd ℂ p.1) =
        starRingEnd ℂ (deriv (fun σ => virV σ p.2) p.1) := by
    filter_upwards [Metric.ball_mem_nhds ((0 : ℂ), (0 : ℂ)) hr] with p hp
    have hd : HasDerivAt (fun σ => virV σ p.2) (deriv (fun σ => virV σ p.2) p.1) p.1 :=
      ((contDiffAt2_virV_slice (hball p hp).2).differentiableAt (by simp)).hasDerivAt
    have hs_mem : (starRingEnd ℂ p.1) ∈ {σ : ℂ | (starRingEnd ℂ σ, p.2) ∈ ball ((0 : ℂ), (0 : ℂ)) r} := by
      simpa only [Set.mem_ofPred_eq, Complex.conj_conj] using hp
    have hev : (fun σ => starRingEnd ℂ (virV (starRingEnd ℂ σ) p.2)) =ᶠ[𝓝 (starRingEnd ℂ p.1)]
        fun σ => virV σ (starRingEnd ℂ p.2) := by
      have h_isOpen : IsOpen {σ : ℂ | (starRingEnd ℂ σ, p.2) ∈ ball ((0 : ℂ), (0 : ℂ)) r} :=
        isOpen_ball.preimage (Complex.continuous_conj.prodMk continuous_const)
      have hn_mem : {σ : ℂ | (starRingEnd ℂ σ, p.2) ∈ ball ((0 : ℂ), (0 : ℂ)) r} ∈ 𝓝 (starRingEnd ℂ p.1) :=
        h_isOpen.mem_nhds hs_mem
      filter_upwards [hn_mem] with σ hσ
      have hc := (hball (starRingEnd ℂ σ, p.2) hσ).1
      dsimp only at hc
      rw [← hc, Complex.conj_conj]
    rw [← hev.deriv_eq]
    exact (hasDerivAt_conj_conj hd).deriv
  have hsnd : Tendsto (fun p : ℂ × ℂ => p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 (0 : ℂ)) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [hmsq_slit, hv_strip, virV_conj, hderiv_conj, hsnd.eventually virXPrime_conj,
    hv_pair.eventually virU_conj] with p hmsq hv_st hv_c hd_c hx_c hu_c
  have hU_eq : virU ((starRingEnd ℂ p.1) ^ 2) (starRingEnd ℂ p.2) =
      starRingEnd ℂ (virU (p.1 ^ 2) p.2) := by
    have h1 := hu_c
    simp only [map_pow] at h1
    exact h1
  have hmsq_c : virMSq (starRingEnd ℂ p.1) (starRingEnd ℂ p.2) = starRingEnd ℂ (virMSq p.1 p.2) := by
    unfold virMSq
    rw [hv_c, virEdgeG'_conj hv_st, hU_eq, hd_c, map_mul, map_mul, map_mul, map_pow, Complex.conj_ofReal]
  have hsqrt_c : (virMSq (starRingEnd ℂ p.1) (starRingEnd ℂ p.2)) ^ (1 / 2 : ℂ) =
      starRingEnd ℂ ((virMSq p.1 p.2) ^ (1 / 2 : ℂ)) := by
    have hc := Complex.cpow_conj (virMSq p.1 p.2) (1 / 2 : ℂ) (Complex.mem_slitPlane_iff_arg.mp hmsq).1
    have h12 : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [map_div₀, map_one, map_ofNat]
    rw [h12] at hc
    rw [hmsq_c, hc, Complex.conj_conj]
  have hedge_c : virEdgeFC (virV (starRingEnd ℂ p.1) (starRingEnd ℂ p.2)) =
      starRingEnd ℂ (virEdgeFC (virV p.1 p.2)) := by
    rw [hv_c, virEdgeFC_conj hv_st]
  have hexp_conj (w : ℂ) : Complex.exp (-(4 * π : ℂ) * starRingEnd ℂ w) =
      starRingEnd ℂ (Complex.exp (-(4 * π : ℂ) * w)) := by
    have h4pi : -(4 * π : ℂ) * starRingEnd ℂ w = starRingEnd ℂ (-(4 * π : ℂ) * w) := by
      simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal]
    rw [h4pi, Complex.exp_conj]
  unfold virMGeo
  rw [hsqrt_c, hedge_c, hx_c, hexp_conj, hexp_conj]
  simp only [map_mul, map_div₀, map_sub, map_one, map_pow]

lemma virMGeo_saddle_one : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < 0 →
    virMGeo (√(-a) : ℂ) (a : ℂ) = 1 ∧ virMGeo (-(√(-a) : ℂ)) (a : ℂ) = 1 := by
  have hts : Tendsto (fun a : ℝ => (√(max (-a) 0) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous fun a : ℝ => (√(max (-a) 0) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_neg.max continuous_const).sqrt)
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hta : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
  have hpair : Tendsto (fun a : ℝ => ((√(max (-a) 0) : ℂ), (a : ℂ))) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    hts.prodMk_nhds hta
  obtain ⟨r1, hr1, h1⟩ := Metric.eventually_nhds_iff_ball.mp (virV_conj.and contDiffAt2_virV)
  obtain ⟨r1', hr1', h1'⟩ := Metric.eventually_nhds_iff_ball.mp
    ((contDiffAt_virDerivS.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞')).eventually (by simp : (1 : WithTop ℕ∞) ≠ ∞'))
  obtain ⟨r2, hr2, h2⟩ := Metric.eventually_nhds_iff_ball.mp virPhiDualC_virV_eq
  obtain ⟨r3, hr3, h3⟩ := Metric.eventually_nhds_iff_ball.mp virXPrime_conj
  let rM : ℝ := min (min r1 r1') r2
  have hrM : 0 < rM := lt_min (lt_min hr1 hr1') hr2
  have hball_virV : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), ((√(max (-a) 0) : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rM :=
    hpair.eventually (Metric.ball_mem_nhds (0, 0) hrM)
  filter_upwards [virV_saddle_real, hball_virV, hta.eventually (Metric.ball_mem_nhds 0 hr3),
    hpair.eventually virMGeo_neg] with a hsad hmem ha3 hneg ha0
  obtain ⟨hβ_pos, hV_val, hedge_val, _⟩ := hsad ha0
  have hx_im : (virXPrime (a : ℂ)).im = 0 := by
    have hc := h3 _ ha3
    rw [Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  set s0 : ℝ := √(-a) with hs0_def
  have hs0_pos : 0 < s0 := Real.sqrt_pos.mpr (neg_pos.mpr ha0)
  have hs0_max : max (-a) 0 = -a := max_eq_left (by linarith)
  have hpair_mem : ((s0 : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rM := by
    simpa [hs0_def, hs0_max] using hmem
  have hV_real_nhds : ∀ᶠ σ : ℝ in 𝓝 s0,
      ((σ : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rM := by
    have htsig : Tendsto (fun σ : ℝ => ((σ : ℂ), (a : ℂ))) (𝓝 s0) (𝓝 ((s0 : ℂ), (a : ℂ))) :=
      ((Complex.continuous_ofReal.prodMk continuous_const).continuousAt (x := s0)).tendsto
    exact htsig.eventually (isOpen_ball.mem_nhds hpair_mem)
  have hv_im : ∀ᶠ σ : ℝ in 𝓝 s0, (virV (σ : ℂ) (a : ℂ)).im = 0 := by
    filter_upwards [hV_real_nhds] with σ hσ
    have hc := (h1 _ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hσ)).1
    simp only [Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hV_cd_s0 : ∀ᶠ σ : ℝ in 𝓝 s0, ContDiffAt ℂ 2 (fun τ : ℂ => virV τ (a : ℂ)) (σ : ℂ) := by
    filter_upwards [hV_real_nhds] with σ hσ
    exact contDiffAt2_virV_slice (h1 _ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hσ)).2
  have hderiv_at_s0 : (4 * π / 3) * edgeF' (√(virBetaOfA (a : ℂ)).re) *
      ((deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)).re) ^ 2 = 2 * s0 := by
    let vReal : ℝ → ℝ := fun σ => (virV (σ : ℂ) (a : ℂ)).re
    let vReal' : ℝ → ℝ := fun σ => (deriv (fun τ : ℂ => virV τ (a : ℂ)) (σ : ℂ)).re
    have hcd_s0 : ContDiffAt ℂ 2 (fun τ : ℂ => virV τ (a : ℂ)) (s0 : ℂ) :=
      contDiffAt2_virV_slice (h1 _ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hpair_mem)).2
    have hv_hd : HasDerivAt vReal (vReal' s0) s0 := by
      have hd_r : HasDerivAt (fun σ : ℝ => virV (σ : ℂ) (a : ℂ))
          (deriv (fun τ : ℂ => virV τ (a : ℂ)) (s0 : ℂ)) s0 :=
        (hcd_s0.differentiableAt (by simp)).hasDerivAt.comp_ofReal
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s0 hd_r
    have hv'_diff : DifferentiableAt ℝ vReal' s0 := by
      have hcd_d : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => deriv (fun τ : ℂ => virV τ p.2) p.1) ((s0 : ℂ), (a : ℂ)) :=
        h1' _ (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hpair_mem)
      have hcd_d1 : ContDiffAt ℂ 1 (fun τ : ℂ => deriv (fun w : ℂ => virV w (a : ℂ)) τ) (s0 : ℂ) :=
        ContDiffAt.comp (g := fun p : ℂ × ℂ => deriv (fun w : ℂ => virV w p.2) p.1)
          (f := fun τ : ℂ => (τ, (a : ℂ))) (s0 : ℂ) hcd_d (contDiff_id.prodMk contDiff_const).contDiffAt
      have hd_r : HasDerivAt (fun σ : ℝ => deriv (fun w : ℂ => virV w (a : ℂ)) (σ : ℂ))
          (deriv (fun τ : ℂ => deriv (fun w : ℂ => virV w (a : ℂ)) τ) (s0 : ℂ)) s0 :=
        (hcd_d1.differentiableAt (by simp)).hasDerivAt.comp_ofReal
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s0 hd_r).differentiableAt
    have hV_s0 : vReal s0 = √(virBetaOfA (a : ℂ)).re := by
      dsimp [vReal]; rw [hV_val, Complex.ofReal_re]
    set x' : ℝ := (virXPrime (a : ℂ)).re
    have hx'_c : virXPrime (a : ℂ) = (x' : ℂ) := Complex.ext rfl hx_im
    have hedge_x' : edgeF (vReal s0) = x' := by
      rw [hV_s0, ← Complex.ofReal_re (edgeF _), ← virEdgeFC_ofReal, hedge_val]
    have hlhs_hd : HasDerivAt (fun σ : ℝ => (4 * π / 3) * (edgeF (vReal σ) - x') * vReal' σ)
        (((4 * π / 3) * edgeF' (vReal s0) * vReal' s0) * vReal' s0 +
          ((4 * π / 3) * (edgeF (vReal s0) - x')) * deriv vReal' s0) s0 := by
      have hf1 : HasDerivAt (fun σ : ℝ => (4 * π / 3) * (edgeF (vReal σ) - x'))
          ((4 * π / 3) * edgeF' (vReal s0) * vReal' s0) s0 := by
        have he := (hasDerivAt_edgeF (vReal s0)).comp s0 hv_hd
        simpa [mul_assoc] using (he.sub_const x').const_mul (4 * π / 3)
      exact hf1.mul hv'_diff.hasDerivAt
    have hcont_edgeF : Continuous edgeF := continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgeF u).continuousAt
    have hphi_eq : (fun σ : ℝ => (4 * π / 3) * (edgeF (vReal σ) - x') * vReal' σ) =ᶠ[𝓝 s0]
        fun σ : ℝ => a + σ ^ 2 := by
      filter_upwards [hV_real_nhds, hV_cd_s0] with σ hσ hcd
      have hphi_nhds : (fun τ : ℝ => phiDual (vReal τ) x') =ᶠ[𝓝 σ] fun τ : ℝ => a * τ + τ ^ 3 / 3 := by
        have hnh : ∀ᶠ τ : ℝ in 𝓝 σ, ((τ : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rM := by
          have htsig : Tendsto (fun τ : ℝ => ((τ : ℂ), (a : ℂ))) (𝓝 σ) (𝓝 ((σ : ℂ), (a : ℂ))) :=
            ((Complex.continuous_ofReal.prodMk continuous_const).continuousAt (x := σ)).tendsto
          exact htsig.eventually (isOpen_ball.mem_nhds hσ)
        filter_upwards [hnh] with τ hτ
        have hτ_im : (virV (τ : ℂ) (a : ℂ)).im = 0 := by
          have hc := (h1 _ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hτ)).1
          simp only [Complex.conj_ofReal] at hc
          exact Complex.conj_eq_iff_im.mp hc.symm
        have hVτ_c : virV (τ : ℂ) (a : ℂ) = ((vReal τ : ℝ) : ℂ) := Complex.ext rfl hτ_im
        have hp := h2 _ (ball_subset_ball (min_le_right _ _) hτ)
        dsimp only at hp
        rw [hVτ_c, hx'_c, virPhiDualC_ofReal] at hp
        have hre := congrArg Complex.re hp
        simp only [Complex.ofReal_re] at hre
        have h1_re : ((a : ℂ) * (τ : ℂ) + (τ : ℂ) ^ 3 / 3).re = a * τ + τ ^ 3 / 3 := by
          norm_cast
        simpa [h1_re] using hre
      have hv_σ : HasDerivAt vReal (vReal' σ) σ :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ (hcd.differentiableAt (by simp)).hasDerivAt.comp_ofReal
      have hphi_deriv_σ : HasDerivAt (fun w : ℝ => phiDual w x') ((4 * π / 3) * (edgeF (vReal σ) - x')) (vReal σ) := by
        have hc : Continuous fun u : ℝ => edgeF u - x' := hcont_edgeF.sub continuous_const
        unfold phiDual
        have h_int : HasDerivAt (fun w : ℝ => ∫ u in (0 : ℝ)..w, (edgeF u - x')) (edgeF (vReal σ) - x') (vReal σ) :=
          intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (vReal σ))
            (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
        exact h_int.const_mul (4 * π / 3)
      have hd1 : HasDerivAt (fun τ : ℝ => phiDual (vReal τ) x') ((4 * π / 3) * (edgeF (vReal σ) - x') * vReal' σ) σ := by
        have hph := hphi_deriv_σ.comp σ hv_σ
        simpa [Function.comp_def, mul_assoc] using hph
      have hd2 : HasDerivAt (fun τ : ℝ => a * τ + τ ^ 3 / 3) (a + σ ^ 2) σ := by
        have hd_a : HasDerivAt (fun τ : ℝ => a * τ) a σ := by
          simpa using (hasDerivAt_id σ).const_mul a
        have hd_c : HasDerivAt (fun τ : ℝ => τ ^ 3 / 3) (σ ^ 2) σ := by
          have h3 := (hasDerivAt_pow 3 σ).div_const 3
          refine h3.congr_deriv ?_
          norm_num
        exact hd_a.add hd_c
      exact (hd1.congr_of_eventuallyEq hphi_nhds.symm).unique hd2
    have hrhs_hd : HasDerivAt (fun σ : ℝ => a + σ ^ 2) (2 * s0) s0 := by
      have h1_d := (hasDerivAt_const s0 a).add (hasDerivAt_pow 2 s0)
      exact h1_d.congr_deriv (by ring)
    have heq_d := (hlhs_hd.congr_of_eventuallyEq hphi_eq.symm).unique hrhs_hd
    rw [hedge_x', sub_self, mul_zero, zero_mul, add_zero, hV_s0] at heq_d
    linear_combination heq_d
  have hM_pos : virMGeo (s0 : ℂ) (a : ℂ) = 1 := by
    have hV_mul : virV (s0 : ℂ) (a : ℂ) = (s0 : ℂ) * virU ((s0 : ℂ) ^ 2) (a : ℂ) := virV_eq_mul_virU _ _
    have hG_mul : virV (s0 : ℂ) (a : ℂ) * virEdgeG' (virV (s0 : ℂ) (a : ℂ)) = virEdgeFC' (virV (s0 : ℂ) (a : ℂ)) :=
      virEdgeG'_mul _
    have hs0_ne : (s0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0_pos.ne'
    have hMSq_eq : virMSq (s0 : ℂ) (a : ℂ) = 1 := by
      unfold virMSq
      have h_eq_msq : ((2 * π / 3 : ℝ) : ℂ) * virEdgeG' (virV (s0 : ℂ) (a : ℂ)) * virU ((s0 : ℂ) ^ 2) (a : ℂ) *
          (deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)) ^ 2 =
          ((2 * π / 3 : ℝ) : ℂ) * virEdgeFC' (virV (s0 : ℂ) (a : ℂ)) / (s0 : ℂ) *
            (deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)) ^ 2 := by
        rw [← hG_mul, hV_mul]
        field_simp [hs0_ne]
      rw [h_eq_msq, hV_val, virEdgeFC'_ofReal]
      have hd_im : (deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)).im = 0 := by
        have hcd0 : ContDiffAt ℂ 2 (fun w : ℂ => virV w (a : ℂ)) (s0 : ℂ) :=
          contDiffAt2_virV_slice (h1 _ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hpair_mem)).2
        have him_hd : HasDerivAt (fun σ : ℝ => (virV (σ : ℂ) (a : ℂ)).im)
            (deriv (fun w : ℂ => virV w (a : ℂ)) (s0 : ℂ)).im s0 :=
          Complex.imCLM.hasFDerivAt.comp_hasDerivAt s0 (hcd0.differentiableAt (by simp)).hasDerivAt.comp_ofReal
        have him_zero : HasDerivAt (fun σ : ℝ => (virV (σ : ℂ) (a : ℂ)).im) 0 s0 :=
          (hasDerivAt_const s0 (0 : ℝ)).congr_of_eventuallyEq (hv_im.mono fun _ h => h)
        exact him_hd.unique him_zero
      have hd_c_eq : deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ) =
          (((deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hd_im
      rw [hd_c_eq]
      have hre_eq : (2 * π / 3) * edgeF' (√(virBetaOfA (a : ℂ)).re) / s0 *
          ((deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)).re) ^ 2 = 1 := by
        have hs0_r : s0 ≠ 0 := hs0_pos.ne'
        field_simp [hs0_r]
        linarith only [hderiv_at_s0]
      push_cast
      have : ((2 : ℂ) * ↑π / 3 * ↑(edgeF' √(virBetaOfA ↑a).re) / ↑s0 *
          ↑((deriv (fun σ => virV σ ↑a) ↑s0).re) ^ 2) =
          (((2 * π / 3) * edgeF' (√(virBetaOfA (a : ℂ)).re) / s0 *
            ((deriv (fun σ => virV σ (a : ℂ)) (s0 : ℂ)).re) ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, hre_eq, Complex.ofReal_one]
    have hden_ne : 1 - Complex.exp (-(4 * π : ℂ) * virXPrime (a : ℂ)) ≠ 0 := by
      have hx_gt : xiStar < (virXPrime (a : ℂ)).re := by
        rw [← hedge_val, virEdgeFC_ofReal, Complex.ofReal_re, ← edgeF_zero]
        exact edgeF_strictMonoOn le_rfl (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hβ_pos)
      have hx_c : virXPrime (a : ℂ) = (((virXPrime (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hx_im
      rw [hx_c, sub_ne_zero]
      intro h
      have hre := congrArg Complex.re h
      rw [show -(4 * π : ℂ) * (((virXPrime (a : ℂ)).re : ℝ) : ℂ) =
          (((-4 * π * (virXPrime (a : ℂ)).re : ℝ) : ℂ)) by push_cast; ring,
        ← Complex.ofReal_exp, Complex.ofReal_re, Complex.one_re] at hre
      have hneg' : -4 * π * (virXPrime (a : ℂ)).re < 0 := by
        have := Real.pi_pos; have := xiStar_pos; nlinarith
      linarith [Real.exp_lt_one_iff.mpr hneg']
    unfold virMGeo
    rw [hMSq_eq, Complex.one_cpow, one_mul, hV_val, hedge_val, div_self hden_ne, one_pow]
  refine ⟨hM_pos, ?_⟩
  have hneg' := hneg
  change virMGeo (-((√(max (-a) 0) : ℝ) : ℂ)) (a : ℂ) = virMGeo ((√(max (-a) 0) : ℝ) : ℂ) (a : ℂ) at hneg'
  rw [hs0_max] at hneg'
  rw [hneg', hM_pos]

lemma virMGeo_ofReal_pos : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), 0 < p.1 →
    0 < (virV (p.1 : ℂ) (p.2 : ℂ)).re ∧
    (virV (p.1 : ℂ) (p.2 : ℂ)).im = 0 ∧
    (virXPrime (p.2 : ℂ)).im = 0 ∧
    0 < (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).re ∧
    (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).im = 0 ∧
    virMGeo (p.1 : ℂ) (p.2 : ℂ) =
      (((√(2 * π / 3) * √(edgeF' (virV (p.1 : ℂ) (p.2 : ℂ)).re / p.1) *
        (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).re *
        ((1 - Real.exp (-4 * π * edgeF (virV (p.1 : ℂ) (p.2 : ℂ)).re)) /
          (1 - Real.exp (-4 * π * (virXPrime (p.2 : ℂ)).re))) ^ 2 : ℝ) : ℂ)) := by
  have hc_real : Tendsto (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    ((Complex.continuous_ofReal.comp continuous_fst).prodMk
      (Complex.continuous_ofReal.comp continuous_snd) |>.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).tendsto
  have hc_snd : Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ)) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (0 : ℂ)) :=
    ((Complex.continuous_ofReal.comp continuous_snd).continuousAt (x := ((0 : ℝ), (0 : ℝ)))).tendsto
  have hc_upair : Tendsto (fun p : ℝ × ℝ => (((p.1 : ℂ) ^ 2), (p.2 : ℂ))) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have hcont := ((Complex.continuous_ofReal.comp continuous_fst).pow 2).prodMk
      (Complex.continuous_ofReal.comp continuous_snd)
    simpa using (hcont.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).tendsto
  have hu_pos : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), 0 < (virU ((p.1 : ℂ) ^ 2) (p.2 : ℂ)).re := by
    have hc_re : ContinuousAt (fun q : ℂ × ℂ => (virU q.1 q.2).re) ((0 : ℂ), (0 : ℂ)) :=
      Complex.continuous_re.continuousAt.comp contDiffAt_virU.continuousAt
    have h0 : 0 < (virU (0 : ℂ) (0 : ℂ)).re := by
      rw [virU_zero_zero, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
      exact inv_pos.mpr virD0_pos
    exact hc_upair.eventually (hc_re.eventually (isOpen_Ioi.mem_nhds h0))
  have hd_pos : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), 0 < (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).re := by
    have hc_re : ContinuousAt (fun q : ℂ × ℂ => (deriv (fun σ => virV σ q.2) q.1).re) ((0 : ℂ), (0 : ℂ)) :=
      Complex.continuous_re.continuousAt.comp contDiffAt_virDerivS.continuousAt
    have h0 : 0 < (deriv (fun σ => virV σ (0 : ℂ)) (0 : ℂ)).re := by
      rw [virDerivS_zero_zero, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
      exact inv_pos.mpr virD0_pos
    exact hc_real.eventually (hc_re.eventually (isOpen_Ioi.mem_nhds h0))
  have hx_pos : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), 0 < (virXPrime (p.2 : ℂ)).re := by
    have hc_re : ContinuousAt (fun a : ℂ => (virXPrime a).re) (0 : ℂ) :=
      Complex.continuous_re.continuousAt.comp contDiffAt_virXPrime.continuousAt
    have h0 : 0 < (virXPrime (0 : ℂ)).re := by
      rw [virXPrime_zero, Complex.ofReal_re]; exact xiStar_pos
    exact hc_snd.eventually (hc_re.eventually (isOpen_Ioi.mem_nhds h0))
  obtain ⟨r1, hr1, h1⟩ := Metric.eventually_nhds_iff_ball.mp (virV_conj.and contDiffAt2_virV)
  have hv_ball : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ((p.1 : ℂ), (p.2 : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r1 :=
    hc_real.eventually (Metric.ball_mem_nhds (0, 0) hr1)
  filter_upwards [hv_ball, hc_real.eventually virV_conj, hc_snd.eventually virXPrime_conj,
    hu_pos, hd_pos, hx_pos] with p hp hvc hxc hup hdp hxp hs_pos
  have hv_im : (virV (p.1 : ℂ) (p.2 : ℂ)).im = 0 := by
    have hc := hvc
    simp only [Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hx_im : (virXPrime (p.2 : ℂ)).im = 0 := by
    have hc := hxc
    rw [Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hv_re_pos : 0 < (virV (p.1 : ℂ) (p.2 : ℂ)).re := by
    have hm : virV (p.1 : ℂ) (p.2 : ℂ) = (p.1 : ℂ) * virU ((p.1 : ℂ) ^ 2) (p.2 : ℂ) := virV_eq_mul_virU _ _
    rw [hm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hs_pos hup
  have hd_im : (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).im = 0 := by
    have hV_real_nhds : ∀ᶠ σ : ℝ in 𝓝 p.1, (virV (σ : ℂ) (p.2 : ℂ)).im = 0 := by
      have htsig : Tendsto (fun σ : ℝ => ((σ : ℂ), (p.2 : ℂ))) (𝓝 p.1) (𝓝 ((p.1 : ℂ), (p.2 : ℂ))) :=
        ((Complex.continuous_ofReal.prodMk continuous_const).continuousAt (x := p.1)).tendsto
      filter_upwards [htsig.eventually (isOpen_ball.mem_nhds hp)] with σ hσ
      have hc := (h1 ((σ : ℂ), (p.2 : ℂ)) hσ).1
      simp only [Complex.conj_ofReal] at hc
      exact Complex.conj_eq_iff_im.mp hc.symm
    have hcd0 : ContDiffAt ℂ 2 (fun w : ℂ => virV w (p.2 : ℂ)) (p.1 : ℂ) :=
      contDiffAt2_virV_slice (h1 _ hp).2
    have him_hd : HasDerivAt (fun σ : ℝ => (virV (σ : ℂ) (p.2 : ℂ)).im)
        (deriv (fun w : ℂ => virV w (p.2 : ℂ)) (p.1 : ℂ)).im p.1 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt p.1 (hcd0.differentiableAt (by simp)).hasDerivAt.comp_ofReal
    have him_zero : HasDerivAt (fun σ : ℝ => (virV (σ : ℂ) (p.2 : ℂ)).im) 0 p.1 :=
      (hasDerivAt_const p.1 (0 : ℝ)).congr_of_eventuallyEq (hV_real_nhds.mono fun _ h => h)
    exact him_hd.unique him_zero
  refine ⟨hv_re_pos, hv_im, hx_im, hdp, hd_im, ?_⟩
  set v : ℝ := (virV (p.1 : ℂ) (p.2 : ℂ)).re
  set x' : ℝ := (virXPrime (p.2 : ℂ)).re
  set d : ℝ := (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)).re
  have hv_c : virV (p.1 : ℂ) (p.2 : ℂ) = (v : ℂ) := Complex.ext rfl hv_im
  have hx_c : virXPrime (p.2 : ℂ) = (x' : ℂ) := Complex.ext rfl hx_im
  have hd_c : deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ) = (d : ℂ) := Complex.ext rfl hd_im
  have hp1_ne : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
  have hmsq_val : virMSq (p.1 : ℂ) (p.2 : ℂ) =
      (((2 * π / 3) * (edgeF' v / p.1) * d ^ 2 : ℝ) : ℂ) := by
    unfold virMSq
    have h_eq : ((2 * π / 3 : ℝ) : ℂ) * virEdgeG' (virV (p.1 : ℂ) (p.2 : ℂ)) * virU ((p.1 : ℂ) ^ 2) (p.2 : ℂ) *
        (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)) ^ 2 =
        ((2 * π / 3 : ℝ) : ℂ) * virEdgeFC' (virV (p.1 : ℂ) (p.2 : ℂ)) / (p.1 : ℂ) *
          (deriv (fun σ => virV σ (p.2 : ℂ)) (p.1 : ℂ)) ^ 2 := by
      have hG := virEdgeG'_mul (virV (p.1 : ℂ) (p.2 : ℂ))
      have hV := virV_eq_mul_virU (p.1 : ℂ) (p.2 : ℂ)
      rw [← hG, hV]; field_simp [hp1_ne]
    rw [h_eq, hv_c, virEdgeFC'_ofReal, hd_c]
    push_cast; ring
  have hedge'_pos : 0 < edgeF' v := edgeF'_pos hv_re_pos
  have hmsq_r_pos : 0 < (2 * π / 3) * (edgeF' v / p.1) * d ^ 2 := by
    have := Real.pi_pos; positivity
  have hsqrt_c : (virMSq (p.1 : ℂ) (p.2 : ℂ)) ^ (1 / 2 : ℂ) =
      (((√(2 * π / 3) * √(edgeF' v / p.1) * d : ℝ)) : ℂ) := by
    rw [hmsq_val, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hmsq_r_pos.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by have := Real.pi_pos; positivity),
      Real.sqrt_mul (by have := Real.pi_pos; positivity), Real.sqrt_sq hdp.le]
  unfold virMGeo
  rw [hsqrt_c, hv_c, hx_c, virEdgeFC_ofReal,
    show -(4 * π : ℂ) * (edgeF v : ℂ) = ((-4 * π * edgeF v : ℝ) : ℂ) by push_cast; ring,
    show -(4 * π : ℂ) * (x' : ℂ) = ((-4 * π * x' : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast; rfl

end

end FormalResearch.ModularBootstrap.FiveTerm

