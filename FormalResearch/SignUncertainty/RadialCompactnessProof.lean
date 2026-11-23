module

public import FormalResearch.SignUncertainty.RadialProfileFatou
public import FormalResearch.SignUncertainty.RadialCompactness

/-!
# Proof of `profile_compactness` (`lem:radial-compactness`, Steps 3-4)

Assembles the pieces: a subsequence with `W_{c_k} → W` locally uniformly (`exists_radialW_limit`), the
limit `F = radialF W` (entire, real on `ℝ`, Airy class), the window identification
`Ψ_{f,c} = Ψ̃_{f,c}` and the locally uniform convergence of profiles and derivatives, `C¹` on windows,
and Fatou for the `L¹` clause. `radial_compactness : RadialCompactness`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma window_lemma {c ε R : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1)
    (hk : Real.pi ^ 2 * radialEps c ^ 2 * (|R| / hankelBeta1 + 1) ≤ 1 / 2) :
    (∀ y ∈ Ioo (-R) R, hankelWindowProfile c f y = profTilde c f y) ∧
    (∀ y ∈ Ioo (-R) R, HasDerivAt (profTilde c f) (profTildeD c f y) y) ∧
    (∀ y ∈ Ioo (-R) R, ContinuousAt (profTildeD c f) y) := by
  have hβ := hankelBeta1_pos
  have hc0 : 0 < c := by linarith
  have hpe : 0 ≤ Real.pi ^ 2 * radialEps c ^ 2 := by positivity
  have hy : ∀ y ∈ Ioo (-R) R, |y| ≤ |R| := fun y hy =>
    (abs_le.mpr ⟨by linarith [hy.1, le_abs_self R, neg_le_abs R], by linarith [hy.2, le_abs_self R]⟩)
  have hS2 : ∀ y ∈ Ioo (-R) R, Real.pi ^ 2 * radialEps c ^ 2 * (|-y / hankelBeta1| + 1) ≤ 1 / 2 := by
    intro y hyy
    refine le_trans ?_ hk
    gcongr
    rw [abs_div, abs_neg, abs_of_pos hβ]
    exact div_le_div_of_nonneg_right (hy y hyy) hβ.le
  refine ⟨fun y hyy => ?_, fun y hyy => hasDerivAt_profTilde hc hf hε (hS2 y hyy),
    fun y hyy => continuousAt_profTildeD hc hf hε (hS2 y hyy)⟩
  refine profile_eq_tilde (by linarith) hf hε ?_
  refine window_xi_pos hc0 (R := |R|) (hy y hyy) ?_
  refine le_trans ?_ hk
  gcongr
  linarith

lemma contDiffOn_window {c ε R : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1)
    (hk : Real.pi ^ 2 * radialEps c ^ 2 * (|R| / hankelBeta1 + 1) ≤ 1 / 2) :
    ContDiffOn ℝ 1 (hankelWindowProfile c f) (Ioo (-R) R) := by
  obtain ⟨h1, h2, h3⟩ := window_lemma hc hf hε hk
  refine ContDiffOn.congr ?_ h1
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun y hy => (h2 y hy).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  refine ContinuousOn.congr (f := profTildeD c f) (fun y hy => (h3 y hy).continuousWithinAt) ?_
  intro y hy
  exact (h2 y hy).deriv

/-- **`profile_compactness`** (`lem:radial-compactness`): see `RadialCompactness`. -/
theorem profile_compactness_thm (M₀ ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hc : Tendsto c atTop atTop) (hf : ∀ n, IsHankelEigenfn (c n) ε (f n))
    (hM : ∀ n, hankelMass (c n) (f n) ≤ M₀) :
    ∃ (ms : ℕ → ℕ) (F : ℂ → ℂ) (C ν : ℝ),
      StrictMono ms ∧
      TendstoLocallyUniformlyOn (fun k u => hankelWindowProfile (c (ms k)) (f (ms k)) u)
        (fun u : ℝ => (F (u : ℂ)).re) atTop univ ∧
      (∀ R : ℝ, ∀ᶠ k in atTop,
        ContDiffOn ℝ 1 (hankelWindowProfile (c (ms k)) (f (ms k))) (Ioo (-R) R)) ∧
      TendstoLocallyUniformlyOn (fun k u => deriv (hankelWindowProfile (c (ms k)) (f (ms k))) u)
        (fun u : ℝ => deriv (fun x : ℝ => (F (x : ℂ)).re) u) atTop univ ∧
      Differentiable ℂ F ∧
      Integrable (fun u : ℝ => F (u : ℂ)) ∧
      0 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) ∧
      (∀ u : ℝ, (F (u : ℂ)).im = 0) := by
  have hβ := hankelBeta1_pos
  have hM0 : 0 ≤ M₀ := by
    obtain ⟨n, hn⟩ := (hc.eventually_gt_atTop 0).exists
    exact (hankelMass_nonneg hn _).trans (hM n)
  obtain ⟨ms, W, hms, hWd, hWb, hWl⟩ := exists_radialW_limit hε hc hf hM hM0
  have hc' : Tendsto (fun k => c (ms k)) atTop atTop := hc.comp hms.tendsto_atTop
  have hf' : ∀ k, IsHankelEigenfn (c (ms k)) ε (f (ms k)) := fun k => hf _
  have hM' : ∀ k, hankelMass (c (ms k)) (f (ms k)) ≤ M₀ := fun k => hM _
  have hWp : ∀ w : ℂ, 0 < w.re →
      Tendsto (fun k => radialW (c (ms k)) (f (ms k)) w) atTop (𝓝 (W w)) :=
    fun w hw => hWl.tendsto_at hw
  obtain ⟨C, hC0, hCb⟩ := radialF_airy_bound hWb hWd
  have hlim_eq : (fun u : ℝ => (radialF W (u : ℂ)).re) =
      fun u : ℝ => hankelBeta1⁻¹ * (XiL W ((-u / hankelBeta1 : ℝ) : ℂ)).re := funext (radialF_re W)
  have hin : ∀ x : ℝ, ∀ y ∈ Ioo (x - 1) (x + 1), y ∈ Ioo (-(|x| + 1)) (|x| + 1) := by
    intro x y hy
    exact ⟨by linarith [hy.1, neg_abs_le x], by linarith [hy.2, le_abs_self x]⟩
  have h1 : TendstoLocallyUniformlyOn (fun k u => hankelWindowProfile (c (ms k)) (f (ms k)) u)
      (fun u : ℝ => (radialF W (u : ℂ)).re) atTop univ := by
    rw [tendstoLocallyUniformlyOn_univ, hlim_eq]
    refine tlu_congr_eventually (profTilde_tlu hε hc' hf' hM' hWp) fun x => ⟨Ioo (x - 1) (x + 1),
      Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    filter_upwards [eventually_good hc' (|(|x| + 1)| / hankelBeta1 + 1)] with k hk y hy
    exact (window_lemma hk.1 (hf' k) hε hk.2).1 y (hin x y hy)
  have h2 : ∀ R : ℝ, ∀ᶠ k in atTop,
      ContDiffOn ℝ 1 (hankelWindowProfile (c (ms k)) (f (ms k))) (Ioo (-R) R) := by
    intro R
    filter_upwards [eventually_good hc' (|R| / hankelBeta1 + 1)] with k hk
    exact contDiffOn_window hk.1 (hf' k) hε hk.2
  have hder : ∀ u : ℝ, deriv (fun x : ℝ => (radialF W (x : ℂ)).re) u =
      -(hankelBeta1⁻¹ * hankelBeta1⁻¹) * (∫ v : ℝ, radialdAlim W (-u / hankelBeta1) v).re := by
    intro u
    rw [hlim_eq]
    exact (hasDerivAt_phi hε hc' hf' hM' hWp u).deriv
  have h3 : TendstoLocallyUniformlyOn
      (fun k u => deriv (hankelWindowProfile (c (ms k)) (f (ms k))) u)
      (fun u : ℝ => deriv (fun x : ℝ => (radialF W (x : ℂ)).re) u) atTop univ := by
    rw [tendstoLocallyUniformlyOn_univ, funext hder]
    refine tlu_congr_eventually (profTildeD_tlu hε hc' hf' hM' hWp) fun x => ⟨Ioo (x - 1) (x + 1),
      Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    filter_upwards [eventually_good hc' (|(|x| + 1)| / hankelBeta1 + 1)] with k hk y hy
    obtain ⟨e1, e2, -⟩ := window_lemma hk.1 (hf' k) hε hk.2
    have hyw := hin x y hy
    have hev : hankelWindowProfile (c (ms k)) (f (ms k)) =ᶠ[𝓝 y] profTilde (c (ms k)) (f (ms k)) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hyw) (fun z hz => e1 z hz)
    exact ((e2 y hyw).congr_of_eventuallyEq hev).deriv
  have hdiff : Differentiable ℂ (radialF W) := by
    unfold radialF
    exact (differentiable_const _).mul ((differentiable_XiL hWb hWd).comp (by fun_prop))
  have him : ∀ u : ℝ, (radialF W (u : ℂ)).im = 0 := by
    intro u
    rw [radialF_ofReal, Complex.im_ofReal_mul, XiL_im_eq_zero hε hc' hf' hM' hWp, mul_zero]
  have hint : Integrable (fun u : ℝ => radialF W (u : ℂ)) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hc'.eventually_gt_atTop 0)
    have hcont : Continuous fun u : ℝ => (radialF W (u : ℂ)).re :=
      Complex.continuous_re.comp (hdiff.continuous.comp Complex.continuous_ofReal)
    have hI : Integrable (fun u : ℝ => (radialF W (u : ℂ)).re) := by
      refine integrable_of_fatou (Ψ := fun k => hankelWindowProfile (c (ms (k + N))) (f (ms (k + N))))
        (M := M₀) (fun k => ?_) (fun k => ?_) (fun u => ?_) hcont.aestronglyMeasurable
      · exact (integrable_hankelWindowProfile_iff (hN (k + N) (by omega)) _).mpr (hf' _).int
      · rw [integral_abs_hankelWindowProfile (hN (k + N) (by omega))]
        exact hM' _
      · exact ((h1.tendsto_at (mem_univ u)).comp (tendsto_add_atTop_nat N))
    refine (hI.ofReal (𝕜 := ℂ)).congr (Eventually.of_forall fun u => ?_)
    exact (Complex.ext (by simp) (by simp [him u])).symm
  refine ⟨ms, radialF W, C, 1 / 2, hms, h1, h2, ?_, hdiff, hint, hC0, hCb, him⟩
  exact h3

/-- `lem:radial-compactness` for the concrete Hankel problem (`RadialCompactness`), proved. -/
theorem radial_compactness : RadialCompactness := ⟨profile_compactness_thm⟩

end FormalResearch.SignUncertainty
