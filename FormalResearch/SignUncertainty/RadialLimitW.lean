module

public import FormalResearch.SignUncertainty.MontelHol
public import FormalResearch.SignUncertainty.RadialXiRepr
public import FormalResearch.SignUncertainty.RadialDomination

/-!
# The limit `W` of `W_{c_k}` (`lem:radial-compactness`, Step 3)

Montel's theorem applied to `W_{c_n}` (holomorphic on `0 < Re w`, `ε_c Re w < 1`, bounded by `4 M₀` on the rectangles
`montelO j` once `c_n` is large): a subsequence converges locally uniformly on `{Re w > 0}` to a holomorphic `W` with
`‖W‖ ≤ M₀` (`exists_radialW_limit`).
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma montelO_subset {j : ℕ} {w : ℂ} (hw : w ∈ montelO j) : 0 < w.re ∧ w.re < (j : ℝ) + 2 ∧ ‖w‖ < 2 * ((j : ℝ) + 2) := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hpos : 0 < 1 / (4 * ((j : ℝ) + 1)) := by positivity
  refine ⟨by linarith, h2, ?_⟩
  have := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_pos (by linarith : 0 < w.re)] at this
  linarith

theorem exists_radialW_limit {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ n, IsHankelEigenfn (c n) ε (f n))
    (hM : ∀ n, hankelMass (c n) (f n) ≤ M₀) (hM0 : 0 ≤ M₀) :
    ∃ (ms : ℕ → ℕ) (W : ℂ → ℂ), StrictMono ms ∧ DifferentiableOn ℂ W {w : ℂ | 0 < w.re} ∧
      (∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀) ∧
      TendstoLocallyUniformlyOn (fun k => radialW (c (ms k)) (f (ms k))) W atTop {w : ℂ | 0 < w.re} := by
  have hεc : Tendsto (fun n => radialEps (c n)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  -- eventual smallness
  have hev : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, 1000 ≤ c n ∧ radialEps (c n) * R ≤ 1 / 2 := by
    intro R
    have h1 := hc.eventually_ge_atTop 1000
    have h2 : Tendsto (fun n => radialEps (c n) * R) atTop (𝓝 0) := by simpa using hεc.mul_const R
    exact eventually_atTop.mp (h1.and (h2.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))))
  have hdom : ∀ j : ℕ, ∀ n, 1000 ≤ c n → radialEps (c n) * ((j : ℝ) + 2) ≤ 1 / 2 →
      montelO j ⊆ {w : ℂ | 0 < w.re ∧ radialEps (c n) * w.re < 1} := by
    intro j n hcn he w hw
    obtain ⟨h0, h1, -⟩ := montelO_subset hw
    have he0 := radialEps_pos (by linarith : 0 < c n)
    exact ⟨h0, by nlinarith⟩
  have hd : ∀ j : ℕ, ∃ N, ∀ n ≥ N, DifferentiableOn ℂ (radialW (c n) (f n)) (montelO j) := by
    intro j
    obtain ⟨N, hN⟩ := hev ((j : ℝ) + 2)
    exact ⟨N, fun n hn => (radialW_differentiableOn (by linarith [(hN n hn).1]) (hf n)).mono
      (hdom j n (hN n hn).1 (hN n hn).2)⟩
  have hb : ∀ j : ℕ, ∃ B : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ montelO j, ‖radialW (c n) (f n) w‖ ≤ B := by
    intro j
    obtain ⟨N, hN⟩ := hev ((j : ℝ) + 2)
    refine ⟨4 * M₀, N, fun n hn w hw => ?_⟩
    obtain ⟨hc1, he⟩ := hN n hn
    obtain ⟨h0, h1, h2⟩ := montelO_subset hw
    have he0 := radialEps_pos (by linarith : 0 < c n)
    have hw1 : radialEps (c n) * w.re < 1 := by nlinarith
    have hb := radialW_norm_le (by linarith : 3 / 2 < c n) (hf n) hε h0.le hw1
    refine hb.trans ?_
    have hmass0 : 0 ≤ hankelMass (c n) (f n) := hankelMass_nonneg (by linarith) _
    have hn1 : ‖1 + (radialEps (c n) : ℂ) * w‖ ≤ 2 := by
      calc _ ≤ ‖(1 : ℂ)‖ + ‖(radialEps (c n) : ℂ) * w‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg he0.le]
          have : radialEps (c n) * ‖w‖ ≤ 1 := by nlinarith
          linarith
        _ = 2 := by norm_num
    have hr : ‖1 + (radialEps (c n) : ℂ) * w‖ ^ (1 / 2 : ℝ) ≤ 2 := by
      calc _ ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by gcongr
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    have hex : Real.exp (1 / (6 * c n)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    calc hankelMass (c n) (f n) * ‖1 + (radialEps (c n) : ℂ) * w‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c n))
        ≤ M₀ * 2 * (11 / 10) := by gcongr; exact hM n
      _ ≤ 4 * M₀ := by linarith
  obtain ⟨φ, G, hφ, hLU⟩ := montel_rightHalfPlane (fun n => radialW (c n) (f n)) hd hb
  have hdiffG : DifferentiableOn ℂ G {w : ℂ | 0 < w.re} := by
    intro w hw
    obtain ⟨j, hj⟩ := exists_montelK_superset (isCompact_singleton (x := w)) (by simpa using hw)
    have hwO : w ∈ montelO j := montelK_subset_montelO j (hj rfl)
    have hOj : DifferentiableOn ℂ G (montelO j) := by
      obtain ⟨N, hN⟩ := hd j
      refine (hLU.mono ?_).differentiableOn ?_ (isOpen_montelO j)
      · intro z hz; exact (montelO_subset hz).1
      · filter_upwards [eventually_ge_atTop N] with k hk
        exact hN _ (hk.trans (hφ.id_le k))
    exact (hOj.differentiableAt ((isOpen_montelO j).mem_nhds hwO)).differentiableWithinAt
  refine ⟨φ, G, hφ, hdiffG, ?_, hLU⟩
  intro w hw
  have ht := hLU.tendsto_at hw
  have hφc : Tendsto (fun k => c (φ k)) atTop atTop := hc.comp hφ.tendsto_atTop
  have hφe : Tendsto (fun k => radialEps (c (φ k))) atTop (𝓝 0) := radialEps_tendsto.comp hφc
  have hlim : Tendsto (fun k => M₀ * ‖1 + (radialEps (c (φ k)) : ℂ) * w‖ ^ (1 / 2 : ℝ) *
      Real.exp (1 / (6 * c (φ k)))) atTop (𝓝 (M₀ * 1 * 1)) := by
    have h1 : Tendsto (fun k => ‖1 + (radialEps (c (φ k)) : ℂ) * w‖ ^ (1 / 2 : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun k => 1 + (radialEps (c (φ k)) : ℂ) * w) atTop (𝓝 1) := by
        have : Tendsto (fun k => (radialEps (c (φ k)) : ℂ)) atTop (𝓝 0) := by
          simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hφe
        simpa using tendsto_const_nhds.add (this.mul_const w)
      have hcn : Continuous fun x : ℂ => ‖x‖ ^ (1 / 2 : ℝ) :=
        continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))
      simpa [Function.comp_def] using (hcn.tendsto 1).comp h0
    have h2 : Tendsto (fun k => Real.exp (1 / (6 * c (φ k)))) atTop (𝓝 1) := by
      have : Tendsto (fun k => 1 / (6 * c (φ k))) atTop (𝓝 0) := by
        have h6 : Tendsto (fun k => 6 * c (φ k)) atTop atTop := hφc.const_mul_atTop (by norm_num)
        simp only [one_div]; exact h6.inv_tendsto_atTop
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp this
    exact (tendsto_const_nhds.mul h1).mul h2
  have hle : ∀ᶠ k in atTop, ‖radialW (c (φ k)) (f (φ k)) w‖ ≤ M₀ * ‖1 + (radialEps (c (φ k)) : ℂ) * w‖ ^ (1 / 2 : ℝ) *
      Real.exp (1 / (6 * c (φ k))) := by
    have hw1 : ∀ᶠ k in atTop, radialEps (c (φ k)) * w.re < 1 := by
      have : Tendsto (fun k => radialEps (c (φ k)) * w.re) atTop (𝓝 (0 * w.re)) := hφe.mul_const _
      simp only [zero_mul] at this
      exact this.eventually (Iio_mem_nhds one_pos)
    filter_upwards [hw1, hφc.eventually_ge_atTop 1000] with k hk hck
    refine (radialW_norm_le (by linarith) (hf _) hε hw.le hk).trans ?_
    have := hM (φ k)
    gcongr
  have := le_of_tendsto_of_tendsto ht.norm hlim hle
  simpa using this

/-- info: 'FormalResearch.SignUncertainty.exists_radialW_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_radialW_limit

end FormalResearch.SignUncertainty
