module

public import FormalResearch.SignUncertainty.StripGExpansion
public import FormalResearch.SignUncertainty.RadialCompactnessKernel
public import FormalResearch.Asymptotics.BinetRemainder

/-!
# The rescaled kernel and its pointwise limit (`lem:radial-compactness`, Step 3)

`radialK c w s = K₀(ε_c w, ξ_c(s))`, `ε_c = c^{-1/3}`, `ξ_c(s) = 1/π² + ε_c² s`, tends to
`exp(π² w³/36 + π² s w)` as `c → ∞`, `s → s₀` (`radialK_tendsto`), for every `w ∈ ℂ`.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The rescaled kernel `K_c(w, s) = K₀(ε_c w, ξ_c(s))`. -/
noncomputable def radialK (c : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  mellinK0 c ((radialEps c : ℂ) * w) (radialXi c s)

/-- The limit kernel `exp(π² w³/36 + π² s w)`. -/
noncomputable def radialKlim (w : ℂ) (s : ℝ) : ℂ :=
  Complex.exp ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + (Real.pi ^ 2 : ℂ) * (s : ℂ) * w)

lemma radialEps_tendsto : Tendsto radialEps atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (by norm_num)

lemma real_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 1
  simp only [Finset.sum_range_one, abs_neg] at h
  have e : (-x) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + Real.log (1 - -x) = Real.log (1 + x) - x := by
    simp; ring
  rw [e] at h
  refine h.trans ?_
  have hab : |x| ^ (1 + 1) = x ^ 2 := by rw [pow_two, pow_two, abs_mul_abs_self]
  rw [hab, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

theorem radialK_tendsto {ι : Type*} {l : Filter ι} {c s : ι → ℝ} {s₀ : ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (𝓝 s₀)) (w : ℂ) :
    Tendsto (fun i => radialK (c i) w (s i)) l (𝓝 (radialKlim w s₀)) := by
  set ε : ι → ℝ := fun i => radialEps (c i) with hεdef
  have hε : Tendsto ε l (𝓝 0) := radialEps_tendsto.comp hc
  have hcpos : ∀ᶠ i in l, 0 < c i := hc.eventually_gt_atTop 0
  have hcube : ∀ᶠ i in l, c i * ε i ^ 3 = 1 := hcpos.mono fun i hi => radialEps_cube hi
  have hεpos : ∀ᶠ i in l, 0 < ε i := hcpos.mono fun i hi => radialEps_pos hi
  have hsmall : ∀ᶠ i in l, ε i * ‖w‖ ≤ 1 / 4 := by
    have : Tendsto (fun i => ε i * ‖w‖) l (𝓝 (0 * ‖w‖)) := hε.mul_const _
    simp only [zero_mul] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hxs : Tendsto (fun i => Real.pi ^ 2 * ε i ^ 2 * s i) l (𝓝 0) := by
    have := ((hε.pow 2).const_mul (Real.pi ^ 2)).mul hs
    simpa using this
  -- factor 1
  have h1 : Tendsto (fun i => (1 - (ε i : ℂ) * w) ^ (-(1 / 2 : ℂ))) l (𝓝 1) := by
    have h0 : Tendsto (fun i => 1 - (ε i : ℂ) * w) l (𝓝 1) := by
      have : Tendsto (fun i => (ε i : ℂ)) l (𝓝 0) := by
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hε
      simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub (this.mul_const w)
    have := ((continuousAt_cpow_const (a := (1 : ℂ)) (b := -(1 / 2 : ℂ))
      (by simp)).tendsto).comp h0
    simpa [Function.comp_def] using this
  -- factor 2
  have h2 : Tendsto (fun i => Complex.exp (FormalResearch.Asymptotics.binetDiff (c i) ((ε i : ℂ) * w)))
      l (𝓝 1) := by
    have hb : Tendsto (fun i => FormalResearch.Asymptotics.binetDiff (c i) ((ε i : ℂ) * w)) l (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ?_ (a := fun i => (1 / (12 * c i)) * (7 / 3))
      · filter_upwards [hcpos, hεpos, hsmall] with i hci hεi hsi
        have hre : ((ε i : ℂ) * w).re ≤ 1 / 4 := by
          have : ((ε i : ℂ) * w).re = ε i * w.re := by simp
          rw [this]
          nlinarith [Complex.re_le_norm w]
        have := FormalResearch.Asymptotics.binetDiff_norm_le hci (ζ := (ε i : ℂ) * w) (by linarith)
        refine this.trans ?_
        gcongr
        have h3 : 1 / (1 - ((ε i : ℂ) * w).re) ≤ 4 / 3 := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith
      · have : Tendsto (fun i => 1 / (12 * c i)) l (𝓝 0) := by
          have h12 : Tendsto (fun i => 12 * c i) l atTop := hc.const_mul_atTop (by norm_num)
          simp only [one_div]; exact h12.inv_tendsto_atTop
        simpa using this.mul_const (7 / 3 : ℝ)
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto 0).comp hb
  -- factor 3
  have hA : Tendsto (fun i => (c i : ℂ) * stripS0Tilde ((ε i : ℂ) * w)) l
      (𝓝 ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (hε.pow 2).mul_const (10 * ‖w‖ ^ 5) : Tendsto (fun i => ε i ^ 2 * (10 * ‖w‖ ^ 5)) l (𝓝 0))
    filter_upwards [hcpos, hεpos, hsmall, hcube] with i hci hεi hsi hcu
    have hnorm : ‖(ε i : ℂ) * w‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεi.le]; exact hsi
    have h5 := stripS0Tilde_sub_le hnorm
    have hcu' : (c i : ℂ) * (ε i : ℂ) ^ 3 = 1 := by exact_mod_cast hcu
    have e : (c i : ℂ) * stripS0Tilde ((ε i : ℂ) * w) - (Real.pi ^ 2 / 36 : ℂ) * w ^ 3 =
        (c i : ℂ) * (stripS0Tilde ((ε i : ℂ) * w) - (Real.pi ^ 2 / 36 : ℂ) * ((ε i : ℂ) * w) ^ 3) := by
      have : (Real.pi ^ 2 / 36 : ℂ) * w ^ 3 = (Real.pi ^ 2 / 36 : ℂ) * w ^ 3 * ((c i : ℂ) * (ε i : ℂ) ^ 3) := by
        rw [hcu']; ring
      rw [this]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hci.le]
    calc c i * ‖stripS0Tilde ((ε i : ℂ) * w) - (Real.pi ^ 2 / 36 : ℂ) * ((ε i : ℂ) * w) ^ 3‖
        ≤ c i * (10 * ‖(ε i : ℂ) * w‖ ^ 5) := by gcongr
      _ = ε i ^ 2 * (10 * ‖w‖ ^ 5) * (c i * ε i ^ 3) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεi.le]; ring
      _ = ε i ^ 2 * (10 * ‖w‖ ^ 5) := by rw [hcu, mul_one]
  have hB : Tendsto (fun i => c i * ε i * Real.log (Real.pi ^ 2 * radialXi (c i) (s i))) l
      (𝓝 (Real.pi ^ 2 * s₀)) := by
    have hdiff : Tendsto (fun i => c i * ε i * Real.log (Real.pi ^ 2 * radialXi (c i) (s i)) - Real.pi ^ 2 * s i)
        l (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ?_ (a := fun i => 2 * Real.pi ^ 4 * ε i ^ 2 * s i ^ 2)
      · filter_upwards [hcpos, hεpos, hcube, hxs.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1 / 2))]
          with i hci hεi hcu hxi
        have hxi' : |Real.pi ^ 2 * ε i ^ 2 * s i| ≤ 1 / 2 := by
          have := Metric.mem_ball.mp hxi; rw [Real.dist_eq, sub_zero] at this; exact this.le
        have hxx : Real.pi ^ 2 * radialXi (c i) (s i) = 1 + Real.pi ^ 2 * ε i ^ 2 * s i := by
          simp only [radialXi, hεdef]; field_simp
        rw [hxx, Real.norm_eq_abs]
        have hlg := real_log_one_add_sub_le hxi'
        have e : c i * ε i * Real.log (1 + Real.pi ^ 2 * ε i ^ 2 * s i) - Real.pi ^ 2 * s i =
            c i * ε i * (Real.log (1 + Real.pi ^ 2 * ε i ^ 2 * s i) - Real.pi ^ 2 * ε i ^ 2 * s i) := by
          have : Real.pi ^ 2 * s i = c i * ε i * (Real.pi ^ 2 * ε i ^ 2 * s i) := by
            have : c i * ε i * (Real.pi ^ 2 * ε i ^ 2 * s i) = Real.pi ^ 2 * s i * (c i * ε i ^ 3) := by ring
            rw [this, hcu, mul_one]
          rw [mul_sub, ← this]
        rw [e, abs_mul, abs_of_pos (mul_pos hci hεi)]
        calc c i * ε i * |Real.log (1 + Real.pi ^ 2 * ε i ^ 2 * s i) - Real.pi ^ 2 * ε i ^ 2 * s i|
            ≤ c i * ε i * (2 * (Real.pi ^ 2 * ε i ^ 2 * s i) ^ 2) := by gcongr
          _ = 2 * Real.pi ^ 4 * ε i ^ 2 * s i ^ 2 * (c i * ε i ^ 3) := by ring
          _ = _ := by rw [hcu, mul_one]
      · have := ((hε.pow 2).const_mul (2 * Real.pi ^ 4)).mul (hs.pow 2)
        simpa using this
    have := hdiff.add ((hs.const_mul (Real.pi ^ 2)))
    simpa using this
  have h3 : Tendsto (fun i => Complex.exp ((c i : ℂ) * mellinPhi ((ε i : ℂ) * w) (radialXi (c i) (s i)))) l
      (𝓝 (radialKlim w s₀)) := by
    have hlim : Tendsto (fun i => (c i : ℂ) * stripS0Tilde ((ε i : ℂ) * w) +
        ((c i * ε i * Real.log (Real.pi ^ 2 * radialXi (c i) (s i)) : ℝ) : ℂ) * w) l
        (𝓝 ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + (Real.pi ^ 2 : ℂ) * (s₀ : ℂ) * w)) := by
      have hB' : Tendsto (fun i => ((c i * ε i * Real.log (Real.pi ^ 2 * radialXi (c i) (s i)) : ℝ) : ℂ))
          l (𝓝 ((Real.pi ^ 2 * s₀ : ℝ) : ℂ)) := by
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp hB
      have := hA.add (hB'.mul_const w)
      convert this using 2
      push_cast; ring
    have hev : ∀ᶠ i in l, (c i : ℂ) * mellinPhi ((ε i : ℂ) * w) (radialXi (c i) (s i)) =
        (c i : ℂ) * stripS0Tilde ((ε i : ℂ) * w) +
          ((c i * ε i * Real.log (Real.pi ^ 2 * radialXi (c i) (s i)) : ℝ) : ℂ) * w := by
      filter_upwards [hxs.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1 / 2))] with i hxi
      have hxi' : |Real.pi ^ 2 * ε i ^ 2 * s i| ≤ 1 / 2 := by
        have := Metric.mem_ball.mp hxi; rw [Real.dist_eq, sub_zero] at this; exact this.le
      have hxx : Real.pi ^ 2 * radialXi (c i) (s i) = 1 + Real.pi ^ 2 * ε i ^ 2 * s i := by
        simp only [radialXi, hεdef]; field_simp
      have hpos : 0 ≤ Real.pi ^ 2 * radialXi (c i) (s i) := by
        rw [hxx]; have := neg_abs_le (Real.pi ^ 2 * ε i ^ 2 * s i); linarith
      simp only [mellinPhi]
      have hlog : Complex.log ((Real.pi ^ 2 * radialXi (c i) (s i) : ℝ) : ℂ) =
          ((Real.log (Real.pi ^ 2 * radialXi (c i) (s i)) : ℝ) : ℂ) := (Complex.ofReal_log hpos).symm
      push_cast at hlog ⊢
      rw [hlog]; ring
    have := (Complex.continuous_exp.tendsto _).comp hlim
    refine (this.congr' ?_).trans ?_
    · filter_upwards [hev] with i hi; simp [Function.comp_def, hi]
    · simp [radialKlim]
  have := (h1.mul h2).mul h3
  simpa [radialK, mellinK0] using this

/-- info: 'FormalResearch.SignUncertainty.radialK_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialK_tendsto

end FormalResearch.SignUncertainty
