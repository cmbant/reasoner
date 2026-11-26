module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroSlit

/-!
# `G_outer` and the edge coupling (FIVE-0 slice 4): `G(iy) K_edge(y) = G(e^{-iψ}) e^{iψ} 2y²/(1+y²)`

`cts:coupling` for `Gout`.  Since `h̄_a(1-s) = h̄_a(s)` and `σ(iy) = e^{-iψ} = sTan(1 - iτ)`, the two sides of the
coupling share the factor `exp h̄_a(iτ)` and differ by the explicit factor `ρ(σ z)/ρ(z)` evaluated at `z = iy`;
the identity is then an identity between explicit products of principal powers, checked in polar form
(`ex a b = exp(a + i b)`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- Polar form `e^{a + i b}`. -/
noncomputable def ex (a b : ℝ) : ℂ := Complex.exp ((a : ℂ) + (b : ℂ) * Complex.I)

lemma ex_mul (a b a' b' : ℝ) : ex a b * ex a' b' = ex (a + a') (b + b') := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_inv (a b : ℝ) : (ex a b)⁻¹ = ex (-a) (-b) := by
  unfold ex; rw [← Complex.exp_neg]; congr 1; push_cast; ring

lemma ex_div (a b a' b' : ℝ) : ex a b / ex a' b' = ex (a - a') (b - b') := by
  rw [div_eq_mul_inv, ex_inv, ex_mul]; congr 1

lemma ex_pow (a b : ℝ) (n : ℕ) : ex a b ^ n = ex (n * a) (n * b) := by
  unfold ex; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma ex_congr {a b a' b' : ℝ} (ha : a = a') (hb : b = b') : ex a b = ex a' b' := by rw [ha, hb]

lemma ex_ne_zero (a b : ℝ) : ex a b ≠ 0 := Complex.exp_ne_zero _

lemma ex_cpow {a b : ℝ} (h1 : -π < b) (h2 : b ≤ π) (r : ℝ) : ex a b ^ (r : ℂ) = ex (r * a) (r * b) := by
  have hl : Complex.log (ex a b) = (a : ℂ) + (b : ℂ) * Complex.I := by
    unfold ex; exact Complex.log_exp (by simpa using h1) (by simpa using h2)
  rw [Complex.cpow_def_of_ne_zero (ex_ne_zero a b), hl]
  unfold ex; congr 1; push_cast; ring

lemma ofReal_eq_ex {r : ℝ} (hr : 0 < r) : (r : ℂ) = ex (Real.log r) 0 := by
  unfold ex; push_cast; rw [zero_mul, add_zero, ← Complex.ofReal_exp, Real.exp_log hr]

lemma eq_ex_arg {x : ℂ} (hx : x ≠ 0) : x = ex (Real.log ‖x‖) (Complex.arg x) := by
  have h : Complex.log x = (Real.log ‖x‖ : ℂ) + (Complex.arg x : ℂ) * Complex.I := rfl
  unfold ex
  rw [← h, Complex.exp_log hx]

lemma I_eq_ex : Complex.I = ex 0 (π / 2) := by
  unfold ex; push_cast; rw [zero_add, Complex.exp_pi_div_two_mul_I]

lemma slitVal_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    slitVal y = ((1 / 2 : ℂ) - Complex.I * (vOf y : ℂ)) / (xOf y : ℂ) := by
  unfold slitVal
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx : (xOf y : ℂ) ≠ 0 := by exact_mod_cast (xOf_pos hy).ne'
  have hv : (vOf y : ℂ) = (Real.arsinh (√(uSlit y - 1)) : ℂ) / π := by unfold vOf; push_cast; ring
  have hxe : (xOf y : ℂ) = (Real.arsinh (√(uSlit y)) : ℂ) / π := by unfold xOf; push_cast; ring
  rw [hv, hxe]
  have hB : (Real.arsinh (√(uSlit y)) : ℂ) ≠ 0 := by
    intro h; apply hx; rw [hxe, h]; simp
  field_simp

lemma conj_wPt (y : ℝ) :
    starRingEnd ℂ (wPt y) = (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) := by
  rw [wPt_eq, map_div₀]
  simp [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma norm_one_add_I_mul (y : ℝ) : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
  have : (1 : ℂ) + Complex.I * (y : ℂ) = (1 : ℝ) + ((y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]; simp

lemma norm_one_sub_I_mul (y : ℝ) : ‖(1 : ℂ) - Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
  have : (1 : ℂ) - Complex.I * (y : ℂ) = (1 : ℝ) + ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]; simp

/-- The algebraic core of the coupling: at `z = iy`, `ρ(σ z)/ρ(z)` times the kernel. -/
lemma coupling_alg {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 *
        (slitVal y) ^ (-(1 / 4 : ℂ)) * Kedge y =
      (1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) /
        (1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ 2 *
        (slitVal y)⁻¹ ^ (-(1 / 4 : ℂ)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  have h1y : (0 : ℝ) < 1 + y ^ 2 := by positivity
  set c : ℝ := √(1 + y ^ 2) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr h1y
  have hlc : Real.log c = Real.log (1 + y ^ 2) / 2 := by
    rw [hcdef, Real.log_sqrt h1y.le]
  have hne_p : (1 : ℂ) + Complex.I * (y : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hne_m : (1 : ℂ) - Complex.I * (y : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  set θ : ℝ := Complex.arg (1 + Complex.I * (y : ℂ)) with hθdef
  have hθ : |θ| < π / 2 := by
    rw [hθdef]; apply Complex.abs_arg_lt_pi_div_two_iff.mpr; left; simp
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  have e_p : (1 : ℂ) + Complex.I * (y : ℂ) = ex (Real.log c) θ := by
    have h := eq_ex_arg hne_p
    rw [norm_one_add_I_mul] at h; exact h
  have e_m : (1 : ℂ) - Complex.I * (y : ℂ) = ex (Real.log c) (-θ) := by
    have h := eq_ex_arg hne_m
    have hconj : (1 : ℂ) - Complex.I * (y : ℂ) = starRingEnd ℂ ((1 : ℂ) + Complex.I * (y : ℂ)) := by
      simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, sub_eq_add_neg]
    have harg : Complex.arg ((1 : ℂ) - Complex.I * (y : ℂ)) = -θ := by
      have hne : θ ≠ π := by linarith [hθ'.2]
      rw [hconj, Complex.arg_conj, ite_eq_right hne]
    rw [norm_one_sub_I_mul, harg] at h; exact h
  -- σ(iy)
  have e_σ1 : 1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) =
      ex (Real.log (2 * y) - Real.log c) (π / 2 - θ) := by
    have : 1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) =
        (((2 * y : ℝ) : ℂ)) * Complex.I / (1 + Complex.I * (y : ℂ)) := by
      field_simp; push_cast; ring
    rw [this, ofReal_eq_ex (by positivity : 0 < 2 * y), e_p, I_eq_ex, ex_mul, ex_div]
    exact ex_congr (by ring) (by ring)
  have e_σ2 : 1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) =
      ex (Real.log 2 - Real.log c) (-θ) := by
    have : 1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) = (2 : ℂ) / (1 + Complex.I * (y : ℂ)) := by
      field_simp; ring
    have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, h2, ofReal_eq_ex (by norm_num : (0 : ℝ) < 2), e_p, ex_div]
    exact ex_congr (by ring) (by ring)
  have e_w : wPt y = ex 0 (2 * θ) := by
    rw [wPt_eq, e_p, e_m, ex_div]; exact ex_congr (by ring) (by ring)
  -- the slit value
  have hx := xOf_pos hy'
  set x : ℝ := xOf y with hxdef
  set v : ℝ := vOf y with hvdef
  have hrb : 0 < √(v ^ 2 + 1 / 4) := Real.sqrt_pos.mpr (by positivity)
  set rb : ℝ := √(v ^ 2 + 1 / 4) with hrbdef
  have hs0ne : ((1 / 2 : ℂ) - Complex.I * (v : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  set φ : ℝ := Complex.arg ((1 / 2 : ℂ) - Complex.I * (v : ℂ)) with hφdef
  have hφ : |φ| < π / 2 := by
    rw [hφdef]; apply Complex.abs_arg_lt_pi_div_two_iff.mpr; left; simp
  have hφ' := abs_lt.mp hφ
  have e_s0 : (1 / 2 : ℂ) - Complex.I * (v : ℂ) = ex (Real.log rb) φ := by
    have h := eq_ex_arg hs0ne
    have hn : ‖(1 / 2 : ℂ) - Complex.I * (v : ℂ)‖ = rb := by
      have : (1 / 2 : ℂ) - Complex.I * (v : ℂ) = ((1 / 2 : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_add_mul_I, hrbdef]
      congr 1; ring
    rw [hn] at h; exact h
  have e_sv : slitVal y = ex (Real.log rb - Real.log x) φ := by
    rw [slitVal_eq hy', e_s0, ofReal_eq_ex hx, ex_div]
    exact ex_congr rfl (by ring)
  have e_b : (v : ℂ) + Complex.I / 2 = ex (Real.log rb) (π / 2 + φ) := by
    have : (v : ℂ) + Complex.I / 2 = Complex.I * ((1 / 2 : ℂ) - Complex.I * (v : ℂ)) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this, e_s0, I_eq_ex, ex_mul]; exact ex_congr (by ring) rfl
  have hF : 0 < 2 * y / (1 + y ^ 2) := by positivity
  have hxF : 0 < x * (2 * y / (1 + y ^ 2)) := by positivity
  have e_K : Kedge y = ex (1 / 2 * (Real.log rb - Real.log (x * (2 * y / (1 + y ^ 2)))) + 3 * Real.log y + 3 * 0)
      (1 / 2 * (π / 2 + φ - 0) + 3 * 0 + 3 * (2 * θ)) := by
    unfold Kedge
    rw [← hvdef, ← hxdef]
    rw [e_b, ofReal_eq_ex hxF, ex_div]
    have hh : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hh, ex_cpow (by linarith) (by linarith), ofReal_eq_ex hy0, e_w, ex_pow, ex_pow, ex_mul, ex_mul]
    exact ex_congr (by push_cast; ring) (by push_cast; ring)
  have e_Q5 : ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) = ex (Real.log (2 * y ^ 2 / (1 + y ^ 2))) 0 :=
    ofReal_eq_ex (by positivity)
  have hqe : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hqf : (-(1 / 4 : ℂ)) = ((-(1 / 4) : ℝ) : ℂ) := by push_cast; ring
  have A1 : (1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) = ex (1 / 2 * Real.log c) (1 / 2 * (-θ)) := by
    rw [hqe, e_m, ex_cpow (by linarith) (by linarith)]
  have A2 : (1 + Complex.I * (y : ℂ)) ^ 2 = ex (2 * Real.log c) (2 * θ) := by
    rw [e_p, ex_pow]; exact ex_congr (by push_cast; ring) (by push_cast; ring)
  have A3 : (slitVal y) ^ (-(1 / 4 : ℂ)) = ex (-(1 / 4) * (Real.log rb - Real.log x)) (-(1 / 4) * φ) := by
    rw [hqf, e_sv, ex_cpow (by linarith) (by linarith)]
  have B1 : (1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) =
      ex (1 / 2 * (Real.log (2 * y) - Real.log c)) (1 / 2 * (π / 2 - θ)) := by
    rw [hqe, e_σ1, ex_cpow (by linarith) (by linarith)]
  have B2 : (1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ 2 =
      ex (2 * (Real.log 2 - Real.log c)) (2 * (-θ)) := by
    rw [e_σ2, ex_pow]; exact ex_congr (by push_cast; ring) (by push_cast; ring)
  have B3 : (slitVal y)⁻¹ ^ (-(1 / 4 : ℂ)) =
      ex (-(1 / 4) * (-(Real.log rb - Real.log x))) (-(1 / 4) * (-φ)) := by
    rw [hqf, e_sv, ex_inv, ex_cpow (by linarith) (by linarith)]
  rw [A1, A2, A3, e_K, B1, B2, B3, e_w, e_Q5]
  simp only [ex_mul, ex_div]
  have hl2y : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hlF : Real.log (2 * y / (1 + y ^ 2)) = Real.log 2 + Real.log y - Real.log (1 + y ^ 2) := by
    rw [Real.log_div (by positivity) h1y.ne', hl2y]
  have hlxF : Real.log (x * (2 * y / (1 + y ^ 2))) = Real.log x + Real.log (2 * y / (1 + y ^ 2)) :=
    Real.log_mul hx.ne' hF.ne'
  have hlQ : Real.log (2 * y ^ 2 / (1 + y ^ 2)) = Real.log 2 + 2 * Real.log y - Real.log (1 + y ^ 2) := by
    rw [Real.log_div (by positivity) h1y.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  exact ex_congr (by rw [hlxF, hlF, hl2y, hlQ]; rw [hlc]; ring) (by ring)

lemma sigma_slit_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) =
      sTan (1 + ((-slitTau y : ℝ) : ℂ) * Complex.I) := by
  rw [sTan_one_add]
  have : Real.tanh (π * (-slitTau y) / 4) = -y := by
    rw [show π * (-slitTau y) / 4 = -(π * slitTau y / 4) by ring, Real.tanh_neg, tanh_slitTau hy]
  rw [this]; push_cast; ring_nf

lemma sigma_slit_mem_cl {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) ∈ closure halfDisc := by
  rw [sigma_slit_eq hy]
  exact sTan_mem_closure ⟨by simp, by simp⟩

lemma sInv_sigma_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    sInv ((1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) = 1 - (slitTau y : ℂ) * Complex.I := by
  rw [sigma_slit_eq hy]
  have := sInv_sTan (s := 1 + ((-slitTau y : ℝ) : ℂ) * Complex.I) ⟨by simp, by simp⟩
  rw [this]; push_cast; ring

lemma qBd_sigma_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    qBd ((1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) = (slitVal y)⁻¹ := by
  have hne : (1 : ℂ) + Complex.I * (y : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hL : slitVal y ≠ 0 := by
    rw [← qBd_slit hy]; exact Complex.slitPlane_ne_zero (qBd_mem_slit (slit_mem_diff hy))
  exact extLim_eq_of_tendsto (sigma_slit_mem_cl hy)
    (tendsto_qHat_sigma hne hL (tendsto_qHat_slit hy.1 hy.2))

/-- **`cts:coupling`**: `G(iy) K_edge(y) = G(e^{-iψ}) e^{iψ} 2y²/(1+y²)`. -/
theorem gout_coupling {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Gout (Complex.I * (y : ℂ)) * Kedge y =
      Gout (starRingEnd ℂ (wPt y)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) := by
  have key := coupling_alg hy
  have hA : hbarA aAmp (1 - (slitTau y : ℂ) * Complex.I) = hbarA aAmp ((slitTau y : ℂ) * Complex.I) :=
    hbarA_oneSub amp_aAmp (slit_mem_closedStrip _ |> fun h => ⟨h.1, h.2⟩)
  rw [conj_wPt]
  unfold Gout
  rw [sInv_slit hy, sInv_sigma_slit hy, hA, qBd_slit hy, qBd_sigma_slit hy]
  linear_combination (Complex.exp (hbarA aAmp ((slitTau y : ℂ) * Complex.I))) * key

end FormalResearch.ModularBootstrap.FiveTerm
