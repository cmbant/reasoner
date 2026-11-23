module

public import FormalResearch.CohnElkies.CancelledSymbolAndLaplace

/-!
# Heat equation and `y`-derivatives of the Gaussian kernel `gaussKern y u = exp(-u²/(4y))`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, the derivative (symbol) bounds `(e27)` of Lemma U.1
(`|∂_Ω^r F̃| ≲ |Ω|^{-5/2-r}`), via the exact integration-by-parts identity of `gaussian_2d_ibp_asymp`.

These are standard lemmas about the Gaussian kernel, proved here from `norm_iteratedDeriv_gaussKern_le` in
`CancelledSymbolAndLaplace`:

* `hasDerivAt_gaussKern_y` (a1): the `y`-derivative of the kernel.
* `deriv_y_gaussKern_eq` (a2): the heat equation `∂_y K = ∂_u² K + K/(2y)`, written as `(u²/(4y²)) K = ∂_u² K + K/(2y)`.
* `hasDerivAt_iteratedDeriv_gaussKern_y` (a3): `∂_y` commutes with `∂_u^n` up to the same `1/(2y)` term.
* `norm_deriv_y_iteratedDeriv_gaussKern_le` (a4): uniform bounds of the first and second `y`-derivative on
  `{0 < Re y, 1 ≤ |y|}`.

Method. Let `s² y = 1`. Then `K(y,u) = E(s u)` with `E(t) = exp(-t²/4)`, so `∂_u^n K = sⁿ E⁽ⁿ⁾(s u)` (scaling). The
profile satisfies `E⁽ⁿ⁺²⁾ + (t/2) E⁽ⁿ⁺¹⁾ + ((n+1)/2) E⁽ⁿ⁾ = 0`. Near a given `y ≠ 0` the square root `s(z)` is a
differentiable branch with `s(z)² z = 1`, and the `y`-derivative is a chain rule in `s(z)`. The helpers are named `gkHeat_`.

Negative regression (for (a4)): the condition `0 < Re y` cannot be replaced by `Re y < 0`. There
`|gaussKern y u| = exp(|Re(1/y)| u²/4)` grows in `u`, and no polynomial bound `B (1+|u|)^k` holds.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.CohnElkies

/-! ### The profile `E(t) = exp(-t²/4)` -/

/-- The profile `E(t) = exp(-t²/4)`; `gaussKern z u = E (s u)` whenever `s² z = 1`. -/
noncomputable def gkHeat_E (t : ℂ) : ℂ := Complex.exp (-(t ^ 2) / 4)

lemma gkHeat_E_contDiff : ContDiff ℂ ⊤ gkHeat_E :=
  (Complex.differentiable_exp.contDiff).comp (((contDiff_id.pow 2).neg).div_const 4)

lemma gkHeat_E_hasDerivAt (t : ℂ) : HasDerivAt gkHeat_E (-(t / 2) * gkHeat_E t) t := by
  have h1 : HasDerivAt (fun s : ℂ => -(s ^ 2) / 4) (-(2 * t) / 4) t := by
    have h := ((hasDerivAt_pow 2 t).neg).div_const 4
    convert h using 1
    norm_num
  unfold gkHeat_E
  convert h1.cexp using 1
  ring

/-- Iterated complex derivatives of a `C^∞` complex function are differentiable with the next derivative. -/
lemma gkHeat_hasDerivAt_iter (F : ℂ → ℂ) (hF : ContDiff ℂ ⊤ F) (m : ℕ) (w : ℂ) :
    HasDerivAt (iteratedDeriv m F) (iteratedDeriv (m + 1) F w) w := by
  rw [iteratedDeriv_succ]
  exact (hF.differentiable_iteratedDeriv m (by simp)).differentiableAt.hasDerivAt

lemma gkHeat_ode0 (t : ℂ) :
    iteratedDeriv 2 gkHeat_E t + (t / 2) * iteratedDeriv 1 gkHeat_E t + (1 / 2) * gkHeat_E t = 0 := by
  have hd1 : iteratedDeriv 1 gkHeat_E = fun s : ℂ => -(s / 2) * gkHeat_E s :=
    funext fun s => by rw [iteratedDeriv_one]; exact (gkHeat_E_hasDerivAt s).deriv
  have hL : HasDerivAt (fun s : ℂ => -(s / 2)) (-(1 / 2)) t := ((hasDerivAt_id' t).div_const 2).neg
  have hd2 : iteratedDeriv 2 gkHeat_E t = -(1 / 2) * gkHeat_E t + -(t / 2) * (-(t / 2) * gkHeat_E t) := by
    show iteratedDeriv (1 + 1) gkHeat_E t = _
    rw [iteratedDeriv_succ, hd1]
    exact (hL.mul (gkHeat_E_hasDerivAt t)).deriv
  rw [hd2, iteratedDeriv_one, (gkHeat_E_hasDerivAt t).deriv]
  ring

/-- The Hermite-type ODE for the derivatives of `E`: `E⁽ⁿ⁺²⁾ + (t/2) E⁽ⁿ⁺¹⁾ + ((n+1)/2) E⁽ⁿ⁾ = 0`. -/
lemma gkHeat_ode (n : ℕ) (t : ℂ) :
    iteratedDeriv (n + 2) gkHeat_E t + (t / 2) * iteratedDeriv (n + 1) gkHeat_E t +
      ((n : ℂ) + 1) / 2 * iteratedDeriv n gkHeat_E t = 0 := by
  induction n generalizing t with
  | zero => simpa using gkHeat_ode0 t
  | succ k ih =>
    have hfun : (fun s : ℂ => iteratedDeriv (k + 2) gkHeat_E s + (s / 2) * iteratedDeriv (k + 1) gkHeat_E s +
        ((k : ℂ) + 1) / 2 * iteratedDeriv k gkHeat_E s) = fun _ => 0 :=
      funext fun s => ih s
    have hD : HasDerivAt (fun s : ℂ => iteratedDeriv (k + 2) gkHeat_E s + (s / 2) * iteratedDeriv (k + 1) gkHeat_E s +
        ((k : ℂ) + 1) / 2 * iteratedDeriv k gkHeat_E s)
        (iteratedDeriv (k + 1 + 2) gkHeat_E t + (1 / 2 * iteratedDeriv (k + 1) gkHeat_E t +
          t / 2 * iteratedDeriv (k + 1 + 1) gkHeat_E t) + ((k : ℂ) + 1) / 2 * iteratedDeriv (k + 1) gkHeat_E t) t :=
      ((gkHeat_hasDerivAt_iter gkHeat_E gkHeat_E_contDiff (k + 2) t).add
        (((hasDerivAt_id' t).div_const 2).mul (gkHeat_hasDerivAt_iter gkHeat_E gkHeat_E_contDiff (k + 1) t))).add
        ((gkHeat_hasDerivAt_iter gkHeat_E gkHeat_E_contDiff k t).const_mul (((k : ℂ) + 1) / 2))
    have h0 : deriv (fun s : ℂ => iteratedDeriv (k + 2) gkHeat_E s + (s / 2) * iteratedDeriv (k + 1) gkHeat_E s +
        ((k : ℂ) + 1) / 2 * iteratedDeriv k gkHeat_E s) t = 0 := by
      rw [hfun]; exact deriv_const t 0
    rw [hD.deriv] at h0
    push_cast
    linear_combination h0

/-! ### Scaling: `∂_u^n [F(s u)] = sⁿ F⁽ⁿ⁾(s u)` -/

lemma gkHeat_iteratedDeriv_comp_mul (F : ℂ → ℂ) (hF : ContDiff ℂ ⊤ F) (c : ℂ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (fun v : ℝ => F (c * v)) u = c ^ n * iteratedDeriv n F (c * u) := by
  induction n generalizing u with
  | zero => simp
  | succ k ih =>
    have hk : iteratedDeriv k (fun v : ℝ => F (c * v)) = fun v : ℝ => c ^ k * iteratedDeriv k F (c * v) :=
      funext ih
    have hlin : HasDerivAt (fun w : ℂ => c * w) c (u : ℂ) := by
      simpa using (hasDerivAt_id' (u : ℂ)).const_mul c
    have hin : HasDerivAt (fun w : ℂ => iteratedDeriv k F (c * w)) (iteratedDeriv (k + 1) F (c * u) * c) (u : ℂ) :=
      HasDerivAt.comp (u : ℂ) (gkHeat_hasDerivAt_iter F hF k (c * u)) hlin
    have hreal : HasDerivAt (fun v : ℝ => iteratedDeriv k F (c * v)) (iteratedDeriv (k + 1) F (c * u) * c) u :=
      hin.comp_ofReal
    rw [iteratedDeriv_succ, hk]
    exact (hreal.const_mul (c ^ k)).deriv.trans (by ring)

/-- Scaling form of the kernel: if `s² z = 1` then `∂_u^n gaussKern z u = sⁿ E⁽ⁿ⁾(s u)`. -/
lemma gkHeat_gauss_scale {z s : ℂ} (hs : s ^ 2 * z = 1) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (gaussKern z) u = s ^ n * iteratedDeriv n gkHeat_E (s * u) := by
  have hfun : gaussKern z = fun v : ℝ => gkHeat_E (s * v) := by
    funext v
    unfold gaussKern gkHeat_E
    congr 1
    have hz : z ≠ 0 := by rintro rfl; simp at hs
    field_simp
    linear_combination ((v : ℂ) ^ 2) * hs
  rw [hfun]
  exact gkHeat_iteratedDeriv_comp_mul gkHeat_E gkHeat_E_contDiff s n u

/-! ### The square-root branch -/

/-- For `y ≠ 0` there is `s` with `s² y = 1`, and a differentiable branch `c` with `c y = s`, `c'(y) = -s/(2y)`,
and `c(z)² z = 1` near `y`. -/
lemma gkHeat_branch {y : ℂ} (hy : y ≠ 0) :
    ∃ s : ℂ, s ^ 2 * y = 1 ∧ ∃ c : ℂ → ℂ, c y = s ∧ HasDerivAt c (-(s / (2 * y))) y ∧
      ∀ᶠ z in 𝓝 y, c z ^ 2 * z = 1 := by
  set s : ℂ := (y⁻¹) ^ (1 / 2 : ℂ) with hs_def
  have hs2 : s ^ 2 = y⁻¹ := by
    rw [hs_def, ← Complex.cpow_nat_mul, show ((2 : ℕ) : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one]
  have hsy : s ^ 2 * y = 1 := by rw [hs2, inv_mul_cancel₀ hy]
  refine ⟨s, hsy, fun z => s * (z / y) ^ (-(1 / 2 : ℂ)), by simp [div_self hy], ?_, ?_⟩
  · have hf : HasDerivAt (fun z : ℂ => z / y) (1 / y) y := (hasDerivAt_id' y).div_const y
    have hmem : (fun z : ℂ => z / y) y ∈ Complex.slitPlane := by
      show y / y ∈ Complex.slitPlane
      rw [div_self hy]
      exact Complex.one_mem_slitPlane
    have hp := (hf.cpow_const (c := -(1 / 2 : ℂ)) hmem).const_mul s
    convert hp using 1
    rw [div_self hy, Complex.one_cpow]
    ring
  · have hcont : ContinuousAt (fun z : ℂ => z / y) y := (continuous_id.div_const y).continuousAt
    have hev : ∀ᶠ z in 𝓝 y, z / y ∈ Complex.slitPlane :=
      hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by
        show y / y ∈ Complex.slitPlane
        rw [div_self hy]
        exact Complex.one_mem_slitPlane))
    filter_upwards [hev] with z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_div, Complex.mem_slitPlane_iff] at hz
      simp at hz
    show (s * (z / y) ^ (-(1 / 2 : ℂ))) ^ 2 * z = 1
    rw [mul_pow, hs2, ← Complex.cpow_nat_mul (z / y) 2 (-(1 / 2 : ℂ)),
      show ((2 : ℕ) : ℂ) * (-(1 / 2 : ℂ)) = -1 by norm_num, Complex.cpow_neg_one]
    field_simp

/-! ### (a1) `y`-derivative of the kernel -/

/-- (a1) `∂_y exp(-u²/(4y)) = u²/(4y²) · exp(-u²/(4y))` for `y ≠ 0`. -/
theorem hasDerivAt_gaussKern_y {y : ℂ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℂ => gaussKern y x) ((x : ℂ) ^ 2 / (4 * y ^ 2) * gaussKern y x) y := by
  have h4 : (4 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hq : HasDerivAt (fun z : ℂ => -((x : ℂ) ^ 2) / (4 * z)) ((x : ℂ) ^ 2 / (4 * y ^ 2)) y := by
    have h := (hasDerivAt_const y (-((x : ℂ) ^ 2))).div ((hasDerivAt_id' y).const_mul 4) h4
    convert h using 1
    field_simp
    ring
  unfold gaussKern
  exact (hq.cexp).congr_deriv (by ring)


/-- info: 'FormalResearch.CohnElkies.hasDerivAt_gaussKern_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_gaussKern_y

/-! ### (a2) The heat equation -/

/-- (a2) `(u²/(4y²)) K = ∂_u² K + K/(2y)`, i.e. `∂_y K = ∂_u² K + K/(2y)` with `K = gaussKern y`. -/
theorem deriv_y_gaussKern_eq {y : ℂ} (hy : y ≠ 0) (x : ℝ) :
    (x : ℂ) ^ 2 / (4 * y ^ 2) * gaussKern y x =
      iteratedDeriv 2 (gaussKern y) x + (1 / (2 * y)) * gaussKern y x := by
  obtain ⟨s, hsy, -⟩ := gkHeat_branch hy
  have hinv : 1 / (2 * y) = s ^ 2 / 2 := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hy) two_ne_zero]
    linear_combination (-2 : ℂ) * hsy
  have hy2 : (x : ℂ) ^ 2 / (4 * y ^ 2) = s ^ 4 * (x : ℂ) ^ 2 / 4 := by
    rw [div_eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)]
    linear_combination (-4 * (x : ℂ) ^ 2 * (s ^ 2 * y + 1)) * hsy
  have hK : gaussKern y x = gkHeat_E (s * x) := by
    simpa using gkHeat_gauss_scale hsy 0 x
  have hI2 : iteratedDeriv 2 gkHeat_E (s * x) = (((s * x) ^ 2) / 4 - 1 / 2) * gkHeat_E (s * x) := by
    have h := gkHeat_ode0 (s * x)
    rw [iteratedDeriv_one, (gkHeat_E_hasDerivAt (s * x)).deriv] at h
    linear_combination h
  rw [gkHeat_gauss_scale hsy 2 x, hK, hinv, hy2, hI2]
  ring

/-- info: 'FormalResearch.CohnElkies.deriv_y_gaussKern_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.deriv_y_gaussKern_eq

/-! ### (a3) `∂_y` commutes with `∂_u^n` up to the `1/(2y)` term -/

/-- (a3) `∂_y ∂_u^n K = ∂_u^{n+2} K + (1/(2y)) ∂_u^n K` for `y ≠ 0`, `K = gaussKern y`. -/
theorem hasDerivAt_iteratedDeriv_gaussKern_y (n : ℕ) {y : ℂ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℂ => iteratedDeriv n (gaussKern y) x)
      (iteratedDeriv (n + 2) (gaussKern y) x + (1 / (2 * y)) * iteratedDeriv n (gaussKern y) x) y := by
  obtain ⟨s, hsy, c, hcy, hcd, hcev⟩ := gkHeat_branch hy
  have hscale : ∀ᶠ z in 𝓝 y,
      iteratedDeriv n (gaussKern z) x = c z ^ n * iteratedDeriv n gkHeat_E (c z * x) := by
    filter_upwards [hcev] with z hz
    exact gkHeat_gauss_scale hz n x
  have hinner : HasDerivAt (fun z : ℂ => c z * (x : ℂ)) (-(s / (2 * y)) * (x : ℂ)) y :=
    hcd.mul_const (x : ℂ)
  have hEn : HasDerivAt (fun z : ℂ => iteratedDeriv n gkHeat_E (c z * x))
      (iteratedDeriv (n + 1) gkHeat_E (c y * x) * (-(s / (2 * y)) * x)) y := by
    have h := HasDerivAt.comp y (gkHeat_hasDerivAt_iter gkHeat_E gkHeat_E_contDiff n (c y * x)) hinner
    exact h
  have hψ := (hcd.pow n).mul hEn
  simp only [hcy, Pi.pow_apply] at hψ
  have hsc : ∀ m : ℕ, iteratedDeriv m (gaussKern y) x = s ^ m * iteratedDeriv m gkHeat_E (s * x) :=
    fun m => gkHeat_gauss_scale hsy m x
  have hinv : 1 / (2 * y) = s ^ 2 / 2 := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hy) two_ne_zero]
    linear_combination (-2 : ℂ) * hsy
  have hsy3 : s / (2 * y) = s ^ 3 / 2 := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hy) two_ne_zero]
    linear_combination (-2 * s) * hsy
  have hn : (n : ℂ) * s ^ (n - 1) * s ^ 3 = n * s ^ (n + 2) := by
    rcases n with _ | k
    · simp
    · rw [Nat.add_sub_cancel]; push_cast; ring
  have hode := gkHeat_ode n (s * x)
  refine (hψ.congr_of_eventuallyEq hscale).congr_deriv ?_
  rw [hsc (n + 2), hsc n, hinv, hsy3]
  linear_combination (-(s ^ (n + 2))) * hode + (-(1 / 2) * iteratedDeriv n gkHeat_E (s * x)) * hn

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_iteratedDeriv_gaussKern_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_iteratedDeriv_gaussKern_y

/-! ### Second `y`-derivative (helpers for (a4)) -/

lemma gkHeat_hasDerivAt_inv_two_mul (y : ℂ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℂ => 1 / (2 * z)) (-(1 / (2 * y ^ 2))) y := by
  have h2 : (2 : ℂ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
  have h := (hasDerivAt_const y (1 : ℂ)).div ((hasDerivAt_id' y).const_mul 2) h2
  convert h using 1
  field_simp
  ring

/-- The `y`-derivative of `∂_u^{n+2} K + (1/(2y)) ∂_u^n K`, simplified. -/
lemma gkHeat_second_formula (n : ℕ) {y : ℂ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun z : ℂ => iteratedDeriv (n + 2) (gaussKern z) x + (1 / (2 * z)) * iteratedDeriv n (gaussKern z) x)
      (iteratedDeriv (n + 2 + 2) (gaussKern y) x + (1 / y) * iteratedDeriv (n + 2) (gaussKern y) x -
        (1 / (4 * y ^ 2)) * iteratedDeriv n (gaussKern y) x) y :=
  ((hasDerivAt_iteratedDeriv_gaussKern_y (n + 2) hy x).add
    ((gkHeat_hasDerivAt_inv_two_mul y hy).mul (hasDerivAt_iteratedDeriv_gaussKern_y n hy x))).congr_deriv
    (by ring)

/-! ### (a4) Uniform bounds of the first and second `y`-derivative -/

/-- (a4) For `Re y > 0` and `|y| ≥ 1`, `|∂_y ∂_u^n K| ≤ B (1+|u|)^{n+2}` and `|∂_y² ∂_u^n K| ≤ B (1+|u|)^{n+4}`,
with one constant `B` for all `u`. Negative regression: `0 < Re y` cannot be replaced by `Re y < 0`, since then
`|gaussKern y u| = exp(|Re(1/y)| u²/4)` grows in `u` and no polynomial bound holds. -/
theorem norm_deriv_y_iteratedDeriv_gaussKern_le (n : ℕ) : ∃ B > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ x : ℝ,
    ‖deriv (fun y : ℂ => iteratedDeriv n (gaussKern y) x) y‖ ≤ B * (1 + |x|) ^ (n + 2) ∧
    ‖deriv (deriv (fun y : ℂ => iteratedDeriv n (gaussKern y) x)) y‖ ≤ B * (1 + |x|) ^ (n + 4) := by
  obtain ⟨B₀, hB₀, h₀⟩ := norm_iteratedDeriv_gaussKern_le n
  obtain ⟨B₂, hB₂, h₂⟩ := norm_iteratedDeriv_gaussKern_le (n + 2)
  obtain ⟨B₄, hB₄, h₄⟩ := norm_iteratedDeriv_gaussKern_le (n + 4)
  refine ⟨B₀ + B₂ + B₄, by positivity, fun {y} hre hy1 x => ?_⟩
  have hy0 : y ≠ 0 := fun h => by simp [h] at hre
  have hP1 : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hP0 : (0 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hPn : ∀ a b : ℕ, a ≤ b → (1 + |x|) ^ a ≤ (1 + |x|) ^ b :=
    fun a b hab => pow_le_pow_right₀ hP1 hab
  have hinv : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖(1 : ℂ) / w‖ ≤ 1 := fun w hw => by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hw
  have hi1 : ‖(1 : ℂ) / (2 * y)‖ ≤ 1 :=
    hinv _ (by rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith)
  have hi2 : ‖(1 : ℂ) / y‖ ≤ 1 := hinv _ hy1
  have hi3 : ‖(1 : ℂ) / (4 * y ^ 2)‖ ≤ 1 :=
    hinv _ (by rw [norm_mul, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]; nlinarith)
  constructor
  · rw [(hasDerivAt_iteratedDeriv_gaussKern_y n hy0 x).deriv]
    have hA : ‖iteratedDeriv (n + 2) (gaussKern y) x‖ ≤ B₂ * (1 + |x|) ^ (n + 2) := h₂ hre hy1 x
    have hB : ‖iteratedDeriv n (gaussKern y) x‖ ≤ B₀ * (1 + |x|) ^ n := h₀ hre hy1 x
    have hmulle : ‖(1 : ℂ) / (2 * y)‖ * ‖iteratedDeriv n (gaussKern y) x‖ ≤ B₀ * (1 + |x|) ^ n :=
      (mul_le_of_le_one_left (norm_nonneg _) hi1).trans hB
    have hPn' : (1 + |x|) ^ n ≤ (1 + |x|) ^ (n + 2) := hPn _ _ (by omega)
    have hPpos : 0 ≤ (1 + |x|) ^ (n + 2) := pow_nonneg hP0 _
    have hB0P : B₀ * (1 + |x|) ^ n ≤ B₀ * (1 + |x|) ^ (n + 2) := mul_le_mul_of_nonneg_left hPn' hB₀.le
    have hB0 : 0 ≤ B₀ * (1 + |x|) ^ (n + 2) := mul_nonneg hB₀.le hPpos
    have hB2 : 0 ≤ B₄ * (1 + |x|) ^ (n + 2) := mul_nonneg hB₄.le hPpos
    have hBB : B₂ * (1 + |x|) ^ (n + 2) ≤ (B₀ + B₂ + B₄) * (1 + |x|) ^ (n + 2) := by
      rw [add_mul, add_mul]
      linarith
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    refine (add_le_add hA hmulle).trans ?_
    rw [add_mul, add_mul] at *
    linarith
  · have hev : deriv (fun z : ℂ => iteratedDeriv n (gaussKern z) x) =ᶠ[𝓝 y]
        (fun z : ℂ => iteratedDeriv (n + 2) (gaussKern z) x + (1 / (2 * z)) * iteratedDeriv n (gaussKern z) x) := by
      filter_upwards [eventually_ne_nhds hy0] with z hz
      exact (hasDerivAt_iteratedDeriv_gaussKern_y n hz x).deriv
    rw [hev.deriv_eq, (gkHeat_second_formula n hy0 x).deriv]
    have hA4 : ‖iteratedDeriv (n + 2 + 2) (gaussKern y) x‖ ≤ B₄ * (1 + |x|) ^ (n + 4) := h₄ hre hy1 x
    have hB2 : ‖(1 : ℂ) / y * iteratedDeriv (n + 2) (gaussKern y) x‖ ≤ B₂ * (1 + |x|) ^ (n + 2) :=
      (norm_mul _ _).le.trans ((mul_le_of_le_one_left (norm_nonneg _) hi2).trans (h₂ hre hy1 x))
    have hC0 : ‖(1 : ℂ) / (4 * y ^ 2) * iteratedDeriv n (gaussKern y) x‖ ≤ B₀ * (1 + |x|) ^ n :=
      (norm_mul _ _).le.trans ((mul_le_of_le_one_left (norm_nonneg _) hi3).trans (h₀ hre hy1 x))
    have hP2 : (1 + |x|) ^ (n + 2) ≤ (1 + |x|) ^ (n + 4) := hPn _ _ (by omega)
    have hP0' : (1 + |x|) ^ n ≤ (1 + |x|) ^ (n + 4) := hPn _ _ (by omega)
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add hA4 hB2) hC0).trans ?_
    rw [add_mul, add_mul]
    nlinarith [mul_le_mul_of_nonneg_left hP2 hB₂.le, mul_le_mul_of_nonneg_left hP0' hB₀.le]

/-- info: 'FormalResearch.CohnElkies.norm_deriv_y_iteratedDeriv_gaussKern_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_deriv_y_iteratedDeriv_gaussKern_le

end FormalResearch.CohnElkies
