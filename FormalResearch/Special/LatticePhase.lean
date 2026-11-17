module

public import FormalResearch.Special.BarnesGrowth

/-!
# The phase `arg Γ(½ + is)` as an analytic function on the strip `|Im s| < ½`

Source: `Weyl/free_fermion/paper/parts/constants.tex`, proof of `lem:latticesum`: the function
`s ↦ arg Γ(½ + is) = (1/2i)[log Γ(½+is) - log Γ(½-is)]` is analytic in `|Im s| < ½` (poles of
`Γ(½ ± is)` at `s = ± i(½ + k)`), real and odd on the real axis, with derivative `Re ψ(½ + is)`.

Because the polar argument of `Γ(½+is)` winds around the origin as `s → ∞`, the principal `Complex.log`
cannot be used; we define the **continuous branch** with value `0` at `s = 0` by Gauss' series for `ψ`
(`Barnes.digamma_eq_series`):
`argGammaHalf s = -γ s + ∑_{k≥0} [ s/(k+1) - (1/2i)(log(k+½+is) - log(k+½-is)) ]`
(the bracket is `s/(k+1) - arctan(s/(k+½))` for real `s`; the principal logarithms are of numbers
with positive real part when `|Im s| < ½`).

* `hasDerivAt_argGammaHalf` : on `|Im s| < ½` the derivative is `(ψ(½+is)+ψ(½-is))/2`;
* `argGammaHalf_neg` (odd), `argGammaHalf_real` (real on `ℝ`), `argGammaHalf_deriv_real`
  (`= Re ψ(½+is)` for real `s`).

Not formalised here: identification of this branch with the polar argument of `Γ(½+is)` (see
`LatticePhaseGamma`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

local notation "γ" => Real.eulerMascheroniConstant

/-- The strip `|Im s| < ½`. -/
def halfStrip : Set ℂ := {s | |s.im| < 1 / 2}

lemma isOpen_halfStrip : IsOpen halfStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The `k`-th term of the series for the phase. -/
noncomputable def phTerm (k : ℕ) (s : ℂ) : ℂ :=
  s / ((k : ℂ) + 1) - (1 / (2 * I)) * (Complex.log ((k : ℂ) + 1 / 2 + I * s) -
    Complex.log ((k : ℂ) + 1 / 2 - I * s))

/-- The derivative of the `k`-th term. -/
noncomputable def phTermDeriv (k : ℕ) (s : ℂ) : ℂ :=
  1 / ((k : ℂ) + 1) - (1 / 2) * (1 / ((k : ℂ) + 1 / 2 + I * s) + 1 / ((k : ℂ) + 1 / 2 - I * s))

lemma phTerm_zero (k : ℕ) : phTerm k 0 = 0 := by simp [phTerm]

lemma re_add_I_mul {k : ℕ} {s : ℂ} : (((k : ℂ) + 1 / 2 + I * s)).re = (k : ℝ) + 1 / 2 - s.im := by
  simp [sub_eq_add_neg]

lemma re_sub_I_mul {k : ℕ} {s : ℂ} : (((k : ℂ) + 1 / 2 - I * s)).re = (k : ℝ) + 1 / 2 + s.im := by
  simp [sub_eq_add_neg]

lemma mem_slit_plus {k : ℕ} {s : ℂ} (hs : |s.im| < 1 / 2) :
    ((k : ℂ) + 1 / 2 + I * s) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  rw [re_add_I_mul]
  have := (abs_lt.mp hs).2
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma mem_slit_minus {k : ℕ} {s : ℂ} (hs : |s.im| < 1 / 2) :
    ((k : ℂ) + 1 / 2 - I * s) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  rw [re_sub_I_mul]
  have := (abs_lt.mp hs).1
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma hasDerivAt_phTerm (k : ℕ) {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt (phTerm k) (phTermDeriv k s) s := by
  have h1 : HasDerivAt (fun s : ℂ => (k : ℂ) + 1 / 2 + I * s) I s :=
    (((hasDerivAt_id s).const_mul I).const_add _).congr_deriv (by simp)
  have h2 : HasDerivAt (fun s : ℂ => (k : ℂ) + 1 / 2 - I * s) (-I) s :=
    (((hasDerivAt_id s).const_mul I).const_sub _).congr_deriv (by simp)
  have l1 := h1.clog (mem_slit_plus hs)
  have l2 := h2.clog (mem_slit_minus hs)
  have h0 : HasDerivAt (fun s : ℂ => s / ((k : ℂ) + 1)) (1 / ((k : ℂ) + 1)) s :=
    (hasDerivAt_id s).div_const _
  have h3 := h0.sub ((l1.sub l2).const_mul (1 / (2 * I)))
  refine (h3.congr_deriv ?_)
  unfold phTermDeriv
  have hI : I ≠ 0 := I_ne_zero
  have e1 := slitPlane_ne_zero (mem_slit_plus (k := k) hs)
  have e2 := slitPlane_ne_zero (mem_slit_minus (k := k) hs)
  field_simp
  ring

lemma norm_phTermDeriv_le {δ R : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ}
    (hs : |s.im| ≤ 1 / 2 - δ) (hsR : ‖s‖ ≤ R) (k : ℕ) :
    ‖phTermDeriv k s‖ ≤ (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hsR
  have hk1 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg hkp.le]
  have him := abs_le.mp hs
  -- generic bound for one of the two pieces
  have key : ∀ z : ℂ, δ * ((k : ℝ) + 1) ≤ z.re → ‖z - ((k : ℂ) + 1)‖ ≤ R + 1 / 2 →
      ‖1 / ((k : ℂ) + 1) - 1 / z‖ ≤ (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro z hz hzk
    have hzpos : 0 < z.re := lt_of_lt_of_le (by positivity) hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzpos; simp at hzpos
    have hk0' : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hzn : δ * ((k : ℝ) + 1) ≤ ‖z‖ := le_trans hz (Complex.re_le_norm _)
    have : 1 / ((k : ℂ) + 1) - 1 / z = (z - ((k : ℂ) + 1)) / (((k : ℂ) + 1) * z) := by
      field_simp
    rw [this, norm_div, norm_mul, hk1]
    calc ‖z - ((k : ℂ) + 1)‖ / (((k : ℝ) + 1) * ‖z‖)
        ≤ (R + 1) / (((k : ℝ) + 1) * (δ * ((k : ℝ) + 1))) := by
          refine div_le_div₀ (by linarith) (by linarith) (by positivity)
            (mul_le_mul_of_nonneg_left hzn hkp.le)
      _ = (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by field_simp
  have e1 : ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 + I * s)‖ ≤
      (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
    apply key
    · rw [re_add_I_mul]
      nlinarith [him.1, him.2]
    · have : ((k : ℂ) + 1 / 2 + I * s) - ((k : ℂ) + 1) = I * s - 1 / 2 := by ring
      rw [this]
      calc ‖I * s - 1 / 2‖ ≤ ‖I * s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 / 2 := by
          rw [norm_mul, Complex.norm_I, one_mul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          linarith
  have e2 : ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 - I * s)‖ ≤
      (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
    apply key
    · rw [re_sub_I_mul]
      nlinarith [him.1, him.2]
    · have : ((k : ℂ) + 1 / 2 - I * s) - ((k : ℂ) + 1) = -(I * s) - 1 / 2 := by ring
      rw [this]
      calc ‖-(I * s) - 1 / 2‖ ≤ ‖-(I * s)‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 / 2 := by
          rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          linarith
  have : phTermDeriv k s = (1 / 2) * ((1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 + I * s)) +
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 - I * s))) := by
    unfold phTermDeriv; ring
  rw [this, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h12]
  have := norm_add_le (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 + I * s))
    (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 / 2 - I * s))
  linarith

/-- The continuous branch of `arg Γ(½ + is)`, `argGammaHalf 0 = 0`. -/
noncomputable def argGammaHalf (s : ℂ) : ℂ := -(γ : ℂ) * s + ∑' k : ℕ, phTerm k s

/-- Termwise differentiation of the series on the strip. -/
theorem phase_series_calculus {s : ℂ} (hs : |s.im| < 1 / 2) :
    Summable (fun k : ℕ => phTerm k s) ∧
    HasDerivAt (fun w => ∑' k : ℕ, phTerm k w) (∑' k : ℕ, phTermDeriv k s) s := by
  set δ : ℝ := min (1 / 4) ((1 / 2 - |s.im|) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ (1 / 2 - |s.im|) / 2 := min_le_right _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
  set R : ℝ := ‖s‖ + 1
  set U : Set ℂ := {w | |w.im| < 1 / 2 - δ ∧ ‖w‖ < R}
  have hUo : IsOpen U := (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
    (isOpen_lt continuous_norm continuous_const)
  have hUc : Convex ℝ U := by
    have h1 : Convex ℝ {w : ℂ | |w.im| < 1 / 2 - δ} := by
      have : {w : ℂ | |w.im| < 1 / 2 - δ} = {w : ℂ | w.im ∈ Ioo (-(1 / 2 - δ)) (1 / 2 - δ)} := by
        ext w; simp [abs_lt]
      rw [this]
      exact (convex_Ioo _ _).linear_preimage Complex.imLm
    have : U = {w : ℂ | |w.im| < 1 / 2 - δ} ∩ Metric.ball 0 R := by ext w; simp [U]
    rw [this]; exact h1.inter (convex_ball _ _)
  have hzU : s ∈ U := ⟨by linarith, by simp [R]⟩
  have h0U : (0 : ℂ) ∈ U := ⟨by simp; linarith, by simp [R]; positivity⟩
  have hUs : ∀ w ∈ U, |w.im| < 1 / 2 := fun w hw => by have := hw.1; linarith
  have hsum : Summable (fun k : ℕ => (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2)) := by
    refine Summable.mul_left _ ?_
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hder : ∀ (k : ℕ), ∀ y ∈ U, HasDerivAt (phTerm k) (phTermDeriv k y) y :=
    fun k y hy => hasDerivAt_phTerm k (hUs y hy)
  have hbd : ∀ (k : ℕ), ∀ y ∈ U, ‖phTermDeriv k y‖ ≤ (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) :=
    fun k y hy => norm_phTermDeriv_le hδ0 hδ1 hy.1.le hy.2.le k
  have h0sum : Summable (fun k : ℕ => phTerm k 0) := by simp [phTerm_zero]
  exact ⟨summable_of_summable_hasDerivAt_of_isPreconnected hsum hUo hUc.isPreconnected hder hbd
      h0U h0sum hzU,
    hasDerivAt_tsum_of_isPreconnected hsum hUo hUc.isPreconnected hder hbd h0U h0sum hzU⟩

/-- The terms of the derivative series, in terms of Gauss' series for `ψ`. -/
lemma phTermDeriv_eq (k : ℕ) (s : ℂ) :
    phTermDeriv k s = (1 / 2) * ((1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 + I * s))) +
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 - I * s)))) := by
  unfold phTermDeriv; rw [show ((k : ℂ) + (1 / 2 - I * s)) = (k : ℂ) + 1 / 2 - I * s by ring,
    show ((k : ℂ) + (1 / 2 + I * s)) = (k : ℂ) + 1 / 2 + I * s by ring]; ring

theorem hasDerivAt_argGammaHalf {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt argGammaHalf ((digamma (1 / 2 + I * s) + digamma (1 / 2 - I * s)) / 2) s := by
  obtain ⟨hsm, hd⟩ := phase_series_calculus hs
  have h := (hasDerivAt_id s).const_mul (-(γ : ℂ)) |>.add hd
  refine h.congr_deriv ?_
  have hre1 : 0 < (1 / 2 + I * s).re := by
    have := (abs_lt.mp hs).2; simp; linarith
  have hre2 : 0 < (1 / 2 - I * s).re := by
    have := (abs_lt.mp hs).1; simp; linarith
  rw [digamma_eq_series hre1, digamma_eq_series hre2]
  have s1 : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 + I * s))) := by
    exact summable_psiTerm hre1.le
  have s2 : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 - I * s))) := by
    exact summable_psiTerm hre2.le
  simp_rw [phTermDeriv_eq]
  rw [tsum_mul_left, Summable.tsum_add s1 s2]
  simp
  ring
end FormalResearch.Special.Lattice
