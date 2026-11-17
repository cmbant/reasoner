module

public import FormalResearch.Special.LatticeMain
public import FormalResearch.Special.BarnesVI

/-!
# The variance weight `h(s) = [4 cosh²(πs)]⁻¹` and its lattice integral

Ingredients of `lem:varcore` (`Weyl/free_fermion/paper/parts/constants.tex`):

* `hvar` is analytic on `|Im s| ≤ ¼` with `‖hvar s‖ ≤ 2 e^{-2π|Re s|}` there;
* on the real line `hvar x = wR (2x) = ν(2πx)(1 - ν(2πx))`, `ν(e) = (1+e^e)⁻¹`;
* `∫_ℝ h(s) G'(s)/π ds = (ℓ_Σ + ϰ(1+γ))/(2π²)`, from `lem:VI` (`integral_wR`, `integral_wR_mul_rhoR`)
  and the substitution `ξ = 2s`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

local notation "γ" => Real.eulerMascheroniConstant

/-- The Fermi function `ν(e) = (1 + e^e)⁻¹`. -/
noncomputable def nuR (e : ℝ) : ℝ := (1 + Real.exp e)⁻¹

/-- The complex variance weight `h(s) = 1/(4 cosh²(πs))`. -/
noncomputable def hvar (s : ℂ) : ℂ := 1 / (4 * Complex.cosh (Real.pi * s) ^ 2)

lemma norm_cosh_sq_ge {s : ℂ} (hs : |s.im| ≤ 1 / 4) :
    Real.cosh (Real.pi * s.re) ^ 2 / 2 ≤ ‖Complex.cosh (Real.pi * s)‖ ^ 2 := by
  have hpi := Real.pi_pos
  have h1 : ‖Complex.cosh (Real.pi * s)‖ ^ 2 =
      (Real.cosh (Real.pi * s.re) * Real.cos (Real.pi * s.im)) ^ 2 +
        (Real.sinh (Real.pi * s.re) * Real.sin (Real.pi * s.im)) ^ 2 := by
    have hz : (Real.pi : ℂ) * s = ((Real.pi * s.re : ℝ) : ℂ) + ((Real.pi * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hc : Complex.cosh (Real.pi * s) =
        ((Real.cosh (Real.pi * s.re) * Real.cos (Real.pi * s.im) : ℝ) : ℂ) +
          ((Real.sinh (Real.pi * s.re) * Real.sin (Real.pi * s.im) : ℝ) : ℂ) * Complex.I := by
      rw [hz, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
      push_cast
      try simp only [Complex.ofReal_cosh, Complex.ofReal_sinh, Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    rw [hc, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    ring
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (Real.pi * s.im) ^ 2 := by
    have habs : |Real.pi * s.im| ≤ Real.pi / 4 := by
      rw [abs_mul, abs_of_pos hpi]; nlinarith
    have hc : Real.cos (Real.pi / 4) ≤ Real.cos (Real.pi * s.im) := by
      rw [← Real.cos_abs (Real.pi * s.im)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
    have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    have := pow_le_pow_left₀ hs2 (h4 ▸ hc) 2
    have e : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    linarith
  rw [h1]
  have := sq_nonneg (Real.sinh (Real.pi * s.re) * Real.sin (Real.pi * s.im))
  have hc2 : (Real.cosh (Real.pi * s.re) * Real.cos (Real.pi * s.im)) ^ 2 =
      Real.cosh (Real.pi * s.re) ^ 2 * Real.cos (Real.pi * s.im) ^ 2 := by ring
  have hcc : 0 ≤ Real.cosh (Real.pi * s.re) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hcos hcc]

lemma cosh_ne_zero_strip {s : ℂ} (hs : |s.im| ≤ 1 / 4) : Complex.cosh (Real.pi * s) ≠ 0 := by
  intro h
  have := norm_cosh_sq_ge hs
  rw [h, norm_zero] at this
  have hc := Real.cosh_pos (Real.pi * s.re)
  nlinarith

lemma differentiableOn_hvar : DifferentiableOn ℂ hvar {s | |s.im| ≤ 1 / 4} := by
  intro s hs
  have hs' : |s.im| ≤ 1 / 4 := hs
  have hne := cosh_ne_zero_strip hs'
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold hvar
  have h1 : DifferentiableAt ℂ (fun s : ℂ => 4 * Complex.cosh (Real.pi * s) ^ 2) s := by fun_prop
  exact (differentiableAt_const _).div h1 (by simpa using hne)

lemma norm_hvar_le {s : ℂ} (hs : |s.im| ≤ 1 / 4) :
    ‖hvar s‖ ≤ 2 * Real.exp (-(2 * Real.pi) * |s.re|) := by
  have hpi := Real.pi_pos
  have h := norm_cosh_sq_ge hs
  have hne := cosh_ne_zero_strip hs
  have hcosh : Real.exp (Real.pi * |s.re|) / 2 ≤ Real.cosh (Real.pi * s.re) := by
    rw [← Real.cosh_abs, show Real.pi * |s.re| = |Real.pi * s.re| by
      rw [abs_mul, abs_of_pos hpi]]
    rw [Real.cosh_eq]
    have : 0 ≤ Real.exp (-|Real.pi * s.re|) := (Real.exp_pos _).le
    rw [show |Real.pi * s.re| = Real.pi * |s.re| by rw [abs_mul, abs_of_pos hpi]] at this ⊢
    linarith
  have hE : Real.exp (-(2 * Real.pi) * |s.re|) = (Real.exp (Real.pi * |s.re|))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold hvar
  rw [norm_div, norm_one, norm_mul, norm_pow]
  have hn : (‖(4 : ℂ)‖) = 4 := by simp
  rw [hn]
  have hE0 := Real.exp_pos (Real.pi * |s.re|)
  have hnorm : 0 < ‖Complex.cosh (Real.pi * s)‖ := norm_pos_iff.2 hne
  rw [hE, div_le_iff₀ (by positivity)]
  have h2 : Real.exp (Real.pi * |s.re|) ^ 2 / 4 ≤ ‖Complex.cosh (Real.pi * s)‖ ^ 2 * 2 := by
    have := pow_le_pow_left₀ (by positivity) hcosh 2
    nlinarith
  have h3 : (Real.exp (Real.pi * |s.re|))⁻¹ ^ 2 * Real.exp (Real.pi * |s.re|) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hE0.ne']; simp
  nlinarith

lemma hvar_real (x : ℝ) : hvar (x : ℂ) = ((wR (2 * x) : ℝ) : ℂ) := by
  unfold hvar wR
  have : (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_cosh]
  have e : Real.pi * (2 * x) / 2 = Real.pi * x := by ring
  rw [e]; push_cast; ring

lemma nuR_mul_one_sub (x : ℝ) : nuR (2 * Real.pi * x) * (1 - nuR (2 * Real.pi * x)) = wR (2 * x) := by
  unfold nuR wR
  have e : Real.pi * (2 * x) / 2 = Real.pi * x := by ring
  rw [e, Real.cosh_eq]
  have h1 : 0 < 1 + Real.exp (2 * Real.pi * x) := by positivity
  have h2 : Real.exp (2 * Real.pi * x) = Real.exp (Real.pi * x) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (-(Real.pi * x)) = (Real.exp (Real.pi * x))⁻¹ := Real.exp_neg _
  rw [h3, h2]
  have hE := Real.exp_pos (Real.pi * x)
  field_simp
  ring

lemma nuR_mem (e : ℝ) : 0 ≤ nuR e ∧ nuR e ≤ 1 := by
  unfold nuR
  have h : 1 ≤ 1 + Real.exp e := by linarith [Real.exp_pos e]
  exact ⟨by positivity, inv_le_one_of_one_le₀ h⟩

lemma integrable_wR : Integrable wR := by
  by_contra h
  have := integral_undef h
  rw [integral_wR] at this
  have : (1 : ℝ) / Real.pi ≠ 0 := by positivity
  contradiction

lemma integrable_wR_mul_rhoR : Integrable (fun x => wR x * rhoR x) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_wR_mul_rhoR] at h0
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hpi := Real.pi_pos
  have : -(1 + γ) / Real.pi < 0 := div_neg_of_neg_of_pos (by linarith) hpi
  linarith

lemma digamma_half_line (s : ℝ) : (digamma (1 / 2 + Complex.I * s)).re = rhoR (2 * s) := by
  unfold rhoR zOf
  congr 3
  push_cast; ring

/-- `∫_ℝ h(s) G'(s)/π ds = (ℓ_Σ + ϰ(1+γ))/(2π²)` (from `lem:VI`). -/
theorem integral_hvar_gdens (nc : ℕ) (ℓ : ℝ) :
    ∫ s : ℝ, hvar (s : ℂ) * ((gdens nc ℓ s : ℝ) : ℂ) =
      (((ℓ + nc * (1 + γ)) / (2 * Real.pi ^ 2) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have h1 : ∀ s : ℝ, hvar (s : ℂ) * ((gdens nc ℓ s : ℝ) : ℂ) =
      ((wR (2 * s) * ((ℓ - nc * rhoR (2 * s)) / Real.pi) : ℝ) : ℂ) := by
    intro s
    rw [hvar_real]; unfold gdens; rw [digamma_half_line]; push_cast; ring
  simp_rw [h1]
  rw [integral_complex_ofReal]
  congr 1
  have i1 : Integrable (fun s : ℝ => wR (2 * s)) := integrable_wR.comp_mul_left' (by norm_num)
  have i2 : Integrable (fun s : ℝ => wR (2 * s) * rhoR (2 * s)) :=
    integrable_wR_mul_rhoR.comp_mul_left' (by norm_num)
  have e : ∀ s : ℝ, wR (2 * s) * ((ℓ - nc * rhoR (2 * s)) / Real.pi) =
      ℓ / Real.pi * wR (2 * s) - nc / Real.pi * (wR (2 * s) * rhoR (2 * s)) := fun s => by ring
  simp_rw [e]
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left (fun x => wR x) 2,
    Measure.integral_comp_mul_left (fun x => wR x * rhoR x) 2, integral_wR, integral_wR_mul_rhoR]
  simp only [smul_eq_mul]
  rw [show |(2 : ℝ)⁻¹| = 1 / 2 by rw [abs_of_pos (by norm_num)]; norm_num]
  field_simp
  ring

lemma lipschitz_var {l v : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |l * (1 - l) - v * (1 - v)| ≤ |l - v| := by
  have e : l * (1 - l) - v * (1 - v) = (l - v) * (1 - l - v) := by ring
  rw [e, abs_mul]
  have : |1 - l - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc |l - v| * |1 - l - v| ≤ |l - v| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |l - v| := mul_one _

/-- **`lem:varcore` (i)** for the Gamma phase: `∑_r λ_r(1-λ_r) = (ℓ_Σ + ϰ(1+γ))/(2π²) + O(L^{-b₁} +
ϰ X log L ε_λ)`; the count of levels is kept explicit, `n ≤ 4ϰ X log L/π + 2`. -/
theorem varcore_gamma (nc : ℕ) (hnc : 1 ≤ nc) {b cs b1 Fm Fp : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hb1 : 0 < b1)
    (hb1b : b1 < b) (hb1δ : b1 < nc * (1 / 4)) (hFm : 0 < Fm) (hFmp : Fm ≤ Fp) :
    ∃ C L0 : ℝ, 0 < C ∧ 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      ∀ (lam : ℝ → ℝ) (epl : ℝ), 0 ≤ epl →
        (∀ x ∈ S, 0 ≤ lam x ∧ lam x ≤ 1 ∧ |lam x - nuR (2 * Real.pi * x)| ≤ epl) →
        |∑ x ∈ S, lam x * (1 - lam x) - (lsum nc L F + nc * (1 + γ)) / (2 * Real.pi ^ 2)| ≤
          C * L ^ (-b1) + (4 * nc * X * Real.log L / Real.pi + 2) * epl := by
  have hb1δ' : b1 < nc * min (1 / 4 : ℝ) (1 / 4) := by rwa [min_self]
  obtain ⟨C, L0, hC, hL0, H⟩ := latticesum_gamma nc hnc (b := b) (cs := cs) (δ := 1 / 4)
    (κ := 2 * Real.pi) (b1 := b1) (Fm := Fm) (Fp := Fp) hb hcs0 hcs (by norm_num)
    (by positivity) hb1 hb1b hb1δ' hFm hFmp
  refine ⟨2 * C, L0, by positivity, hL0, ?_⟩
  intro L hL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS lam epl hε hlam
  obtain ⟨ho, hii⟩ := H L hL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hsum := hii hvar 2 (by norm_num) differentiableOn_hvar
    (fun s hs => norm_hvar_le hs)
  rw [integral_hvar_gdens] at hsum
  have hS1 : ∑ x ∈ S, hvar (x : ℂ) = ((∑ x ∈ S, wR (2 * x) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun x _ => hvar_real x)
  rw [hS1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hsum
  -- replacing λ by ν
  have hrep : |∑ x ∈ S, lam x * (1 - lam x) - ∑ x ∈ S, wR (2 * x)| ≤ S.card * epl := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ S, |lam x * (1 - lam x) - wR (2 * x)| ≤ ∑ _x ∈ S, epl := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨h0, h1, h2⟩ := hlam x hx
          rw [← nuR_mul_one_sub x]
          exact (lipschitz_var h0 h1 (nuR_mem _).1 (nuR_mem _).2).trans h2
      _ = S.card * epl := by simp
  -- the count of levels
  have hcard : (S.card : ℝ) ≤ 4 * nc * X * Real.log L / Real.pi + 2 := by
    have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hX
    have h := ho.1 (-X) X (le_refl _) (by linarith) (le_refl _)
    have hfil : S.filter (fun x => x ∈ Icc (-X) X) = S :=
      Finset.filter_true_of_mem (fun x hx => ((hS x).1 hx).1)
    rw [hfil] at h
    calc (S.card : ℝ) ≤ _ := h
      _ = 4 * nc * X * Real.log L / Real.pi + 2 := by ring
  calc |∑ x ∈ S, lam x * (1 - lam x) - (lsum nc L F + nc * (1 + γ)) / (2 * Real.pi ^ 2)|
      ≤ |∑ x ∈ S, lam x * (1 - lam x) - ∑ x ∈ S, wR (2 * x)| +
        |∑ x ∈ S, wR (2 * x) - (lsum nc L F + nc * (1 + γ)) / (2 * Real.pi ^ 2)| := by
        have := abs_add_le (∑ x ∈ S, lam x * (1 - lam x) - ∑ x ∈ S, wR (2 * x))
          (∑ x ∈ S, wR (2 * x) - (lsum nc L F + nc * (1 + γ)) / (2 * Real.pi ^ 2))
        simpa using this
    _ ≤ S.card * epl + 2 * C * L ^ (-b1) := by
        have : |∑ x ∈ S, wR (2 * x) - (lsum nc L F + nc * (1 + γ)) / (2 * Real.pi ^ 2)| ≤
            2 * C * L ^ (-b1) := by simpa [mul_assoc, mul_comm, mul_left_comm] using hsum
        linarith
    _ ≤ 2 * C * L ^ (-b1) + (4 * nc * X * Real.log L / Real.pi + 2) * epl := by
        have := mul_le_mul_of_nonneg_right hcard hε
        linarith

/-- info: 'FormalResearch.Special.Lattice.varcore_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms varcore_gamma

end FormalResearch.Special.Lattice
