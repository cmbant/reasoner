module

public import FormalResearch.CohnElkies.FiniteGaussianBase

/-!
# Laguerre Orthogonal Basis and Jacobi Matrix Spectral Bound

Pochhammer symbols, Laguerre integration by parts, orthonormalized `laguerreHat`,
three-term recurrence, tridiagonal Hermitian Jacobi matrix `jacobiMatrix`, and Rayleigh
spectral lower bound `lagMeasure_pos_radius_bound`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform Polynomial RealInnerProductSpace SchwartzMap Matrix

namespace FormalResearch.CohnElkies

/-! ### Section 6: Theorem E.3a — Sublinear-Degree Limitation (`thm:ce-laguerre-limit`, `(eq:finite:E.5c)`–`(eq:finite:E.5d)`) -/

/-- Rising Pochhammer product `∏_{i=0}^{n-1} (c + i)`. -/
noncomputable def poch (c : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (c + i)

/-- Real generalized binomial coefficient `\binom{m + c}{m}`. -/
noncomputable def laguerreBinom (m : ℕ) (c : ℝ) : ℝ := poch (c + 1) m / (m.factorial : ℝ)

lemma poch_zero (c : ℝ) : poch c 0 = 1 := by simp [poch]

lemma poch_succ_right (c : ℝ) (n : ℕ) : poch c (n + 1) = poch c n * (c + n) := by
  simp [poch, Finset.prod_range_succ]

lemma poch_succ_left (c : ℝ) (n : ℕ) : poch c (n + 1) = c * poch (c + 1) n := by
  simp only [poch, Finset.prod_range_succ', Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]; congr 1; refine Finset.prod_congr rfl fun i _ => by ring

lemma poch_pos {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 < poch c n := by
  unfold poch; exact Finset.prod_pos fun i _ => by positivity

lemma poch_pascal_sum (c : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), poch c n / (n.factorial : ℝ) = laguerreBinom m c := by
  induction m with
  | zero => simp [laguerreBinom, poch_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold laguerreBinom
    have hf : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h1 : poch (c + 1) m * (m + 1 : ℝ) + poch c (m + 1) = poch (c + 1) (m + 1) := by
      rw [poch_succ_left c m, poch_succ_right (c + 1) m]; ring
    rw [hf, div_add_div _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) (by positivity)]
    have hm_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    field_simp [hm_ne, (by positivity : ((m : ℝ) + 1) ≠ 0)]
    push_cast; linarith

lemma gamma_add_nat_eq_poch {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Real.Gamma (c + n) = poch c n * Real.Gamma c := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    push_cast
    rw [show c + ((n : ℝ) + 1) = (c + n) + 1 by ring, Real.Gamma_add_one (by positivity), ih,
      poch_succ_right]; ring

lemma laguerreBinom_pos {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 < laguerreBinom m c := by
  unfold laguerreBinom; exact div_pos (poch_pos (by linarith) m) (Nat.cast_pos.mpr (Nat.factorial_pos m))

/-- Adjoint differential operator `D_c Q = X Q' + (c - X) Q`. -/
noncomputable def laguerreOp (c : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  Polynomial.X * Polynomial.derivative Q + (Polynomial.C c - Polynomial.X) * Q

/-- Unnormalized Rodrigues Laguerre polynomials `n! L_n^{(c - 1)}`. -/
noncomputable def laguerrePoly (c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => laguerreOp c (laguerrePoly (c + 1) n)

private lemma laguerreOp_natDegree_le (c : ℝ) (Q : ℝ[X]) :
    (laguerreOp c Q).natDegree ≤ Q.natDegree + 1 := by
  unfold laguerreOp
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_mul_le).trans ?_
    exact (add_le_add Polynomial.natDegree_X_le (Polynomial.natDegree_derivative_le Q)).trans (by omega)
  · refine (Polynomial.natDegree_mul_le).trans (add_le_add
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)) le_rfl |>.trans (by omega))

private lemma laguerrePoly_natDegree_le (c : ℝ) (n : ℕ) : (laguerrePoly c n).natDegree ≤ n := by
  induction n generalizing c with
  | zero => simp [laguerrePoly]
  | succ n ih => exact (laguerreOp_natDegree_le c _).trans (Nat.add_le_add_right (ih (c + 1)) 1)

private lemma laguerrePoly_coeff_top (c : ℝ) (n : ℕ) :
    (laguerrePoly c n).coeff n = (-1 : ℝ) ^ n := by
  induction n generalizing c with
  | zero => simp [laguerrePoly]
  | succ n ih =>
    unfold laguerrePoly laguerreOp
    have hdeg := laguerrePoly_natDegree_le (c + 1) n
    have hz : (laguerrePoly (c + 1) n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hzd : (Polynomial.derivative (laguerrePoly (c + 1) n)).coeff n = 0 := by
      rw [Polynomial.coeff_derivative, hz]; ring
    simp only [sub_mul, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, hzd, hz, mul_zero, zero_add, ih (c + 1), zero_sub]
    ring

private lemma laguerrePoly_coeff_sub (c : ℝ) (n : ℕ) :
    (laguerrePoly c (n + 1)).coeff n = (-1 : ℝ) ^ n * (((n + 1 : ℝ) * (c + n))) := by
  induction n generalizing c with
  | zero => simp [laguerrePoly, laguerreOp]
  | succ n ih =>
    unfold laguerrePoly laguerreOp
    have htop := laguerrePoly_coeff_top (c + 1) (n + 1)
    have hsub := ih (c + 1)
    simp only [sub_mul, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_derivative, htop, hsub]
    push_cast; ring

private lemma laguerrePoly_eval_zero (c : ℝ) (n : ℕ) : (laguerrePoly c n).eval 0 = poch c n := by
  induction n generalizing c with
  | zero => simp [laguerrePoly, poch_zero]
  | succ n ih =>
    simp [laguerrePoly, laguerreOp, ih (c + 1), poch_succ_left]

private lemma integrableOn_poly_gamma {c : ℝ} (hc : 0 < c) (P : ℝ[X]) :
    IntegrableOn (fun s : ℝ => P.eval s * (s ^ (c - 1) * Real.exp (-s))) (Ioi 0) := by
  have hsum : ∀ S : Finset ℕ,
      IntegrableOn (fun s : ℝ => ∑ k ∈ S, P.coeff k * (Real.exp (-s) * s ^ (c + (k : ℝ) - 1))) (Ioi 0) := by
    intro S; induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact integrableOn_zero
    | @insert a S ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact ((Real.GammaIntegral_convergent (by positivity : 0 < c + (a : ℝ))).const_mul _).add ih
  refine (hsum P.support).congr_fun (fun s hs => ?_) measurableSet_Ioi
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsp : 0 < s := hs
  calc P.coeff k * (Real.exp (-s) * s ^ (c + (k : ℝ) - 1))
      = P.coeff k * (Real.exp (-s) * (s ^ (c - 1) * s ^ (k : ℝ))) := by
          rw [show c + (k : ℝ) - 1 = (c - 1) + (k : ℝ) by ring, Real.rpow_add hsp]
    _ = P.coeff k * s ^ k * (s ^ (c - 1) * Real.exp (-s)) := by
          rw [Real.rpow_natCast s k]; ring

/-- Laguerre probability-weighted expectation `∫_0^∞ P(s) s^{c-1} e^{-s} ds / Γ(c)`. -/
noncomputable def lagMeasure (c : ℝ) (P : ℝ[X]) : ℝ :=
  ∫ s in Ioi (0 : ℝ), P.eval s * (s ^ (c - 1) * Real.exp (-s)) / Real.Gamma c

/-- Inner product `⟨P, Q⟩_{μ_c}` on `ℝ[X]`. -/
noncomputable def lagInner (c : ℝ) (P Q : ℝ[X]) : ℝ := lagMeasure c (P * Q)

lemma lagInner_comm (c : ℝ) (P Q : ℝ[X]) : lagInner c P Q = lagInner c Q P := by
  simp [lagInner, mul_comm]

lemma lagInner_add_left (c : ℝ) {hc : 0 < c} (P₁ P₂ Q : ℝ[X]) :
    lagInner c (P₁ + P₂) Q = lagInner c P₁ Q + lagInner c P₂ Q := by
  unfold lagInner lagMeasure
  have hi1 := (integrableOn_poly_gamma hc (P₁ * Q)).div_const (Real.Gamma c)
  have hi2 := (integrableOn_poly_gamma hc (P₂ * Q)).div_const (Real.Gamma c)
  rw [← integral_add hi1 hi2]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul]; ring

lemma lagInner_smul_left (c : ℝ) (a : ℝ) (P Q : ℝ[X]) :
    lagInner c (a • P) Q = a * lagInner c P Q := by
  unfold lagInner lagMeasure
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_smul, smul_eq_mul]; ring

private lemma lagInner_sub_left (c : ℝ) {hc : 0 < c} (P₁ P₂ Q : ℝ[X]) :
    lagInner c (P₁ - P₂) Q = lagInner c P₁ Q - lagInner c P₂ Q := by
  rw [sub_eq_add_neg, lagInner_add_left c (hc := hc), ← neg_one_smul ℝ P₂,
    lagInner_smul_left]; ring

private lemma lagInner_add_right (c : ℝ) {hc : 0 < c} (P Q₁ Q₂ : ℝ[X]) :
    lagInner c P (Q₁ + Q₂) = lagInner c P Q₁ + lagInner c P Q₂ := by
  rw [lagInner_comm, lagInner_add_left c (hc := hc), lagInner_comm c P Q₁, lagInner_comm c P Q₂]

private lemma lagInner_smul_right (c : ℝ) (a : ℝ) (P Q : ℝ[X]) :
    lagInner c P (a • Q) = a * lagInner c P Q := by
  rw [lagInner_comm, lagInner_smul_left, lagInner_comm]

private lemma lagInner_sub_right (c : ℝ) {hc : 0 < c} (P Q₁ Q₂ : ℝ[X]) :
    lagInner c P (Q₁ - Q₂) = lagInner c P Q₁ - lagInner c P Q₂ := by
  rw [lagInner_comm, lagInner_sub_left c (hc := hc), lagInner_comm c P Q₁, lagInner_comm c P Q₂]

lemma lagInner_sum_left {ι : Type*} (s : Finset ι) (c : ℝ) {hc : 0 < c}
    (f : ι → ℝ[X]) (Q : ℝ[X]) :
    lagInner c (∑ i ∈ s, f i) Q = ∑ i ∈ s, lagInner c (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lagInner, lagMeasure]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lagInner_add_left c (hc := hc), ih]

private lemma lagMeasure_const_one {c : ℝ} (hc : 0 < c) : lagMeasure c 1 = 1 := by
  unfold lagMeasure
  rw [integral_div]
  simp only [Polynomial.eval_one, one_mul]
  rw [show (∫ s in Ioi (0 : ℝ), s ^ (c - 1) * Real.exp (-s)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ (c - 1) by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => mul_comm _ _,
    ← Real.Gamma_eq_integral hc, div_self (Real.Gamma_pos_of_pos hc).ne']

private lemma laguerreOp_ibp {c : ℝ} (hc : 0 < c) (P Q : ℝ[X]) :
    ∫ s in Ioi (0 : ℝ), P.eval s * (laguerreOp c Q).eval s * (s ^ (c - 1) * Real.exp (-s)) =
      - ∫ s in Ioi (0 : ℝ), (Polynomial.derivative P).eval s * Q.eval s * (s ^ c * Real.exp (-s)) := by
  let u : ℝ → ℝ := fun s => P.eval s
  let u' : ℝ → ℝ := fun s => (Polynomial.derivative P).eval s
  let v : ℝ → ℝ := fun s => s ^ c * Real.exp (-s) * Q.eval s
  let v' : ℝ → ℝ := fun s => (laguerreOp c Q).eval s * (s ^ (c - 1) * Real.exp (-s))
  have hu : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt u (u' s) s := fun s _ => P.hasDerivAt s
  have hv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt v (v' s) s := fun s hs => by
    have hsp : 0 < s := hs
    have hrpow : HasDerivAt (fun x : ℝ => x ^ c) (1 * c * s ^ (c - 1)) s :=
      (hasDerivAt_id s).rpow_const (p := c) (Or.inl hsp.ne')
    have hd := (hrpow.mul (hasDerivAt_id s).neg.exp).mul (Q.hasDerivAt s)
    refine hd.congr_deriv ?_
    have hsc : s ^ c = s * s ^ (c - 1) := by
      conv_lhs => rw [show c = 1 + (c - 1) by ring, Real.rpow_add hsp, Real.rpow_one]
    dsimp [v', laguerreOp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_C, hsc]
    ring
  have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
    refine (integrableOn_poly_gamma hc (P * laguerreOp c Q)).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [u, v', Polynomial.eval_mul, mul_assoc]
  have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
    refine (integrableOn_poly_gamma (by positivity : 0 < c + 1)
      (Polynomial.derivative P * Q)).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [u', v, Polynomial.eval_mul]; ring
  have h_zero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun s : ℝ => P.eval s * (s ^ c * Real.exp (-s) * Q.eval s))
        (𝓝[>] 0) (𝓝 (P.eval 0 * ((0 : ℝ) ^ c * Real.exp (-0) * Q.eval 0))) :=
      (P.continuous.continuousWithinAt).mul
        ((((Real.continuous_rpow_const hc.le).continuousWithinAt).mul
          (Real.continuous_exp.comp continuous_neg).continuousWithinAt).mul
            Q.continuous.continuousWithinAt)
    rw [Real.zero_rpow hc.ne'] at hlim
    change Tendsto (fun s => u s * v s) (𝓝[>] 0) (𝓝 0)
    simpa [u, v] using hlim
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hev : (fun s => (u * v) s) =ᶠ[atTop]
        fun s => ∑ k ∈ (P * Q).support, (P * Q).coeff k * (s ^ (c + (k : ℝ)) * Real.exp (-s)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      dsimp [u, v]
      rw [show P.eval s * (s ^ c * Real.exp (-s) * Q.eval s) =
          (P * Q).eval s * (s ^ c * Real.exp (-s)) by simp [Polynomial.eval_mul]; ring,
        Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases eq_or_lt_of_le hs with rfl | hsp
      · by_cases hk : k = 0
        · subst hk; simp
        · simp [zero_pow hk, Real.zero_rpow (by positivity : c + (k : ℝ) ≠ 0)]
      · rw [← Real.rpow_natCast s k]; calc
          (P * Q).coeff k * s ^ (k : ℝ) * (s ^ c * Real.exp (-s))
              = (P * Q).coeff k * (s ^ c * s ^ (k : ℝ) * Real.exp (-s)) := by ring
            _ = (P * Q).coeff k * (s ^ (c + (k : ℝ)) * Real.exp (-s)) := by
                  rw [← Real.rpow_add hsp]
    refine Tendsto.congr' hev.symm ?_
    have hsum0 := tendsto_finsetSum (P * Q).support fun k _ =>
      (tendsto_const_nhds (x := (P * Q).coeff k)).mul (by
        simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c + (k : ℝ)) 1 one_pos)
    simpa using hsum0
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [sub_self, zero_sub] at hibp
  convert hibp using 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    dsimp [u, v']; ring
  · congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    dsimp [u', v]; ring

private lemma integral_poly_mul_laguerrePoly {c : ℝ} (hc : 0 < c) (n : ℕ) (P : ℝ[X]) :
    ∫ s in Ioi (0 : ℝ), P.eval s * (laguerrePoly c n).eval s * (s ^ (c - 1) * Real.exp (-s)) =
      (-1 : ℝ) ^ n * ∫ s in Ioi (0 : ℝ),
        ((Polynomial.derivative^[n] P).eval s) * (s ^ (c + n - 1) * Real.exp (-s)) := by
  induction n generalizing c P with
  | zero => simp [laguerrePoly]
  | succ n ih =>
    unfold laguerrePoly
    rw [laguerreOp_ibp hc P (laguerrePoly (c + 1) n)]
    simp_rw [show ∀ s : ℝ, s ^ c = s ^ ((c + 1) - 1) from fun s => by simp]
    have hstep := ih (by positivity : 0 < c + 1) (Polynomial.derivative P)
    rw [hstep, Function.iterate_succ_apply]
    push_cast
    rw [show c + 1 + (n : ℝ) - 1 = c + ((n : ℝ) + 1) - 1 by ring]
    ring

private lemma iterate_derivative_eq_C_mul (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    Polynomial.derivative^[n] P = Polynomial.C ((n.factorial : ℝ) * P.coeff n) := by
  induction n generalizing P with
  | zero => simpa using Polynomial.eq_C_of_natDegree_le_zero hP
  | succ n ih =>
    rw [Function.iterate_succ_apply,
      ih (Polynomial.derivative P) ((Polynomial.natDegree_derivative_le P).trans (by omega)),
      Polynomial.coeff_derivative, Nat.factorial_succ]
    push_cast; ring_nf

private lemma lagInner_laguerrePoly_lt {c : ℝ} (hc : 0 < c) {m n : ℕ} (hmn : m < n) :
    lagInner c (laguerrePoly c m) (laguerrePoly c n) = 0 := by
  unfold lagInner lagMeasure
  rw [integral_div]
  have hp : ∫ s in Ioi (0 : ℝ), (laguerrePoly c m * laguerrePoly c n).eval s *
      (s ^ (c - 1) * Real.exp (-s)) = 0 := by
    have hcongr : (∫ s in Ioi (0 : ℝ), (laguerrePoly c m * laguerrePoly c n).eval s *
        (s ^ (c - 1) * Real.exp (-s))) =
        ∫ s in Ioi (0 : ℝ), (laguerrePoly c m).eval s * (laguerrePoly c n).eval s *
          (s ^ (c - 1) * Real.exp (-s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp [Polynomial.eval_mul]
    rw [hcongr, integral_poly_mul_laguerrePoly hc n (laguerrePoly c m)]
    have hd : Polynomial.derivative^[n] (laguerrePoly c m) = 0 := by
      rw [iterate_derivative_eq_C_mul n _ ((laguerrePoly_natDegree_le c m).trans hmn.le),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((laguerrePoly_natDegree_le c m).trans_lt hmn),
        mul_zero, map_zero]
    simp [hd]
  rw [hp, zero_div]

private lemma lagInner_laguerrePoly_self {c : ℝ} (hc : 0 < c) (n : ℕ) :
    lagInner c (laguerrePoly c n) (laguerrePoly c n) = (n.factorial : ℝ) * poch c n := by
  unfold lagInner lagMeasure
  rw [integral_div]
  have hcongr : (∫ s in Ioi (0 : ℝ), (laguerrePoly c n * laguerrePoly c n).eval s *
      (s ^ (c - 1) * Real.exp (-s))) =
      ∫ s in Ioi (0 : ℝ), (laguerrePoly c n).eval s * (laguerrePoly c n).eval s *
        (s ^ (c - 1) * Real.exp (-s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp [Polynomial.eval_mul]
  rw [hcongr, integral_poly_mul_laguerrePoly hc n (laguerrePoly c n),
    iterate_derivative_eq_C_mul n _ (laguerrePoly_natDegree_le c n), laguerrePoly_coeff_top]
  simp only [Polynomial.eval_C]
  rw [show (∫ s in Ioi (0 : ℝ), (n.factorial : ℝ) * (-1 : ℝ) ^ n * (s ^ (c + (n : ℝ) - 1) * Real.exp (-s))) =
      ((n.factorial : ℝ) * (-1 : ℝ) ^ n) * ∫ s in Ioi (0 : ℝ), s ^ (c + (n : ℝ) - 1) * Real.exp (-s) by
    exact integral_const_mul _ _,
    show (∫ s in Ioi (0 : ℝ), s ^ (c + (n : ℝ) - 1) * Real.exp (-s)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ ((c + n) - 1) by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => mul_comm _ _,
    ← Real.Gamma_eq_integral (by positivity : 0 < c + n), gamma_add_nat_eq_poch hc n]
  have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc (-1 : ℝ) ^ n * (((n.factorial : ℝ) * (-1 : ℝ) ^ n) * (poch c n * Real.Gamma c)) / Real.Gamma c
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * ((n.factorial : ℝ) * poch c n) *
          (Real.Gamma c / Real.Gamma c) := by ring
    _ = (n.factorial : ℝ) * poch c n := by rw [hsq, div_self (Real.Gamma_pos_of_pos hc).ne']; ring

/-- Orthonormalized Laguerre polynomials `φ_n = (-1)^n L̃_n^{(c-1)}` wrt `μ_c`. -/
noncomputable def laguerreHat (c : ℝ) (n : ℕ) : ℝ[X] :=
  ((-1 : ℝ) ^ n / Real.sqrt ((n.factorial : ℝ) * poch c n)) • laguerrePoly c n

private lemma laguerreHat_natDegree_le (c : ℝ) (n : ℕ) : (laguerreHat c n).natDegree ≤ n :=
  (Polynomial.natDegree_smul_le _ _).trans (laguerrePoly_natDegree_le c n)

private lemma laguerreHat_coeff_top {c : ℝ} (_hc : 0 < c) (n : ℕ) :
    (laguerreHat c n).coeff n = 1 / Real.sqrt ((n.factorial : ℝ) * poch c n) := by
  unfold laguerreHat
  rw [Polynomial.coeff_smul, smul_eq_mul, laguerrePoly_coeff_top]
  have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc ((-1 : ℝ) ^ n / Real.sqrt ((n.factorial : ℝ) * poch c n)) * (-1 : ℝ) ^ n
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) / Real.sqrt ((n.factorial : ℝ) * poch c n) := by ring
    _ = _ := by rw [hsq]

private lemma laguerreHat_coeff_top_ne_zero {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (laguerreHat c n).coeff n ≠ 0 := by
  rw [laguerreHat_coeff_top hc]
  exact div_ne_zero one_ne_zero (Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    (poch_pos hc n))).ne'

lemma laguerreHat_eval_zero {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (laguerreHat c n).eval 0 = (-1 : ℝ) ^ n * Real.sqrt (poch c n / (n.factorial : ℝ)) := by
  unfold laguerreHat
  rw [Polynomial.eval_smul, smul_eq_mul, laguerrePoly_eval_zero]
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hp : 0 < poch c n := poch_pos hc n
  rw [Real.sqrt_mul hf.le, Real.sqrt_div hp.le]
  have h1 : Real.sqrt (poch c n) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have h2 : Real.sqrt (n.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
  calc ((-1 : ℝ) ^ n / (Real.sqrt (n.factorial : ℝ) * Real.sqrt (poch c n))) * poch c n
      = (-1 : ℝ) ^ n * ((Real.sqrt (poch c n) * Real.sqrt (poch c n)) /
          (Real.sqrt (n.factorial : ℝ) * Real.sqrt (poch c n))) := by
            rw [Real.mul_self_sqrt hp.le]; ring
    _ = (-1 : ℝ) ^ n * (Real.sqrt (poch c n) / Real.sqrt (n.factorial : ℝ)) := by
          field_simp [h1, h2]

private lemma lagInner_laguerreHat_eq {c : ℝ} (hc : 0 < c) (m n : ℕ) :
    lagInner c (laguerreHat c m) (laguerreHat c n) = if m = n then 1 else 0 := by
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · simp only [hlt.ne, ↓reduceIte]
    unfold laguerreHat
    rw [lagInner_smul_left, lagInner_smul_right, lagInner_laguerrePoly_lt hc hlt]; ring
  · simp only [↓reduceIte]
    unfold laguerreHat
    rw [lagInner_smul_left, lagInner_smul_right, lagInner_laguerrePoly_self hc m]
    have hnorm : (0 : ℝ) < (m.factorial : ℝ) * poch c m :=
      mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) (poch_pos hc m)
    have hsq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
    calc ((-1 : ℝ) ^ m / Real.sqrt ((m.factorial : ℝ) * poch c m)) *
          (((-1 : ℝ) ^ m / Real.sqrt ((m.factorial : ℝ) * poch c m)) * ((m.factorial : ℝ) * poch c m))
        = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * ((m.factorial : ℝ) * poch c m /
            (Real.sqrt ((m.factorial : ℝ) * poch c m) * Real.sqrt ((m.factorial : ℝ) * poch c m))) := by ring
      _ = 1 := by rw [hsq, Real.mul_self_sqrt hnorm.le, div_self hnorm.ne']; ring
  · simp only [hgt.ne', ↓reduceIte]
    unfold laguerreHat
    rw [lagInner_smul_left, lagInner_smul_right, lagInner_comm c (laguerrePoly c m) (laguerrePoly c n),
      lagInner_laguerrePoly_lt hc hgt]; ring

private lemma lagInner_eq_zero_of_lt {c : ℝ} (hc : 0 < c) {P : ℝ[X]} {n : ℕ}
    (hP : P.natDegree < n) : lagInner c P (laguerreHat c n) = 0 := by
  rw [laguerreHat, lagInner_smul_right]
  have hp : lagInner c P (laguerrePoly c n) = 0 := by
    unfold lagInner lagMeasure
    rw [integral_div]
    have hcongr : (∫ s in Ioi (0 : ℝ), (P * laguerrePoly c n).eval s *
        (s ^ (c - 1) * Real.exp (-s))) =
        ∫ s in Ioi (0 : ℝ), P.eval s * (laguerrePoly c n).eval s *
          (s ^ (c - 1) * Real.exp (-s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp [Polynomial.eval_mul]
    rw [hcongr, integral_poly_mul_laguerrePoly hc n P]
    have hd : Polynomial.derivative^[n] P = 0 := by
      rw [iterate_derivative_eq_C_mul n _ hP.le, Polynomial.coeff_eq_zero_of_natDegree_lt hP,
        mul_zero, map_zero]
    simp [hd]
  rw [hp, mul_zero]

private lemma lagInner_orthogonal_vanish {c : ℝ} (hc : 0 < c) :
    ∀ (N : ℕ) (P : ℝ[X]), P.natDegree ≤ N →
      (∀ k ≤ N, lagInner c P (laguerreHat c k) = 0) → P = 0 := by
  intro N
  induction N with
  | zero =>
    intro P hP h0
    have hc0 : lagInner c P (laguerreHat c 0) = P.coeff 0 := by
      have hL0 : laguerreHat c 0 = 1 := by
        unfold laguerreHat laguerrePoly; simp [poch_zero]
      have hPc := Polynomial.eq_C_of_natDegree_le_zero hP
      conv_lhs => rw [hPc, hL0,
        show Polynomial.C (P.coeff 0) = P.coeff 0 • (1 : ℝ[X]) by simp [Algebra.smul_def]]
      rw [lagInner_smul_left]
      have h1 : lagInner c 1 1 = 1 := by simpa [lagInner] using lagMeasure_const_one hc
      rw [h1, mul_one]
    rw [Polynomial.eq_C_of_natDegree_le_zero hP, ← hc0, h0 0 le_rfl, map_zero]
  | succ N ih =>
    intro P hP h0
    let α : ℝ := P.coeff (N + 1) / (laguerreHat c (N + 1)).coeff (N + 1)
    let Q : ℝ[X] := P - α • laguerreHat c (N + 1)
    have hQ_coeff : Q.coeff (N + 1) = 0 := by
      dsimp [Q, α]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ (laguerreHat_coeff_top_ne_zero hc (N + 1)), sub_self]
    have hQ_deg : Q.natDegree ≤ N := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with h_eq | h_gt
      · rw [← h_eq, hQ_coeff]
      · have hle : Q.natDegree ≤ N + 1 :=
          (Polynomial.natDegree_sub_le _ _).trans
            (max_le hP ((Polynomial.natDegree_smul_le _ _).trans (laguerreHat_natDegree_le c (N + 1))))
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (hle.trans_lt (by omega))
    have hQ_orth : ∀ k ≤ N, lagInner c Q (laguerreHat c k) = 0 := fun k hk => by
      dsimp [Q]
      rw [lagInner_sub_left c (hc := hc), lagInner_smul_left, h0 k (by omega),
        lagInner_laguerreHat_eq hc (N + 1) k]
      simp [show N + 1 ≠ k by omega]
    have hQ0 : Q = 0 := ih Q hQ_deg hQ_orth
    have hP_eq : P = α • laguerreHat c (N + 1) := sub_eq_zero.mp hQ0
    have hα : α = 0 := by
      have h1 := h0 (N + 1) le_rfl
      rw [hP_eq, lagInner_smul_left, lagInner_laguerreHat_eq hc] at h1
      simpa using h1
    rw [hP_eq, hα, zero_smul]

lemma poly_expand_laguerreHat {c : ℝ} (hc : 0 < c) {N : ℕ} {P : ℝ[X]}
    (hP : P.natDegree ≤ N) :
    P = ∑ n ∈ Finset.range (N + 1), lagInner c P (laguerreHat c n) • laguerreHat c n := by
  let R : ℝ[X] := P - ∑ n ∈ Finset.range (N + 1), lagInner c P (laguerreHat c n) • laguerreHat c n
  have hR_deg : R.natDegree ≤ N := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hP ?_)
    exact (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun n hn =>
      (Polynomial.natDegree_smul_le _ _).trans
        ((laguerreHat_natDegree_le c n).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))))
  have hR_orth : ∀ k ≤ N, lagInner c R (laguerreHat c k) = 0 := fun k hk => by
    dsimp [R]
    rw [lagInner_sub_left c (hc := hc), lagInner_sum_left _ c (hc := hc)]
    have hsum : (∑ n ∈ Finset.range (N + 1),
        lagInner c (lagInner c P (laguerreHat c n) • laguerreHat c n) (laguerreHat c k)) =
        lagInner c P (laguerreHat c k) := by
      rw [Finset.sum_eq_single k]
      · rw [lagInner_smul_left, lagInner_laguerreHat_eq hc k k]; simp
      · intro n _ hnk
        rw [lagInner_smul_left, lagInner_laguerreHat_eq hc n k]; simp [hnk]
      · intro hk_mem; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk_mem
    rw [hsum, sub_self]
  exact (sub_eq_zero.mp (lagInner_orthogonal_vanish hc N R hR_deg hR_orth))

noncomputable def jacobiOff (c : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + c))

private lemma sqrt_norm_succ {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Real.sqrt (((k + 1).factorial : ℝ) * poch c (k + 1)) =
      jacobiOff c k * Real.sqrt ((k.factorial : ℝ) * poch c k) := by
  have h1 : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) + c) := by positivity
  have h2 : 0 ≤ (k.factorial : ℝ) * poch c k :=
    mul_nonneg (Nat.cast_nonneg _) (poch_pos hc k).le
  rw [Nat.factorial_succ, Nat.cast_mul, poch_succ_right,
    show ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) * (poch c k * (c + k)) =
      (((k : ℝ) + 1) * ((k : ℝ) + c)) * ((k.factorial : ℝ) * poch c k) by push_cast; ring,
    Real.sqrt_mul h1, jacobiOff]

private lemma laguerreHat_three_term {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Polynomial.X * laguerreHat c n =
      jacobiOff c n • laguerreHat c (n + 1) + (2 * (n : ℝ) + c) • laguerreHat c n +
        (if 0 < n then jacobiOff c (n - 1) • laguerreHat c (n - 1) else 0) := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_add, lt_self_iff_false, ↓reduceIte, add_zero]
    have h0 : laguerreHat c 0 = 1 := by unfold laguerreHat laguerrePoly; simp [poch_zero]
    have h1 : laguerreHat c 1 = (-(1 : ℝ) / Real.sqrt c) • (Polynomial.C c - Polynomial.X) := by
      unfold laguerreHat laguerrePoly laguerreOp
      simp [poch_zero, poch_succ_right, laguerrePoly]
    rw [h0, h1, mul_one]
    have hsc : jacobiOff c 0 = Real.sqrt c := by unfold jacobiOff; simp
    rw [hsc, smul_smul, show Real.sqrt c * (-1 / Real.sqrt c) = -1 by
      field_simp [(Real.sqrt_pos.mpr hc).ne']]
    ext k; simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul,
      Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one]
    split_ifs <;> ring
  | succ n =>
    simp only [Nat.succ_pos', ↓reduceIte, Nat.add_sub_cancel]
    let RHS : ℝ[X] :=
      jacobiOff c (n + 1) • laguerreHat c (n + 2) +
        (2 * ((n + 1 : ℕ) : ℝ) + c) • laguerreHat c (n + 1) +
        jacobiOff c n • laguerreHat c n
    let D : ℝ[X] := Polynomial.X * laguerreHat c (n + 1) - RHS
    have hdeg_X : (Polynomial.X * laguerreHat c (n + 1)).natDegree ≤ n + 2 :=
      (Polynomial.natDegree_mul_le).trans ((add_le_add Polynomial.natDegree_X_le
        (laguerreHat_natDegree_le c (n + 1))).trans (by omega))
    have hdeg_R : RHS.natDegree ≤ n + 2 := by
      dsimp [RHS]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans (max_le
          ((Polynomial.natDegree_smul_le _ _).trans (laguerreHat_natDegree_le c (n + 2)))
          ((Polynomial.natDegree_smul_le _ _).trans ((laguerreHat_natDegree_le c (n + 1)).trans (by omega)))))
        ((Polynomial.natDegree_smul_le _ _).trans ((laguerreHat_natDegree_le c n).trans (by omega))))
    have hdeg_D2 : D.natDegree ≤ n + 2 := (Polynomial.natDegree_sub_le _ _).trans (max_le hdeg_X hdeg_R)
    have hnorm_pos : ∀ k : ℕ, 0 < (k.factorial : ℝ) * poch c k := fun k =>
      mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) (poch_pos hc k)
    have hcoeff_sub : ∀ k : ℕ, (laguerreHat c (k + 1)).coeff k =
        -((k : ℝ) + 1) * ((k : ℝ) + c) / Real.sqrt (((k + 1).factorial : ℝ) * poch c (k + 1)) := fun k => by
      unfold laguerreHat
      rw [Polynomial.coeff_smul, smul_eq_mul, laguerrePoly_coeff_sub]
      have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
        rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
      calc ((-1 : ℝ) ^ (k + 1) / Real.sqrt (((k + 1).factorial : ℝ) * poch c (k + 1))) *
            ((-1 : ℝ) ^ k * (((k : ℝ) + 1) * (c + k)))
          = ((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k) * (((k : ℝ) + 1) * ((k : ℝ) + c)) /
              Real.sqrt (((k + 1).factorial : ℝ) * poch c (k + 1)) := by ring
        _ = _ := by rw [hsign]; ring
    have hD_n2 : D.coeff (n + 2) = 0 := by
      dsimp [D, RHS]
      have hLn1_n2 : (laguerreHat c (n + 1)).coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt ((laguerreHat_natDegree_le c (n + 1)).trans_lt (by omega))
      have hLn_n2 : (laguerreHat c n).coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt ((laguerreHat_natDegree_le c n).trans_lt (by omega))
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_add,
        Polynomial.coeff_smul, smul_eq_mul, hLn1_n2, hLn_n2, mul_zero, add_zero]
      rw [laguerreHat_coeff_top hc (n + 1), laguerreHat_coeff_top hc (n + 2), sqrt_norm_succ hc (n + 1)]
      have hs1 : jacobiOff c (n + 1) ≠ 0 := by unfold jacobiOff; positivity
      have hs2 : Real.sqrt (((n + 1).factorial : ℝ) * poch c (n + 1)) ≠ 0 :=
        (Real.sqrt_pos.mpr (hnorm_pos (n + 1))).ne'
      field_simp [hs1, hs2]; ring
    have hD_n1 : D.coeff (n + 1) = 0 := by
      dsimp [D, RHS]
      have hLn_n1 : (laguerreHat c n).coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt ((laguerreHat_natDegree_le c n).trans_lt (by omega))
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_add,
        Polynomial.coeff_smul, smul_eq_mul, hLn_n1, mul_zero, add_zero]
      rw [hcoeff_sub n, hcoeff_sub (n + 1), laguerreHat_coeff_top hc (n + 1), sqrt_norm_succ hc (n + 1)]
      have hsq : jacobiOff c (n + 1) * jacobiOff c (n + 1) =
          (((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + c) := by
        unfold jacobiOff; exact Real.mul_self_sqrt (by positivity)
      have hs1 : jacobiOff c (n + 1) ≠ 0 := by unfold jacobiOff; positivity
      have hs2 : Real.sqrt (((n + 1).factorial : ℝ) * poch c (n + 1)) ≠ 0 :=
        (Real.sqrt_pos.mpr (hnorm_pos (n + 1))).ne'
      field_simp [hs1, hs2]
      push_cast at hsq ⊢
      nlinarith [hsq]
    have hD_deg : D.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with h1 | hk'
      · rw [← h1]; exact hD_n1
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk') with h2 | _
        · rw [← h2]; exact hD_n2
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg_D2.trans_lt (by omega))
    have hD_orth : ∀ k ≤ n, lagInner c D (laguerreHat c k) = 0 := fun k hk => by
      dsimp [D, RHS]
      rw [lagInner_sub_left c (hc := hc), lagInner_add_left c (hc := hc),
        lagInner_add_left c (hc := hc), lagInner_smul_left, lagInner_smul_left, lagInner_smul_left,
        lagInner_laguerreHat_eq hc (n + 2) k, lagInner_laguerreHat_eq hc (n + 1) k,
        lagInner_laguerreHat_eq hc n k]
      simp only [show ¬(n + 2 = k) by omega, show ¬(n + 1 = k) by omega, ↓reduceIte, mul_zero,
        zero_add]
      have hX_comm : lagInner c (Polynomial.X * laguerreHat c (n + 1)) (laguerreHat c k) =
          lagInner c (Polynomial.X * laguerreHat c k) (laguerreHat c (n + 1)) := by
        simp [lagInner, mul_assoc, mul_left_comm, mul_comm]
      rw [hX_comm]
      rcases lt_or_eq_of_le hk with hlt | rfl
      · have hdegk : (Polynomial.X * laguerreHat c k).natDegree < n + 1 :=
          ((Polynomial.natDegree_mul_le).trans
            (add_le_add Polynomial.natDegree_X_le (laguerreHat_natDegree_le c k))).trans_lt
            (by omega)
        rw [lagInner_eq_zero_of_lt hc hdegk]
        simp only [hlt.ne.symm, ↓reduceIte, mul_zero, sub_zero]
      · simp only [↓reduceIte, mul_one]
        let Qk : ℝ[X] := Polynomial.X * laguerreHat c k - jacobiOff c k • laguerreHat c (k + 1)
        have hQk_deg : Qk.natDegree < k + 1 := by
          have hdeg_Xk : (Polynomial.X * laguerreHat c k).natDegree ≤ k + 1 :=
            (Polynomial.natDegree_mul_le).trans ((add_le_add Polynomial.natDegree_X_le
              (laguerreHat_natDegree_le c k)).trans (by omega))
          have hdeg_Qk1 : Qk.natDegree ≤ k + 1 := (Polynomial.natDegree_sub_le _ _).trans
            (max_le hdeg_Xk ((Polynomial.natDegree_smul_le _ _).trans
              (laguerreHat_natDegree_le c (k + 1))))
          have hcoeff_top : Qk.coeff (k + 1) = 0 := by
            dsimp [Qk]
            simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_smul, smul_eq_mul]
            rw [laguerreHat_coeff_top hc k, laguerreHat_coeff_top hc (k + 1), sqrt_norm_succ hc k]
            have hs1 : jacobiOff c k ≠ 0 := by unfold jacobiOff; positivity
            have hs2 : Real.sqrt ((k.factorial : ℝ) * poch c k) ≠ 0 :=
              (Real.sqrt_pos.mpr (hnorm_pos k)).ne'
            field_simp [hs1, hs2]; ring
          rw [← Nat.le_iff_lt_add_one, Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro j hj
          rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with h1 | _
          · rw [← h1]; exact hcoeff_top
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg_Qk1.trans_lt (by omega))
        have hQ_orth : lagInner c Qk (laguerreHat c (k + 1)) = 0 :=
          lagInner_eq_zero_of_lt hc hQk_deg
        dsimp [Qk] at hQ_orth
        rw [lagInner_sub_left c (hc := hc), lagInner_smul_left,
          lagInner_laguerreHat_eq hc (k + 1) (k + 1)] at hQ_orth
        simp only [↓reduceIte, mul_one, sub_eq_zero] at hQ_orth
        rw [hQ_orth]; ring
    exact sub_eq_zero.mp (lagInner_orthogonal_vanish hc n D hD_deg hD_orth)

/-- Symmetric tridiagonal Jacobi matrix `J_{m+1}` of size `(m+1) × (m+1)`. -/
noncomputable def jacobiMatrix (c : ℝ) (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    if i = j then 2 * (i : ℝ) + c
    else if (i : ℕ) + 1 = (j : ℕ) then jacobiOff c i
    else if (j : ℕ) + 1 = (i : ℕ) then jacobiOff c j
    else 0

private lemma jacobiMatrix_isHermitian (c : ℝ) (m : ℕ) : (jacobiMatrix c m).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, jacobiMatrix]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte]
    by_cases h1 : (j : ℕ) + 1 = (i : ℕ)
    · have h2 : ¬((i : ℕ) + 1 = (j : ℕ)) := by omega
      simp [h1, h2]
    · by_cases h2 : (i : ℕ) + 1 = (j : ℕ)
      · simp [h1, h2]
      · simp [h1, h2]

private lemma laguerreHat_mul_X_eq_col {c : ℝ} (hc : 0 < c) (m : ℕ) (i : Fin (m + 1)) :
    Polynomial.X * laguerreHat c i =
      (∑ j : Fin (m + 1), jacobiMatrix c m j i • laguerreHat c j) +
        (if (i : ℕ) = m then jacobiOff c m • laguerreHat c (m + 1) else 0) := by
  have h3 := laguerreHat_three_term hc i.val
  have hsum : (∑ j : Fin (m + 1), jacobiMatrix c m j i • laguerreHat c j) =
      (if _h : (i : ℕ) + 1 ≤ m then jacobiOff c i • laguerreHat c (i + 1) else 0) +
        (2 * (i : ℝ) + c) • laguerreHat c i +
        (if 0 < (i : ℕ) then jacobiOff c (i - 1) • laguerreHat c (i - 1) else 0) := by
    have hdiag : ∀ j : Fin (m + 1), jacobiMatrix c m j i • laguerreHat c j =
        (if j = i then (2 * (i : ℝ) + c) • laguerreHat c i else 0) +
        (if (j : ℕ) = (i : ℕ) + 1 then jacobiOff c i • laguerreHat c (i + 1) else 0) +
        (if (j : ℕ) + 1 = (i : ℕ) then jacobiOff c (i - 1) • laguerreHat c (i - 1) else 0) := by
      intro j
      rcases eq_or_ne j i with rfl | hji
      · simp [jacobiMatrix]
      · by_cases hup : (j : ℕ) = (i : ℕ) + 1
        · have hdn : ¬((j : ℕ) + 1 = (i : ℕ)) := by omega
          have hval : jacobiMatrix c m j i = jacobiOff c i := by
            simp only [jacobiMatrix, hji, hdn, hup.symm, ↓reduceIte]
          have hne1 : ¬((i : ℕ) + 1 + 1 = (i : ℕ)) := by omega
          simp only [hval, hji, hup, hne1, ↓reduceIte, add_zero, zero_add]
        · by_cases hdn : (j : ℕ) + 1 = (i : ℕ)
          · have hsub : (j : ℕ) = (i : ℕ) - 1 := by omega
            have hval : jacobiMatrix c m j i = jacobiOff c (i - 1) := by
              have h1 : jacobiMatrix c m j i = jacobiOff c j := by
                simp only [jacobiMatrix, hji, hdn, ↓reduceIte]
              rw [h1, hsub]
            have hne2 : ¬((i : ℕ) - 1 = (i : ℕ) + 1) := by omega
            have heq3 : (i : ℕ) - 1 + 1 = (i : ℕ) := by omega
            simp only [hval, hji, hsub, hne2, heq3, ↓reduceIte, zero_add]
          · have hn2 : ¬((i : ℕ) + 1 = (j : ℕ)) := fun h => hup h.symm
            have hval : jacobiMatrix c m j i = 0 := by
              simp only [jacobiMatrix, hji, hdn, hn2, ↓reduceIte]
            simp only [hval, zero_smul, hji, hup, hdn, ↓reduceIte, add_zero]
    simp_rw [hdiag, Finset.sum_add_distrib]
    have s1 : (∑ j : Fin (m + 1), if j = i then (2 * (i : ℝ) + c) • laguerreHat c i else 0) =
        (2 * (i : ℝ) + c) • laguerreHat c i := by simp
    have s2 : (∑ j : Fin (m + 1), if (j : ℕ) = (i : ℕ) + 1 then
          jacobiOff c i • laguerreHat c (i + 1) else 0) =
        if _h : (i : ℕ) + 1 ≤ m then jacobiOff c i • laguerreHat c (i + 1) else 0 := by
      by_cases hi : (i : ℕ) + 1 ≤ m
      · simp only [hi, ↓reduceDIte]
        rw [Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
        · simp
        · intro j _ hj; simp only [show (j : ℕ) ≠ (i : ℕ) + 1 from fun h => hj (Fin.ext h), ↓reduceIte]
        · intro hm'; exact absurd (Finset.mem_univ _) hm'
      · simp only [hi, ↓reduceDIte]
        exact Finset.sum_eq_zero fun j _ => by simp only [show (j : ℕ) ≠ (i : ℕ) + 1 by omega, ↓reduceIte]
    have s3 : (∑ j : Fin (m + 1), if (j : ℕ) + 1 = (i : ℕ) then
          jacobiOff c (i - 1) • laguerreHat c (i - 1) else 0) =
        if 0 < (i : ℕ) then jacobiOff c (i - 1) • laguerreHat c (i - 1) else 0 := by
      by_cases hi0 : 0 < (i : ℕ)
      · simp only [hi0, ↓reduceIte]
        rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · simp [Nat.sub_add_cancel hi0]
        · intro j _ hj
          simp only [show (j : ℕ) + 1 ≠ (i : ℕ) from fun h => hj (Fin.ext (by simp; omega)), ↓reduceIte]
        · intro hm'; exact absurd (Finset.mem_univ _) hm'
      · simp only [hi0, ↓reduceIte]
        exact Finset.sum_eq_zero fun j _ => by simp only [show (j : ℕ) + 1 ≠ (i : ℕ) by omega, ↓reduceIte]
    rw [s1, s2, s3, add_comm ((if _h : (i : ℕ) + 1 ≤ m then _ else _) + _),
      ← add_assoc, add_comm (_ + _)]
    abel
  rw [h3, hsum]
  by_cases him : (i : ℕ) = m
  · rw [him]
    simp only [show ¬(m + 1 ≤ m) by omega, ↓reduceDIte, ↓reduceIte]; abel
  · have hi_lt : (i : ℕ) + 1 ≤ m := by omega
    simp only [hi_lt, ↓reduceDIte, him, ↓reduceIte, add_zero]

private lemma jacobi_pow_basis_expansion {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∀ k : ℕ, k ≤ m →
      (∀ i : Fin (m + 1), k < (i : ℕ) →
        ((jacobiMatrix c m ^ k) *ᵥ Pi.single 0 1) i = 0) ∧
      Polynomial.X ^ k =
        ∑ i : Fin (m + 1), ((jacobiMatrix c m ^ k) *ᵥ Pi.single 0 1) i • laguerreHat c i := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi0 : i ≠ 0 := fun h => by subst h; simp at hi
      simp only [pow_zero, Matrix.one_mulVec, Pi.single_apply, hi0, ↓reduceIte]
    · simp only [pow_zero, Matrix.one_mulVec]
      rw [Finset.sum_eq_single 0]
      · simp [laguerreHat, laguerrePoly, poch_zero]
      · intro i _ hi0; simp [Pi.single_eq_of_ne hi0]
      · intro h0; exact absurd (Finset.mem_univ _) h0
  | succ k ih =>
    intro hk
    obtain ⟨ih_supp, ih_poly⟩ := ih (Nat.le_of_succ_le hk)
    let u : Fin (m + 1) → ℝ := (jacobiMatrix c m ^ k) *ᵥ Pi.single 0 1
    have hu_succ : ((jacobiMatrix c m ^ (k + 1)) *ᵥ Pi.single 0 1) = jacobiMatrix c m *ᵥ u := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hu_succ, Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hjk : k < (j : ℕ)
      · dsimp [u]; rw [ih_supp j hjk, mul_zero]
      · have hj_le : (j : ℕ) ≤ k := Nat.le_of_not_lt hjk
        have hij : ¬(i = j) ∧ ¬((i : ℕ) + 1 = (j : ℕ)) ∧ ¬((j : ℕ) + 1 = (i : ℕ)) :=
          ⟨fun h => by omega, by omega, by omega⟩
        simp [jacobiMatrix, hij.1, hij.2.1, hij.2.2]
    · calc Polynomial.X ^ (k + 1)
          = Polynomial.X * Polynomial.X ^ k := by ring
        _ = Polynomial.X * ∑ i : Fin (m + 1), u i • laguerreHat c i := by rw [ih_poly]
        _ = ∑ i : Fin (m + 1), u i • (Polynomial.X * laguerreHat c i) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
              rw [mul_smul_comm]
        _ = ∑ i : Fin (m + 1), u i • ∑ j : Fin (m + 1), jacobiMatrix c m j i • laguerreHat c j := by
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases him : (i : ℕ) = m
              · dsimp [u]; rw [ih_supp i (by omega), zero_smul, zero_smul]
              · rw [laguerreHat_mul_X_eq_col hc m i]
                simp only [him, ↓reduceIte, add_zero]
        _ = ∑ j : Fin (m + 1), (∑ i : Fin (m + 1), jacobiMatrix c m j i * u i) • laguerreHat c j := by
              simp_rw [Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_smul]
              refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
        _ = ∑ j : Fin (m + 1), (jacobiMatrix c m *ᵥ u) j • laguerreHat c j := rfl
        _ = _ := by rw [hu_succ]

lemma lagMeasure_pow_eq_jacobi {c : ℝ} (hc : 0 < c) (m : ℕ) {k : ℕ} (hk : k ≤ 2 * m + 1) :
    lagMeasure c (Polynomial.X ^ k) =
      Pi.single (0 : Fin (m + 1)) (1 : ℝ) ⬝ᵥ ((jacobiMatrix c m ^ k) *ᵥ Pi.single 0 1) := by
  let e₀ : Fin (m + 1) → ℝ := Pi.single 0 1
  let J := jacobiMatrix c m
  have hJ_sym : Jᵀ = J := (jacobiMatrix_isHermitian c m).isSymm
  have hpow_sym : ∀ n : ℕ, (J ^ n)ᵀ = J ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      calc (J ^ (n + 1))ᵀ = (J ^ n * J)ᵀ := by rw [pow_succ]
        _ = Jᵀ * (J ^ n)ᵀ := Matrix.transpose_mul _ _
        _ = J * J ^ n := by rw [hJ_sym, ih]
        _ = J ^ (n + 1) := (pow_succ' J n).symm
  have hdot_pow : ∀ a b : ℕ, (J ^ a *ᵥ e₀) ⬝ᵥ (J ^ b *ᵥ e₀) = e₀ ⬝ᵥ (J ^ (a + b) *ᵥ e₀) :=
    fun a b => by
      have h1 := Matrix.dotProduct_transpose_mulVec (J ^ a) e₀ (J ^ b *ᵥ e₀)
      rw [hpow_sym a] at h1
      rw [dotProduct_comm, ← h1, Matrix.mulVec_mulVec, ← pow_add]
  have hdot_pair : ∀ u v : Fin (m + 1) → ℝ,
      lagInner c (∑ i, u i • laguerreHat c i) (∑ j, v j • laguerreHat c j) = u ⬝ᵥ v := fun u v => by
    rw [lagInner_sum_left _ c (hc := hc)]
    simp_rw [lagInner_comm c _ (∑ j, v j • laguerreHat c j), lagInner_sum_left _ c (hc := hc),
      lagInner_smul_left, lagInner_smul_right, lagInner_laguerreHat_eq hc]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [↓reduceIte, mul_one]; ring
    · intro j _ hji
      simp only [show (j : ℕ) ≠ (i : ℕ) from fun h => hji (Fin.ext h), ↓reduceIte, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ _) hi
  rcases le_or_gt k (2 * m) with hk2m | hk2m1
  · let a : ℕ := min k m
    let b : ℕ := k - a
    have ha : a ≤ m := min_le_right _ _
    have hb : b ≤ m := by omega
    have hab : a + b = k := by omega
    rw [← hab, pow_add, show lagMeasure c (Polynomial.X ^ a * Polynomial.X ^ b) =
        lagInner c (Polynomial.X ^ a) (Polynomial.X ^ b) by rfl,
      (jacobi_pow_basis_expansion hc m a ha).2, (jacobi_pow_basis_expansion hc m b hb).2,
      hdot_pair, hdot_pow, hab]
  · have hkeq : k = 2 * m + 1 := by omega
    subst hkeq
    rw [show Polynomial.X ^ (2 * m + 1) = (Polynomial.X * Polynomial.X ^ m) * Polynomial.X ^ m by ring,
      show lagMeasure c ((Polynomial.X * Polynomial.X ^ m) * Polynomial.X ^ m) =
        lagInner c (Polynomial.X * Polynomial.X ^ m) (Polynomial.X ^ m) by rfl]
    let u := J ^ m *ᵥ e₀
    have hm_exp := (jacobi_pow_basis_expansion hc m m le_rfl).2
    have hX_exp : Polynomial.X * Polynomial.X ^ m =
        (∑ j : Fin (m + 1), (J *ᵥ u) j • laguerreHat c j) +
          (u ⟨m, Nat.lt_succ_self m⟩ * jacobiOff c m) • laguerreHat c (m + 1) := by
      calc Polynomial.X * Polynomial.X ^ m
          = Polynomial.X * ∑ i : Fin (m + 1), u i • laguerreHat c i := by rw [hm_exp]
        _ = ∑ i : Fin (m + 1), u i • (Polynomial.X * laguerreHat c i) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
              rw [mul_smul_comm]
        _ = ∑ i : Fin (m + 1), (u i • ∑ j : Fin (m + 1), J j i • laguerreHat c j +
              u i • (if (i : ℕ) = m then jacobiOff c m • laguerreHat c (m + 1) else 0)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [laguerreHat_mul_X_eq_col hc m i, smul_add]
        _ = (∑ i : Fin (m + 1), u i • ∑ j : Fin (m + 1), J j i • laguerreHat c j) +
              (u ⟨m, Nat.lt_succ_self m⟩ * jacobiOff c m) • laguerreHat c (m + 1) := by
              rw [Finset.sum_add_distrib]; congr 1
              rw [Finset.sum_eq_single ⟨m, Nat.lt_succ_self m⟩]
              · simp [smul_smul]
              · intro i _ him
                simp only [show (i : ℕ) ≠ m from fun h => him (Fin.ext h), ↓reduceIte, smul_zero]
              · intro hm'; exact absurd (Finset.mem_univ _) hm'
        _ = _ := by
              congr 1; simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
              simp only [Matrix.mulVec, dotProduct]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_smul]
              refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    rw [hX_exp, lagInner_add_left c (hc := hc), hm_exp, lagInner_smul_left]
    have horth : lagInner c (laguerreHat c (m + 1)) (∑ i : Fin (m + 1), u i • laguerreHat c i) = 0 := by
      rw [lagInner_comm, lagInner_sum_left _ c (hc := hc)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [lagInner_smul_left, lagInner_laguerreHat_eq hc i.val (m + 1)]
      simp only [show i.val ≠ m + 1 by omega, ↓reduceIte, mul_zero]
    rw [horth, mul_zero, add_zero, hdot_pair]
    dsimp [u]
    calc (J *ᵥ (J ^ m *ᵥ e₀)) ⬝ᵥ (J ^ m *ᵥ e₀)
        = ((J ^ (m + 1)) *ᵥ e₀) ⬝ᵥ (J ^ m *ᵥ e₀) := by rw [Matrix.mulVec_mulVec, ← pow_succ']
      _ = e₀ ⬝ᵥ ((J ^ (m + 1 + m)) *ᵥ e₀) := hdot_pow (m + 1) m
      _ = Pi.single (0 : Fin (m + 1)) (1 : ℝ) ⬝ᵥ ((jacobiMatrix c m ^ (2 * m + 1)) *ᵥ Pi.single 0 1) := by
            congr 3; omega

private lemma aeval_mulVec_eigenvector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) (s : ℝ) (hv : M *ᵥ v = s • v) (P : ℝ[X]) :
    (Polynomial.aeval M P) *ᵥ v = P.eval s • v := by
  induction P using Polynomial.induction_on with
  | C a =>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add p q ihp ihq =>
    simp [map_add, Matrix.add_mulVec, ihp, ihq, add_smul]
  | monomial n a ih =>
    have hp : Polynomial.C a * Polynomial.X ^ (n + 1) =
        (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    calc (Polynomial.aeval M (Polynomial.C a * Polynomial.X ^ (n + 1))) *ᵥ v
        = (Polynomial.aeval M ((Polynomial.C a * Polynomial.X ^ n) * Polynomial.X)) *ᵥ v := by rw [hp]
      _ = (Polynomial.aeval M (Polynomial.C a * Polynomial.X ^ n)) *ᵥ (M *ᵥ v) := by
            rw [map_mul, Polynomial.aeval_X, Matrix.mulVec_mulVec]
      _ = (s * Polynomial.eval s (Polynomial.C a * Polynomial.X ^ n)) • v := by
            rw [hv, Matrix.mulVec_smul, ih, smul_smul]
      _ = Polynomial.eval s (Polynomial.C a * Polynomial.X ^ (n + 1)) • v := by
            congr 1; simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
              Polynomial.eval_pow]; ring

private lemma jacobi_rayleigh_ge (c : ℝ) (hc : 0 ≤ c) (m : ℕ) (v : Fin (m + 1) → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    c - 2 * Real.sqrt ((m : ℝ) * ((m : ℝ) + c - 1)) ≤ v ⬝ᵥ (jacobiMatrix c m *ᵥ v) := by
  have hquad : v ⬝ᵥ (jacobiMatrix c m *ᵥ v) =
      (∑ i : Fin (m + 1), (2 * (i : ℝ) + c) * v i ^ 2) +
        2 * ∑ k : Fin m, jacobiOff c k * (v k.castSucc * v k.succ) := by
    let J := jacobiMatrix c m
    have hsplit : ∀ i j : Fin (m + 1), v i * (J i j * v j) =
        (if i = j then (2 * (i : ℝ) + c) * v i ^ 2 else 0) +
        (if (i : ℕ) + 1 = (j : ℕ) then jacobiOff c i * (v i * v j) else 0) +
        (if (j : ℕ) + 1 = (i : ℕ) then jacobiOff c j * (v i * v j) else 0) := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · simp [J, jacobiMatrix]; ring
      · by_cases h1 : (i : ℕ) + 1 = (j : ℕ)
        · have h2 : ¬((j : ℕ) + 1 = (i : ℕ)) := by omega
          simp [J, jacobiMatrix, hij, h1, h2]; ring
        · by_cases h2 : (j : ℕ) + 1 = (i : ℕ)
          · simp [J, jacobiMatrix, hij, h1, h2]; ring
          · simp [J, jacobiMatrix, hij, h1, h2]
    calc v ⬝ᵥ (J *ᵥ v)
        = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), v i * (J i j * v j) := by
            simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = (∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i = j then (2 * (i : ℝ) + c) * v i ^ 2 else 0) +
          (∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if (i : ℕ) + 1 = (j : ℕ) then jacobiOff c i * (v i * v j) else 0) +
          (∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if (j : ℕ) + 1 = (i : ℕ) then jacobiOff c j * (v i * v j) else 0) := by
            simp_rw [hsplit, Finset.sum_add_distrib]
      _ = (∑ i : Fin (m + 1), (2 * (i : ℝ) + c) * v i ^ 2) +
          2 * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            if (i : ℕ) + 1 = (j : ℕ) then jacobiOff c i * (v i * v j) else 0 := by
            have h1 : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
                if i = j then (2 * (i : ℝ) + c) * v i ^ 2 else 0) =
                ∑ i : Fin (m + 1), (2 * (i : ℝ) + c) * v i ^ 2 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_ite_eq Finset.univ i (fun _ => (2 * (i : ℝ) + c) * v i ^ 2)]
              simp
            have h2 : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
                if (j : ℕ) + 1 = (i : ℕ) then jacobiOff c j * (v i * v j) else 0) =
                ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
                  if (i : ℕ) + 1 = (j : ℕ) then jacobiOff c i * (v i * v j) else 0 := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
              split_ifs <;> ring
            rw [h1, h2]; ring
      _ = _ := by
            congr 2; rw [Fin.sum_univ_castSucc]
            have hlast : (∑ j : Fin (m + 1),
                if (Fin.last m : ℕ) + 1 = (j : ℕ) then jacobiOff c (Fin.last m) * (v (Fin.last m) * v j) else 0) = 0 :=
              Finset.sum_eq_zero fun j _ => by
                simp only [show (Fin.last m : ℕ) + 1 ≠ (j : ℕ) by simp; omega, ↓reduceIte]
            rw [hlast, add_zero]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_eq_single k.succ]
            · simp
            · intro j _ hj
              have hne : (k.castSucc : ℕ) + 1 ≠ (j : ℕ) := fun h => hj (Fin.ext (by simp at h; simp [h]))
              simp only [hne, ↓reduceIte]
            · intro hk'; exact absurd (Finset.mem_univ _) hk'
  have hdiag_ge : c ≤ ∑ i : Fin (m + 1), (2 * (i : ℝ) + c) * v i ^ 2 := by
    calc c = ∑ i : Fin (m + 1), c * v i ^ 2 := by
            rw [← Finset.mul_sum]; have : ∑ i : Fin (m + 1), v i ^ 2 = 1 := by
              simpa [dotProduct, sq] using hv
            rw [this, mul_one]
      _ ≤ ∑ i : Fin (m + 1), (2 * (i : ℝ) + c) * v i ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]) (sq_nonneg _)
  let B : ℝ := Real.sqrt ((m : ℝ) * ((m : ℝ) + c - 1))
  have hoff_ge : -2 * B ≤ 2 * ∑ k : Fin m, jacobiOff c k * (v k.castSucc * v k.succ) := by
    have hterm : ∀ k : Fin m, -B * (v k.castSucc ^ 2 + v k.succ ^ 2) ≤
        2 * (jacobiOff c k * (v k.castSucc * v k.succ)) := fun k => by
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun hm0 => Fin.elim0 (hm0 ▸ k)
      have hk_le : (k : ℕ) + 1 ≤ m := k.isLt
      have hk_b : jacobiOff c k ≤ B := by
        unfold jacobiOff; dsimp [B]
        refine Real.sqrt_le_sqrt ?_
        have hk_real : ((k : ℝ) + 1) ≤ m := by exact_mod_cast hk_le
        have hkc_le : (k : ℝ) + c ≤ (m : ℝ) + c - 1 := by linarith
        exact mul_le_mul hk_real hkc_le (by positivity) (by positivity)
      have hjb : 0 ≤ jacobiOff c k := Real.sqrt_nonneg _
      have hab : -(2 * (v k.castSucc * v k.succ)) ≤ v k.castSucc ^ 2 + v k.succ ^ 2 := by
        nlinarith [sq_nonneg (v k.castSucc + v k.succ)]
      calc -B * (v k.castSucc ^ 2 + v k.succ ^ 2)
          ≤ -(jacobiOff c k * (v k.castSucc ^ 2 + v k.succ ^ 2)) := by
            nlinarith [sq_nonneg (v k.castSucc), sq_nonneg (v k.succ)]
        _ ≤ -(jacobiOff c k * (-(2 * (v k.castSucc * v k.succ)))) := by
            nlinarith [mul_le_mul_of_nonneg_left hab hjb]
        _ = 2 * (jacobiOff c k * (v k.castSucc * v k.succ)) := by ring
    have hsum_v : ∑ k : Fin m, (v k.castSucc ^ 2 + v k.succ ^ 2) ≤ 2 := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ k : Fin m, v k.castSucc ^ 2 ≤ ∑ i : Fin (m + 1), v i ^ 2 := by
        rw [Fin.sum_univ_castSucc]; linarith [sq_nonneg (v (Fin.last m))]
      have h2 : ∑ k : Fin m, v k.succ ^ 2 ≤ ∑ i : Fin (m + 1), v i ^ 2 := by
        rw [Fin.sum_univ_succ]; linarith [sq_nonneg (v 0)]
      have hv1 : ∑ i : Fin (m + 1), v i ^ 2 = 1 := by simpa [dotProduct, sq] using hv
      linarith
    calc -2 * B
        = -B * 2 := by ring
      _ ≤ -B * ∑ k : Fin m, (v k.castSucc ^ 2 + v k.succ ^ 2) := by
          exact mul_le_mul_of_nonpos_left hsum_v (neg_nonpos.mpr (Real.sqrt_nonneg _))
      _ = ∑ k : Fin m, (-B * (v k.castSucc ^ 2 + v k.succ ^ 2)) := by rw [Finset.mul_sum]
      _ ≤ ∑ k : Fin m, (2 * (jacobiOff c k * (v k.castSucc * v k.succ))) := Finset.sum_le_sum fun k _ => hterm k
      _ = 2 * ∑ k : Fin m, jacobiOff c k * (v k.castSucc * v k.succ) := by rw [← Finset.mul_sum]
  linarith

lemma lagMeasure_pos_radius_bound {c : ℝ} (hc : 0 < c) (m : ℕ) {P : ℝ[X]}
    (hP_deg : P.natDegree ≤ 2 * m + 1) (hP_pos : 0 < lagMeasure c P)
    {R : ℝ} (hP_nonpos : ∀ s : ℝ, R ≤ s → P.eval s ≤ 0) :
    c - 2 * Real.sqrt ((m : ℝ) * ((m : ℝ) + c - 1)) < R := by
  let J := jacobiMatrix c m
  have hJ := jacobiMatrix_isHermitian c m
  let e₀ : Fin (m + 1) → ℝ := Pi.single 0 1
  let E₀ : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 e₀
  have hquad : lagMeasure c P = e₀ ⬝ᵥ ((Polynomial.aeval J P) *ᵥ e₀) := by
    have hPsum : P = ∑ k ∈ Finset.range (2 * m + 2), P.coeff k • Polynomial.X ^ k := by
      ext j
      rw [Polynomial.finsetSum_coeff]
      by_cases hj : j < 2 * m + 2
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj; simp [Polynomial.coeff_X_pow, Ne.symm hkj]
        · intro hjm; exact absurd (Finset.mem_range.mpr hj) hjm
      · have hjgt : P.natDegree < j := hP_deg.trans_lt (by omega)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hjgt, Finset.sum_eq_zero]
        intro k hk
        have hjk : j ≠ k := by have := Finset.mem_range.mp hk; omega
        simp [Polynomial.coeff_X_pow, hjk]
    conv_lhs => rw [hPsum]
    have hl : lagMeasure c (∑ k ∈ Finset.range (2 * m + 2), P.coeff k • Polynomial.X ^ k) =
        ∑ k ∈ Finset.range (2 * m + 2), P.coeff k * lagMeasure c (Polynomial.X ^ k) := by
      rw [show ∀ Q : ℝ[X], lagMeasure c Q = lagInner c Q 1 from fun Q => by simp [lagInner],
        lagInner_sum_left _ c (hc := hc)]
      refine Finset.sum_congr rfl fun k _ => by rw [lagInner_smul_left]; simp [lagInner]
    rw [hl]
    have hr : e₀ ⬝ᵥ ((Polynomial.aeval J (∑ k ∈ Finset.range (2 * m + 2),
          P.coeff k • (Polynomial.X : ℝ[X]) ^ k)) *ᵥ e₀) =
        ∑ k ∈ Finset.range (2 * m + 2), P.coeff k * (e₀ ⬝ᵥ ((J ^ k) *ᵥ e₀)) := by
      have hterm : ∀ k : ℕ, Polynomial.aeval J (P.coeff k • (Polynomial.X : ℝ[X]) ^ k) =
          P.coeff k • J ^ k := fun k => by
        rw [Polynomial.smul_eq_C_mul, map_mul, Polynomial.aeval_C, map_pow,
          Polynomial.aeval_X, Algebra.smul_def]
      rw [map_sum]; simp_rw [hterm]
      rw [Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    conv_rhs => rw [hPsum]
    rw [hr]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [lagMeasure_pow_eq_jacobi hc m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  let b := hJ.eigenvectorBasis
  have hspec : e₀ ⬝ᵥ ((Polynomial.aeval J P) *ᵥ e₀) =
      ∑ j : Fin (m + 1), (⟪b j, E₀⟫) ^ 2 * P.eval (hJ.eigenvalues j) := by
    have hE₀_eq : e₀ = ∑ j : Fin (m + 1), ⟪b j, E₀⟫ • ⇑(b j) := by
      have hrepr := b.sum_repr E₀
      ext i
      have hof_sum : ∀ s : Finset (Fin (m + 1)), ∀ f : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1)),
          (∑ j ∈ s, f j).ofLp i = ∑ j ∈ s, (f j).ofLp i := by
        intro s f; classical induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, WithLp.ofLp_zero, Pi.zero_apply]
        | @insert a s ha ih => simp only [Finset.sum_insert ha, WithLp.ofLp_add, Pi.add_apply, ih]
      have hof := congr_fun (congr_arg WithLp.ofLp hrepr) i
      simp only [b.repr_apply_apply] at hof
      change (∑ j : Fin (m + 1), ⟪b j, E₀⟫ • b j).ofLp i = e₀ i at hof
      rw [← hof, hof_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [WithLp.ofLp_smul]
    have hM : (Polynomial.aeval J P) *ᵥ e₀ =
        ∑ j : Fin (m + 1), (⟪b j, E₀⟫ * P.eval (hJ.eigenvalues j)) • ⇑(b j) := by
      conv_lhs => rw [hE₀_eq]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, aeval_mulVec_eigenvector J ⇑(b j) (hJ.eigenvalues j)
        (hJ.mulVec_eigenvectorBasis j) P, smul_smul]
    rw [hM, dotProduct_sum]
    have he₀_dot : ∀ j : Fin (m + 1), e₀ ⬝ᵥ ⇑(b j) = ⟪b j, E₀⟫ := fun j => by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    refine Finset.sum_congr rfl fun j _ => by
      rw [dotProduct_smul, smul_eq_mul, he₀_dot j]; ring
  rw [hquad, hspec] at hP_pos
  have hex : ∃ j : Fin (m + 1), 0 < P.eval (hJ.eigenvalues j) := by
    by_contra hneg; push Not at hneg
    have hsum_le : ∑ j : Fin (m + 1), ⟪b j, E₀⟫ ^ 2 * P.eval (hJ.eigenvalues j) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg j)
    linarith
  obtain ⟨j₀, hj₀⟩ := hex
  have hlt_R : hJ.eigenvalues j₀ < R := by
    by_contra hge; exact absurd hj₀ (not_lt.mpr (hP_nonpos _ (not_lt.mp hge)))
  have hnorm_v : (⇑(b j₀) : Fin (m + 1) → ℝ) ⬝ᵥ ⇑(b j₀) = 1 := by
    have h1 := b.orthonormal.1 j₀
    rw [norm_eq_sqrt_real_inner, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Real.sqrt_eq_one] at h1
    exact h1
  have hray := jacobi_rayleigh_ge c hc.le m ⇑(b j₀) hnorm_v
  have heig : hJ.eigenvalues j₀ = ⇑(b j₀) ⬝ᵥ (J *ᵥ ⇑(b j₀)) := by
    simpa [star_trivial] using hJ.eigenvalues_eq j₀
  linarith


/-- info: 'FormalResearch.CohnElkies.lagMeasure_pow_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagMeasure_pow_eq_jacobi

/-- info: 'FormalResearch.CohnElkies.lagMeasure_pos_radius_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagMeasure_pos_radius_bound

end FormalResearch.CohnElkies
