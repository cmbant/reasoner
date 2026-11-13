module

public import FormalResearch.Racah.P2AnalyticBulk6j
public import FormalResearch.Racah.P2AnalyticNLO6jAlg

/-!
# First `6j` correction: the `t`-derivative of the carrier germ (Weyl P2, `thm:6jclosedcorrection`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jclosedcorrection` (proof: the intrinsic
inhomogeneous recurrence `eq:grec`, the stretched seed `eq:kappa`, `eq:kappaClosedMatch`,
`eq:trianglePairIdentities`), `thm:6jeven` (`G_{f,2} = S^{-2} ∂_t G(·,0)`).

In the canonical sector `|n| ≤ m` (`m ∓ n = p, q ∈ ℕ`), `F = m + d`, `x = cosA α β γ`,
`ρ = (α⁻²+β⁻²)/8`, for a strict-triangle shape:

* `nlo6_sigma`: `∑_{q ∈ Q_F} q² = F(F+1)(2F+1)/6`;
* `hasDerivAt_piSixT_t`, `hasDerivAt_edgeSqT_t`: `∂_t Π_F^{-1/2}` and `∂_t E` at `t = 0`;
* `q6 m n d α β τ = ∂_t P̃_{m+d}(τ; t/α², t/β², t/(αβ))|_{t=0}`; `q6_zero`, `q6_one_of_eq`
  (`= -1/(8αβ)`), `q6_one_of_ne`, `q6_rank` (the carrier recurrence `eq:6jrankpoly` differentiated in
  `t`);
* `hasDerivAt_G6c_t`: `∂_t G6c(·,t)|_{t=0} = (ρ(2F+1)F(F+1)/6 - μ) · dZero6c + W · q6`,
  `W = √(((1-x)/2)^p ((1+x)/2)^q)`, `μ = nlo6Mu p q ρ (1/(αβ)) x`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set

/-! ### `∂_t` of the central polynomials -/

lemma nlo6cc_add_two (r : ℕ) : nlo6cc ((r + 2 : ℕ) : ℝ) = nlo6cc (r : ℝ) + ((r : ℝ) + 1) ^ 2 / 4 := by
  unfold nlo6cc; push_cast; ring

/-- **`∂_t 𝔠_r(u;t)` at `t = 0`**: `-c_r u^r / u²`. -/
lemma hasDerivAt_Ct6 (r : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t => Ct r u t) (-(nlo6cc (r : ℝ)) * u ^ r / u ^ 2) 0 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ =>
      have : (fun t => Ct 0 u t) = fun _ => (1 : ℝ) := by funext t; rfl
      rw [this]; simpa [nlo6cc] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    | 1, _ =>
      have : (fun t => Ct 1 u t) = fun _ => u := by funext t; rfl
      rw [this]; simpa [nlo6cc] using hasDerivAt_const (0 : ℝ) u
    | r + 2, ih =>
      have h0 := ih r (by omega)
      have h1 : HasDerivAt (fun t : ℝ => u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t)
          (-(((r : ℝ) + 1) ^ 2 / 4)) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul (((r : ℝ) + 1) ^ 2 / 4)).const_sub (u ^ 2)
        simpa using this
      have h2 := h1.mul h0
      have e : (fun t => Ct (r + 2) u t) =
          (fun t : ℝ => u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t) * fun t => Ct r u t := by
        funext t; rfl
      rw [e]
      refine h2.congr_deriv ?_
      rw [Ct_zero_t, nlo6cc_add_two]
      simp only [mul_zero, sub_zero]
      field_simp
      ring

/-- The `t`-derivative at `0` of the product of four central polynomials over `D`. -/
lemma hasDerivAt_E4 (P Q : ℕ) (a1 a2 a3 a4 D : ℝ) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (h4 : a4 ≠ 0) :
    HasDerivAt (fun t => Ct P a1 t * Ct P a2 t * Ct Q a3 t * Ct Q a4 t / D)
      (a1 ^ P * a2 ^ P * a3 ^ Q * a4 ^ Q / D *
        (-(nlo6cc (P : ℝ) / a1 ^ 2 + nlo6cc (P : ℝ) / a2 ^ 2 + nlo6cc (Q : ℝ) / a3 ^ 2 +
          nlo6cc (Q : ℝ) / a4 ^ 2))) 0 := by
  have g1 := hasDerivAt_Ct6 P h1
  have g2 := hasDerivAt_Ct6 P h2
  have g3 := hasDerivAt_Ct6 Q h3
  have g4 := hasDerivAt_Ct6 Q h4
  have := (((g1.mul g2).mul g3).mul g4).div_const D
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Ct_zero_t]
  field_simp
  ring

/-! ### `Σ q²` -/

/-- `∑_{k<⌈F⌉} (F-k)² = F(F+1)(2F+1)/6` for `2F ∈ ℕ`. -/
lemma nlo6_sigma_aux (N : ℕ) : ∀ F : ℚ, 2 * F = N →
    ∑ k ∈ Finset.range ⌈F⌉₊, ((F : ℝ) - k) ^ 2 = (F : ℝ) * ((F : ℝ) + 1) * (2 * (F : ℝ) + 1) / 6 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro F hF
    match N, ih with
    | 0, _ =>
      have : F = 0 := by push_cast at hF; linarith
      subst this; simp
    | 1, _ =>
      have : F = 1 / 2 := by push_cast at hF; linarith
      subst this
      have hc : ⌈(1 / 2 : ℚ)⌉₊ = 1 := by
        rw [Nat.ceil_eq_iff (by omega)]; norm_num
      rw [hc]; simp; norm_num
    | N + 2, ih =>
      have hF' : 2 * (F - 1) = (N : ℚ) := by push_cast at hF; linarith
      have hg : (0 : ℚ) ≤ F - 1 := by
        have : (0 : ℚ) ≤ N := Nat.cast_nonneg N
        linarith
      have key := ih N (by omega) (F - 1) hF'
      have hc : ⌈F⌉₊ = ⌈F - 1⌉₊ + 1 := by
        have := Nat.ceil_add_one hg
        rwa [sub_add_cancel] at this
      rw [hc, Finset.sum_range_succ']
      push_cast at key ⊢
      have : ∀ k ∈ Finset.range ⌈F - 1⌉₊, ((F : ℝ) - ((k : ℝ) + 1)) ^ 2 =
          ((F : ℝ) - 1 - k) ^ 2 := by intro k _; ring
      rw [Finset.sum_congr rfl this, key]
      ring

lemma nlo6_sigma (F : ℚ) (hF : IsNat (2 * F)) :
    ∑ k ∈ Finset.range ⌈F⌉₊, ((F : ℝ) - k) ^ 2 = (F : ℝ) * ((F : ℝ) + 1) * (2 * (F : ℝ) + 1) / 6 := by
  obtain ⟨N, hN⟩ := hF
  exact nlo6_sigma_aux N F hN

/-- **`∂_t Π_F` at `t = 0`**: `-(α⁻²+β⁻²)/4 · F(F+1)(2F+1)/6`. -/
lemma hasDerivAt_piSixT_t (F : ℚ) (hF : IsNat (2 * F)) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    HasDerivAt (fun t => piSixT F α β t)
      (-((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 4 * ((F : ℝ) * ((F : ℝ) + 1) * (2 * (F : ℝ) + 1) / 6)) 0 := by
  have hk : ∀ k ∈ Finset.range ⌈F⌉₊, HasDerivAt
      (fun t : ℝ => (1 - ((F : ℝ) - k) ^ 2 * t / (4 * α ^ 2)) * (1 - ((F : ℝ) - k) ^ 2 * t / (4 * β ^ 2)))
      (-(((F : ℝ) - k) ^ 2 / (4 * α ^ 2)) - ((F : ℝ) - k) ^ 2 / (4 * β ^ 2)) 0 := by
    intro k _
    have a1 : HasDerivAt (fun t : ℝ => 1 - ((F : ℝ) - k) ^ 2 * t / (4 * α ^ 2))
        (-(((F : ℝ) - k) ^ 2 / (4 * α ^ 2))) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (((F : ℝ) - k) ^ 2)).div_const (4 * α ^ 2)).const_sub 1
      simpa using this
    have a2 : HasDerivAt (fun t : ℝ => 1 - ((F : ℝ) - k) ^ 2 * t / (4 * β ^ 2))
        (-(((F : ℝ) - k) ^ 2 / (4 * β ^ 2))) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (((F : ℝ) - k) ^ 2)).div_const (4 * β ^ 2)).const_sub 1
      simpa using this
    have := a1.mul a2
    refine this.congr_deriv ?_
    simp
    ring
  have hp := HasDerivAt.fun_finsetProd hk
  unfold piSixT
  refine hp.congr_deriv ?_
  have h1 : ∀ i ∈ Finset.range ⌈F⌉₊, ∏ j ∈ (Finset.range ⌈F⌉₊).erase i,
      ((1 - ((F : ℝ) - j) ^ 2 * (0 : ℝ) / (4 * α ^ 2)) * (1 - ((F : ℝ) - j) ^ 2 * (0 : ℝ) / (4 * β ^ 2))) = 1 := by
    intro i _
    exact Finset.prod_eq_one (fun j _ => by simp)
  rw [Finset.sum_congr rfl (fun i hi => by rw [h1 i hi])]
  simp only [smul_eq_mul, one_mul]
  have : ∑ i ∈ Finset.range ⌈F⌉₊, (-(((F : ℝ) - i) ^ 2 / (4 * α ^ 2)) - ((F : ℝ) - i) ^ 2 / (4 * β ^ 2)) =
      -((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 4 * ∑ i ∈ Finset.range ⌈F⌉₊, ((F : ℝ) - i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [this, nlo6_sigma F hF]


/-! ### Triangle-pair identities (`eq:trianglePairIdentities`) -/

lemma nlo6_pair12 (α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) (h1 : α - β + γ ≠ 0) (h2 : -α + β + γ ≠ 0)
    (_hx : 1 - cosA α β γ ≠ 0) :
    ((α - β + γ) ^ 2)⁻¹ + ((-α + β + γ) ^ 2)⁻¹ =
      (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) - (1 + cosA α β γ) * (1 / (α * β))) / (1 - cosA α β γ) ^ 2 := by
  have e : 1 - cosA α β γ = (α - β + γ) * (-α + β + γ) / (2 * α * β) := by
    unfold cosA; field_simp; ring
  rw [e]
  unfold cosA
  field_simp
  ring

lemma nlo6_pair34 (α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) (h3 : α + β - γ ≠ 0) (h4 : α + β + γ ≠ 0)
    (_hx : 1 + cosA α β γ ≠ 0) :
    ((α + β - γ) ^ 2)⁻¹ + ((α + β + γ) ^ 2)⁻¹ =
      (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) + (1 - cosA α β γ) * (1 / (α * β))) / (1 + cosA α β γ) ^ 2 := by
  have e : 1 + cosA α β γ = (α + β - γ) * (α + β + γ) / (2 * α * β) := by
    unfold cosA; field_simp; ring
  rw [e]
  unfold cosA
  field_simp
  ring

/-- For a strict-triangle shape the cosine lies strictly between `-1` and `1`, with
`1 - x = Δ₁Δ₂/(2αβ)`, `1 + x = Δ₃Δ₄/(2αβ)`. -/
lemma nlo6_cosA_mem_Ioo {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    cosA α β γ ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨hα, hβ, hγ, h1, h2, h3⟩ := hz
  have e1 : 1 - cosA α β γ = (α - β + γ) * (-α + β + γ) / (2 * α * β) := by
    unfold cosA; field_simp; ring
  have e2 : 1 + cosA α β γ = (α + β - γ) * (α + β + γ) / (2 * α * β) := by
    unfold cosA; field_simp; ring
  have a1 : 0 < α - β + γ := by linarith
  have a2 : 0 < -α + β + γ := by linarith
  have a3 : 0 < α + β - γ := by linarith
  have a4 : 0 < α + β + γ := by linarith
  have p1 : 0 < 1 - cosA α β γ := by rw [e1]; positivity
  have p2 : 0 < 1 + cosA α β γ := by rw [e2]; positivity
  constructor <;> linarith

/-! ### The carrier along the ray `t ↦ (t/α², t/β², t/(αβ))` -/

/-- The carrier `P̃_{m+d}(τ; t/α², t/β², t/(αβ))` as a function of `t`. -/
noncomputable def Pt6 (m n : ℚ) (d : ℕ) (α β τ t : ℝ) : ℝ :=
  ptilde6 m n τ (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d

lemma Pt6_zero_t (m n : ℚ) (d : ℕ) (α β τ : ℝ) : Pt6 m n d α β τ 0 = ptilde6 m n τ 0 0 0 d := by
  simp [Pt6]

lemma differentiableAt_Pt6 (m n : ℚ) (d : ℕ) (α β τ : ℝ) :
    DifferentiableAt ℝ (fun t => Pt6 m n d α β τ t) 0 := by
  have := analyticAt_ptilde6 m n d (x := (0 : ℝ)) (τ := fun _ => τ) (u := fun t => t / α ^ 2)
    (v := fun t => t / β ^ 2) (w := fun t => t / (α * β)) analyticAt_const
    (analyticAt_id.div_const) (analyticAt_id.div_const) (analyticAt_id.div_const)
  exact this.differentiableAt

/-- `q_d = ∂_t P̃_{m+d}(τ; t/α², t/β², t/(αβ))|_{t=0}`. -/
noncomputable def q6 (m n : ℚ) (d : ℕ) (α β τ : ℝ) : ℝ :=
  deriv (fun t => Pt6 m n d α β τ t) 0

lemma hasDerivAt_Pt6 (m n : ℚ) (d : ℕ) (α β τ : ℝ) :
    HasDerivAt (fun t => Pt6 m n d α β τ t) (q6 m n d α β τ) 0 :=
  (differentiableAt_Pt6 m n d α β τ).hasDerivAt

/-- The extremal start does not depend on `t`. -/
lemma q6_zero (m n : ℚ) (α β τ : ℝ) : q6 m n 0 α β τ = 0 := by
  unfold q6
  have : (fun t => Pt6 m n 0 α β τ t) = fun _ => Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := by
    funext t; simp [Pt6, ptilde6_zero]
  rw [this]; simp

/-- Scalar sector: `P̃_1 = 1 - 2τ - w/8`, so `q_1 = -1/(8αβ)`. -/
lemma q6_one_of_eq (n : ℚ) (α β τ : ℝ) : q6 0 n 1 α β τ = -(1 / (α * β)) / 8 := by
  unfold q6
  have : (fun t => Pt6 0 n 1 α β τ t) = fun t => 1 - 2 * τ - (t / (α * β)) / 8 := by
    funext t; simp only [Pt6, ptilde6_one_of_eq]
  rw [this]
  have h : HasDerivAt (fun t : ℝ => 1 - 2 * τ - (t / (α * β)) / 8) (-(1 / (α * β)) / 8) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).div_const (α * β)).div_const 8).const_sub (1 - 2 * τ))
    simpa [neg_div] using this
  exact h.deriv

/-- The carrier recurrence `eq:6jrankpoly`, cross-multiplied, along the ray. -/
lemma Pt6_cross (m n : ℚ) (d : ℕ) (α β τ t : ℝ)
    (hFR : ((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1) ≠ 0) :
    ((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1) * Pt6 m n (d + 2) α β τ t =
      (2 * ((m : ℝ) + d + 1) + 1) * (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) *
          (1 - 2 * τ - (2 * ((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) + 1 -
            ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 * (t / (α * β))) - m * n) * Pt6 m n (d + 1) α β τ t -
        ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1)) *
          ((1 - ((m : ℝ) + d + 1) ^ 2 / 4 * (t / α ^ 2)) *
            (1 - ((m : ℝ) + d + 1) ^ 2 / 4 * (t / β ^ 2))) * Pt6 m n d α β τ t := by
  have h := ptilde6_succ_succ m n τ (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d
  simp only [Pt6]
  rw [h, ← mul_assoc, mul_one_div_cancel hFR, one_mul]
  ring

/-- **The carrier recurrence `eq:6jrankpoly` differentiated in `t` at `t = 0`**, rows
`F = m + d + 1` (`R_k = rootR m n k`, `S = m²+n²`): with `P_j = P̃_{m+j}(τ;0,0,0)`,
`F R_{F+1} q_{d+2} = (2F+1)(F(F+1)(1-2τ) - mn) q_{d+1}
   - (2F+1)F(F+1)(2F(F+1)+1-S)/(8αβ) P_{d+1} - (F+1) R_F (q_d - F²(α⁻²+β⁻²)/4 · P_d)`. -/
theorem q6_rank (m n : ℚ) (d : ℕ) (α β τ : ℝ)
    (hFR : ((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1) ≠ 0) :
    ((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1) * q6 m n (d + 2) α β τ =
      (2 * ((m : ℝ) + d + 1) + 1) *
          (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) * (1 - 2 * τ) - m * n) *
            q6 m n (d + 1) α β τ -
        (2 * ((m : ℝ) + d + 1) + 1) * (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1)) *
          (2 * (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) /
            8 * (1 / (α * β)) * ptilde6 m n τ 0 0 0 (d + 1) -
        ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1)) *
          (q6 m n d α β τ - ((m : ℝ) + d + 1) ^ 2 / 4 * ((α ^ 2)⁻¹ + (β ^ 2)⁻¹) *
            ptilde6 m n τ 0 0 0 d) := by
  set F : ℝ := (m : ℝ) + d + 1 with hF
  set R1 : ℝ := rootR m n F with hR1
  set R2 : ℝ := rootR m n (F + 1) with hR2
  set Sg : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hSg
  have hfun : (fun t => F * R2 * Pt6 m n (d + 2) α β τ t) =
      fun t => (2 * F + 1) * (F * (F + 1) * (1 - 2 * τ - (2 * F * (F + 1) + 1 - Sg) / 8 * (t / (α * β))) -
          m * n) * Pt6 m n (d + 1) α β τ t -
        ((F + 1) * R1) * ((1 - F ^ 2 / 4 * (t / α ^ 2)) * (1 - F ^ 2 / 4 * (t / β ^ 2))) *
          Pt6 m n d α β τ t := by
    funext t
    exact Pt6_cross m n d α β τ t hFR
  have hA := (hasDerivAt_Pt6 m n (d + 2) α β τ).const_mul (F * R2)
  have hB1 : HasDerivAt (fun t : ℝ => (2 * F + 1) * (F * (F + 1) *
        (1 - 2 * τ - (2 * F * (F + 1) + 1 - Sg) / 8 * (t / (α * β))) - m * n))
      ((2 * F + 1) * (F * (F + 1) * (-((2 * F * (F + 1) + 1 - Sg) / 8 * (1 / (α * β)))))) 0 := by
    have h0 := ((((hasDerivAt_id (0 : ℝ)).div_const (α * β)).const_mul
      ((2 * F * (F + 1) + 1 - Sg) / 8)).const_sub (1 - 2 * τ)).const_mul (F * (F + 1))
    have h1 := (h0.sub_const ((m : ℝ) * n)).const_mul (2 * F + 1)
    simpa using h1
  have hB2 : HasDerivAt (fun t : ℝ => ((F + 1) * R1) * ((1 - F ^ 2 / 4 * (t / α ^ 2)) *
        (1 - F ^ 2 / 4 * (t / β ^ 2))))
      (((F + 1) * R1) * (-(F ^ 2 / 4 * (1 / α ^ 2)) - F ^ 2 / 4 * (1 / β ^ 2))) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => 1 - F ^ 2 / 4 * (t / α ^ 2)) (-(F ^ 2 / 4 * (1 / α ^ 2))) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).div_const (α ^ 2)).const_mul (F ^ 2 / 4)).const_sub 1
      simpa using this
    have a2 : HasDerivAt (fun t : ℝ => 1 - F ^ 2 / 4 * (t / β ^ 2)) (-(F ^ 2 / 4 * (1 / β ^ 2))) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).div_const (β ^ 2)).const_mul (F ^ 2 / 4)).const_sub 1
      simpa using this
    have := (a1.mul a2).const_mul ((F + 1) * R1)
    refine this.congr_deriv ?_
    simp only [zero_div, mul_zero, sub_zero, mul_one, one_mul]
    ring
  have hB := (hB1.mul (hasDerivAt_Pt6 m n (d + 1) α β τ)).sub (hB2.mul (hasDerivAt_Pt6 m n d α β τ))
  rw [hfun] at hA
  have := hA.unique hB
  simp only [Pt6_zero_t] at this
  simp only [mul_zero, zero_div, sub_zero, mul_one] at this
  have hG : ∀ y : ℝ, (1 - 2 * τ - (2 * F * (F + 1) + 1 - Sg) / 8 * y) = (1 - 2 * τ - (2 * F * (F + 1) + 1 - Sg) / 8 * y) := fun _ => rfl
  rw [this]
  field_simp
  ring


/-- The second start for `m ≠ 0` (`R_m = 0` row of the recurrence):
`m R_{m+1} q_1 = -(2m+1)m(m+1)(2m(m+1)+1-S)/(8αβ) · P_0`. -/
theorem q6_one_of_ne (m n : ℚ) (α β τ : ℝ)
    (hmR : (m : ℝ) * rootR m n ((m : ℝ) + 1) ≠ 0) :
    (m : ℝ) * rootR m n ((m : ℝ) + 1) * q6 m n 1 α β τ =
      -((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) *
        (2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 * (1 / (α * β)) *
          ptilde6 m n τ 0 0 0 0) := by
  have hm : m ≠ 0 := by
    intro h; apply hmR; simp [h]
  have hfun : (fun t => (m : ℝ) * rootR m n ((m : ℝ) + 1) * Pt6 m n 1 α β τ t) =
      fun t => (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) *
        (1 - 2 * τ - (2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 *
          (t / (α * β))) - m * n) * ptilde6 m n τ 0 0 0 0 := by
    funext t
    simp only [Pt6]
    rw [ptilde6_one_of_ne m n hm, ptilde6_zero]
    have hR := right_ne_zero_of_mul hmR
    have hm' := left_ne_zero_of_mul hmR
    field_simp
    ring
  have hA := (hasDerivAt_Pt6 m n 1 α β τ).const_mul ((m : ℝ) * rootR m n ((m : ℝ) + 1))
  rw [hfun] at hA
  have hB : HasDerivAt (fun t : ℝ => (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) *
        (1 - 2 * τ - (2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 *
          (t / (α * β))) - m * n) * ptilde6 m n τ 0 0 0 0)
      ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) *
        (-((2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 * (1 / (α * β))))) *
          ptilde6 m n τ 0 0 0 0) 0 := by
    have h0 := ((((hasDerivAt_id (0 : ℝ)).div_const (α * β)).const_mul
      ((2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8)).const_sub
        (1 - 2 * τ)).const_mul ((m : ℝ) * ((m : ℝ) + 1))
    have h1 := ((h0.sub_const ((m : ℝ) * n)).const_mul (2 * (m : ℝ) + 1)).mul_const
      (ptilde6 m n τ 0 0 0 0)
    simpa using h1
  have := hA.unique hB
  rw [this]; ring

/-! ### The `t`-derivative of the germ `G6c` -/

/-- **`∂_t G6c` at `t = 0`** (canonical sector, strict-triangle shape): with `F = m + d`,
`ρ = (α⁻²+β⁻²)/8`, `x = cosA α β γ`,
`∂_t G6c(·,t)|_{t=0} = (ρ F(F+1)(2F+1)/6 - μ) · dZero6c + √(((1-x)/2)^p((1+x)/2)^q) · q_d`. -/
theorem hasDerivAt_G6c_t (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ)
    {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    HasDerivAt (fun t => G6c m n d α β γ t)
      ((((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8 *
            (((m : ℝ) + d) * (((m : ℝ) + d) + 1) * (2 * ((m : ℝ) + d) + 1) / 6) -
          nlo6Mu (p : ℝ) (q : ℝ) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ)) *
          dZero6c m n d (cosA α β γ) +
        Real.sqrt (((1 - cosA α β γ) / 2) ^ p * ((1 + cosA α β γ) / 2) ^ q) *
          q6 m n d α β ((1 - cosA α β γ) / 2)) 0 := by
  have hz' := hz
  obtain ⟨hα, hβ, hγ, h1, h2, h3⟩ := hz
  have a1 : 0 < α - β + γ := by linarith
  have a2 : 0 < -α + β + γ := by linarith
  have a3 : 0 < α + β - γ := by linarith
  have a4 : 0 < α + β + γ := by linarith
  have hxI := nlo6_cosA_mem_Ioo hz'
  have hx1 : 0 < 1 - cosA α β γ := by linarith [hxI.2]
  have hx2 : 0 < 1 + cosA α β γ := by linarith [hxI.1]
  obtain ⟨f1, f2, f3⟩ := floor_labels m n p q hp hq
  have hF : IsNat (2 * (m + (d : ℚ))) := ⟨p + q + 2 * d, by
    have : 2 * m = ((p + q : ℕ) : ℚ) := by push_cast; linarith
    push_cast at this ⊢; linarith⟩
  -- the edge factor
  have hE : HasDerivAt (fun t => edgeSqT m n α β γ t)
      ((α - β + γ) ^ p * (-α + β + γ) ^ p * (α + β - γ) ^ q * (α + β + γ) ^ q /
          (4 * α * β) ^ (p + q) *
        (-(nlo6cc (p : ℝ) / (α - β + γ) ^ 2 + nlo6cc (p : ℝ) / (-α + β + γ) ^ 2 +
          nlo6cc (q : ℝ) / (α + β - γ) ^ 2 + nlo6cc (q : ℝ) / (α + β + γ) ^ 2))) 0 := by
    have := hasDerivAt_E4 p q (α - β + γ) (-α + β + γ) (α + β - γ) (α + β + γ)
      ((4 * α * β) ^ (p + q)) a1.ne' a2.ne' a3.ne' a4.ne'
    unfold edgeSqT
    simp only [f1, f2, f3]
    exact this
  have hE0 : edgeSqT m n α β γ 0 = ((1 - cosA α β γ) / 2) ^ p * ((1 + cosA α β γ) / 2) ^ q := by
    have := edgeSqT_zero m n p q hp hq α β γ hα.ne' hβ.ne'
    rwa [f1, f2] at this
  have hE0' : edgeSqT m n α β γ 0 =
      (α - β + γ) ^ p * (-α + β + γ) ^ p * (α + β - γ) ^ q * (α + β + γ) ^ q /
          (4 * α * β) ^ (p + q) := by
    unfold edgeSqT
    simp only [f1, f2, f3, Ct_zero_t]
  have hEpos : 0 < edgeSqT m n α β γ 0 := by
    rw [hE0]; positivity
  have hP := hasDerivAt_piSixT_t (m + (d : ℚ)) hF α β hα.ne' hβ.ne'
  have hsE := hE.sqrt hEpos.ne'
  have hsP := hP.sqrt (by rw [piSixT_zero]; exact one_ne_zero)
  have hsPi := hsP.inv (by rw [piSixT_zero]; simp)
  have hfin := (hsE.mul hsPi).mul (hasDerivAt_Pt6 m n d α β ((1 - cosA α β γ) / 2))
  unfold G6c
  refine hfin.congr_deriv ?_
  -- algebra
  have hpair12 := nlo6_pair12 α β γ hα.ne' hβ.ne' a1.ne' a2.ne' hx1.ne'
  have hpair34 := nlo6_pair34 α β γ hα.ne' hβ.ne' a3.ne' a4.ne' hx2.ne'
  have hK : -(nlo6cc (p : ℝ) / (α - β + γ) ^ 2 + nlo6cc (p : ℝ) / (-α + β + γ) ^ 2 +
          nlo6cc (q : ℝ) / (α + β - γ) ^ 2 + nlo6cc (q : ℝ) / (α + β + γ) ^ 2) =
      -2 * nlo6Mu (p : ℝ) (q : ℝ) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ) := by
    unfold nlo6Mu
    have e1 : nlo6cc (p : ℝ) / (α - β + γ) ^ 2 + nlo6cc (p : ℝ) / (-α + β + γ) ^ 2 =
        nlo6cc (p : ℝ) * (((α - β + γ) ^ 2)⁻¹ + ((-α + β + γ) ^ 2)⁻¹) := by ring
    have e2 : nlo6cc (q : ℝ) / (α + β - γ) ^ 2 + nlo6cc (q : ℝ) / (α + β + γ) ^ 2 =
        nlo6cc (q : ℝ) * (((α + β - γ) ^ 2)⁻¹ + ((α + β + γ) ^ 2)⁻¹) := by ring
    have e3 : (8 * (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8)) = (α ^ 2)⁻¹ + (β ^ 2)⁻¹ := by ring
    rw [e3]
    linear_combination (-(nlo6cc (p : ℝ))) * hpair12 - (nlo6cc (q : ℝ)) * hpair34 + 0 * e1 + 0 * e2
  rw [hK, ← hE0']
  simp only [Pi.mul_apply, Pi.inv_apply, piSixT_zero, Real.sqrt_one, inv_one, one_pow, Pt6_zero_t]
  have hd : dZero6c m n d (cosA α β γ) =
      Real.sqrt (edgeSqT m n α β γ 0) * ptilde6 m n ((1 - cosA α β γ) / 2) 0 0 0 d := by
    unfold dZero6c
    rw [hE0, f1, f2]
  rw [hd, ← hE0]
  have hs : Real.sqrt (edgeSqT m n α β γ 0) ^ 2 = edgeSqT m n α β γ 0 := Real.sq_sqrt hEpos.le
  have hs0 : Real.sqrt (edgeSqT m n α β γ 0) ≠ 0 := (Real.sqrt_pos.mpr hEpos).ne'
  push_cast
  generalize Real.sqrt (edgeSqT m n α β γ 0) = s at *
  generalize edgeSqT m n α β γ 0 = E at *
  generalize ptilde6 m n ((1 - cosA α β γ) / 2) 0 0 0 d = P
  generalize q6 m n d α β ((1 - cosA α β γ) / 2) = Q
  rw [← hs]
  field_simp
  ring

/-- info: 'FormalResearch.Racah.q6_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms q6_rank

/-- info: 'FormalResearch.Racah.q6_one_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms q6_one_of_ne

/-- info: 'FormalResearch.Racah.hasDerivAt_G6c_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_G6c_t

end FormalResearch.Racah
