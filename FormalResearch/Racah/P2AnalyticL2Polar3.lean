module

public import FormalResearch.Racah.P2AnalyticL2Polar2

/-!
# The continuum gauge `G_c` and the Wigner-Jacobi identification (Weyl P2, `eq:GcGauge`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, Appendix `app:beta-polar`
(`eq:GcGauge`, `eq:physicalGaugeModes`), `prop:betabinomialpolar` (`eq:SNpolar`).

* `Gc`: `G_c : P_D → L²(-1,1)`, the linear map with `G_c J_n = gauge(J_n)`, where
  `gaugeC f (x) = 2^{-1/2} [t^α(1-t)^β/B]^{1/2} f(t)`, `t = (1-x)/2` (`eq:GcGauge`); it is defined on
  the basis `J_n` of `P_D` and extended linearly (the gauge formula is the definition on `J_n`);
* `uN_eq_Gc`: `u_L = (-1)^α G_c J_n` (`eq:physicalGaugeModes`), from `wignerSmallD_eq_jacobi` (the
  standard Jacobi formula for `d^L_{Mσ}`), with the positive constants matched by `L²(-1,1)`-norms;
* `Gc_inner`, `Gc_range`: `G_c` is an isometry onto `𝒱_N = span{u_L}`;
* `eq_SNpolar`: **`S_N G_c = G_d U_D`**, i.e. `S_N = G_d U_D G_c^{-1}` on `𝒱_N` (`eq:SNpolar`);
  `eq_SNpolar_inv` is the same statement with `G_c^{-1}` spelled out;
* `sing_sq_physical`: `eq:physicalsingularvalues`.
-/

@[expose] public section

namespace FormalResearch.Racah

open MeasureTheory Polar FormalResearch.Special FormalResearch.Wigner
open scoped InnerProductSpace

/-! ### `L2cont` calculus -/

lemma L2cont_eq_of_eqOn {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = g x) : L2cont f hf = L2cont g hg := by
  unfold L2cont
  apply MemLp.toLp_congr
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall h

lemma L2cont_smul (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    c • L2cont f hf = L2cont (fun x => c * f x) (continuous_const.mul hf) := by
  unfold L2cont
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => rfl

/-! ### The gauge `G_c` -/

/-- **`eq:GcGauge`**: `(G_c p)(x) = 2^{-1/2} [t^α(1-t)^β/B]^{1/2} p(t)`, `t = (1-x)/2`, as a function
of `x`. -/
noncomputable def gaugeC (α β : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * Real.sqrt (wtJ α β ((1 - x) / 2) / betaB α β) * f ((1 - x) / 2)

lemma gaugeC_continuous (α β : ℕ) {f : ℝ → ℝ} (hf : Continuous f) : Continuous (gaugeC α β f) := by
  unfold gaugeC
  have h : Continuous (fun x : ℝ => (1 - x) / 2) := by fun_prop
  exact (continuous_const.mul ((wtJ_div_continuous α β).comp h).sqrt).mul (hf.comp h)

/-- `G_c [f]`: the gauge applied to the class in `L²(-1,1)`. -/
noncomputable def GcFun (α β : ℕ) (f : ℝ → ℝ) (hf : Continuous f) : L2m11 :=
  L2cont (gaugeC α β f) (gaugeC_continuous α β hf)

/-- **`G_c : P_D → L²(-1,1)`** (`eq:GcGauge`), the linear map with `G_c J_n = gauge(J_n)`. -/
noncomputable def Gc (α β D : ℕ) : PD α β D →ₗ[ℝ] L2m11 :=
  (JV α β D).toBasis.constr ℝ (fun n => GcFun α β (Jmode α β n) (Jmode_continuous α β n))

lemma Gc_JV (α β D : ℕ) (n : Fin (D + 1)) :
    Gc α β D (JV α β D n) = GcFun α β (Jmode α β n) (Jmode_continuous α β n) := by
  have := (JV α β D).toBasis.constr_basis ℝ
    (fun n => GcFun α β (Jmode α β n) (Jmode_continuous α β n)) n
  rw [OrthonormalBasis.coe_toBasis] at this
  exact this


/-! ### The Wigner mode is `(-1)^α` times the gauged Jacobi mode -/

lemma sin_cos_pow (α β : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sin (Real.arccos x / 2) ^ α * Real.cos (Real.arccos x / 2) ^ β =
      Real.sqrt (wtJ α β ((1 - x) / 2)) := by
  set θ := Real.arccos x with hθ
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg x
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi x
  have hcos : Real.cos θ = x := Real.cos_arccos hx.1 hx.2
  have hc2 : Real.cos (θ / 2) ^ 2 = 1 - (1 - x) / 2 := by
    rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring, hcos]; ring
  have hs2 : Real.sin (θ / 2) ^ 2 = (1 - x) / 2 := by rw [Real.sin_sq, hc2]; ring
  have hs0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hnn : 0 ≤ Real.sin (θ / 2) ^ α * Real.cos (θ / 2) ^ β := by positivity
  rw [← Real.sqrt_sq hnn]
  congr 1
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm α 2, mul_comm β 2, pow_mul, pow_mul, hs2, hc2]
  rfl

/-- `F_n(x) = √(t^α(1-t)^β) · jT_n(t)`, `t = (1-x)/2`: the common shape of both gauged modes. -/
noncomputable def Fgauge (α β n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (wtJ α β ((1 - x) / 2)) * jT α β n ((1 - x) / 2)

lemma Fgauge_continuous (α β n : ℕ) : Continuous (Fgauge α β n) := by
  unfold Fgauge
  have h : Continuous (fun x : ℝ => (1 - x) / 2) := by fun_prop
  exact (((wtJ_continuous α β).comp h).sqrt).mul ((jT_continuous α β n).comp h)

/-- **Wigner mode = `(-1)^α`-signed Jacobi shape**: `u_L(x) = (-1)^α K₁ F_n(x)`, `K₁ > 0`
(`wignerSmallD_eq_jacobi`, the standard Jacobi formula for `d^L_{Mσ}`). -/
lemma uWig_eq_F {M σ : ℚ} {α β : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (n : ℕ) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      uWig (max |M| |σ| + n) M σ x = (-1 : ℝ) ^ α * (K₁ * Fgauge α β n x) := by
  have hmax := chamber_max hα hβ
  have hM0 : (0 : ℝ) ≤ M := by
    have : (0 : ℚ) ≤ M := by
      have h1 : (0 : ℚ) ≤ α := Nat.cast_nonneg _
      have h2 : (0 : ℚ) ≤ β := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hcJ := cJ_pos α n
  refine ⟨Real.sqrt ((2 * (((max |M| |σ| + n : ℚ)) : ℝ) + 1) / 2) *
    Real.sqrt ((n.factorial : ℝ) * (n + α + β).factorial /
      (((n + α).factorial : ℝ) * (n + β).factorial)) / cJ α n, ?_, fun x hx => ?_⟩
  · have : (0 : ℝ) ≤ (max |M| |σ| + n : ℚ) := by
      rw [hmax]; push_cast; positivity
    positivity
  · unfold uWig wignerSmallDx
    rw [wignerSmallD_eq_jacobi (j := max |M| |σ| + n) (m' := M) (m := σ) hα hβ
      (by rw [hmax]; ring), Real.cos_arccos hx.1 hx.2]
    have hP : (jacobi (α : ℝ) (β : ℝ) n).eval x = jT α β n ((1 - x) / 2) / cJ α n := by
      rw [jT_half]; field_simp
    rw [show ∀ a b c d e : ℝ, a * b * c * d * e = a * b * (c * d) * e from fun a b c d e => by ring,
      sin_cos_pow α β hx, hP]
    unfold Fgauge
    field_simp

/-- **Gauged Jacobi mode shape**: `gauge(J_n)(x) = K₂ F_n(x)`, `K₂ > 0`. -/
lemma gaugeC_eq_F (α β n : ℕ) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ x : ℝ, gaugeC α β (Jmode α β n) x = K₂ * Fgauge α β n x := by
  have hB := betaB_pos α β
  have hn := jT_norm_pos α β n
  refine ⟨(1 / Real.sqrt 2) * (1 / Real.sqrt (betaB α β)) *
    (1 / Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n))), by positivity, fun x => ?_⟩
  unfold gaugeC Fgauge Jmode
  rw [Real.sqrt_div' _ hB.le]
  ring


/-- `‖G_c J_n‖ = 1`: `∫_{-1}^1 gauge(J_n)² dx = ∫_0^1 J_n² dν_H = 1`. -/
theorem integral_gaugeC_sq (α β n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (gaugeC α β (Jmode α β n) x) ^ 2 = 1 := by
  have hB := betaB_pos α β
  have h1 : (1 / betaB α β) * ipJ α β (Jmode α β n) (Jmode α β n) = 1 := by
    have := JL_inner α β n n
    unfold JL at this
    rw [inner_L2nuc] at this
    simpa using this
  have e : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, (gaugeC α β (Jmode α β n) x) ^ 2 =
      (1 / 2) * ((fun t => (1 / betaB α β) * (wtJ α β t * (Jmode α β n t * Jmode α β n t)))
        ((1 - x) / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have ht : (1 - x) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hw := wtJ_nonneg (α := α) (β := β) ht
    have h3 := Real.sq_sqrt (show 0 ≤ wtJ α β ((1 - x) / 2) / betaB α β by positivity)
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    unfold gaugeC
    rw [mul_pow, mul_pow, div_pow, one_pow, h2, h3]
    field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
    ← integral01_eq (fun t => (1 / betaB α β) * (wtJ α β t * (Jmode α β n t * Jmode α β n t)))]
  rw [intervalIntegral.integral_const_mul]
  exact h1

lemma neg_one_pow_mul_self (α : ℕ) : (-1 : ℝ) ^ α * (-1 : ℝ) ^ α = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- **`u_L = (-1)^{α_H} G_c J_n`** (`eq:physicalGaugeModes`, continuum half): in the chamber
`M ≥ |σ|` (`α = M-σ`, `β = M+σ`, `D = N-M-1`, `n = L-M`), the Wigner mode `uN n` of `prop:SN`
equals `(-1)^α G_c J_n`.  The positive constants of the Jacobi formula for `d^L_{Mσ}` and of the
unit-normalised `J_n` are matched by comparing `L²(-1,1)` norms (both modes have norm 1 and are
positive multiples of the same function, up to the sign `(-1)^α`). -/
theorem uN_eq_Gc {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : Fin (D + 1)) :
    uN M σ (K := D + 1) n = ((-1 : ℝ) ^ α) • Gc α β D (JV α β D n) := by
  have hA := chamber_specAdm hα hβ hD
  have hK : ((D + 1 : ℕ) : ℚ) = N - max |M| |σ| := by
    rw [chamber_max hα hβ]; push_cast; linarith
  have hadm : DAdm (max |M| |σ| + ((n : ℕ) : ℚ)) M σ := dadm_rkN hA hK n
  rw [Gc_JV]
  unfold uN L2uWig GcFun
  rw [L2cont_smul]
  apply L2cont_eq_of_eqOn
  intro x hx
  obtain ⟨K₁, hK₁, h1⟩ := uWig_eq_F hα hβ n
  obtain ⟨K₂, hK₂, h2⟩ := gaugeC_eq_F α β n
  have hu1 : ∫ x in (-1 : ℝ)..1, uWig (max |M| |σ| + ((n : ℕ) : ℚ)) M σ x *
      uWig (max |M| |σ| + ((n : ℕ) : ℚ)) M σ x =
      K₁ ^ 2 * ∫ x in (-1 : ℝ)..1, (Fgauge α β n x) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hy
    simp only [h1 y hy]
    linear_combination (K₁ ^ 2 * Fgauge α β n y ^ 2) * neg_one_pow_mul_self α
  have hu2 : ∫ x in (-1 : ℝ)..1, (gaugeC α β (Jmode α β n) x) ^ 2 =
      K₂ ^ 2 * ∫ x in (-1 : ℝ)..1, (Fgauge α β n x) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y _ => by simp only [h2 y]; ring
  have hn1 := integral_uWig_mul hadm hadm
  have hn2 := integral_gaugeC_sq α β n
  simp only [uWig] at hu1 hn1
  have hI : K₁ ^ 2 * ∫ x in (-1 : ℝ)..1, (Fgauge α β n x) ^ 2 = 1 := by
    rw [← hu1]; simpa using hn1
  rw [hu2] at hn2
  have hK12 : K₁ = K₂ := by
    have hsq : K₁ ^ 2 = K₂ ^ 2 := by
      have hI0 : ∫ x in (-1 : ℝ)..1, (Fgauge α β n x) ^ 2 ≠ 0 := fun h => by
        rw [h] at hI; simp at hI
      exact mul_right_cancel₀ hI0 (hI.trans hn2.symm)
    nlinarith [sq_nonneg (K₁ - K₂), sq_nonneg (K₁ + K₂)]
  show uWig (rkN M σ n) M σ x = (-1 : ℝ) ^ α * gaugeC α β (Jmode α β n) x
  unfold rkN
  rw [h1 x hx, h2 x, hK12]


/-! ### `eq:SNpolar` -/

/-- `S_N` as a linear map. -/
noncomputable def SNlin (M σ N : ℚ) {K : ℕ} (u : Fin K → L2m11) : L2m11 →ₗ[ℝ] (Fin K → ℝ) where
  toFun := SNmap M σ N u
  map_add' x y := by
    unfold SNmap
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    unfold SNmap
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]

lemma Gc_JV_eq {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D)
    (n : Fin (D + 1)) :
    Gc α β D (JV α β D n) = ((-1 : ℝ) ^ α) • uN M σ (K := D + 1) n := by
  rw [uN_eq_Gc hα hβ hD, smul_smul, neg_one_pow_mul_self, one_smul]

/-- **`G_c` is isometric** `P_D → L²(-1,1)` (the gauge `eq:GcGauge` is unitary onto its range). -/
theorem Gc_inner {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D)
    (p q : PD α β D) : ⟪Gc α β D p, Gc α β D q⟫_ℝ = ⟪p, q⟫_ℝ := by
  have hA := chamber_specAdm hα hβ hD
  have hK : ((D + 1 : ℕ) : ℚ) = N - max |M| |σ| := by
    rw [chamber_max hα hβ]; push_cast; linarith
  have hon := uN_orthonormal hA hK
  have hon' : Orthonormal ℝ (fun n : Fin (D + 1) => Gc α β D (JV α β D n)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Gc_JV_eq hα hβ hD, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [orthonormal_iff_ite.1 hon i j, ← mul_assoc, neg_one_pow_mul_self]
    simp
  conv_lhs => rw [← (JV α β D).sum_repr' p, ← (JV α β D).sum_repr' q]
  simp only [map_sum, map_smul]
  rw [hon'.inner_sum (fun n => ⟪JV α β D n, p⟫_ℝ) (fun n => ⟪JV α β D n, q⟫_ℝ) Finset.univ]
  conv_rhs => rw [← (JV α β D).sum_inner_mul_inner p q]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [RCLike.conj_to_real]
  rw [real_inner_comm p (JV α β D n)]

/-- **`G_c` maps `P_D` onto `𝒱_N = span{u_L}`**, so `G_c^{-1}` is defined on `𝒱_N`. -/
theorem Gc_range {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D) :
    LinearMap.range (Gc α β D) = Submodule.span ℝ (Set.range (uN M σ : Fin (D + 1) → L2m11)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [← (JV α β D).sum_repr' p, map_sum]
    refine Submodule.sum_mem _ fun n _ => ?_
    rw [map_smul, Gc_JV_eq hα hβ hD]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨((-1 : ℝ) ^ α) • JV α β D n, ?_⟩
    rw [map_smul, Gc_JV_eq hα hβ hD, smul_smul, neg_one_pow_mul_self, one_smul]

/-- **`eq:SNpolar`**: `S_N = G_d U_D G_c^{-1}`, i.e. `S_N G_c = G_d U_D` on `P_D`.  The common
phase `(-1)^{α_H}` of `u_L = (-1)^α G_c J_n` and `v_L = (-1)^α G_d H_n` cancels. -/
theorem eq_SNpolar {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D)
    (p : PD α β D) :
    SNmap M σ N (uN M σ : Fin (D + 1) → L2m11) (Gc α β D p) = Gd N D (D + 1) (UD α β D p) := by
  have hA := chamber_specAdm hα hβ hD
  have hK : ((D + 1 : ℕ) : ℚ) = N - max |M| |σ| := by
    rw [chamber_max hα hβ]; push_cast; linarith
  have hon := uN_orthonormal hA hK
  have h : SNlin M σ N (uN M σ : Fin (D + 1) → L2m11) ∘ₗ Gc α β D = Gd N D (D + 1) ∘ₗ UD α β D := by
    refine (JV α β D).toBasis.ext fun n => ?_
    rw [OrthonormalBasis.coe_toBasis]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [UD_JV, Gc_JV_eq hα hβ hD, map_smul]
    change ((-1 : ℝ) ^ α) • SNmap M σ N (uN M σ : Fin (D + 1) → L2m11) (uN M σ n) = _
    rw [SNmap_u hon, vN_eq_Gd hα hβ hD, smul_smul, neg_one_pow_mul_self, one_smul]
  exact congrArg (fun F => F p) h

/-- **`eq:SNpolar` on `𝒱_N`**: `S_N x = G_d U_D G_c^{-1} x` for `x ∈ 𝒱_N`, whenever `G_c p = x`
(and `p` is then unique, `G_c` being isometric). -/
theorem eq_SNpolar_inv {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) {x : L2m11}
    (hx : x ∈ Submodule.span ℝ (Set.range (uN M σ : Fin (D + 1) → L2m11))) :
    ∃! p : PD α β D, Gc α β D p = x ∧
      SNmap M σ N (uN M σ : Fin (D + 1) → L2m11) x = Gd N D (D + 1) (UD α β D p) := by
  rw [← Gc_range hα hβ hD] at hx
  obtain ⟨p, rfl⟩ := hx
  refine ⟨p, ⟨rfl, eq_SNpolar hα hβ hD p⟩, fun q ⟨hq, _⟩ => ?_⟩
  have h0 : ⟪q - p, q - p⟫_ℝ = 0 := by
    rw [← Gc_inner hα hβ hD, map_sub, hq, sub_self]; simp
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- **`eq:physicalsingularvalues`**: `s_{L-M}² = ∏_{r=M+1}^{L} (N-r)/(N+r)`, `L = M + n`. -/
theorem sing_sq_physical {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : Fin (D + 1)) :
    sing α β D n ^ 2 = ∏ k ∈ Finset.range n,
      (((N : ℝ) - ((M : ℝ) + k + 1)) / ((N : ℝ) + ((M : ℝ) + k + 1))) := by
  have hr := chamber_real hα hβ hD
  rw [sing, Real.sq_sqrt (singularSq_pos α β D n (by omega)).le]
  exact singularSq_physical α β D n (M : ℝ) (N : ℝ) (by rw [hr.1]; ring) (by rw [hr.2.2, hr.1])

/-- info: 'FormalResearch.Racah.integral_gaugeC_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_gaugeC_sq

/-- info: 'FormalResearch.Racah.uN_eq_Gc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uN_eq_Gc

/-- info: 'FormalResearch.Racah.Gc_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc_inner

/-- info: 'FormalResearch.Racah.Gc_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc_range

/-- info: 'FormalResearch.Racah.eq_SNpolar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_SNpolar

/-- info: 'FormalResearch.Racah.eq_SNpolar_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_SNpolar_inv

/-- info: 'FormalResearch.Racah.sing_sq_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sing_sq_physical

end FormalResearch.Racah
