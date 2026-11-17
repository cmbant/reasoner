module

public import FormalResearch.Special.AiryPwsDeriv

/-!
# The functions `L_n = Ai/(u - a_n)`: the sum rule for their derivatives and the expansion of `A v`

With `a_n = airyZ n` the zeros of `Ai` and `L_n(u) = Ai(u)/(u-a_n) = K(u,a_n)/Ai'(a_n)` (`airyLn`; `L_n(a_n) = Ai'(a_n)`),
`φ_n = 1_{t>0} Ai(a_n+t)/Ai'(a_n)` (`airyPwsPhi`, an orthonormal family of `L²(0,∞)`, and `A φ_n = L_n`):

* `airyLn_iteratedDeriv_sq_hasSum` (the CFT PR 240 branch note `CE_O1_ROUTE.md` (not yet on `main`) (O.11ad.5), the reproducing identity applied to derivatives): for every
  `j ≥ 0` and `y ∈ ℝ`,
  `Σ_{n ≥ 1} |L_n^{(j)}(y)|² = ∫_y^∞ Ai^{(j)}(t)² dt`.
  (With `y = -x` this is `Σ |L_n^{(j)}(-x)|² = ∫_{-x}^∞ Ai^{(j)}(t)² dt`.)  Proof: `L_n^{(j)}(y) = Ψg(a_n)/Ai'(a_n)`
  with `g = 1_{t>0} Ai^{(j)}(y+t) ∈ L²(0,∞)` (differentiation under the integral, `AiryPwsDeriv`), then Parseval
  at the zeros (`airy_parseval_psi`).
* `airy_expansion` (the CFT PR 240 branch note `CE_O1_ROUTE.md` (not yet on `main`) O.11f, O.11n): for `v ∈ L²(ℝ)` supported in `(0,∞)` and
  `H(u) = ∫_0^∞ Ai(u+t) v(t) dt` (`airyPsi v`), with `b_n = ⟨φ_n, v⟩ = Ψv(a_n)/Ai'(a_n)`:
  `‖H‖₂ = ‖v‖₂ = (Σ b_n²)^{1/2}` (so `b ∈ ℓ²`), `v = Σ b_n φ_n` and `A v = Σ b_n L_n` in `L²`, and `H(u) = Σ b_n L_n(u)`
  for **every** real `u`, the series converging absolutely and **locally uniformly** with the explicit remainder
  `|H(u) - Σ_{n<N} b_n L_n(u)| ≤ √K(u,u) ‖v - Σ_{n<N} b_nφ_n‖`.

Numerical checks (mpmath, 25 digits): (a) for `j = 0,1,2`, `y ∈ {-8,-3,1/2}` the sum of the first 1500 terms plus the leading
tail `Ai^{(j)}(y)² Σ_{n>1500} a_n^{-2}` agrees with the integral to relative `2·10⁻⁴` (`3·10⁻⁶` for `y = -8`);
(b) for `v(t) = t e^{-t}` the truncation to 300 terms reproduces `H(-2) = 0.341179` to `7·10⁻⁵` (tail `O(N^{-1/3})`).

**Not formalised:** the same statement for complex `u` (only the real-line identity is stated; `L_n` and `H` are entire),
the rate of the tail `Σ_{n>N}`, and `v ∈ L²(ℝ)` not supported in `(0,∞)` (apply to `Pv`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

/-! ### `L_n` -/

/-- `L_n(u) = K(u,a_n)/Ai'(a_n)`, the entire function `Ai(u)/(u - a_n)` (value `Ai'(a_n)` at `u = a_n`). -/
noncomputable def airyLn (n : ℕ) (u : ℝ) : ℝ := airyKer u (airyZ n) / airyAi' (airyZ n)

lemma airyLn_of_ne {n : ℕ} {u : ℝ} (h : u ≠ airyZ n) : airyLn n u = airyAi u / (u - airyZ n) := by
  have hn := airyAi'_airyZ_ne_zero n
  have hs : u - airyZ n ≠ 0 := sub_ne_zero.mpr h
  unfold airyLn
  rw [airyKer_of_ne h]
  unfold airyKernelAi
  rw [airyAi_airyZ]
  field_simp
  ring

lemma airyLn_self (n : ℕ) : airyLn n (airyZ n) = airyAi' (airyZ n) := by
  have hn := airyAi'_airyZ_ne_zero n
  unfold airyLn
  rw [airyKer_self, airyAi_airyZ]
  field_simp
  ring

lemma iteratedDeriv_airyLn (j n : ℕ) :
    iteratedDeriv j (airyLn n) = fun x => airyKerD j x (airyZ n) / airyAi' (airyZ n) := by
  induction j with
  | zero => funext x; rw [iteratedDeriv_zero]; simp [airyLn, airyKerD_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact ((hasDerivAt_airyKerD' j x (airyZ n)).div_const _).deriv

/-! ### `L²` elements from continuous functions supported on `(0,∞)` -/

lemma airyLp_memLp {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0)) :
    MemLp (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (g t : ℂ)) t) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (g t : ℂ)) t) volume :=
    (Continuous.aestronglyMeasurable (by fun_prop)).indicator measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq_norm hm]
  rw [← integrable_indicator_iff measurableSet_Ioi] at hi
  refine hi.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht, Complex.norm_real, sq_abs]

/-- `1_{t>0} g(t)` as an element of `L²(ℝ)`. -/
noncomputable def airyLp {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0)) :
    AiryL2 := (airyLp_memLp hg hi).toLp _

lemma airyLp_coeFn {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0)) :
    airyLp hg hi =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (g t : ℂ)) t :=
  (airyLp_memLp hg hi).coeFn_toLp

lemma airyPL_airyLp {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0)) :
    airyPL (airyLp hg hi) = airyLp hg hi := by
  rw [airyPL_apply, airyIndProj_eq_self_iff]
  filter_upwards [airyLp_coeFn hg hi] with t ht htn
  rw [ht]; simp [htn]

lemma airyPsi_airyLp {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0))
    (u : ℝ) : airyPsi (airyLp hg hi) u = ((∫ t in Ioi 0, g t * airyAi (u + t) : ℝ) : ℂ) := by
  unfold airyPsi
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [airyLp_coeFn hg hi] with t ht htm
  rw [ht]; simp [htm]

lemma inner_airyLp_self {g : ℝ → ℝ} (hg : Continuous g) (hi : IntegrableOn (fun t => g t ^ 2) (Ioi 0)) :
    inner ℂ (airyLp hg hi) (airyLp hg hi) = ((∫ t in Ioi 0, g t ^ 2 : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [airyLp_coeFn hg hi] with t ht
  rw [ht]
  by_cases h : t ∈ Ioi (0 : ℝ)
  · simp [h, sq, ← Complex.ofReal_mul, abs_mul_abs_self]
  · simp [h]

/-! ### The sum rule for derivatives -/

/-- **Reproducing identity for derivatives** (the CFT PR 240 branch note `CE_O1_ROUTE.md` (not yet on `main`) (O.11ad.5)): for `L_n(u) = Ai(u)/(u - a_n)`, every `j ≥ 0`
and every real `y`, `Σ_{n ≥ 1} (L_n^{(j)}(y))² = ∫_y^∞ Ai^{(j)}(t)² dt`. -/
theorem airyLn_iteratedDeriv_sq_hasSum (j : ℕ) (y : ℝ) :
    HasSum (fun n : ℕ => (iteratedDeriv j (airyLn n) y) ^ 2) (∫ t in Ioi y, airyD j t ^ 2) := by
  have hg : Continuous fun t : ℝ => airyD j (y + t) := by
    have := continuous_airyD j; fun_prop
  have hi := integrableOn_airyD_sq j y
  set g : AiryL2 := airyLp hg hi with hgdef
  have h := airy_parseval_psi g g
  rw [airyPL_airyLp, inner_airyLp_self] at h
  have e1 : ∫ t in Ioi 0, airyD j (y + t) ^ 2 = ∫ t in Ioi y, airyD j t ^ 2 :=
    integral_Ioi_add_left (fun t => airyD j t ^ 2) y
  rw [e1] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  funext n
  rw [hgdef, airyPsi_airyLp, iteratedDeriv_airyLn]
  have hn : airyAi' (airyZ n) ≠ 0 := airyAi'_airyZ_ne_zero n
  have : (∫ t in Ioi 0, airyD j (y + t) * airyAi (airyZ n + t)) = airyKerD j y (airyZ n) := rfl
  rw [this]
  simp only [Complex.conj_ofReal]
  push_cast
  field_simp

/-! ### The expansion of `A v` in `L_n` -/

/-- `φ_n = 1_{t>0} Ai(a_n + t)/Ai'(a_n)`, a unit vector of `L²(0,∞)`. -/
noncomputable def airyPwsPhi (n : ℕ) : AiryL2 := (((1 / airyAi' (airyZ n) : ℝ) : ℂ)) • airyHalf (airyZ n)

lemma airyPL_airyPwsPhi (n : ℕ) : airyPL (airyPwsPhi n) = airyPwsPhi n := by
  unfold airyPwsPhi
  rw [map_smul, airyPL_airyHalf]

lemma inner_airyPwsPhi_airyPwsPhi (n m : ℕ) : inner ℂ (airyPwsPhi n) (airyPwsPhi m) = if n = m then 1 else 0 := by
  have hn := airyAi'_airyZ_ne_zero n
  have hm := airyAi'_airyZ_ne_zero m
  unfold airyPwsPhi
  rw [inner_smul_left, inner_smul_right, inner_airyHalf_airyHalf, airyKer_airyZ]
  by_cases h : n = m
  · subst h
    simp only [↓reduceIte, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : (1 / airyAi' (airyZ n)) * ((1 / airyAi' (airyZ n)) * airyAi' (airyZ n) ^ 2) = 1 := by
      field_simp
    rw [this]; simp
  · simp [h]

lemma inner_airyPwsPhi_left (n : ℕ) (v : AiryL2) :
    inner ℂ (airyPwsPhi n) v = airyPsi v (airyZ n) / ((airyAi' (airyZ n) : ℝ) : ℂ) := by
  have hn := airyAi'_airyZ_ne_zero n
  unfold airyPwsPhi
  rw [inner_smul_left, Complex.conj_ofReal, ← airyPsi_eq_inner]
  have : ((airyAi' (airyZ n) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  push_cast
  field_simp

/-- `A φ_n = L_n` almost everywhere. -/
lemma airyA_airyPwsPhi_ae (n : ℕ) : airyA (airyPwsPhi n) =ᵐ[volume] fun u : ℝ => (airyLn n u : ℂ) := by
  have h := airyKerL2_ae (airyZ n)
  have : airyA (airyPwsPhi n) = (((1 / airyAi' (airyZ n) : ℝ) : ℂ)) • airyKerL2 (airyZ n) := by
    unfold airyPwsPhi airyKerL2
    rw [map_smul]
  rw [this]
  filter_upwards [h, Lp.coeFn_smul (((1 / airyAi' (airyZ n) : ℝ) : ℂ)) (airyKerL2 (airyZ n))] with u hu hs
  rw [hs, Pi.smul_apply, hu, smul_eq_mul]
  unfold airyLn
  rw [airyKer_comm]
  push_cast
  ring

lemma airyA_airyBasisVec (n : ℕ) :
    airyA (airyBasisVec n) = (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) • airyHalf (airyZ n) := by
  unfold airyBasisVec airyKerL2
  rw [map_smul, airyA_airyA]

lemma airy_inv_abs_mul_self (n : ℕ) :
    (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) * (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) =
      1 / (((airyAi' (airyZ n) : ℝ) : ℂ) * ((airyAi' (airyZ n) : ℝ) : ℂ)) := by
  have : (1 / |airyAi' (airyZ n)|) * (1 / |airyAi' (airyZ n)|) =
      1 / (airyAi' (airyZ n) * airyAi' (airyZ n)) := by
    rw [div_mul_div_comm, one_mul, abs_mul_abs_self]
  exact_mod_cast this

/-- The expansion `v = Σ ⟨φ_n, v⟩ φ_n` of `v ∈ L²(0,∞)`: the family `φ_n` is a Hilbert basis of `L²(0,∞)`. -/
theorem airy_hasSum_airyPwsPhi (v : AiryL2) (hv : airyPL v = v) :
    HasSum (fun n : ℕ => inner ℂ (airyPwsPhi n) v • airyPwsPhi n) v := by
  have hmem : airyA v ∈ airyPW := (mem_airyPW_iff_exists _).mpr ⟨v, hv, rfl⟩
  let xPW : airyPW := ⟨airyA v, hmem⟩
  have hrep := airyPW_hilbertBasis.hasSum_repr xPW
  have h1 := hrep.mapL (Submodule.subtypeL airyPW)
  have h2 := h1.mapL airyAL
  have hAA : airyAL ((Submodule.subtypeL airyPW) xPW) = v := by
    simp [airyAL_apply, xPW, airyA_airyA]
  rw [hAA] at h2
  convert h2 using 1
  funext n
  simp only [ContinuousLinearMap.map_smul, Submodule.subtypeL_apply, coe_airyPW_hilbertBasis,
    HilbertBasis.repr_apply_apply, airyBasisVecPW, airyAL_apply]
  have hn := airyAi'_airyZ_ne_zero n
  have hnc : ((airyAi' (airyZ n) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  rw [Submodule.coe_inner, show ((xPW : airyPW) : AiryL2) = airyA v from rfl,
    inner_airyBasisVec_airyA, airyA_airyBasisVec, inner_airyPwsPhi_left]
  unfold airyPwsPhi
  rw [smul_smul, smul_smul]
  congr 1
  have e : ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * airyPsi v (airyZ n) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) =
      airyPsi v (airyZ n) * (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) := by
    ring
  rw [e, airy_inv_abs_mul_self]
  push_cast
  field_simp

/-- **Expansion of `A v` in the functions `L_n`** (the CFT PR 240 branch note `CE_O1_ROUTE.md` (not yet on `main`) O.11f, O.11n): let `v ∈ L²(ℝ)` vanish on `(-∞,0]`,
`H = A v`, `H(u) = ∫_0^∞ Ai(u+t) v(t) dt` (`airyPsi v`), `b_n = ⟨φ_n, v⟩ = Ψv(a_n)/Ai'(a_n)`. Then `‖H‖ = ‖v‖`,
`Σ |b_n|² = ‖v‖²`, `v = Σ b_n φ_n`, `A v = Σ b_n A φ_n` (`A φ_n = L_n`) in `L²`, and for every real `u`
`H(u) = Σ b_n L_n(u)`, absolutely convergent, locally uniformly in `u`. -/
theorem airy_expansion (v : AiryL2) (hv : airyPL v = v) :
    ‖airyA v‖ = ‖v‖ ∧
    (∀ n, inner ℂ (airyPwsPhi n) v = airyPsi v (airyZ n) / ((airyAi' (airyZ n) : ℝ) : ℂ)) ∧
    HasSum (fun n : ℕ => ‖inner ℂ (airyPwsPhi n) v‖ ^ 2) (‖v‖ ^ 2) ∧
    HasSum (fun n : ℕ => inner ℂ (airyPwsPhi n) v • airyPwsPhi n) v ∧
    HasSum (fun n : ℕ => inner ℂ (airyPwsPhi n) v • airyA (airyPwsPhi n)) (airyA v) ∧
    (∀ u : ℝ, HasSum (fun n : ℕ => inner ℂ (airyPwsPhi n) v * (airyLn n u : ℂ)) (airyPsi v u)) ∧
    (∀ u : ℝ, Summable fun n : ℕ => ‖inner ℂ (airyPwsPhi n) v * (airyLn n u : ℂ)‖) ∧
    TendstoLocallyUniformly
      (fun (N : ℕ) (u : ℝ) => ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v * (airyLn n u : ℂ))
      (fun u => airyPsi v u) atTop := by
  have h3 := airy_hasSum_airyPwsPhi v hv
  -- inner products with `airyHalf u`
  have hu : ∀ u : ℝ, HasSum (fun n : ℕ => inner ℂ (airyPwsPhi n) v * (airyLn n u : ℂ)) (airyPsi v u) := by
    intro u
    have := h3.mapL (innerSL ℂ (airyHalf u))
    rw [innerSL_apply_apply, ← airyPsi_eq_inner] at this
    convert this using 1
    funext n
    rw [innerSL_apply_apply, inner_smul_right]
    unfold airyPwsPhi
    rw [inner_smul_right, inner_airyHalf_airyHalf]
    unfold airyLn
    push_cast
    ring
  have hpars : HasSum (fun n : ℕ => ‖inner ℂ (airyPwsPhi n) v‖ ^ 2) (‖v‖ ^ 2) := by
    have h := airy_parseval_psi v v
    rw [hv, inner_self_eq_norm_sq_to_K] at h
    rw [← Complex.hasSum_ofReal]
    convert h using 1
    · funext n
      rw [inner_airyPwsPhi_left, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      have hn : ((airyAi' (airyZ n) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (airyAi'_airyZ_ne_zero n)
      rw [map_div₀, Complex.conj_ofReal]
      push_cast
      field_simp
    · simp
  refine ⟨airyA_norm v, fun n => inner_airyPwsPhi_left n v, hpars, h3, ?_, hu, ?_, ?_⟩
  · have := h3.mapL airyAL
    simpa only [ContinuousLinearMap.map_smul, airyAL_apply] using this
  · intro u
    have hL : Summable fun n : ℕ => (airyLn n u) ^ 2 := by
      have := (airyLn_iteratedDeriv_sq_hasSum 0 u).summable
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((hpars.summable.add hL).mul_left (1 / 2))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := two_mul_le_add_sq ‖inner ℂ (airyPwsPhi n) v‖ |airyLn n u|
    rw [sq_abs] at this
    linarith
  · -- locally uniform convergence
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    have hcont : ContinuousOn (fun u : ℝ => √(airyKer u u)) (Metric.closedBall x 1) :=
      (continuous_airyKer_diag.sqrt).continuousOn
    obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hcont
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    have hconv : Tendsto (fun N : ℕ => ‖v - ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v • airyPwsPhi n‖)
        atTop (𝓝 0) := by
      have := h3.tendsto_sum_nat
      have h0 := (this.const_sub v)
      rw [sub_self] at h0
      simpa using h0.norm
    have hpos : 0 < ε / (|M| + 1) := by positivity
    filter_upwards [hconv.eventually (gt_mem_nhds hpos)] with N hN u hu
    have hres : airyPsi v u - ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v * (airyLn n u : ℂ) =
        inner ℂ (airyHalf u) (v - ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v • airyPwsPhi n) := by
      rw [inner_sub_right, ← airyPsi_eq_inner, inner_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [inner_smul_right]
      unfold airyPwsPhi
      rw [inner_smul_right, inner_airyHalf_airyHalf]
      unfold airyLn
      push_cast
      ring
    rw [dist_eq_norm, hres]
    refine lt_of_le_of_lt (norm_inner_le_norm _ _) ?_
    have hK : ‖airyHalf u‖ ≤ |M| + 1 := by
      rw [← Real.sqrt_sq (norm_nonneg (airyHalf u)), norm_airyHalf_sq]
      have := hM u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
      linarith [le_abs_self M]
    calc ‖airyHalf u‖ * ‖v - ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v • airyPwsPhi n‖
        ≤ (|M| + 1) * ‖v - ∑ n ∈ Finset.range N, inner ℂ (airyPwsPhi n) v • airyPwsPhi n‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ < (|M| + 1) * (ε / (|M| + 1)) := by gcongr
      _ = ε := by field_simp

/-- info: 'FormalResearch.Special.airyLn_iteratedDeriv_sq_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyLn_iteratedDeriv_sq_hasSum

/-- info: 'FormalResearch.Special.airy_hasSum_airyPwsPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_hasSum_airyPwsPhi

/-- info: 'FormalResearch.Special.airy_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_expansion

end FormalResearch.Special
