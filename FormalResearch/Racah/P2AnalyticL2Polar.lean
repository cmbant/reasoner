module

public import FormalResearch.Racah.P2AnalyticL2Singular
public import FormalResearch.Racah.P2AnalyticL2PolarAbs

/-!
# The beta-binomial polar factor `𝖴_D` in `L²(ν_H)` (Weyl P2, `prop:betabinomialpolar`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:betabinomialpolar`
(`eq:betameasure`-`eq:singularvaluesgeneral`), `lem:polarintertwiner`, Appendix `app:beta-polar`.

## Formulation

* `nuH α β` is the beta measure `ν_H` (`eq:betameasure`) on `[0,1]` and `L2nu α β = L²(ν_H)` the genuine
  `Lp ℝ 2 (nuH α β)`; `L2nuc f` is the class of a continuous function and `inner_L2nu` gives
  `⟪[f],[g]⟫ = (1/B) ∫_0^1 t^α(1-t)^β f g`.
* `ℓ²(p_D)` is realised as `EuclideanSpace ℝ (Fin (D+1))` through the unitary identification
  `q ↦ (√p_D(u) q(u))_u` (`wvec`; `inner_wvec : ⟪wvec f, wvec g⟫ = Σ_u p_D(u) f(u) g(u)`).
  The Hahn mode `H_n` is `HW n = wvec (Hmode n)`.
* `Cfull : L²(ν_H) →ₗ ℓ²(p_D)` is the conditional expectation `eq:conditionalC`
  (`Cfull_L2nuc : Cfull [f] = wvec (CopBeta f)`, i.e. `(C_D f)(u) = ⟪b_u^D, f⟫_{ν_H}/p_D(u)`), and
  `TD = Cfull|_{P_D}` on `PD = span{J_0,…,J_D}` (`eq:conditionalC` restricted).
* `JV : OrthonormalBasis (Fin (D+1)) ℝ (PD α β D)` consists of the unit Jacobi modes `J_n = Jmode`.

## Proved here

* `TD_JV`: `T_D J_n = s_n H_n`, `s_n = √(singularSq)` `> 0` (`eq:singularvaluesgeneral`, from `singular_pair`);
* `TD_bijective`: `T_D` is invertible between the two `(D+1)`-dimensional spaces;
* `UD := polarFactor TD` `= T_D (T_D^* T_D)^{-1/2}` (`Polar.polarFactor`): `UD_unitary` (isometric and
  bijective) and `UD_JV : U_D J_n = H_n`.
-/

@[expose] public section

namespace FormalResearch.Racah

open MeasureTheory Polar FormalResearch.Special
open scoped InnerProductSpace

/-! ### `L²(ν_H)` -/

/-- The beta measure `dν_H(t) = t^α(1-t)^β/B(α+1,β+1) dt` on `[0,1]` (`eq:betameasure`). -/
noncomputable def nuH (α β : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (wtJ α β t / betaB α β))

lemma wtJ_nonneg {α β : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ wtJ α β t := by
  unfold wtJ
  have h1 : 0 ≤ t := ht.1
  have h2 : 0 ≤ 1 - t := by linarith [ht.2]
  positivity

lemma wtJ_div_continuous (α β : ℕ) : Continuous (fun t => wtJ α β t / betaB α β) :=
  (wtJ_continuous α β).div_const _

instance nuH_finite (α β : ℕ) : IsFiniteMeasure (nuH α β) := by
  unfold nuH
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact ((wtJ_div_continuous α β).integrableOn_Icc (a := 0) (b := 1)).hasFiniteIntegral

/-- `L²(ν_H)`. -/
abbrev L2nu (α β : ℕ) : Type := Lp ℝ 2 (nuH α β)

lemma memLp_nu (α β : ℕ) {f : ℝ → ℝ} (hf : Continuous f) : MemLp f 2 (nuH α β) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  have h : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖f t‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall hC
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- The class in `L²(ν_H)` of a continuous function. -/
noncomputable def L2nuc (α β : ℕ) (f : ℝ → ℝ) (hf : Continuous f) : L2nu α β :=
  (memLp_nu α β hf).toLp f

/-- `⟪[f],[g]⟫_{L²(ν_H)} = (1/B) ∫_0^1 t^α(1-t)^β f g dt`. -/
theorem inner_L2nuc (α β : ℕ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ⟪L2nuc α β f hf, L2nuc α β g hg⟫_ℝ = (1 / betaB α β) * ipJ α β f g := by
  unfold L2nuc
  rw [MeasureTheory.L2.inner_def]
  have h1 := (memLp_nu α β hf).coeFn_toLp
  have h2 := (memLp_nu α β hg).coeFn_toLp
  have : ∫ a, ⟪(memLp_nu α β hf).toLp f a, (memLp_nu α β hg).toLp g a⟫_ℝ ∂nuH α β =
      ∫ a, f a * g a ∂nuH α β := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with a ha hb
    rw [ha, hb]
    simp [mul_comm]
  rw [this]
  unfold nuH
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun t => ENNReal.ofReal (wtJ α β t / betaB α β))
    (ENNReal.measurable_ofReal.comp (wtJ_div_continuous α β).measurable)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have e : ∫ x, (ENNReal.ofReal (wtJ α β x / betaB α β)).toReal • (f x * g x)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∫ x, (1 / betaB α β) * (wtJ α β x * (f x * g x))
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have := wtJ_nonneg (α := α) (β := β) hx
    have hB := betaB_pos α β
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    field_simp
  rw [e, integral_const_mul]
  congr 1
  unfold ipJ
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]


/-! ### The modes `J_n`, `H_n` and the channel `C_D` -/

lemma Jmode_continuous (α β n : ℕ) : Continuous (Jmode α β n) :=
  (jT_continuous α β n).div_const _

/-- The unit Jacobi mode `J_n ∈ L²(ν_H)`. -/
noncomputable def JL (α β n : ℕ) : L2nu α β := L2nuc α β (Jmode α β n) (Jmode_continuous α β n)

/-- The Bernstein polynomial `b_u^D ∈ L²(ν_H)`. -/
noncomputable def bL (α β D u : ℕ) : L2nu α β := L2nuc α β (bern D u) (bern_continuous D u)

lemma jT_norm_pos (α β n : ℕ) : 0 < (1 / betaB α β) * ipJ α β (jT α β n) (jT α β n) :=
  mul_pos (by have := betaB_pos α β; positivity) (ipJ_jT_pos α β n)

lemma ipJ_div (α β : ℕ) (f g : ℝ → ℝ) (c d : ℝ) :
    ipJ α β (fun t => f t / c) (fun t => g t / d) = (c * d)⁻¹ * ipJ α β f g := by
  unfold ipJ
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only
  ring

lemma ipJ_Jmode (α β n m : ℕ) :
    ipJ α β (Jmode α β n) (Jmode α β m) =
      (Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n)) *
        Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β m) (jT α β m)))⁻¹ *
        ipJ α β (jT α β n) (jT α β m) :=
  ipJ_div α β (jT α β n) (jT α β m) _ _

/-- `⟪J_n, J_m⟫ = δ_{nm}` in `L²(ν_H)`. -/
theorem JL_inner (α β n m : ℕ) : ⟪JL α β n, JL α β m⟫_ℝ = if n = m then 1 else 0 := by
  unfold JL
  rw [inner_L2nuc, ipJ_Jmode]
  by_cases h : n = m
  · subst h
    simp only [↓reduceIte]
    have hp := jT_norm_pos α β n
    have hI := ipJ_jT_pos α β n
    have hB := betaB_pos α β
    rw [Real.mul_self_sqrt hp.le]
    field_simp
  · simp [h, ipJ_jT_orth α β h]

lemma bL_inner (α β D u : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    ⟪bL α β D u, L2nuc α β f hf⟫_ℝ = (1 / betaB α β) * ∫ t in (0 : ℝ)..1, bern D u t * f t * wtJ α β t := by
  unfold bL
  rw [inner_L2nuc]
  congr 1
  unfold ipJ
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- The conditional expectation `C_D : L²(ν_H) → ℓ²(p_D)` (`eq:conditionalC`), in the coordinates
`ℓ²(p_D) ≅ ℝ^{D+1}`, `q ↦ (√p_D(u) q(u))_u`: `(C_D f)_u = ⟪b_u^D, f⟫_{ν_H}/√p_D(u)`. -/
noncomputable def Cfull (α β D : ℕ) : L2nu α β →ₗ[ℝ] EuclideanSpace ℝ (Fin (D + 1)) where
  toFun x := WithLp.toLp 2 (fun i : Fin (D + 1) =>
    (Real.sqrt (pD α β D i))⁻¹ * ⟪bL α β D i, x⟫_ℝ)
  map_add' x y := by
    ext i
    simp [inner_add_right, mul_add]
  map_smul' c x := by
    ext i
    simp [inner_smul_right]
    ring

/-- `C_D [f] = wvec (C_D f)`: `Cfull` is the conditional expectation `CopBeta` of a continuous
function. -/
theorem Cfull_L2nuc (α β D : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Cfull α β D (L2nuc α β f hf) = wvec α β D (CopBeta α β D f) := by
  ext i
  have hp := pD_pos α β D i (by omega)
  have hs : 0 < Real.sqrt (pD α β D i) := Real.sqrt_pos.2 hp
  have hs2 := Real.sq_sqrt hp.le
  simp only [Cfull, LinearMap.coe_mk, AddHom.coe_mk, wvec, bL_inner]
  unfold CopBeta
  field_simp
  rw [hs2]
  ring

/-! ### Orthonormal bases and `T_D` -/

/-- `P_D = span{J_0,…,J_D} ⊂ L²(ν_H)`. -/
noncomputable def PD (α β D : ℕ) : Submodule ℝ (L2nu α β) :=
  Submodule.span ℝ (Set.range (fun n : Fin (D + 1) => JL α β n))

instance PD_finiteDimensional (α β D : ℕ) : FiniteDimensional ℝ (PD α β D) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

lemma JL_mem (α β D : ℕ) (n : Fin (D + 1)) : JL α β n ∈ PD α β D :=
  Submodule.subset_span ⟨n, rfl⟩

/-- The orthonormal basis `J_0,…,J_D` of `P_D`. -/
noncomputable def JV (α β D : ℕ) : OrthonormalBasis (Fin (D + 1)) ℝ (PD α β D) :=
  OrthonormalBasis.mk
    (v := fun n : Fin (D + 1) => (⟨JL α β n, JL_mem α β D n⟩ : PD α β D))
    (orthonormal_iff_ite.2 fun i j => by
      simp only [Submodule.coe_inner, JL_inner, Fin.val_inj])
    (by
      intro x _
      have h : Submodule.span ℝ (Set.range
          (fun n : Fin (D + 1) => (⟨JL α β n, JL_mem α β D n⟩ : PD α β D))) = ⊤ := by
        apply Submodule.map_injective_of_injective (Submodule.subtype_injective (PD α β D))
        rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
        rfl
      rw [h]; trivial)

lemma JV_coe (α β D : ℕ) (n : Fin (D + 1)) : ((JV α β D n : PD α β D) : L2nu α β) = JL α β n := by
  simp [JV]

/-- The unit Hahn modes `H_n` of `ℓ²(p_D)` (in the coordinates `q ↦ √p_D q`). -/
noncomputable def HW (α β D : ℕ) (n : Fin (D + 1)) : EuclideanSpace ℝ (Fin (D + 1)) :=
  wvec α β D (Hmode α β D n)

lemma HW_inner (α β D : ℕ) (n m : Fin (D + 1)) :
    ⟪HW α β D n, HW α β D m⟫_ℝ = if n = m then 1 else 0 := by
  unfold HW
  rw [inner_wvec]
  have hn := ipP_Q_pos α β D n
  have hm := ipP_Q_pos α β D m
  have hdiv : ∀ (f g : ℕ → ℝ) (c d : ℝ),
      ipP α β D (fun u => f u / c) (fun u => g u / d) = (c * d)⁻¹ * ipP α β D f g := by
    intro f g c d
    unfold ipP
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have e : ipP α β D (Hmode α β D n) (Hmode α β D m) =
      (Real.sqrt (ipP α β D (hahnQ α β D n) (hahnQ α β D n)) *
        Real.sqrt (ipP α β D (hahnQ α β D m) (hahnQ α β D m)))⁻¹ *
        ipP α β D (hahnQ α β D n) (hahnQ α β D m) :=
    hdiv (hahnQ α β D n) (hahnQ α β D m) _ _
  rw [e]
  by_cases h : n = m
  · subst h
    simp only [↓reduceIte]
    rw [Real.mul_self_sqrt hn.le]
    exact inv_mul_cancel₀ hn.ne'
  · have : (n : ℕ) ≠ m := fun e => h (Fin.ext e)
    rw [ipP_Q_orth α β D n m (by omega) (by omega) this]
    simp [h]

/-- The orthonormal basis `H_0,…,H_D` of `ℓ²(p_D) ≅ ℝ^{D+1}`. -/
noncomputable def HB (α β D : ℕ) : OrthonormalBasis (Fin (D + 1)) ℝ (EuclideanSpace ℝ (Fin (D + 1))) :=
  OrthonormalBasis.mk (v := HW α β D)
    (orthonormal_iff_ite.2 fun i j => HW_inner α β D i j)
    (by
      have hon : Orthonormal ℝ (HW α β D) := orthonormal_iff_ite.2 fun i j => HW_inner α β D i j
      exact (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge)

lemma HB_coe (α β D : ℕ) (n : Fin (D + 1)) : HB α β D n = HW α β D n := by
  simp [HB]

/-- **`T_D = C_D|_{P_D} : P_D → ℓ²(p_D)`.** -/
noncomputable def TD (α β D : ℕ) : PD α β D →ₗ[ℝ] EuclideanSpace ℝ (Fin (D + 1)) :=
  Cfull α β D ∘ₗ (PD α β D).subtype

/-- The singular value `s_n = √(D^{\underline n}/(D+α+β+2)_n)`. -/
noncomputable def sing (α β D : ℕ) (n : Fin (D + 1)) : ℝ := Real.sqrt (singularSq α β D n)

lemma sing_pos (α β D : ℕ) (n : Fin (D + 1)) : 0 < sing α β D n :=
  Real.sqrt_pos.2 (singularSq_pos α β D n (by omega))

/-- **`eq:singularvaluesgeneral`**: `T_D J_n = s_n H_n`. -/
theorem TD_JV (α β D : ℕ) (n : Fin (D + 1)) :
    TD α β D (JV α β D n) = sing α β D n • HB α β D n := by
  unfold TD
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply]
  rw [JV_coe, HB_coe]
  unfold JL
  rw [Cfull_L2nuc]
  ext i
  have hp := pD_pos α β D i (by omega)
  simp only [wvec, HW, PiLp.smul_apply, smul_eq_mul, sing]
  rw [singular_pair α β D n (by omega) (u := i) (by omega)]
  ring

/-- `T_D` is injective (and invertible, `TD_bijective`). -/
theorem TD_injective (α β D : ℕ) : Function.Injective (TD α β D) :=
  injective_of_basis (JV α β D) (HB α β D) (sing_pos α β D) (TD_JV α β D)

/-- **`T_D` is invertible between two `(D+1)`-dimensional Hilbert spaces.** -/
theorem TD_bijective (α β D : ℕ) : Function.Bijective (TD α β D) :=
  (bijective_of_basis (JV α β D) (HB α β D) (sing_pos α β D) (TD_JV α β D)).1

/-- **The polar factor** `U_D = T_D (T_D^* T_D)^{-1/2} : P_D → ℓ²(p_D)`. -/
noncomputable def UD (α β D : ℕ) : PD α β D →ₗ[ℝ] EuclideanSpace ℝ (Fin (D + 1)) :=
  polarFactor (TD α β D) (TD_injective α β D)

/-- **`U_D` is unitary** (isometric and bijective). -/
theorem UD_unitary (α β D : ℕ) :
    (∀ x y, ⟪UD α β D x, UD α β D y⟫_ℝ = ⟪x, y⟫_ℝ) ∧ Function.Bijective (UD α β D) :=
  ⟨inner_polarFactor _ _,
    (bijective_of_basis (JV α β D) (HB α β D) (sing_pos α β D) (TD_JV α β D)).2⟩

/-- **`U_D J_n = H_n`** (`prop:betabinomialpolar`). -/
theorem UD_JV (α β D : ℕ) (n : Fin (D + 1)) : UD α β D (JV α β D n) = HB α β D n :=
  polarFactor_basis (JV α β D) (HB α β D) (sing_pos α β D) (TD_JV α β D) n

/-- info: 'FormalResearch.Racah.inner_L2nuc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_L2nuc

/-- info: 'FormalResearch.Racah.JL_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JL_inner

/-- info: 'FormalResearch.Racah.Cfull_L2nuc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cfull_L2nuc

/-- info: 'FormalResearch.Racah.TD_JV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TD_JV

/-- info: 'FormalResearch.Racah.TD_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TD_bijective

/-- info: 'FormalResearch.Racah.UD_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UD_unitary

/-- info: 'FormalResearch.Racah.UD_JV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UD_JV

end FormalResearch.Racah
