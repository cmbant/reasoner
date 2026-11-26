module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasAverage

/-!
# `ct:boas-ineq`: the block assembly in abstract form

`constant_terms_lower.tex`, proof of `ct:boas` (Lemma `ct:boas`, inequality `ct:boas-ineq`), Steps 3 and 5: the partition
of unity `χ_j` on the logarithmic band variable `L`, the reduction to blocks, the sum over blocks of the one-block
lemma `block_average` (`CtBoasAverage`), the truncation to `[L_min, L_far+1]`, and the bounded-overlap aggregation of the
pointwise block errors (`ct:Bj-pointwise`, `ct:sumBj`).

Everything here is real analysis in the variable `L`; no Hankel input.  The Hankel facts enter only through the fields
of `BoasInputs`, each of which is a statement the paper proves separately (see the field docstrings, and the table in the
docstring of `BoasInputs`).

**Proved**: `boas_ineq_assembled`, `sum_block_errors_le`; **assumed**: the fields of `BoasInputs`.
-/

@[expose] public section

open MeasureTheory Set
open FormalResearch.SignUncertainty.CtBoasWindow

namespace FormalResearch.SignUncertainty

/-- The phase factor `1 - 2 sin X(L)` of `ct:boas-ineq`, `X = Ξ - θ_ε ∘ τ₀`. -/
noncomputable def boasKernel (X : ℝ → ℝ) (L : ℝ) : ℝ := 1 - 2 * Real.sin (X L)

/-- The frozen kernel `T_{L₀}(L) = 1 - 2 sin(X(L₀) + ω₀(L - L₀))` (`ct:P-lb`), `ω₀ = ν(L₀) = cτ₀(L₀)`. -/
noncomputable def boasFrozenKernel (X ν : ℝ → ℝ) (L0 L : ℝ) : ℝ :=
  1 - 2 * Real.sin (X L0 + ν L0 * (L - L0))

lemma abs_boasKernel_le (X : ℝ → ℝ) (L : ℝ) : |boasKernel X L| ≤ 3 := by
  unfold boasKernel
  have := Real.neg_one_le_sin (X L); have := Real.sin_le_one (X L)
  rw [abs_le]; constructor <;> linarith

lemma abs_boasFrozenKernel_le (X ν : ℝ → ℝ) (L0 L : ℝ) : |boasFrozenKernel X ν L0 L| ≤ 3 := by
  unfold boasFrozenKernel
  have := Real.neg_one_le_sin (X L0 + ν L0 * (L - L0)); have := Real.sin_le_one (X L0 + ν L0 * (L - L0))
  rw [abs_le]; constructor <;> linarith

lemma measurable_boasKernel {X : ℝ → ℝ} (hX : Measurable X) : Measurable (boasKernel X) := by
  unfold boasKernel
  exact measurable_const.sub (measurable_const.mul (Real.measurable_sin.comp hX))

lemma measurable_boasFrozenKernel {X ν : ℝ → ℝ} (hX : Measurable X) (hν : Measurable ν) :
    Measurable (fun p : ℝ × ℝ => boasFrozenKernel X ν p.2 p.1) := by
  unfold boasFrozenKernel
  have h1 : Measurable fun p : ℝ × ℝ => X p.2 := hX.comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => ν p.2 := hν.comp measurable_snd
  exact measurable_const.sub (measurable_const.mul (Real.measurable_sin.comp
    (h1.add (h2.mul (measurable_fst.sub measurable_snd)))))


/-- **Partition-of-unity data** (`ct:boas` Step 3): `J` blocks `χ_0, …, χ_{J-1}` with `0 ≤ χ_j`, `Σ_j χ_j ≤ 1` on `ℝ`,
`Σ_j χ_j = 1` on `[a, b] = [L_min, L_far + 1]`, every `χ_j` vanishing off `[lo, hi]` (the zero extension to `ℝ`).
The tent partition of `CtBoasTent` is an instance. -/
structure BoasPartition (J : ℕ) (χ : ℕ → ℝ → ℝ) (a b lo hi : ℝ) : Prop where
  meas : ∀ j < J, Measurable (χ j)
  nonneg : ∀ j < J, ∀ L, 0 ≤ χ j L
  sum_le_one : ∀ L, ∑ j ∈ Finset.range J, χ j L ≤ 1
  sum_eq_one : ∀ L ∈ Icc a b, ∑ j ∈ Finset.range J, χ j L = 1
  supp : ∀ j < J, ∀ L, L ∉ Icc lo hi → χ j L = 0
  lo_le_hi : lo ≤ hi

/-- Well-formedness of the band data (regularity only, no paper input): `h = h(L)` integrable, the phase `X`, the
frequency `ν = cτ₀`, the taper `wt = w̃_R(ξ(L)) ∈ [0,1]` and the Gaussian step `sf = 𝔰_far(cξ(L)) ∈ [0,1]` measurable. -/
structure BoasSetting (h X ν wt sf : ℝ → ℝ) : Prop where
  h_int : Integrable h
  X_meas : Measurable X
  ν_meas : Measurable ν
  wt_meas : Measurable wt
  sf_meas : Measurable sf
  wt_mem : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1
  sf_mem : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1


/-- **The separately proved inputs of `ct:boas-ineq`.**  Notation: `L = log(π²ξ)`; `h(L)dL = dm(ξ)`; `wt = w̃_R(ξ(L))`;
`sf = 𝔰_far(cξ(L))`; `Ω_near = wt·(1 - sf)`; `K = 1 - 2 sin X`; `T_{L₀}(L) = 1 - 2 sin(X(L₀) + ν(L₀)(L - L₀))`;
`ω_j = Ω_near χ_j`; `Q_j = I_j^{**}`; `G_{W_j}(u)` the centred Gaussian.  Each field is a statement of
`constant_terms_lower.tex` proved outside the assembly (the Lean module discharging it, when it exists, in brackets):

* `mass` — `∫|h| = M[f] = 1` (`integral_abs_hankelHL`).
* `far`, `εfar` — Step 1, `ℬ_far ≥ -O(c^{-8.8} log c)` (`hankel_psiT_fejer` and the bookkeeping `ℬ_far = ∫ψ̃(1 + 2cos(2πΔ + φ_∞)) + O(c^{-8.8}log c)`
  through `ct:phase-far`, `ct:outer`(3); not yet assembled).
* `trunc_hi`, `εhi` — Step 3 truncation above `L_far + 1`: `Ω_near ≤ 1 - 𝔰_far ≤ e^{-2(log c)²}` there and `∫|h| ≤ 1`.
* `trunc_lo`, `εlo` — Step 3 truncation below `L_min`: the taper estimate `∫_{ξ(0)}^{ξ(-v₀)} w̃_R |dm| = O(c^{-29/21})` of `ct:dyadic`(1),
  with `Ω_near ≤ w̃_R`.
* `P_lb`, `Pb` — `ct:P-lb` (Step 4): `P_j(L₀) ≥ -C c^{-4}√log c` for every `L₀` with `ω_j(L₀) > 0`, in the frozen form
  `∫ G_{W_j}(L - L₀) h(L) T_{L₀}(L) dL ≥ -Pb` (`hankel_frozen_P_lb`; `T_{L₀}` as `1 + 2cos(ω₀L + φ₀ - ω₀L₀)` with `φ₀ = π/2 + X(L₀)`,
  `ω₀ = cτ₀(L₀)`, the block comparison `τ_j/3 ≤ τ₀(L₀) ≤ 3τ_j` being `tau0_ratio`).
* `freeze` — Step 5, "Estimate of `D_j` on the whole line": `|D_j| ≤ 1_{Q_j}(L)(A_j|L - L₀| + B_j(L - L₀)²) + Kd_j(L - L₀)²`
  for all `L, L₀ ∈ ℝ`, `A_j = 3M_j' + 2S_jM_j^θ`, `B_j = S_jM_j''`; the far pairs `|L - L₀| > δ_j` have `|D_j| ≤ 6 ≤ Kd_j(L-L₀)²`
  with `Kd_j = 6/δ_j²` (a Chebyshev tail in place of the TeX's `O(e^{-c^{3/2}})`).  Discharged by `Ξ' = cτ₀`, `Ξ'' = c/m'(τ₀)`,
  `ct:outer`(3) (`|θ_ε'(t)| ≤ C_θ(1+t)^{-2}`), `hankelEdgeM'_bounds`, and the Lipschitz bound of `Ω_near χ_j` on the whole line
  (`ct:Bj-pointwise`(d); the tent partition of `CtBoasTent` supplies the Lipschitz bound of `χ_j`).
* `Kd_W`, `κ` — the far-pair cost `Kd_j W_j² ≤ κ` (`W_j ≤ C c^{-6/7}√(log c) δ_j`, Step 3 block-scale bounds).
* `pointwise`, `s`, `e`, `Kstar` — `ct:Bj-pointwise`: `A_jW_j + B_jW_j² ≤ 3s_j + K_* e(L)` for every `L ∈ Q_j`, with
  `s_j = M_j^σ W_j` and `e(L) = w̃(L)[c(1+τ²)W²/τ + W/τ + W/ℓ]` (`ct:Bj-pointwise`(a)-(d), `ct:taper-harnack`, `ct:Wj-harnack`).
* `mult`, `K0` — bounded overlap `K_0 = 12K_1` of the blocks `Q_j` (`ct:Bj-pointwise`(a); for the tent partition a counting lemma).
* `e_int`, `e_moment`, `εe` — `ct:Bj-pointwise`(f): `∫_{⋃Q_j} h e dL = O(c^{-4/3} log c)` (here `h ≥ 0` on `⋃Q_j`, so `h = |h|`),
  from `ct:dyadic`(1): `∫_0^{R'} v' dm ≤ Cc^{1/3}`, `∫_{L ≥ Λ} h = B₂(R') = O(c^{-1/3})`.
* `s_moment`, `εs` — `ct:Bj-pointwise`(e): `Σ_j s_j ∫_{Q_j}|h| = O(c^{-4/3} log c)` (the derivative of `𝔰_far`).
-/
structure BoasInputs (h X ν wt sf : ℝ → ℝ) (Lmin Lfar : ℝ) (J : ℕ) (χ : ℕ → ℝ → ℝ) (Q : ℕ → Set ℝ)
    (W A B Kd s : ℕ → ℝ) (e : ℝ → ℝ)
    (M εfar εhi εlo Pb κ Kstar K0 εe εs : ℝ) : Prop where
  mass : ∫ L, |h L| ≤ M
  far : -εfar ≤ ∫ L in Ici Lmin, wt L * sf L * (h L * boasKernel X L)
  trunc_hi : ∫ L in Ioi (Lfar + 1), wt L * (1 - sf L) * |h L| ≤ εhi
  trunc_lo : ∫ L in Iio Lmin, wt L * (1 - sf L) * |h L| ≤ εlo
  Pb_nonneg : 0 ≤ Pb
  W_pos : ∀ j < J, 0 < W j
  Q_meas : ∀ j < J, MeasurableSet (Q j)
  A_nonneg : ∀ j < J, 0 ≤ A j
  Kd_nonneg : ∀ j < J, 0 ≤ Kd j
  P_lb : ∀ j < J, ∀ L0, 0 < wt L0 * (1 - sf L0) * χ j L0 →
    -Pb ≤ ∫ L, gaussK (W j) (L - L0) * h L * boasFrozenKernel X ν L0 L
  freeze : ∀ j < J, ∀ L L0,
    |wt L * (1 - sf L) * χ j L * boasKernel X L -
        wt L0 * (1 - sf L0) * χ j L0 * boasFrozenKernel X ν L0 L| ≤
      (Q j).indicator (fun L => A j * |L - L0| + B j * (L - L0) ^ 2) L + Kd j * (L - L0) ^ 2
  Kd_W : ∀ j < J, Kd j * W j ^ 2 ≤ κ
  pointwise : ∀ j < J, ∀ L ∈ Q j, A j * W j + B j * W j ^ 2 ≤ 3 * s j + Kstar * e L
  Kstar_nonneg : 0 ≤ Kstar
  e_nonneg : ∀ L, 0 ≤ e L
  mult : ∀ L, ∑ j ∈ Finset.range J, (Q j).indicator (fun _ => (1 : ℝ)) L ≤ K0
  e_int : Integrable fun L => |h L| * e L
  e_moment : ∫ L in ⋃ j ∈ Finset.range J, Q j, |h L| * e L ≤ εe
  s_moment : ∑ j ∈ Finset.range J, s j * ∫ L in Q j, |h L| ≤ εs


/-- One block of the aggregation: a constant `c ≤ 3 s_j + K e(L)` on `Q` gives
`(∫_Q|h|) c ≤ 3 s_j ∫_Q|h| + K ∫_Q |h| e`. -/
lemma block_err_le {h e : ℝ → ℝ} {Q : Set ℝ} (hQ : MeasurableSet Q) (hh : Integrable h)
    (hint : Integrable fun L => |h L| * e L) {c sj K : ℝ} (hpt : ∀ L ∈ Q, c ≤ 3 * sj + K * e L) :
    (∫ L in Q, |h L|) * c ≤ 3 * (sj * ∫ L in Q, |h L|) + K * ∫ L in Q, |h L| * e L := by
  have i1 : IntegrableOn (fun L => |h L|) Q := hh.abs.integrableOn
  have i2 : IntegrableOn (fun L => |h L| * e L) Q := hint.integrableOn
  have hmono : ∫ L in Q, |h L| * c ≤ ∫ L in Q, (|h L| * (3 * sj) + K * (|h L| * e L)) := by
    refine setIntegral_mono_on (i1.mul_const _) ((i1.mul_const _).add (i2.const_mul _)) hQ fun L hL => ?_
    have := mul_le_mul_of_nonneg_left (hpt L hL) (abs_nonneg (h L))
    nlinarith [this]
  rw [integral_add (i1.mul_const _) (i2.const_mul _), integral_mul_const, integral_mul_const,
    integral_const_mul] at hmono
  linarith

/-- `Σ_j ∫_{Q_j} g ≤ K₀ ∫_{⋃Q_j} g` for `g ≥ 0` integrable and bounded overlap `Σ_j 1_{Q_j} ≤ K₀`. -/
lemma sum_setIntegral_le {g : ℝ → ℝ} {J : ℕ} {Q : ℕ → Set ℝ} {K0 : ℝ} (hQ : ∀ j < J, MeasurableSet (Q j))
    (hg0 : ∀ L, 0 ≤ g L) (hg : Integrable g)
    (hmult : ∀ L, ∑ j ∈ Finset.range J, (Q j).indicator (fun _ => (1 : ℝ)) L ≤ K0) :
    ∑ j ∈ Finset.range J, ∫ L in Q j, g L ≤ K0 * ∫ L in ⋃ j ∈ Finset.range J, Q j, g L := by
  have hU : MeasurableSet (⋃ j ∈ Finset.range J, Q j) :=
    Finset.measurableSet_biUnion _ fun j hj => hQ j (Finset.mem_range.1 hj)
  have e1 : ∀ j ∈ Finset.range J, ∫ L in Q j, g L = ∫ L, (Q j).indicator g L := fun j hj =>
    (integral_indicator (hQ j (Finset.mem_range.1 hj))).symm
  rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ (fun j hj =>
    hg.indicator (hQ j (Finset.mem_range.1 hj))), ← integral_const_mul, ← integral_indicator hU]
  refine integral_mono (integrable_finsetSum _ fun j hj => hg.indicator (hQ j (Finset.mem_range.1 hj)))
    ((hg.const_mul K0).indicator hU) fun L => ?_
  have e2 : ∀ j, (Q j).indicator g L = (Q j).indicator (fun _ => (1 : ℝ)) L * g L := fun j => by
    by_cases hL : L ∈ Q j <;> simp [hL, Set.indicator]
  simp_rw [e2, ← Finset.sum_mul]
  by_cases hLU : L ∈ ⋃ j ∈ Finset.range J, Q j
  · rw [Set.indicator_of_mem hLU]
    exact mul_le_mul_of_nonneg_right (hmult L) (hg0 L)
  · have : ∀ j ∈ Finset.range J, (Q j).indicator (fun _ => (1 : ℝ)) L = 0 := fun j hj => by
      apply Set.indicator_of_notMem
      intro hjL; exact hLU (Set.mem_biUnion hj hjL)
    rw [Finset.sum_eq_zero this, Set.indicator_of_notMem hLU]; simp

/-- **`ct:sumBj`** (aggregation of the block errors): if `A_jW_j + B_jW_j² ≤ 3s_j + K_* e(L)` on `Q_j`, `e ≥ 0`, `K_* ≥ 0`,
and the `Q_j` overlap at most `K₀` times, then
`Σ_j (∫_{Q_j}|h|)(A_jW_j + B_jW_j²) ≤ K_*K₀ ∫_{⋃Q_j}|h|e + 3 Σ_j s_j ∫_{Q_j}|h|`. -/
theorem sum_block_errors_le {h e : ℝ → ℝ} {J : ℕ} {Q : ℕ → Set ℝ} {W A B s : ℕ → ℝ} {Kstar K0 : ℝ}
    (hQ : ∀ j < J, MeasurableSet (Q j)) (hh : Integrable h) (hK : 0 ≤ Kstar) (he0 : ∀ L, 0 ≤ e L)
    (hmult : ∀ L, ∑ j ∈ Finset.range J, (Q j).indicator (fun _ => (1 : ℝ)) L ≤ K0)
    (hint : Integrable fun L => |h L| * e L)
    (hpt : ∀ j < J, ∀ L ∈ Q j, A j * W j + B j * W j ^ 2 ≤ 3 * s j + Kstar * e L) :
    ∑ j ∈ Finset.range J, (∫ L in Q j, |h L|) * (A j * W j + B j * W j ^ 2) ≤
      Kstar * K0 * (∫ L in ⋃ j ∈ Finset.range J, Q j, |h L| * e L) +
        3 * ∑ j ∈ Finset.range J, s j * ∫ L in Q j, |h L| := by
  have h1 : ∀ j ∈ Finset.range J, (∫ L in Q j, |h L|) * (A j * W j + B j * W j ^ 2) ≤
      3 * (s j * ∫ L in Q j, |h L|) + Kstar * ∫ L in Q j, |h L| * e L := fun j hj =>
    block_err_le (hQ j (Finset.mem_range.1 hj)) hh hint (hpt j (Finset.mem_range.1 hj))
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 := sum_setIntegral_le (g := fun L => |h L| * e L) hQ (fun L => mul_nonneg (abs_nonneg _) (he0 L)) hint hmult
  nlinarith [mul_le_mul_of_nonneg_left h2 hK]


/-- A bounded measurable weight times `h K`, `|K| ≤ 3`, is integrable. -/
lemma integrable_wmul {h K m : ℝ → ℝ} (hh : Integrable h) (hK : Measurable K) (hKb : ∀ L, |K L| ≤ 3)
    (hm : Measurable m) (hmb : ∀ L, |m L| ≤ 1) : Integrable fun L => m L * (h L * K L) := by
  refine (hh.abs.const_mul 3).mono' (hm.aestronglyMeasurable.mul (hh.aestronglyMeasurable.mul hK.aestronglyMeasurable))
    (ae_of_all _ fun L => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 := hmb L; have h2 := hKb L
  have h3 : 0 ≤ |h L| := abs_nonneg _
  nlinarith [mul_nonneg h3 (abs_nonneg (K L)), mul_nonneg (abs_nonneg (m L)) (mul_nonneg h3 (abs_nonneg (K L))),
    mul_le_mul_of_nonneg_left h2 h3, abs_nonneg (m L)]


/-- **Reduction to blocks** (`ct:boas` Step 3, "Reduction to blocks"): for a partition function `S = Σ_j χ_j ∈ [0,1]` with
`S = 1` on `[a, b]`, a weight `0 ≤ Ω ≤ 1` and `|K| ≤ 3`,
`∫ S Ω h K - 3∫_{L<a} Ω|h| - 3∫_{L>b} Ω|h| ≤ ∫_{L ≥ a} Ω h K`. -/
lemma reduction_to_blocks {h K Om S : ℝ → ℝ} {a b : ℝ} (hh : Integrable h) (hK : Measurable K)
    (hKb : ∀ L, |K L| ≤ 3) (hOm : Measurable Om) (hOm0 : ∀ L, 0 ≤ Om L) (hOm1 : ∀ L, Om L ≤ 1)
    (hS : Measurable S) (hS0 : ∀ L, 0 ≤ S L) (hS1 : ∀ L, S L ≤ 1) (hSab : ∀ L ∈ Icc a b, S L = 1) :
    (∫ L, S L * Om L * (h L * K L)) - 3 * (∫ L in Iio a, Om L * |h L|) -
      3 * (∫ L in Ioi b, Om L * |h L|) ≤ ∫ L in Ici a, Om L * (h L * K L) := by
  have hg : Integrable fun L => Om L * (h L * K L) :=
    integrable_wmul hh hK hKb hOm fun L => by rw [abs_of_nonneg (hOm0 L)]; exact hOm1 L
  have hSg : Integrable fun L => S L * Om L * (h L * K L) :=
    integrable_wmul hh hK hKb (hS.mul hOm) fun L => by
      rw [abs_of_nonneg (mul_nonneg (hS0 L) (hOm0 L))]
      nlinarith [hS1 L, hOm1 L, hS0 L, hOm0 L, mul_nonneg (hS0 L) (hOm0 L)]
  have hu : Integrable fun L => Om L * |h L| :=
    (hh.abs.mul_bdd hOm.aestronglyMeasurable (ae_of_all _ fun L => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hOm0 L)]; exact hOm1 L)).congr (ae_of_all _ fun L => by ring)
  have hpt : ∀ L, -3 * ((Iio a).indicator (fun L => Om L * |h L|) L + (Ioi b).indicator (fun L => Om L * |h L|) L) ≤
      (Ici a).indicator (fun L => Om L * (h L * K L)) L - S L * Om L * (h L * K L) := by
    intro L
    have hu0 : 0 ≤ Om L * |h L| := mul_nonneg (hOm0 L) (abs_nonneg _)
    have hgb : |Om L * (h L * K L)| ≤ 3 * (Om L * |h L|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hOm0 L)]
      have := mul_le_mul_of_nonneg_left (hKb L) (abs_nonneg (h L))
      nlinarith [hOm0 L]
    have hSgb : |S L * Om L * (h L * K L)| ≤ 3 * (Om L * |h L|) := by
      have : S L * Om L * (h L * K L) = S L * (Om L * (h L * K L)) := by ring
      rw [this, abs_mul, abs_of_nonneg (hS0 L)]
      nlinarith [hS1 L, hS0 L, abs_nonneg (Om L * (h L * K L))]
    have i1 : 0 ≤ (Iio a).indicator (fun L => Om L * |h L|) L := Set.indicator_nonneg (fun _ _ => hu0) L
    have i2 : 0 ≤ (Ioi b).indicator (fun L => Om L * |h L|) L := Set.indicator_nonneg (fun _ _ => hu0) L
    rcases lt_or_ge L a with hla | hla
    · have e1 : (Ici a).indicator (fun L => Om L * (h L * K L)) L = 0 :=
        Set.indicator_of_notMem (by simpa using hla) _
      have e2 : (Iio a).indicator (fun L => Om L * |h L|) L = Om L * |h L| := Set.indicator_of_mem hla _
      rw [e1, e2]
      have := le_abs_self (S L * Om L * (h L * K L))
      linarith
    · have e1 : (Ici a).indicator (fun L => Om L * (h L * K L)) L = Om L * (h L * K L) :=
        Set.indicator_of_mem hla _
      have e2 : (Iio a).indicator (fun L => Om L * |h L|) L = 0 :=
        Set.indicator_of_notMem (by simpa using hla) _
      rw [e1, e2]
      rcases le_or_gt L b with hlb | hlb
      · have e3 : (Ioi b).indicator (fun L => Om L * |h L|) L = 0 := Set.indicator_of_notMem (by simpa using hlb) _
        rw [e3, hSab L ⟨hla, hlb⟩]; linarith
      · have e3 : (Ioi b).indicator (fun L => Om L * |h L|) L = Om L * |h L| := Set.indicator_of_mem hlb _
        rw [e3]
        have h5 : S L * Om L * (h L * K L) = S L * (Om L * (h L * K L)) := by ring
        have h7 := mul_nonneg (sub_nonneg.2 (hS1 L)) (neg_abs_le (Om L * (h L * K L)) |> fun hh => by linarith : 0 ≤ Om L * (h L * K L) + |Om L * (h L * K L)|)
        have h8 := mul_nonneg (hS0 L) (abs_nonneg (Om L * (h L * K L)))
        rw [h5]; nlinarith
  have hint := integral_mono ((((hu.indicator measurableSet_Iio).add (hu.indicator measurableSet_Ioi)).const_mul (-3)))
    ((hg.indicator measurableSet_Ici).sub hSg) hpt
  simp only [Pi.add_apply, Pi.sub_apply] at hint
  rw [integral_const_mul, integral_add (hu.indicator measurableSet_Iio) (hu.indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi,
    integral_sub (hg.indicator measurableSet_Ici) hSg, integral_indicator measurableSet_Ici] at hint
  linarith


/-- **`ct:boas-ineq` (abstract block assembly).**  Under the setting `BoasSetting`, a partition `BoasPartition` of
`[L_min, L_far + 1]` and the separately proved inputs `BoasInputs` (each field named after the paper statement that
discharges it; see its docstring), with `B := ∫_{L ≥ L_min} w̃ h (1 - 2 sin X)`,
`B ≥ -(εfar + 3εhi + 3εlo + Pb(hi - lo) + K_*K₀εe + 3εs + Jκ M)`.
This is `ℬ ≥ -O(c^{-4/3} log c)`: `ℬ = ℬ_near + ℬ_far` with `ℬ_far ≥ -εfar` (Step 1); `ℬ_near - Σ_jℬ_j ≥ -3(εhi + εlo)`
(Step 3, `reduction_to_blocks`); `ℬ_j ≥ -Pb∫ω_j - (∫_{Q_j}|h|)(A_jW_j + B_jW_j²) - Kd_jW_j²∫|h|` (Step 5, `block_average`);
`Σ_j∫ω_j ≤ hi - lo`; and the pointwise block errors aggregate by `sum_block_errors_le`. -/
theorem boas_ineq_assembled {h X ν wt sf : ℝ → ℝ} {Lmin Lfar : ℝ} {J : ℕ} {χ : ℕ → ℝ → ℝ} {Q : ℕ → Set ℝ}
    {W A B Kd s : ℕ → ℝ} {e : ℝ → ℝ} {lo hi M εfar εhi εlo Pb κ Kstar K0 εe εs : ℝ}
    (hS : BoasSetting h X ν wt sf) (hP : BoasPartition J χ Lmin (Lfar + 1) lo hi)
    (hI : BoasInputs h X ν wt sf Lmin Lfar J χ Q W A B Kd s e M εfar εhi εlo Pb κ Kstar K0 εe εs) :
    -(εfar + 3 * εhi + 3 * εlo + Pb * (hi - lo) + Kstar * K0 * εe + 3 * εs + J * κ * M) ≤
      ∫ L in Ici Lmin, wt L * (h L * boasKernel X L) := by
  obtain ⟨hh, hXm, hνm, hwm, hsm, hw, hsf⟩ := hS
  have hKm : Measurable (boasKernel X) := measurable_boasKernel hXm
  have hKb := abs_boasKernel_le X
  set Om : ℝ → ℝ := fun L => wt L * (1 - sf L) with hOmdef
  have hOm : Measurable Om := hwm.mul (measurable_const.sub hsm)
  have hOm0 : ∀ L, 0 ≤ Om L := fun L => mul_nonneg (hw L).1 (sub_nonneg.2 (hsf L).2)
  have hOm1 : ∀ L, Om L ≤ 1 := fun L => by
    have := hw L; have := hsf L
    simp only [hOmdef]; nlinarith
  set S : ℝ → ℝ := fun L => ∑ j ∈ Finset.range J, χ j L with hSdef
  have hSm : Measurable S := Finset.measurable_sum _ fun j hj => hP.meas j (Finset.mem_range.1 hj)
  have hS0 : ∀ L, 0 ≤ S L := fun L => Finset.sum_nonneg fun j hj => hP.nonneg j (Finset.mem_range.1 hj) L
  have hS1 : ∀ L, S L ≤ 1 := hP.sum_le_one
  have hχ1 : ∀ j < J, ∀ L, χ j L ≤ 1 := fun j hj L =>
    (Finset.single_le_sum (f := fun j => χ j L) (fun i hi' => hP.nonneg i (Finset.mem_range.1 hi') L)
      (Finset.mem_range.2 hj)).trans (hP.sum_le_one L)
  -- indicator of `[lo, hi]` dominates every block weight
  have hind : Integrable ((Icc lo hi).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
  have hωint : ∀ j < J, Integrable fun L => Om L * χ j L := by
    intro j hj
    refine hind.mono' ((hOm.mul (hP.meas j hj)).aestronglyMeasurable) (ae_of_all _ fun L => ?_)
    rw [Real.norm_eq_abs]
    by_cases hL : L ∈ Icc lo hi
    · rw [Set.indicator_of_mem hL, abs_of_nonneg (mul_nonneg (hOm0 L) (hP.nonneg j hj L))]
      nlinarith [hOm1 L, hχ1 j hj L, hOm0 L, hP.nonneg j hj L]
    · rw [Set.indicator_of_notMem hL, hP.supp j hj L hL]; simp
  -- one block
  have hblock : ∀ j < J, -(Pb * ∫ L, Om L * χ j L) -
      ((∫ L in Q j, |h L|) * (A j * W j + B j * W j ^ 2) + Kd j * W j ^ 2 * ∫ L, |h L|) ≤
        ∫ L, (Om L * χ j L) * (h L * boasKernel X L) := by
    intro j hj
    exact block_average (hI.W_pos j hj) hh (ω := fun L => Om L * χ j L) (F := boasKernel X)
      (T := boasFrozenKernel X ν) (hOm.mul (hP.meas j hj)) hKm (measurable_boasFrozenKernel hXm hνm)
      (fun L => mul_nonneg (hOm0 L) (hP.nonneg j hj L))
      (fun L => by nlinarith [hOm1 L, hχ1 j hj L, hOm0 L, hP.nonneg j hj L]) (hωint j hj) hKb
      (abs_boasFrozenKernel_le X ν) (fun L0 hL0 => hI.P_lb j hj L0 hL0) (hI.Q_meas j hj)
      (hI.A_nonneg j hj) (hI.Kd_nonneg j hj) (fun L L0 => hI.freeze j hj L L0)
  have hωb : ∀ j < J, ∀ L, |Om L * χ j L| ≤ 1 := fun j hj L => by
    rw [abs_of_nonneg (mul_nonneg (hOm0 L) (hP.nonneg j hj L))]
    nlinarith [hOm1 L, hχ1 j hj L, hOm0 L, hP.nonneg j hj L]
  -- the sum of the block integrals
  have hsumint : ∑ j ∈ Finset.range J, ∫ L, (Om L * χ j L) * (h L * boasKernel X L) =
      ∫ L, S L * Om L * (h L * boasKernel X L) := by
    rw [← integral_finsetSum (f := fun j L => (Om L * χ j L) * (h L * boasKernel X L)) _
      (fun j hj => integrable_wmul hh hKm hKb
        (hOm.mul (hP.meas j (Finset.mem_range.1 hj))) (hωb j (Finset.mem_range.1 hj)))]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    show ∑ i ∈ Finset.range J, Om L * χ i L * (h L * boasKernel X L) = S L * Om L * (h L * boasKernel X L)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    simp only [hSdef]; ring
  -- the sum of the weights is at most `hi - lo`
  have hsumω : ∑ j ∈ Finset.range J, ∫ L, Om L * χ j L ≤ hi - lo := by
    rw [← integral_finsetSum _ (fun j hj => hωint j (Finset.mem_range.1 hj))]
    have hle : ∫ L, ∑ j ∈ Finset.range J, Om L * χ j L ≤ ∫ L, (Icc lo hi).indicator (fun _ => (1 : ℝ)) L := by
      refine integral_mono (integrable_finsetSum _ fun j hj => hωint j (Finset.mem_range.1 hj)) hind fun L => ?_
      by_cases hL : L ∈ Icc lo hi
      · rw [Set.indicator_of_mem hL, ← Finset.mul_sum]
        have : Om L * S L ≤ 1 := by nlinarith [hOm1 L, hS1 L, hOm0 L, hS0 L]
        exact this
      · rw [Set.indicator_of_notMem hL]
        exact Finset.sum_nonpos fun j hj => by
          rw [hP.supp j (Finset.mem_range.1 hj) L hL]; simp
    refine hle.trans (le_of_eq ?_)
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hP.lo_le_hi]
    simp
  -- the errors
  have herr := sum_block_errors_le (W := W) (A := A) (B := B) (s := s) (fun j hj => hI.Q_meas j hj) hh
    hI.Kstar_nonneg hI.e_nonneg hI.mult hI.e_int hI.pointwise
  have hK0 : 0 ≤ K0 := le_trans (Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hI.mult 0)
  have hmass0 : 0 ≤ ∫ L, |h L| := integral_nonneg fun _ => abs_nonneg _
  have hκ : 0 ≤ (J : ℝ) * κ := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp
    · have h1 := hI.Kd_W 0 hJ
      have h2 : 0 ≤ Kd 0 * W 0 ^ 2 := mul_nonneg (hI.Kd_nonneg 0 hJ) (sq_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (h2.trans h1)
  have hKdsum : ∑ j ∈ Finset.range J, Kd j * W j ^ 2 * ∫ L, |h L| ≤ J * κ * M := by
    calc ∑ j ∈ Finset.range J, Kd j * W j ^ 2 * ∫ L, |h L| ≤ ∑ j ∈ Finset.range J, κ * ∫ L, |h L| :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hI.Kd_W j (Finset.mem_range.1 hj)) hmass0
      _ = J * κ * ∫ L, |h L| := by rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]; ring
      _ ≤ J * κ * M := mul_le_mul_of_nonneg_left hI.mass hκ
  -- sum the block inequalities
  have hsum := Finset.sum_le_sum fun j hj => hblock j (Finset.mem_range.1 hj)
  have hlhs : ∑ j ∈ Finset.range J, (-(Pb * ∫ L, Om L * χ j L) -
      ((∫ L in Q j, |h L|) * (A j * W j + B j * W j ^ 2) + Kd j * W j ^ 2 * ∫ L, |h L|)) =
      -(Pb * ∑ j ∈ Finset.range J, ∫ L, Om L * χ j L) -
        ∑ j ∈ Finset.range J, (∫ L in Q j, |h L|) * (A j * W j + B j * W j ^ 2) -
        ∑ j ∈ Finset.range J, Kd j * W j ^ 2 * ∫ L, |h L| := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]; ring
  rw [hlhs, hsumint] at hsum
  have hPb := mul_le_mul_of_nonneg_left hsumω hI.Pb_nonneg
  -- reduction to blocks
  have hred := reduction_to_blocks (K := boasKernel X) (Om := Om) (S := S) (a := Lmin) (b := Lfar + 1) hh hKm hKb hOm
    hOm0 hOm1 hSm hS0 hS1 hP.sum_eq_one
  have hhi : ∫ L in Ioi (Lfar + 1), Om L * |h L| ≤ εhi := hI.trunc_hi
  have hlo : ∫ L in Iio Lmin, Om L * |h L| ≤ εlo := hI.trunc_lo
  -- split `w̃ = Ω_near + w̃ 𝔰_far`
  have hi1 : IntegrableOn (fun L => Om L * (h L * boasKernel X L)) (Ici Lmin) :=
    (integrable_wmul hh hKm hKb hOm fun L => by rw [abs_of_nonneg (hOm0 L)]; exact hOm1 L).integrableOn
  have hi2 : IntegrableOn (fun L => wt L * sf L * (h L * boasKernel X L)) (Ici Lmin) :=
    (integrable_wmul hh hKm hKb (hwm.mul hsm) fun L => by
      show |wt L * sf L| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (hw L).1 (hsf L).1)]
      nlinarith [(hw L).1, (hw L).2, (hsf L).1, (hsf L).2]).integrableOn
  have hsplit : ∫ L in Ici Lmin, wt L * (h L * boasKernel X L) =
      (∫ L in Ici Lmin, Om L * (h L * boasKernel X L)) +
        ∫ L in Ici Lmin, wt L * sf L * (h L * boasKernel X L) := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    simp only [hOmdef]; ring
  have hfar := hI.far
  have hmassK := mul_le_mul_of_nonneg_left (hI.mass) hκ
  have hKe := mul_le_mul_of_nonneg_left hI.e_moment (mul_nonneg hI.Kstar_nonneg hK0)
  rw [hsplit]
  nlinarith [hsum, hPb, hred, hhi, hlo, hfar, herr, hKdsum, hI.s_moment, hKe]

/-- info: 'FormalResearch.SignUncertainty.boas_ineq_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_ineq_assembled

/-- info: 'FormalResearch.SignUncertainty.sum_block_errors_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_block_errors_le

/-- info: 'FormalResearch.SignUncertainty.reduction_to_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reduction_to_blocks

end FormalResearch.SignUncertainty
