module

public import FormalResearch.ModularBootstrap.Stability.MultilevelBase

/-!
# Multilevel Soft-Edge Stability Expansion (`se:terminal-stability`, \eqref{se:multilevel-slope})

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem
`se:terminal-stability`, equation \eqref{se:multilevel-slope}.

For fixed strict Hermite–Biehler data `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`) with top `m` zeros
`S = hbTopZeros hHB hQ` and terminal zero `t_m = hbMinZero hHB hQ`, and real displacements
`h : ↥S → ℝ`, let
`I(h) = inf { ∫ Re f / ‖f‖₁ : 0 ≠ f ∈ 𝒢, f(t + h_t) ≥ 0 (t ∈ S \ {t_m}), f ≥ 0 on (-∞, t_m + h_{t_m}] }`.

Main results:
* `hbMultiSet_bddBelow`: `-1 ≤ r` for all `r ∈ hbMultiSet hHB hQ h`.
* `hbTrial_upper`: the trial family `hbTrial` produces feasible elements with value
  `≤ ∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h t + C_up * ‖h‖²` near `0`.
* `hbMultiSet_lower`: normal-family blowup (`norm_limit_deriv`) + Cauchy second-derivative bound +
  positive quadrature away from `S` gives `∑ b_t h_t - ε * ‖h‖ ≤ r` for all `r ∈ hbMultiSet hHB hQ h`.
* `hbMultiI_expansion`: full asymptotic expansion \eqref{se:multilevel-slope}
  `(fun h => hbMultiI hHB hQ h - ∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h t) =o[𝓝 0] id`
  together with `0 < hbNodeCoeff hHB hQ (hbMinZero hHB hQ)` and positivity of the pure
  terminal problem for all `δ > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set Polynomial
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.SignUncertainty

/-! ### Part 1: Real-linear closure and norm helpers for `AiryG` -/

private lemma airyG_zero : AiryG (fun _ : ℂ => (0 : ℂ)) where
  diff := differentiable_const 0
  integrable := integrable_zero _ _ _
  growth := ⟨0, 0, le_rfl, fun u => by simp⟩
  real := fun _ => by simp

private lemma airyG_real_mul (c : ℝ) {f : ℂ → ℂ} (hf : AiryG f) :
    AiryG (fun u => (c : ℂ) * f u) where
  diff := (differentiable_const (c : ℂ)).mul hf.diff
  integrable := hf.integrable.const_mul (c : ℂ)
  growth := by
    obtain ⟨C, ν, hC, hb⟩ := hf.growth
    refine ⟨|c| * C, ν, mul_nonneg (abs_nonneg c) hC, fun u => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |c| * ‖f u‖ ≤ |c| * (C * (1 + ‖u‖) ^ ν * airyEnv u) :=
          mul_le_mul_of_nonneg_left (hb u) (abs_nonneg c)
      _ = |c| * C * (1 + ‖u‖) ^ ν * airyEnv u := by ring
  real := fun x => by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hf.real x]
    ring

private lemma airyG_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AiryG (f i)) :
    AiryG (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using airyG_zero
  | @insert a s ha ih =>
      have haG : AiryG (f a) := hf a (Finset.mem_insert_self a s)
      have hsG : AiryG (fun u => ∑ i ∈ s, f i u) :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using haG.add hsG

private lemma profileMass_pos_of_airyG {f : ℂ → ℂ} (hf : AiryG f) (hnz : ∃ x : ℝ, f (x : ℂ) ≠ 0) :
    0 < profileMass f := by
  obtain ⟨x₀, hx₀⟩ := hnz
  have hcont : Continuous fun x : ℝ => ‖f (x : ℂ)‖ :=
    (hf.diff.continuous.comp continuous_ofReal).norm
  exact integral_pos_of_integrable_nonneg_ne_zero hcont
    hf.integrable_norm (fun x => norm_nonneg _) (norm_ne_zero_iff.mpr hx₀)

private lemma integrable_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i)) : Integrable (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have h1 : Integrable (f a) := hf a (Finset.mem_insert_self a s)
      have h2 : Integrable (fun x => ∑ i ∈ s, f i x) :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      convert h1.add h2 using 1
      ext x
      simp [Finset.sum_insert ha]

private lemma integral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i)) :
    ∫ x, ∑ i ∈ s, f i x = ∑ i ∈ s, ∫ x, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haI := hf a (Finset.mem_insert_self a s)
      have hsI : Integrable (fun x => ∑ i ∈ s, f i x) :=
        integrable_finset_sum' s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using
        (integral_add haI hsI).trans (by rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)])

private lemma tendsto_finset_sum' {ι α : Type*} {p : Filter α} (s : Finset ι)
    (f : ι → α → ℝ) (l : ι → ℝ) (hf : ∀ i ∈ s, Tendsto (f i) p (𝓝 (l i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) p (𝓝 (∑ i ∈ s, l i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using
        (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ### Part 2: Multilevel variational problem `hbMultiSet` and `hbMultiI` -/

section HBMultilevelExpansion

variable {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)

/-- The canonical element of `↥(hbTopZeros hHB hQ)` corresponding to `hbMinZero hHB hQ`. -/
noncomputable def hbMinNode : ↥(hbTopZeros hHB hQ) :=
  ⟨hbMinZero hHB hQ, (hbTopZeros_spec hHB hQ).2.2.2.1⟩

/-- Feasible normalized integrals `(∫ Re f) / ‖f‖₁` for `0 ≠ f ∈ 𝒢` satisfying
`f(t + h_t) ≥ 0` (`t ∈ S \ {t_m}`) and `f ≥ 0` on `(-∞, t_m + h_{t_m}]` (`se:terminal-stability`). -/
def hbMultiSet (h : ↥(hbTopZeros hHB hQ) → ℝ) : Set ℝ :=
  { r : ℝ | ∃ f : ℂ → ℂ, AiryG f ∧ (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧
    (∀ t : ↥(hbTopZeros hHB hQ), t.1 ≠ hbMinZero hHB hQ →
      0 ≤ (f ((t.1 + h t : ℝ) : ℂ)).re) ∧
    (∀ x : ℝ, x ≤ hbMinZero hHB hQ + h (hbMinNode hHB hQ) → 0 ≤ (f (x : ℂ)).re) ∧
    r = (∫ x : ℝ, (f (x : ℂ)).re) / profileMass f }

/-- Multilevel soft-edge stability infimum `I(h)` of `se:terminal-stability`. -/
noncomputable def hbMultiI (h : ↥(hbTopZeros hHB hQ) → ℝ) : ℝ :=
  sInf (hbMultiSet hHB hQ h)

lemma hbMultiSet_bddBelow (h : ↥(hbTopZeros hHB hQ) → ℝ) :
    BddBelow (hbMultiSet hHB hQ h) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨f, hf, hnz, _, _, rfl⟩
  have hm : 0 < profileMass f := profileMass_pos_of_airyG hf hnz
  have hle : -profileMass f ≤ ∫ x : ℝ, (f (x : ℂ)).re := by
    unfold profileMass
    rw [← integral_neg]
    refine integral_mono hf.integrable_norm.neg hf.integrable_re fun x => ?_
    rw [hf.norm_real x]
    exact neg_abs_le _
  exact (le_div_iff₀ hm).mpr (by linarith)

/-- Monotonicity of `hbMultiSet` when only the terminal coordinate increases. -/
lemma hbMultiSet_mono_tm {h₁ h₂ : ↥(hbTopZeros hHB hQ) → ℝ}
    (hoff : ∀ t : ↥(hbTopZeros hHB hQ), t.1 ≠ hbMinZero hHB hQ → h₁ t = h₂ t)
    (htm : h₁ (hbMinNode hHB hQ) ≤ h₂ (hbMinNode hHB hQ)) :
    hbMultiSet hHB hQ h₂ ⊆ hbMultiSet hHB hQ h₁ := by
  intro r ⟨f, hf, hnz, hnodes, hhalf, hr⟩
  refine ⟨f, hf, hnz, fun t ht => ?_, fun x hx => hhalf x (by linarith), hr⟩
  rw [hoff t ht]
  exact hnodes t ht

/-- Monotonicity of `hbMultiI` when only the terminal coordinate increases. -/
lemma hbMultiI_mono_tm {h₁ h₂ : ↥(hbTopZeros hHB hQ) → ℝ}
    (hoff : ∀ t : ↥(hbTopZeros hHB hQ), t.1 ≠ hbMinZero hHB hQ → h₁ t = h₂ t)
    (htm : h₁ (hbMinNode hHB hQ) ≤ h₂ (hbMinNode hHB hQ))
    (hne : (hbMultiSet hHB hQ h₂).Nonempty) :
    hbMultiI hHB hQ h₁ ≤ hbMultiI hHB hQ h₂ :=
  csInf_le_csInf (hbMultiSet_bddBelow hHB hQ h₁) hne (hbMultiSet_mono_tm hHB hQ hoff htm)

/-- At `h = (0, …, 0, δ)`, `hbMultiSet` agrees with `termSet (hbTerminalData hHB hQ) δ`. -/
lemma hbMultiSet_single_tm (δ : ℝ) :
    hbMultiSet hHB hQ (fun t => if t.1 = hbMinZero hHB hQ then δ else 0) =
      termSet (hbTerminalData hHB hQ) δ := by
  ext r
  constructor
  · rintro ⟨f, hf, hnz, hnodes, hhalf, hr⟩
    refine ⟨f, hf, hnz, ?_, fun x hx => hhalf x (by simpa [hbMinNode, hbTerminalData] using hx), hr⟩
    intro i
    have hi_ne : i.1 ≠ hbMinZero hHB hQ := i.2.2
    have hi_mem : i.1 ∈ hbTopZeros hHB hQ := i.2.1
    change 0 ≤ (f (i.1 : ℂ)).re
    simpa [hi_ne] using hnodes ⟨i.1, hi_mem⟩ hi_ne
  · rintro ⟨f, hf, hnz, hnodes, hhalf, hr⟩
    refine ⟨f, hf, hnz, ?_, fun x hx => hhalf x (by simpa [hbMinNode, hbTerminalData] using hx), hr⟩
    intro t ht
    let i : HbNodes (HermiteBiehlerData.ofQNeZero hHB hQ) := ⟨t.1, t.2, ht⟩
    have hi : 0 ≤ (f (t.1 : ℂ)).re := hnodes i
    simpa [ht] using hi

/-- At `h = (0, …, 0, δ)`, `hbMultiI` agrees with `hbI hHB hQ δ`. -/
lemma hbMultiI_single_tm (δ : ℝ) :
    hbMultiI hHB hQ (fun t => if t.1 = hbMinZero hHB hQ then δ else 0) = hbI hHB hQ δ := by
  unfold hbMultiI hbI termI
  rw [hbMultiSet_single_tm]

/-! ### Part 3: Subset quotients and the multilevel trial family `hbTrial` -/

/-- The quotient `G_N(u) / ∏_{t ∈ A} (u - t)` in `AiryG`, for `A : Finset ↥S`. -/
noncomputable def hbSubsetQuot (A : Finset ↥(hbTopZeros hHB hQ)) : ℂ → ℂ :=
  Classical.choose (hb_quotient_of_subset hHB hQ (A.image Subtype.val) (fun x hx => by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact t.2))

lemma hbSubsetQuot_spec (A : Finset ↥(hbTopZeros hHB hQ)) :
    AiryG (hbSubsetQuot hHB hQ A) ∧
      ∀ u : ℂ, hbExtremal hHB hQ u =
        hbSubsetQuot hHB hQ A u * ∏ t ∈ A, (u - (t.1 : ℂ)) := by
  have hspec := Classical.choose_spec (hb_quotient_of_subset hHB hQ (A.image Subtype.val)
    (fun x hx => by
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      exact t.2))
  unfold hbSubsetQuot
  refine ⟨hspec.1, fun u => ?_⟩
  simpa [Finset.prod_image (fun a _ b _ hab => Subtype.ext hab)] using hspec.2 u

lemma hbSubsetQuot_empty :
    hbSubsetQuot hHB hQ (∅ : Finset ↥(hbTopZeros hHB hQ)) = hbExtremal hHB hQ := by
  ext u
  simpa using (hbSubsetQuot_spec hHB hQ ∅).2 u |>.symm

lemma hbSubsetQuot_singleton (t : ↥(hbTopZeros hHB hQ)) :
    hbSubsetQuot hHB hQ {t} = dslope (hbExtremal hHB hQ) (t.1 : ℂ) := by
  have hspec := hbSubsetQuot_spec hHB hQ {t}
  have hG := hbExtremal_spec hHB hQ
  have hGt : hbExtremal hHB hQ (t.1 : ℂ) = 0 := hG.2.2.2.2.2.2.1 t.1 t.2
  have hcont_l : Continuous (hbSubsetQuot hHB hQ {t}) := hspec.1.diff.continuous
  have hcont_r : Continuous (dslope (hbExtremal hHB hQ) (t.1 : ℂ)) :=
    (EntireDiv.differentiable_dslope_entire hG.1 _).continuous
  have heq_on : ∀ u : ℂ, u ≠ (t.1 : ℂ) →
      hbSubsetQuot hHB hQ {t} u = dslope (hbExtremal hHB hQ) (t.1 : ℂ) u := by
    intro u hu
    have h1 := hspec.2 u
    simp only [Finset.prod_singleton] at h1
    have h2 : hbExtremal hHB hQ u = (u - (t.1 : ℂ)) * dslope (hbExtremal hHB hQ) (t.1 : ℂ) u := by
      have := sub_smul_dslope (hbExtremal hHB hQ) (t.1 : ℂ) u
      rw [smul_eq_mul, hGt, sub_zero] at this
      exact this.symm
    have hsub_ne : u - (t.1 : ℂ) ≠ 0 := sub_ne_zero.mpr hu
    exact mul_right_cancel₀ hsub_ne (by linear_combination h2 - h1)
  exact Continuous.ext_on ((Set.finite_singleton (t.1 : ℂ)).countable.dense_compl ℂ)
    hcont_l hcont_r heq_on

lemma hbSubsetQuot_singleton_int_re (t : ↥(hbTopZeros hHB hQ)) :
    -(∫ x : ℝ, (hbSubsetQuot hHB hQ {t} (x : ℂ)).re) =
      profileMass (hbExtremal hHB hQ) * hbNodeCoeff hHB hQ t.1 := by
  rw [hbSubsetQuot_singleton]
  exact hb_dslope_integral_re hHB hQ t.2

/-- The trial family `G_h(u) = G_N(u) ∏_{t ∈ S} (1 - h_t / (u - t))`, expanded via finite
subset quotients so it is manifestly entire and in `AiryG`. -/
noncomputable def hbTrial (h : ↥(hbTopZeros hHB hQ) → ℝ) (u : ℂ) : ℂ :=
  ∑ A : Finset ↥(hbTopZeros hHB hQ),
    ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) * hbSubsetQuot hHB hQ A u

lemma hbTrial_airyG (h : ↥(hbTopZeros hHB hQ) → ℝ) : AiryG (hbTrial hHB hQ h) :=
  airyG_finset_sum Finset.univ _ fun A _ =>
    airyG_real_mul _ (hbSubsetQuot_spec hHB hQ A).1

/-- Core algebraic identity `G_h(u) ∏_{t ∈ S} (u - t) = G_N(u) ∏_{t ∈ S} (u - t - h_t)`. -/
lemma hbTrial_mul_prod (h : ↥(hbTopZeros hHB hQ) → ℝ) (u : ℂ) :
    hbTrial hHB hQ h u * ∏ t : ↥(hbTopZeros hHB hQ), (u - (t.1 : ℂ)) =
      hbExtremal hHB hQ u * ∏ t : ↥(hbTopZeros hHB hQ), (u - (t.1 : ℂ) - (h t : ℂ)) := by
  classical
  unfold hbTrial
  rw [Finset.sum_mul]
  have hterm : ∀ A : Finset ↥(hbTopZeros hHB hQ),
      ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) * hbSubsetQuot hHB hQ A u *
          ∏ t : ↥(hbTopZeros hHB hQ), (u - (t.1 : ℂ)) =
        hbExtremal hHB hQ u *
          ((∏ t ∈ A, (-(h t : ℂ))) *
            ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ))) := by
    intro A
    have hsplit : (∏ t : ↥(hbTopZeros hHB hQ), (u - (t.1 : ℂ))) =
        (∏ t ∈ A, (u - (t.1 : ℂ))) * ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ)) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ A), mul_comm]
    have hG_A := (hbSubsetQuot_spec hHB hQ A).2 u
    have hneg : (∏ t ∈ A, (-(h t : ℂ))) = ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) := by
      rw [Finset.prod_neg]
      push_cast
      rfl
    rw [hsplit, hneg]
    calc ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) * hbSubsetQuot hHB hQ A u *
          ((∏ t ∈ A, (u - (t.1 : ℂ))) * ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ)))
        = (hbSubsetQuot hHB hQ A u * ∏ t ∈ A, (u - (t.1 : ℂ))) *
            (((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) *
              ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ))) := by ring
      _ = hbExtremal hHB hQ u *
            (((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) *
              ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ))) := by rw [← hG_A]
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  have hadd := Finset.prod_add (fun t : ↥(hbTopZeros hHB hQ) => -(h t : ℂ))
    (fun t : ↥(hbTopZeros hHB hQ) => u - (t.1 : ℂ)) (Finset.univ : Finset ↥(hbTopZeros hHB hQ))
  have hreindex : (∑ t ∈ Finset.univ.powerset,
      (∏ i ∈ t, (-(h i : ℂ))) * ∏ i ∈ Finset.univ \ t, (u - (i.1 : ℂ))) =
      ∑ A : Finset ↥(hbTopZeros hHB hQ),
        (∏ t ∈ A, -(h t : ℂ)) * ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ)) := by
    rw [Finset.powerset_univ]
  calc ∑ A : Finset ↥(hbTopZeros hHB hQ),
        (∏ t ∈ A, -(h t : ℂ)) * ∏ t ∈ Finset.univ \ A, (u - (t.1 : ℂ))
      = ∑ t ∈ Finset.univ.powerset,
          (∏ i ∈ t, (-(h i : ℂ))) * ∏ i ∈ Finset.univ \ t, (u - (i.1 : ℂ)) := hreindex.symm
    _ = ∏ t : ↥(hbTopZeros hHB hQ), (-(h t : ℂ) + (u - (t.1 : ℂ))) := hadd.symm
    _ = ∏ t : ↥(hbTopZeros hHB hQ), (u - (t.1 : ℂ) - (h t : ℂ)) :=
          Finset.prod_congr rfl fun t _ => by ring

/-- Real-axis squared-denominator identity for `hbTrial`:
`Re(G_h(x)) * (∏ (x - t))² = (Re N(x))² * ∏ (t + h_t - x)`. -/
lemma hbTrial_real_mul_sq (h : ↥(hbTopZeros hHB hQ) → ℝ) (x : ℝ) :
    (hbTrial hHB hQ h (x : ℂ)).re *
        (∏ t : ↥(hbTopZeros hHB hQ), (x - t.1)) ^ 2 =
      ((airyPQN P Q (x : ℂ)).re) ^ 2 *
        ∏ t : ↥(hbTopZeros hHB hQ), (t.1 + h t - x) := by
  have h1 := hbTrial_mul_prod hHB hQ h (x : ℂ)
  have hG := (hbExtremal_spec hHB hQ).2.1 (x : ℂ)
  have hpr : at47_pr (hbTopZeros hHB hQ) (x : ℂ) =
      ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ)) := by
    unfold at47_pr
    exact (Finset.prod_coe_sort (hbTopZeros hHB hQ) fun s => (x : ℂ) - (s : ℂ)).symm
  rw [hpr] at hG
  have hc : hbTrial hHB hQ h (x : ℂ) *
      (∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ))) ^ 2 =
      (((-1 : ℝ) ^ (hbTopZeros hHB hQ).card : ℝ) : ℂ) * (airyPQN P Q (x : ℂ)) ^ 2 *
        ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ)) := by
    calc hbTrial hHB hQ h (x : ℂ) *
          (∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ))) ^ 2
        = (hbTrial hHB hQ h (x : ℂ) * ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ))) *
            ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ)) := by ring
      _ = (hbExtremal hHB hQ (x : ℂ) * ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ))) *
            ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ)) := by rw [h1]
      _ = (hbExtremal hHB hQ (x : ℂ) * ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ))) *
            ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ)) := by ring
      _ = _ := by rw [hG]
  have hNim : (airyPQN P Q (x : ℂ)).im = 0 := by rw [airyPQN_ofReal, Complex.ofReal_im]
  have hGh_im : (hbTrial hHB hQ h (x : ℂ)).im = 0 := (hbTrial_airyG hHB hQ h).real x
  have hGhc : hbTrial hHB hQ h (x : ℂ) = (((hbTrial hHB hQ h (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl hGh_im
  have hNc : airyPQN P Q (x : ℂ) = (((airyPQN P Q (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl hNim
  have hflip : ((-1 : ℂ) ^ (hbTopZeros hHB hQ).card) *
      ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ)) =
      ∏ t : ↥(hbTopZeros hHB hQ), ((t.1 : ℂ) + (h t : ℂ) - (x : ℂ)) := by
    have hcard : (hbTopZeros hHB hQ).card = (Finset.univ : Finset ↥(hbTopZeros hHB hQ)).card := by
      simp
    rw [hcard, ← Finset.prod_const (b := (-1 : ℂ)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => by ring
  rw [hGhc, hNc] at hc
  have hcr : (((hbTrial hHB hQ h (x : ℂ)).re *
      (∏ t : ↥(hbTopZeros hHB hQ), (x - t.1)) ^ 2 : ℝ) : ℂ) =
      (((airyPQN P Q (x : ℂ)).re ^ 2 *
        ∏ t : ↥(hbTopZeros hHB hQ), (t.1 + h t - x) : ℝ) : ℂ) := by
    calc (((hbTrial hHB hQ h (x : ℂ)).re *
          (∏ t : ↥(hbTopZeros hHB hQ), (x - t.1)) ^ 2 : ℝ) : ℂ)
        = (((hbTrial hHB hQ h (x : ℂ)).re : ℝ) : ℂ) *
            (∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ))) ^ 2 := by push_cast; rfl
      _ = (((-1 : ℝ) ^ (hbTopZeros hHB hQ).card : ℝ) : ℂ) *
            (((airyPQN P Q (x : ℂ)).re : ℝ) : ℂ) ^ 2 *
            ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ)) := hc
      _ = (((airyPQN P Q (x : ℂ)).re : ℝ) : ℂ) ^ 2 *
            (((-1 : ℂ) ^ (hbTopZeros hHB hQ).card) *
              ∏ t : ↥(hbTopZeros hHB hQ), ((x : ℂ) - (t.1 : ℂ) - (h t : ℂ))) := by push_cast; ring
      _ = (((airyPQN P Q (x : ℂ)).re : ℝ) : ℂ) ^ 2 *
            ∏ t : ↥(hbTopZeros hHB hQ), ((t.1 : ℂ) + (h t : ℂ) - (x : ℂ)) := by rw [hflip]
      _ = _ := by push_cast; rfl
  exact Complex.ofReal_injective hcr

/-- For small `‖h‖`, `hbTrial` vanishes at all displaced sites `t + h_t` and is nonnegative on
`(-∞, t_m + h_{t_m}]`. -/
lemma hbTrial_sign (δ_gap : ℝ) (hδ_pos : 0 < δ_gap)
    (hgap : ∀ s ∈ hbTopZeros hHB hQ, ∀ t ∈ hbTopZeros hHB hQ, s ≠ t → δ_gap ≤ |s - t|)
    {h : ↥(hbTopZeros hHB hQ) → ℝ} (hh : ‖h‖ < δ_gap / 2) :
    (∀ t : ↥(hbTopZeros hHB hQ), hbTrial hHB hQ h ((t.1 + h t : ℝ) : ℂ) = 0) ∧
      (∀ x : ℝ, x ≤ hbMinZero hHB hQ + h (hbMinNode hHB hQ) →
        0 ≤ (hbTrial hHB hQ h (x : ℂ)).re) := by
  have hS := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have hnode_le : ∀ t : ↥(hbTopZeros hHB hQ),
      hbMinZero hHB hQ + h (hbMinNode hHB hQ) ≤ t.1 + h t := by
    intro t
    by_cases htm : t.1 = hbMinZero hHB hQ
    · have hteq : t = hbMinNode hHB hQ := Subtype.ext htm
      rw [hteq]
      exact le_rfl
    · have htm_le : hbMinZero hHB hQ ≤ t.1 := hS.2.2.2.2 t.1 t.2
      have hmin_gap : δ_gap ≤ |hbMinZero hHB hQ - t.1| :=
        hgap _ hS.2.2.2.1 t.1 t.2 (Ne.symm htm)
      have hdif : δ_gap ≤ t.1 - hbMinZero hHB hQ := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htm_le)] at hmin_gap
        exact hmin_gap
      have h1 : |h (hbMinNode hHB hQ)| ≤ ‖h‖ := norm_le_pi_norm h (hbMinNode hHB hQ)
      have h2 : |h t| ≤ ‖h‖ := norm_le_pi_norm h t
      linarith [neg_abs_le (h t), le_abs_self (h (hbMinNode hHB hQ))]
  have hhalf_off : ∀ x : ℝ, x ≤ hbMinZero hHB hQ + h (hbMinNode hHB hQ) →
      x ∉ hbTopZeros hHB hQ → 0 ≤ (hbTrial hHB hQ h (x : ℂ)).re := by
    intro x hx hxS
    have hsq_pos : 0 < (∏ t : ↥(hbTopZeros hHB hQ), (x - t.1)) ^ 2 := by
      refine sq_pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ => ?_)
      exact sub_ne_zero.mpr fun heq => hxS (heq ▸ t.2)
    have hprod_nonneg : 0 ≤ ∏ t : ↥(hbTopZeros hHB hQ), (t.1 + h t - x) :=
      Finset.prod_nonneg fun t _ => sub_nonneg.mpr (le_trans hx (hnode_le t))
    have hmul := hbTrial_real_mul_sq hHB hQ h x
    have hrhs : 0 ≤ ((airyPQN P Q (x : ℂ)).re) ^ 2 *
        ∏ t : ↥(hbTopZeros hHB hQ), (t.1 + h t - x) :=
      mul_nonneg (sq_nonneg _) hprod_nonneg
    rw [← hmul] at hrhs
    exact nonneg_of_mul_nonneg_left hrhs hsq_pos
  have hhalf : ∀ x : ℝ, x ≤ hbMinZero hHB hQ + h (hbMinNode hHB hQ) →
      0 ≤ (hbTrial hHB hQ h (x : ℂ)).re := by
    intro x hx
    have hcont : Continuous fun y : ℝ => (hbTrial hHB hQ h (y : ℂ)).re :=
      Complex.continuous_re.comp ((hbTrial_airyG hHB hQ h).diff.continuous.comp continuous_ofReal)
    let S_below := (hbTopZeros hHB hQ).filter fun s => s < x
    let δ0 : ℝ := if hne : S_below.Nonempty then x - S_below.max' hne else 1
    have hδ0 : 0 < δ0 := by
      dsimp [δ0]
      split_ifs with hne
      · exact sub_pos.mpr (Finset.mem_filter.mp (Finset.max'_mem S_below hne)).2
      · exact one_pos
    let seq : ℕ → ℝ := fun k => x - δ0 / ((k : ℝ) + 2)
    have ht_seq : Tendsto seq atTop (𝓝 x) := by
      have hdiv : Tendsto (fun k : ℕ => δ0 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa [seq] using tendsto_const_nhds.sub hdiv
    refine ge_of_tendsto (hcont.continuousAt.tendsto.comp ht_seq) (Eventually.of_forall fun k => ?_)
    have hk_pos : 0 < δ0 / ((k : ℝ) + 2) := by positivity
    have hk_lt : δ0 / ((k : ℝ) + 2) < δ0 :=
      div_lt_self hδ0 (by linarith : (1 : ℝ) < (k : ℝ) + 2)
    have hle : seq k ≤ hbMinZero hHB hQ + h (hbMinNode hHB hQ) := by dsimp [seq]; linarith
    have hnot : seq k ∉ hbTopZeros hHB hQ := fun hmem => by
      have hlt_x : seq k < x := by dsimp [seq]; linarith
      have hsub_mem : seq k ∈ S_below := Finset.mem_filter.mpr ⟨hmem, hlt_x⟩
      have hne : S_below.Nonempty := ⟨seq k, hsub_mem⟩
      have hle_max : seq k ≤ S_below.max' hne := Finset.le_max' S_below (seq k) hsub_mem
      have hδ0_eq : δ0 = x - S_below.max' hne := by dsimp [δ0]; split_ifs; rfl
      dsimp [seq] at hle_max
      linarith
    exact hhalf_off (seq k) hle hnot
  refine ⟨fun t => ?_, hhalf⟩
  by_cases hmem : t.1 + h t ∈ hbTopZeros hHB hQ
  · have h_eq_t : h t = 0 := by
      by_contra hht
      let s : ↥(hbTopZeros hHB hQ) := ⟨t.1 + h t, hmem⟩
      have hst : s.1 ≠ t.1 := fun heq => hht (by dsimp [s] at heq; linarith)
      have hmin : δ_gap ≤ |s.1 - t.1| := hgap s.1 s.2 t.1 t.2 hst
      have hs_eq : s.1 - t.1 = h t := by dsimp [s]; ring
      rw [hs_eq] at hmin
      have hle : |h t| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h t
      linarith
    rw [h_eq_t, add_zero]
    unfold hbTrial
    refine Finset.sum_eq_zero fun A _ => ?_
    by_cases htA : t ∈ A
    · have hprod0 : ∏ r ∈ A, h r = 0 := Finset.prod_eq_zero htA h_eq_t
      simp [hprod0]
    · have hG_t : hbExtremal hHB hQ (t.1 : ℂ) = 0 := hG.2.2.2.2.2.2.1 t.1 t.2
      have hsp := (hbSubsetQuot_spec hHB hQ A).2 (t.1 : ℂ)
      rw [hG_t] at hsp
      have hprod_ne : (∏ r ∈ A, ((t.1 : ℂ) - (r.1 : ℂ))) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun r hr => ?_
        exact sub_ne_zero.mpr fun heq => htA (by
          have : r = t := Subtype.ext (Complex.ofReal_injective heq).symm
          exact this ▸ hr)
      have hq0 : hbSubsetQuot hHB hQ A (t.1 : ℂ) = 0 :=
        mul_right_cancel₀ hprod_ne (by simpa using hsp.symm)
      rw [hq0, mul_zero]
  · have hmul := hbTrial_real_mul_sq hHB hQ h (t.1 + h t)
    have hprod_zero : ∏ s : ↥(hbTopZeros hHB hQ), (s.1 + h s - (t.1 + h t)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) (by ring)
    rw [hprod_zero, mul_zero] at hmul
    have hsq_ne : (∏ s : ↥(hbTopZeros hHB hQ), (t.1 + h t - s.1)) ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun s _ => ?_)
      exact sub_ne_zero.mpr fun heq => hmem (heq ▸ s.2)
    have hre0 : (hbTrial hHB hQ h ((t.1 + h t : ℝ) : ℂ)).re = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hsq_ne
    have him0 : (hbTrial hHB hQ h ((t.1 + h t : ℝ) : ℂ)).im = 0 :=
      (hbTrial_airyG hHB hQ h).real (t.1 + h t)
    exact Complex.ext hre0 him0

/-- Quantitative `O(‖h‖²)` upper bound from the trial family `hbTrial`:
there exist `C_up ≥ 0` and `δ_up > 0` such that whenever `‖h‖ < δ_up`, `hbTrial h` produces a
feasible element of `hbMultiSet hHB hQ h` with `hbMultiI hHB hQ h ≤ ∑ b_t h_t + C_up * ‖h‖²`. -/
lemma hbMultiI_le :
    ∃ C_up δ_up : ℝ, 0 ≤ C_up ∧ 0 < δ_up ∧
      ∀ h : ↥(hbTopZeros hHB hQ) → ℝ, ‖h‖ < δ_up →
        (hbMultiSet hHB hQ h).Nonempty ∧
        hbMultiI hHB hQ h ≤
          (∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t) + C_up * ‖h‖ ^ 2 := by
  classical
  obtain ⟨δ_gap, hδ_pos, hgap⟩ := hb_nodes_min_gap hHB hQ
  let G := hbExtremal hHB hQ
  let L := profileMass G
  have hL_pos : 0 < L := (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos
  have hG_int_zero : ∫ x : ℝ, (G (x : ℂ)).re = 0 :=
    (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).integral_re
  let U := (Finset.univ : Finset (Finset ↥(hbTopZeros hHB hQ)))
  let A_ge2 : Finset (Finset ↥(hbTopZeros hHB hQ)) := U.filter fun A => 2 ≤ A.card
  let A_ne0 : Finset (Finset ↥(hbTopZeros hHB hQ)) := U.filter fun A => 1 ≤ A.card
  let B_re : ℝ := ∑ A ∈ A_ge2, ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖
  let B_l1 : ℝ := ∑ A ∈ A_ne0, ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖
  have hB_re_nn : 0 ≤ B_re :=
    Finset.sum_nonneg fun A _ => integral_nonneg fun _ => norm_nonneg _
  have hB_l1_nn : 0 ≤ B_l1 :=
    Finset.sum_nonneg fun A _ => integral_nonneg fun _ => norm_nonneg _
  let B_lin : ℝ := ∑ t : ↥(hbTopZeros hHB hQ), |hbNodeCoeff hHB hQ t.1|
  have hB_lin_nn : 0 ≤ B_lin := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let δ_up : ℝ := min 1 (min (δ_gap / 2) (L / (2 * (B_l1 + 1))))
  have hδ_up_pos : 0 < δ_up :=
    lt_min one_pos (lt_min (half_pos hδ_pos) (div_pos hL_pos (by linarith)))
  let C_up : ℝ := (2 / L) * B_re + (2 / L) * B_l1 * B_lin
  have hC_up_nn : 0 ≤ C_up := by positivity
  refine ⟨C_up, δ_up, hC_up_nn, hδ_up_pos, fun h hh => ?_⟩
  have hh1 : ‖h‖ ≤ 1 := (hh.trans_le (min_le_left _ _)).le
  have hh_gap : ‖h‖ < δ_gap / 2 :=
    hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh_l1 : B_l1 * ‖h‖ ≤ L / 2 := by
    have hh_div : ‖h‖ < L / (2 * (B_l1 + 1)) :=
      hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h1 : B_l1 * ‖h‖ ≤ (B_l1 + 1) * (L / (2 * (B_l1 + 1))) :=
      mul_le_mul (by linarith : B_l1 ≤ B_l1 + 1) hh_div.le (norm_nonneg h) (by linarith)
    have h2 : (B_l1 + 1) * (L / (2 * (B_l1 + 1))) = L / 2 := by
      field_simp [show B_l1 + 1 ≠ 0 by linarith]
    linarith
  have hprod_le : ∀ A : Finset ↥(hbTopZeros hHB hQ), ∀ k : ℕ, k ≤ A.card →
      |∏ t ∈ A, h t| ≤ ‖h‖ ^ k := by
    intro A k hk
    calc |∏ t ∈ A, h t| = ∏ t ∈ A, |h t| := Finset.abs_prod A h
      _ ≤ ∏ _t ∈ A, ‖h‖ := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            (fun t _ => by simpa [Real.norm_eq_abs] using norm_le_pi_norm h t)
      _ = ‖h‖ ^ A.card := Finset.prod_const _
      _ ≤ ‖h‖ ^ k := pow_le_pow_of_le_one (norm_nonneg _) hh1 hk
  have htrial_G := hbTrial_airyG hHB hQ h
  have hmass_bound : |profileMass (hbTrial hHB hQ h) - L| ≤ B_l1 * ‖h‖ := by
    have hdiff_eq : ∀ x : ℝ, hbTrial hHB hQ h (x : ℂ) - G (x : ℂ) =
        ∑ A ∈ A_ne0, ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) *
          hbSubsetQuot hHB hQ A (x : ℂ) := by
      intro x
      unfold hbTrial
      change (∑ A ∈ U, _) - G (x : ℂ) = _
      have hdisj : U = insert ∅ A_ne0 := by
        ext A
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, U, A_ne0]
        rcases eq_or_ne A ∅ with rfl | hne
        · simp
        · simp [hne, Nat.succ_le_iff, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)]
      rw [hdisj, Finset.sum_insert (by simp [A_ne0])]
      simp [hbSubsetQuot_empty, G]
    have h_tri : ∀ x : ℝ, |‖hbTrial hHB hQ h (x : ℂ)‖ - ‖G (x : ℂ)‖| ≤
        ∑ A ∈ A_ne0, |∏ t ∈ A, h t| * ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
      intro x
      calc |‖hbTrial hHB hQ h (x : ℂ)‖ - ‖G (x : ℂ)‖|
          ≤ ‖hbTrial hHB hQ h (x : ℂ) - G (x : ℂ)‖ := abs_norm_sub_norm_le _ _
        _ = ‖∑ A ∈ A_ne0, ((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) *
              hbSubsetQuot hHB hQ A (x : ℂ)‖ := by rw [hdiff_eq x]
        _ ≤ ∑ A ∈ A_ne0, ‖((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) *
              hbSubsetQuot hHB hQ A (x : ℂ)‖ := norm_sum_le _ _
        _ = ∑ A ∈ A_ne0, |∏ t ∈ A, h t| * ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
                abs_neg, abs_one, one_pow, one_mul]
    have hint_diff : Integrable (fun x : ℝ => ‖hbTrial hHB hQ h (x : ℂ)‖ - ‖G (x : ℂ)‖) :=
      htrial_G.integrable_norm.sub (hbExtremal_spec hHB hQ).2.2.1.norm
    have hint_rhs : Integrable (fun x : ℝ =>
        ∑ A ∈ A_ne0, |∏ t ∈ A, h t| * ‖hbSubsetQuot hHB hQ A (x : ℂ)‖) :=
      integrable_finset_sum' _ _ fun A _ =>
        ((hbSubsetQuot_spec hHB hQ A).1.integrable_norm).const_mul _
    calc |profileMass (hbTrial hHB hQ h) - L|
        = |∫ x : ℝ, (‖hbTrial hHB hQ h (x : ℂ)‖ - ‖G (x : ℂ)‖)| := by
            dsimp [L, profileMass]
            rw [← integral_sub htrial_G.integrable_norm (hbExtremal_spec hHB hQ).2.2.1.norm]
      _ ≤ ∫ x : ℝ, |‖hbTrial hHB hQ h (x : ℂ)‖ - ‖G (x : ℂ)‖| := abs_integral_le_integral_abs
      _ ≤ ∫ x : ℝ, ∑ A ∈ A_ne0, |∏ t ∈ A, h t| * ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ :=
            integral_mono hint_diff.abs hint_rhs h_tri
      _ = ∑ A ∈ A_ne0, |∏ t ∈ A, h t| * ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
            rw [integral_finset_sum' _ _ fun A _ =>
              ((hbSubsetQuot_spec hHB hQ A).1.integrable_norm).const_mul _]
            exact Finset.sum_congr rfl fun A _ => integral_const_mul _ _
      _ ≤ ∑ A ∈ A_ne0, ‖h‖ * ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
            refine Finset.sum_le_sum fun A hA => ?_
            have hcard1 : 1 ≤ A.card := (Finset.mem_filter.mp hA).2
            exact mul_le_mul_of_nonneg_right (by simpa using hprod_le A 1 hcard1)
              (integral_nonneg fun _ => norm_nonneg _)
      _ = B_l1 * ‖h‖ := by
            rw [← Finset.mul_sum, mul_comm]
  have hmass_ge : L / 2 ≤ profileMass (hbTrial hHB hQ h) := by
    have := neg_abs_le (profileMass (hbTrial hHB hQ h) - L)
    linarith
  have hmass_pos : 0 < profileMass (hbTrial hHB hQ h) := by linarith
  have hnz : ∃ x : ℝ, hbTrial hHB hQ h (x : ℂ) ≠ 0 := by
    by_contra h0
    push Not at h0
    have hzero_mass : profileMass (hbTrial hHB hQ h) = 0 := by
      unfold profileMass
      simp [h0]
    linarith
  obtain ⟨hnodes_zero, hhalf⟩ := hbTrial_sign hHB hQ δ_gap hδ_pos hgap hh_gap
  have hmem_multi : (∫ x : ℝ, (hbTrial hHB hQ h (x : ℂ)).re) / profileMass (hbTrial hHB hQ h) ∈
      hbMultiSet hHB hQ h :=
    ⟨hbTrial hHB hQ h, htrial_G, hnz, fun t _ => by rw [hnodes_zero t]; simp, hhalf, rfl⟩
  have hre_split : ∫ x : ℝ, (hbTrial hHB hQ h (x : ℂ)).re =
      L * (∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t) +
        ∑ A ∈ A_ge2, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
          ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re := by
    have hre_term : ∀ A : Finset ↥(hbTopZeros hHB hQ), ∀ x : ℝ,
        (((((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t : ℝ) : ℂ)) * hbSubsetQuot hHB hQ A (x : ℂ)).re =
          ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) * (hbSubsetQuot hHB hQ A (x : ℂ)).re := by
      intro A x
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h_int_sum : ∫ x : ℝ, (hbTrial hHB hQ h (x : ℂ)).re =
        ∑ A ∈ U, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
          ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re := by
      have hfn : (fun x : ℝ => (hbTrial hHB hQ h (x : ℂ)).re) =
          fun x : ℝ => ∑ A ∈ U, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
            (hbSubsetQuot hHB hQ A (x : ℂ)).re := by
        ext x
        unfold hbTrial
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun A _ => hre_term A x
      rw [hfn, integral_finset_sum' _ _ fun A _ =>
        ((hbSubsetQuot_spec hHB hQ A).1.integrable_re).const_mul _]
      exact Finset.sum_congr rfl fun A _ => integral_const_mul _ _
    rw [h_int_sum]
    have hU_part : U = insert ∅ ((Finset.univ.image
        (fun t : ↥(hbTopZeros hHB hQ) => ({t} : Finset ↥(hbTopZeros hHB hQ)))) ∪ A_ge2) := by
      ext A
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter, U, A_ge2]
      constructor
      · intro _
        rcases le_or_gt 2 A.card with h2 | hlt2
        · exact Or.inr (Or.inr h2)
        · have h01 : A.card = 0 ∨ A.card = 1 := by omega
          rcases h01 with h0 | h1
          · exact Or.inl (Finset.card_eq_zero.mp h0)
          · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
            exact Or.inr (Or.inl ⟨t, ht.symm⟩)
      · intro _; trivial
    have hdisj0 : ∅ ∉ (Finset.univ.image
        (fun t : ↥(hbTopZeros hHB hQ) => ({t} : Finset ↥(hbTopZeros hHB hQ)))) ∪ A_ge2 := by
      simp [A_ge2]
    have hdisj1 : Disjoint (Finset.univ.image
        (fun t : ↥(hbTopZeros hHB hQ) => ({t} : Finset ↥(hbTopZeros hHB hQ)))) A_ge2 := by
      rw [Finset.disjoint_left]
      intro A hA1 hA2
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hA1
      have := (Finset.mem_filter.mp hA2).2
      simp at this
    rw [hU_part, Finset.sum_insert hdisj0, Finset.sum_union hdisj1]
    have h0_val : ((-1 : ℝ) ^ (∅ : Finset ↥(hbTopZeros hHB hQ)).card * ∏ t ∈ (∅ : Finset _), h t) *
        ∫ x : ℝ, (hbSubsetQuot hHB hQ ∅ (x : ℂ)).re = 0 := by
      dsimp [G] at hG_int_zero
      rw [hbSubsetQuot_empty]
      simp [hG_int_zero]
    have h1_val : ∑ A ∈ Finset.univ.image
        (fun t : ↥(hbTopZeros hHB hQ) => ({t} : Finset _)),
        ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) * ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re =
        L * ∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t := by
      rw [Finset.sum_image (fun a _ b _ hab => Finset.singleton_injective hab)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Finset.card_singleton, pow_one, Finset.prod_singleton]
      have hd := hbSubsetQuot_singleton_int_re hHB hQ t
      have hmul := congrArg (· * h t) hd
      dsimp [L]
      linarith [hmul]
    rw [h0_val, zero_add, h1_val]
  have hrem_bound : |∑ A ∈ A_ge2, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
      ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re| ≤ B_re * ‖h‖ ^ 2 := by
    calc |∑ A ∈ A_ge2, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
          ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re|
        ≤ ∑ A ∈ A_ge2, |((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
            ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ A ∈ A_ge2, |∏ t ∈ A, h t| * ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
            refine Finset.sum_le_sum fun A _ => ?_
            rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            calc |∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re|
                ≤ ∫ x : ℝ, |(hbSubsetQuot hHB hQ A (x : ℂ)).re| := abs_integral_le_integral_abs
              _ = ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
                    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
                    exact ((hbSubsetQuot_spec hHB hQ A).1.norm_real x).symm
      _ ≤ ∑ A ∈ A_ge2, ‖h‖ ^ 2 * ∫ x : ℝ, ‖hbSubsetQuot hHB hQ A (x : ℂ)‖ := by
            refine Finset.sum_le_sum fun A hA => ?_
            exact mul_le_mul_of_nonneg_right (hprod_le A 2 (Finset.mem_filter.mp hA).2)
              (integral_nonneg fun _ => norm_nonneg _)
      _ = B_re * ‖h‖ ^ 2 := by rw [← Finset.mul_sum, mul_comm]
  set lin := ∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t
  set int_h := ∫ x : ℝ, (hbTrial hHB hQ h (x : ℂ)).re
  set M_h := profileMass (hbTrial hHB hQ h)
  have hlin_abs : |lin| ≤ B_lin * ‖h‖ := by
    calc |lin| ≤ ∑ t : ↥(hbTopZeros hHB hQ), |hbNodeCoeff hHB hQ t.1 * h t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t : ↥(hbTopZeros hHB hQ), |hbNodeCoeff hHB hQ t.1| * |h t| :=
          Finset.sum_congr rfl fun t _ => abs_mul _ _
      _ ≤ ∑ t : ↥(hbTopZeros hHB hQ), |hbNodeCoeff hHB hQ t.1| * ‖h‖ :=
          Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h t)
              (abs_nonneg _)
      _ = B_lin * ‖h‖ := by rw [← Finset.sum_mul]
  have h_quot_diff : int_h / M_h - lin = ((int_h - L * lin) + lin * (L - M_h)) / M_h := by
    field_simp [hmass_pos.ne']
    ring
  have h_diff_le : int_h / M_h - lin ≤ C_up * ‖h‖ ^ 2 := by
    have hnum_le : |(int_h - L * lin) + lin * (L - M_h)| ≤
        B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖) := by
      calc |(int_h - L * lin) + lin * (L - M_h)|
          ≤ |int_h - L * lin| + |lin * (L - M_h)| := abs_add_le _ _
        _ = |int_h - L * lin| + |lin| * |M_h - L| := by rw [abs_mul, abs_sub_comm L M_h]
        _ ≤ B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖) := by
              have hsub_re : int_h - L * lin =
                  ∑ A ∈ A_ge2, ((-1 : ℝ) ^ A.card * ∏ t ∈ A, h t) *
                    ∫ x : ℝ, (hbSubsetQuot hHB hQ A (x : ℂ)).re := by
                rw [hre_split]
                ring
              rw [hsub_re]
              gcongr
    have hdiv_le : int_h / M_h - lin ≤
        (B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖)) / (L / 2) := by
      rw [h_quot_diff]
      calc ((int_h - L * lin) + lin * (L - M_h)) / M_h
          ≤ |((int_h - L * lin) + lin * (L - M_h))| / M_h :=
              div_le_div_of_nonneg_right (le_abs_self _) hmass_pos.le
        _ ≤ (B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖)) / M_h :=
              div_le_div_of_nonneg_right hnum_le hmass_pos.le
        _ ≤ (B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖)) / (L / 2) :=
              div_le_div_of_nonneg_left (by positivity) (half_pos hL_pos) hmass_ge
    have hrhs_eq : (B_re * ‖h‖ ^ 2 + (B_lin * ‖h‖) * (B_l1 * ‖h‖)) / (L / 2) =
        C_up * ‖h‖ ^ 2 := by
      dsimp [C_up]
      ring
    linarith
  exact ⟨⟨_, hmem_multi⟩, (csInf_le (hbMultiSet_bddBelow hHB hQ h) hmem_multi).trans
    (by linarith)⟩

/-! ### Part 4: Normal-family lower bound and Theorem `se:terminal-stability` (\eqref{se:multilevel-slope}) -/

/-- Lower bound for `hbMultiSet` via `norm_limit_deriv`, Cauchy second-derivative control,
and Hermite–Biehler positive quadrature away from `S`. -/
lemma hbMultiSet_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ↥(hbTopZeros hHB hQ) → ℝ, ‖h‖ < δ →
        ∀ r ∈ hbMultiSet hHB hQ h,
          (∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t) - ε * ‖h‖ ≤ r := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∀ n : ℕ, ∃ h : ↥(hbTopZeros hHB hQ) → ℝ,
      ‖h‖ < 1 / ((n : ℝ) + 1) ∧ ∃ r ∈ hbMultiSet hHB hQ h,
        r < (∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t) - ε * ‖h‖ :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hh_lt r hr_mem hr_lt using hex
  have hf_ex : ∀ n : ℕ, ∃ f : ℂ → ℂ, AiryG f ∧ (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧
      (∀ t : ↥(hbTopZeros hHB hQ), t.1 ≠ hbMinZero hHB hQ →
        0 ≤ (f ((t.1 + h n t : ℝ) : ℂ)).re) ∧
      (∀ x : ℝ, x ≤ hbMinZero hHB hQ + h n (hbMinNode hHB hQ) → 0 ≤ (f (x : ℂ)).re) ∧
      r n = (∫ x : ℝ, (f (x : ℂ)).re) / profileMass f :=
    fun n => hr_mem n
  choose f hf_G hf_nz hf_nodes hf_half hf_r using hf_ex
  let Ψ : ℕ → ℂ → ℂ := fun n u => (((profileMass (f n))⁻¹ : ℝ) : ℂ) * f n u
  have hmass_pos : ∀ n : ℕ, 0 < profileMass (f n) :=
    fun n => profileMass_pos_of_airyG (hf_G n) (hf_nz n)
  have hΨ_G : ∀ n : ℕ, AiryG (Ψ n) :=
    fun n => airyG_real_mul _ (hf_G n)
  have hΨ_norm : ∀ n : ℕ, ∫ x : ℝ, ‖Ψ n (x : ℂ)‖ = 1 := by
    intro n
    have hnorm_eq : (fun x : ℝ => ‖Ψ n (x : ℂ)‖) =
        fun x : ℝ => (profileMass (f n))⁻¹ * ‖f n (x : ℂ)‖ := by
      ext x
      dsimp [Ψ]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (hmass_pos n).le)]
    rw [hnorm_eq, integral_const_mul]
    unfold profileMass
    exact inv_mul_cancel₀ (hmass_pos n).ne'
  have hΨ_re_int : ∀ n : ℕ, ∫ x : ℝ, (Ψ n (x : ℂ)).re = r n := by
    intro n
    have hre_eq : (fun x : ℝ => (Ψ n (x : ℂ)).re) =
        fun x : ℝ => (profileMass (f n))⁻¹ * (f n (x : ℂ)).re := by
      ext x; dsimp [Ψ]; simp [Complex.mul_re]
    rw [hre_eq, integral_const_mul, hf_r n, div_eq_inv_mul]
  have hΨ_nodes : ∀ n : ℕ, ∀ t : ↥(hbTopZeros hHB hQ),
      0 ≤ (Ψ n ((t.1 + h n t : ℝ) : ℂ)).re := by
    intro n t
    have hnonneg : 0 ≤ (f n ((t.1 + h n t : ℝ) : ℂ)).re := by
      by_cases htm : t.1 = hbMinZero hHB hQ
      · have hteq : t = hbMinNode hHB hQ := Subtype.ext htm
        rw [hteq]
        exact hf_half n (hbMinZero hHB hQ + h n (hbMinNode hHB hQ)) le_rfl
      · exact hf_nodes n t htm
    dsimp [Ψ]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (hmass_pos n).le) hnonneg
  have hΨ_half : ∀ n : ℕ, ∀ x : ℝ, x ≤ hbMinZero hHB hQ + h n (hbMinNode hHB hQ) →
      0 ≤ (Ψ n (x : ℂ)).re := by
    intro n x hx
    dsimp [Ψ]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (hmass_pos n).le) (hf_half n x hx)
  have hh_pos : ∀ n : ℕ, 0 < ‖h n‖ := by
    intro n
    by_contra h0
    have hzero : h n = 0 := by
      have : ‖h n‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
      exact norm_eq_zero.mp this
    have hquad := (hb_quad hHB hQ (hΨ_G n)
      (fun x hx => hΨ_half n x (by simpa [hzero] using hx))
      (fun i => by simpa [hzero] using hΨ_nodes n ⟨i.1, i.2.1⟩)).1
    have hlt := hr_lt n
    rw [← hΨ_re_int n, hzero] at hlt
    simp at hlt
    linarith
  let S := hbTopZeros hHB hQ
  let tm := hbMinZero hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  let R : ℕ → ℝ := fun n => max ((n : ℝ) + 1) (|tm| + 2)
  let ς : ℕ → ℝ := fun _ => 0
  let δ_seq : ℕ → ℝ := fun n =>
    max (∫ x : ℝ, (Ψ n (x : ℂ)).re) 0 + tailBound (4 * π)⁻¹ (R n)
  let uT : ℕ → ℝ := fun n => tm + h n (hbMinNode hHB hQ)
  have hS_hyp : ∀ n : ℕ, DensityHyp (4 * π)⁻¹ (R n) (ς n) (δ_seq n) (Ψ n) (uT n) := by
    intro n
    have hR : 1 ≤ R n := le_trans (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) (le_max_left _ _)
    have hh1 : |h n (hbMinNode hHB hQ)| ≤ 1 := by
      have h1 : |h n (hbMinNode hHB hQ)| ≤ ‖h n‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) (hbMinNode hHB hQ)
      have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith [hh_lt n]
    have hRu : -R n ≤ uT n := by
      have hR2 : |tm| + 2 ≤ R n := le_max_right _ _
      have htm_abs : -|tm| ≤ tm := neg_abs_le tm
      have hh_neg : -1 ≤ h n (hbMinNode hHB hQ) := by linarith [neg_abs_le (h n (hbMinNode hHB hQ))]
      dsimp [uT]; linarith
    exact AiryG.densityHyp_of_max_zero (hΨ_G n) (hΨ_norm n) hR hRu (hΨ_half n)
  have hB_lin_nn : 0 ≤ ∑ t : ↥S, |hbNodeCoeff hHB hQ t.1| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hδ_tend : Tendsto δ_seq atTop (𝓝 0) := by
    let B := ∑ t : ↥S, |hbNodeCoeff hHB hQ t.1|
    have h_r_le : ∀ n : ℕ, ∫ x : ℝ, (Ψ n (x : ℂ)).re ≤ B * (1 / ((n : ℝ) + 1)) := by
      intro n
      have h_lin_le : ∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h n t ≤ B * ‖h n‖ := by
        calc ∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h n t
            ≤ ∑ t : ↥S, |hbNodeCoeff hHB hQ t.1 * h n t| :=
              Finset.sum_le_sum fun t _ => le_abs_self _
          _ ≤ ∑ t : ↥S, |hbNodeCoeff hHB hQ t.1| * ‖h n‖ := by
              refine Finset.sum_le_sum fun t _ => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left
                (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) t) (abs_nonneg _)
          _ = B * ‖h n‖ := (Finset.sum_mul _ _ _).symm
      have h1 := hΨ_re_int n
      have h2 := hr_lt n
      have h3 := mul_nonneg hε.le (norm_nonneg (h n))
      have h4 := mul_le_mul_of_nonneg_left (hh_lt n).le hB_lin_nn
      linarith
    have h_max_tend : Tendsto (fun n : ℕ => max (∫ x : ℝ, (Ψ n (x : ℂ)).re) 0) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => le_max_right _ _) (fun n => max_le (h_r_le n) (by positivity)) ?_
      simpa [one_div] using (tendsto_const_nhds (x := B)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    have h_tail_tend : Tendsto (fun n : ℕ => tailBound (4 * π)⁻¹ (R n)) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => tailBound_nonneg (by positivity) _) (fun n => ?_)
        (tailBound_tendsto (4 * π)⁻¹)
      unfold tailBound
      have hRn : (n : ℝ) ≤ R n := le_trans (by linarith) (le_max_left _ _)
      have h_exp : Real.exp (-(5 / 6 : ℝ) * R n) ≤ Real.exp (-(5 / 6 : ℝ) * (n : ℝ)) := by
        rw [Real.exp_le_exp]; linarith
      have hC_nn : 0 ≤ (6 / 5 : ℝ) * (4 * π)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left h_exp hC_nn
    simpa [δ_seq] using h_max_tend.add h_tail_tend
  have hS_seq : DensitySeq (4 * π)⁻¹ R ς δ_seq Ψ uT :=
    { hC0 := by positivity
      hR := tendsto_atTop_mono (fun n => le_max_left _ _)
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      hς0 := Eventually.of_forall fun _ => le_rfl
      hς := tendsto_const_nhds
      hδ := hδ_tend
      hspec := hS_hyp }
  have hbd : ∃ x₀ : ℝ, ∀ n : ℕ, x₀ ≤ uT n := by
    refine ⟨tm - 1, fun n => ?_⟩
    have h1 : |h n (hbMinNode hHB hQ)| ≤ ‖h n‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) (hbMinNode hHB hQ)
    have h2 : ‖h n‖ ≤ 1 := (hh_lt n).le.trans (by
      rw [div_le_one (by positivity)]; linarith)
    dsimp [uT]; linarith [neg_abs_le (h n (hbMinNode hHB hQ))]
  have huT_lim : ∀ x < tm, ∀ᶠ n in atTop, x ≤ uT n := by
    intro x hx
    have hh_tm_tend : Tendsto (fun n : ℕ => |h n (hbMinNode hHB hQ)|) atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _)
        (fun n => ((by simpa [Real.norm_eq_abs] using
          norm_le_pi_norm (h n) (hbMinNode hHB hQ) : |h n (hbMinNode hHB hQ)| ≤ ‖h n‖)).trans (hh_lt n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have h_ev := hh_tm_tend.eventually (gt_mem_nhds (sub_pos.mpr hx))
    exact h_ev.mono fun n hn => by dsimp [uT]; linarith [neg_abs_le (h n (hbMinNode hHB hQ))]
  have hnodes_seq : ∀ i : HbNodes (HermiteBiehlerData.ofQNeZero hHB hQ),
      ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧ ∀ n : ℕ, 0 ≤ (Ψ n (ũ n : ℂ)).re := by
    intro i
    have hi_mem : i.1 ∈ hbTopZeros hHB hQ := i.2.1
    let t : ↥S := ⟨i.1, hi_mem⟩
    refine ⟨fun n => i.1 + h n t, ?_, fun n => hΨ_nodes n t⟩
    have hh_t_tend : Tendsto (fun n : ℕ => h n t) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <|
        squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_le_pi_norm _ _).trans (hh_lt n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add hh_t_tend
  let K_R : ℝ := S.sup' ⟨tm, hs.2.2.2.1⟩ (fun t => |t|) + 1
  have ht_le_KR : ∀ t : ↥S, |t.1| ≤ K_R - 1 := fun t => by
    dsimp [K_R]
    linarith [Finset.le_sup' (fun s : ℝ => |s|) t.2]
  have hKR_pos : 0 < K_R := by
    have : 0 ≤ S.sup' ⟨tm, hs.2.2.2.1⟩ (fun t => |t|) :=
      le_trans (abs_nonneg tm) (Finset.le_sup' (fun s : ℝ => |s|) hs.2.2.2.1)
    dsimp [K_R]; linarith
  let M : ℕ := Nat.ceil (K_R + 1)
  have hKR_lt_M : K_R < (M : ℝ) + 1 := by
    have := Nat.le_ceil (K_R + 1)
    dsimp [M]; linarith
  have hderiv := norm_limit_deriv hS_seq hbd (hbTerminalData hHB hQ).hG
    (hbTerminalData hHB hQ).hP huT_lim hnodes_seq M
  have hderiv2 : TendstoLocallyUniformlyOn (fun n => deriv (deriv (Ψ n)))
      (deriv (deriv (normProfile (hbExtremal hHB hQ)))) atTop (ball (0 : ℂ) ((M : ℝ) + 1)) :=
    hderiv.deriv (Eventually.of_forall fun n => (hΨ_G n).diff.deriv.differentiableOn) isOpen_ball
  have hcomp_sub : closedBall (0 : ℂ) K_R ⊆ ball (0 : ℂ) ((M : ℝ) + 1) :=
    closedBall_subset_ball hKR_lt_M
  have h_unif2 : TendstoUniformlyOn (fun n => deriv (deriv (Ψ n)))
      (deriv (deriv (normProfile (hbExtremal hHB hQ)))) atTop (closedBall (0 : ℂ) K_R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hderiv2 _
      hcomp_sub (isCompact_closedBall _ _)
  have hcont_lim2 : ContinuousOn
      (deriv (deriv (normProfile (hbExtremal hHB hQ)))) (closedBall (0 : ℂ) K_R) :=
    (normProfile_differentiable (hbTerminalData hHB hQ).hG).deriv.deriv.continuous.continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall (0 : ℂ) K_R).exists_bound_of_continuousOn hcont_lim2
  let C₂ : ℝ := max B₂ 0 + 1
  have hC₂_pos : 0 < C₂ := by positivity
  have h_ev_C₂ : ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) K_R, ‖deriv (deriv (Ψ n)) z‖ ≤ C₂ := by
    have h_u := Metric.tendstoUniformlyOn_iff.mp h_unif2 1 one_pos
    refine h_u.mono fun n hn z hz => ?_
    have h1 := hn z hz
    have h2 := hB₂ z hz
    rw [dist_eq_norm, norm_sub_rev] at h1
    have h_tri := (abs_le.mp (abs_norm_sub_norm_le (deriv (deriv (Ψ n)) z)
      (deriv (deriv (normProfile (hbExtremal hHB hQ))) z))).2
    linarith [le_max_left B₂ 0]
  let G := hbExtremal hHB hQ
  let L := profileMass G
  have hL_pos : 0 < L := (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos
  let ω : ↥S → ℝ := fun t => airyPQDr P Q t.1 / (airyPQN' P Q (t.1 : ℂ)).re ^ 2
  have hω_pos : ∀ t : ↥S, 0 < ω t := fun t => by
    have hzw := airyPQ_zero_weight_pos hHB hQ (hs.2.1 t.1 t.2)
    have hN' : (airyPQN' P Q (t.1 : ℂ)).re ≠ 0 := fun h0 => by
      have hne := hzw.2
      rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN'_ofReal, h0] at hne
      simp at hne
    exact div_pos hzw.1 (sq_pos_of_ne_zero hN')
  let Ω : ℝ := ∑ t : ↥S, ω t
  have hΩ_pos : 0 < Ω := Finset.sum_pos (fun t _ => hω_pos t) ⟨hbMinNode hHB hQ, Finset.mem_univ _⟩
  have hderiv_at_t : ∀ t : ↥S, Tendsto (fun n : ℕ =>
      (deriv (Ψ n) (t.1 : ℂ)).re) atTop (𝓝 ((deriv G (t.1 : ℂ)).re / L)) := by
    intro t
    have hmem : (t.1 : ℂ) ∈ ball (0 : ℂ) ((M : ℝ) + 1) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      linarith [ht_le_KR t]
    have htendC := hderiv.tendsto_at hmem
    have hlim_eq : (deriv (normProfile (hbTerminalData hHB hQ).G) (t.1 : ℂ)).re =
        (deriv G (t.1 : ℂ)).re / L := by
      have hnp : normProfile (hbTerminalData hHB hQ).G = fun z : ℂ => ((L⁻¹ : ℝ) : ℂ) * G z := rfl
      rw [hnp, deriv_const_mul _ ((hbExtremal_spec hHB hQ).1 (t.1 : ℂ))]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [div_eq_inv_mul]
    rw [← hlim_eq]
    exact Complex.continuous_re.continuousAt.tendsto.comp htendC
  have h_ev_slope : ∀ᶠ n in atTop,
      ∑ t : ↥S, ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re| < ε / 2 := by
    have hsum_tend : Tendsto (fun n : ℕ =>
        ∑ t : ↥S, ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re|) atTop (𝓝 0) := by
      have hz : (0 : ℝ) = ∑ _t : ↥S, ω _t * |((deriv G (_t.1 : ℂ)).re / L) - ((deriv G (_t.1 : ℂ)).re / L)| := by
        simp
      rw [hz]
      exact tendsto_finset_sum' Finset.univ _ _ fun t _ =>
        tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hderiv_at_t t)).abs)
    exact hsum_tend.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨δ_sub, hδ_sub_pos, h_sub_gap⟩ := hb_sub_below_gap hHB hQ
  have h_ev_h : ∀ᶠ n in atTop, ‖h n‖ < min 1 (min δ_sub (ε / (2 * C₂ * Ω))) := by
    have hm : 0 < min 1 (min δ_sub (ε / (2 * C₂ * Ω))) := by positivity
    have h1_tend : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (h1_tend.eventually (gt_mem_nhds hm)).mono fun n hn => (hh_lt n).trans hn
  obtain ⟨n, ⟨hn_C₂, hn_slope⟩, hn_h⟩ :=
    ((h_ev_C₂.and h_ev_slope).and h_ev_h).exists
  have hn_1 : ‖h n‖ < 1 := hn_h.trans_le (min_le_left _ _)
  have hn_sub : ‖h n‖ < δ_sub := hn_h.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hn_C2Ω : C₂ * Ω * ‖h n‖ < ε / 2 := by
    have hlt := hn_h.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h1 := mul_lt_mul_of_pos_left hlt (mul_pos hC₂_pos hΩ_pos)
    have heq : C₂ * Ω * (ε / (2 * C₂ * Ω)) = ε / 2 := by
      field_simp [hC₂_pos.ne', hΩ_pos.ne']
    linarith
  -- Taylor lower bound at each `t : ↥S`
  have htaylor : ∀ t : ↥S,
      -(h n t * (deriv (Ψ n) (t.1 : ℂ)).re) - C₂ * ‖h n‖ ^ 2 ≤ (Ψ n (t.1 : ℂ)).re := by
    intro t
    let φ : ℝ → ℝ := fun x => (Ψ n (x : ℂ)).re
    let φ' : ℝ → ℝ := fun x => (deriv (Ψ n) (x : ℂ)).re
    let φ'' : ℝ → ℝ := fun x => (deriv (deriv (Ψ n)) (x : ℂ)).re
    have hd1 : ∀ x : ℝ, HasDerivAt φ (φ' x) x := fun x => by
      have hG : HasDerivAt (fun y : ℝ => Ψ n (y : ℂ)) (deriv (Ψ n) (x : ℂ)) x := by
        simpa only [mul_one] using ((hΨ_G n).diff (x : ℂ)).hasDerivAt.comp_ofReal
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hG
    have hd2 : ∀ x : ℝ, HasDerivAt φ' (φ'' x) x := fun x => by
      have hG2 : HasDerivAt (fun y : ℝ => deriv (Ψ n) (y : ℂ))
          (deriv (deriv (Ψ n)) (x : ℂ)) x := by
        simpa only [mul_one] using ((hΨ_G n).diff.deriv (x : ℂ)).hasDerivAt.comp_ofReal
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hG2
    have h_in_KR : ∀ y ∈ uIcc t.1 (t.1 + h n t), (y : ℂ) ∈ closedBall (0 : ℂ) K_R := by
      intro y hy
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have hht : |h n t| ≤ 1 :=
        ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) t : |h n t| ≤ ‖h n‖)).trans hn_1.le
      have hy_bd := Set.mem_uIcc.mp hy
      have ht_bd := ht_le_KR t
      rcases hy_bd with ⟨hyl, hyu⟩ | ⟨hyl, hyu⟩
      · rw [abs_le]; constructor <;> linarith [abs_le.mp ht_bd, abs_le.mp hht]
      · rw [abs_le]; constructor <;> linarith [abs_le.mp ht_bd, abs_le.mp hht]
    have h_diff_φ' : ∀ s ∈ (Icc (0 : ℝ) 1), |φ' (t.1 + s * h n t) - φ' t.1| ≤ C₂ * |h n t| := by
      intro s hs_Icc
      have hsub_in : uIcc t.1 (t.1 + s * h n t) ⊆ uIcc t.1 (t.1 + h n t) := by
        refine uIcc_subset_uIcc left_mem_uIcc ?_
        rw [Set.mem_uIcc]
        rcases le_total 0 (h n t) with hh0 | hh0
        · left; exact ⟨by nlinarith [hs_Icc.1], by nlinarith [hs_Icc.2]⟩
        · right; exact ⟨by nlinarith [hs_Icc.2], by nlinarith [hs_Icc.1]⟩
      have h_ftc : φ' (t.1 + s * h n t) - φ' t.1 = ∫ y in t.1..(t.1 + s * h n t), φ'' y := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd2 y) ?_).symm
        exact (Complex.continuous_re.comp
          ((hΨ_G n).diff.deriv.deriv.continuous.comp continuous_ofReal)).intervalIntegrable _ _
      have h_bd : ∀ y ∈ uIcc t.1 (t.1 + s * h n t), ‖φ'' y‖ ≤ C₂ := fun y hy => by
        have hnorm_re : ‖φ'' y‖ ≤ ‖deriv (deriv (Ψ n)) (y : ℂ)‖ := Complex.abs_re_le_norm _
        exact hnorm_re.trans (hn_C₂ (y : ℂ) (h_in_KR y (hsub_in hy)))
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun y hy => h_bd y (Set.uIoc_subset_uIcc hy))
      rw [← h_ftc] at hnorm
      have hlen : |(t.1 + s * h n t) - t.1| ≤ |h n t| := by
        have : t.1 + s * h n t - t.1 = s * h n t := by ring
        rw [this, abs_mul, abs_of_nonneg hs_Icc.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hs_Icc.2
      exact hnorm.trans (mul_le_mul_of_nonneg_left hlen hC₂_pos.le)
    have h_ftc_φ : φ (t.1 + h n t) - φ t.1 - h n t * φ' t.1 =
        ∫ s in (0 : ℝ)..1, h n t * (φ' (t.1 + s * h n t) - φ' t.1) := by
      have h_int : φ (t.1 + h n t) - φ t.1 = ∫ s in (0 : ℝ)..1, h n t * φ' (t.1 + s * h n t) := by
        have hsub := (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => φ (t.1 + s * h n t))
          (f' := fun s : ℝ => h n t * φ' (t.1 + s * h n t))
          (a := (0 : ℝ)) (b := (1 : ℝ)) (fun s _ => ?_) ?_).symm
        · simpa using hsub
        · have h_lin : HasDerivAt (fun s : ℝ => t.1 + s * h n t) (h n t) s := by
            simpa using (hasDerivAt_id s |>.mul_const (h n t)).const_add t.1
          exact ((hd1 (t.1 + s * h n t)).comp s h_lin).congr_deriv (mul_comm _ _)
        · refine Continuous.intervalIntegrable ?_ _ _
          exact continuous_const.mul (Complex.continuous_re.comp
            (((hΨ_G n).diff.deriv.continuous.comp continuous_ofReal).comp
              (continuous_const.add (continuous_id.mul continuous_const))))
      have hint_s : IntervalIntegrable (fun s : ℝ => φ' (t.1 + s * h n t)) volume 0 1 :=
        Continuous.intervalIntegrable (Complex.continuous_re.comp
          (((hΨ_G n).diff.deriv.continuous.comp continuous_ofReal).comp
            (continuous_const.add (continuous_id.mul continuous_const)))) _ _
      rw [h_int, intervalIntegral.integral_const_mul]
      have hc_eq : h n t * φ' t.1 = h n t * ∫ _s in (0 : ℝ)..1, φ' t.1 := by simp
      rw [hc_eq, ← mul_sub,
        ← intervalIntegral.integral_sub hint_s intervalIntegrable_const,
        ← intervalIntegral.integral_const_mul]
    have h_rem : |φ (t.1 + h n t) - φ t.1 - h n t * φ' t.1| ≤ C₂ * ‖h n‖ ^ 2 := by
      rw [h_ftc_φ]
      have h_bd : ∀ s ∈ uIcc (0 : ℝ) 1, ‖h n t * (φ' (t.1 + s * h n t) - φ' t.1)‖ ≤
          C₂ * ‖h n‖ ^ 2 := by
        intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs, abs_mul]
        calc |h n t| * |φ' (t.1 + s * h n t) - φ' t.1|
            ≤ |h n t| * (C₂ * |h n t|) := mul_le_mul_of_nonneg_left (h_diff_φ' s hs) (abs_nonneg _)
          _ = C₂ * |h n t| ^ 2 := by ring
          _ ≤ C₂ * ‖h n‖ ^ 2 := by
              gcongr
              simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) t
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s hs => h_bd s (Set.uIoc_subset_uIcc hs))
      simpa using hnorm
    have hφ_nonneg : 0 ≤ φ (t.1 + h n t) := hΨ_nodes n t
    have hupper := (abs_le.mp h_rem).2
    dsimp [φ, φ'] at hφ_nonneg hupper
    linarith
  -- Quadrature lower bound using positive terms off S
  have hquad_lower : ∑ t : ↥S, ω t * (Ψ n (t.1 : ℂ)).re ≤ ∫ x : ℝ, (Ψ n (x : ℂ)).re := by
    obtain ⟨C_e, ν_e, hC_e, hb_e⟩ := (hΨ_G n).growth
    have hsumC := airyPQ_hasSum_unc hHB hQ (hΨ_G n).diff (hΨ_G n).integrable hC_e hb_e
    have hsumR := Complex.reCLM.hasSum hsumC
    have h_int_eq : Complex.reCLM (∫ x : ℝ, Ψ n (x : ℂ)) = ∫ x : ℝ, (Ψ n (x : ℂ)).re :=
      (Complex.reCLM.integral_comp_comm (hΨ_G n).integrable).symm
    rw [h_int_eq] at hsumR
    let emb : ↥S → {z : ℂ // airyPQN P Q z = 0} :=
      fun t => ⟨(t.1 : ℂ), hs.2.1 t.1 t.2⟩
    have hemb_inj : Function.Injective emb :=
      fun a b hab => Subtype.ext (Complex.ofReal_injective (congrArg Subtype.val hab))
    let F_S : Finset {z : ℂ // airyPQN P Q z = 0} := Finset.univ.image emb
    have hterm_eq : ∀ z : {z : ℂ // airyPQN P Q z = 0},
        Complex.reCLM (Ψ n z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)) =
          (Ψ n (z.1.re : ℂ)).re * (airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2) := by
      intro z
      have hzr : z.1 = (z.1.re : ℂ) := airyPQ_zero_eq_ofReal hHB z.2
      have hfz : Ψ n z.1 = (((Ψ n (z.1.re : ℂ)).re : ℝ) : ℂ) := by
        conv_lhs => rw [hzr]
        exact Complex.ext rfl ((hΨ_G n).real z.1.re)
      have hDz : airyPQD P Q z.1 = (airyPQDr P Q z.1.re : ℂ) := by
        conv_lhs => rw [hzr]
        exact airyPQD_ofReal P Q z.1.re
      have hN'z : airyPQN' P Q z.1 = ((airyPQN' P Q (z.1.re : ℂ)).re : ℂ) := by
        conv_lhs => rw [hzr]
        rw [airyPQN'_ofReal, Complex.ofReal_re]
      rw [hfz, hDz, hN'z, Complex.reCLM_apply]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h_off_nn : ∀ z ∉ F_S,
        0 ≤ Complex.reCLM (Ψ n z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)) := by
      intro z hzF
      rw [hterm_eq z]
      have hz_real : z.1 = (z.1.re : ℂ) := airyPQ_zero_eq_ofReal hHB z.2
      have hzN : airyPQN P Q (z.1.re : ℂ) = 0 := hz_real ▸ z.2
      have hzS : z.1.re ∉ S := fun hin => by
        apply hzF
        refine Finset.mem_image.mpr ⟨⟨z.1.re, hin⟩, Finset.mem_univ _, ?_⟩
        exact Subtype.ext hz_real.symm
      have hz_le_gap : z.1.re ≤ tm - δ_sub := h_sub_gap z.1.re hzN hzS
      have h1 : |h n (hbMinNode hHB hQ)| ≤ ‖h n‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) (hbMinNode hHB hQ)
      have hz_le_uT : z.1.re ≤ tm + h n (hbMinNode hHB hQ) := by
        linarith [neg_abs_le (h n (hbMinNode hHB hQ))]
      have hΨ_nn := hΨ_half n z.1.re hz_le_uT
      have hzw := airyPQ_zero_weight_pos hHB hQ hzN
      have hN' : (airyPQN' P Q (z.1.re : ℂ)).re ≠ 0 := fun h0 => by
        have hne := hzw.2
        rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
        rw [airyPQN'_ofReal, h0] at hne
        simp at hne
      have hw_nn : 0 ≤ airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2 :=
        div_nonneg hzw.1.le (sq_pos_of_ne_zero hN').le
      exact mul_nonneg hΨ_nn hw_nn
    have h_sum_le := sum_le_hasSum F_S h_off_nn hsumR
    have h_FS_eq : ∑ z ∈ F_S, Complex.reCLM (Ψ n z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)) =
        ∑ t : ↥S, ω t * (Ψ n (t.1 : ℂ)).re := by
      dsimp [F_S]
      rw [Finset.sum_image (fun a _ b _ hab => hemb_inj hab)]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hteq := hterm_eq (emb t)
      simp only [Complex.reCLM_apply] at hteq
      rw [hteq]
      dsimp [emb, ω]
      simp [mul_comm]
    linarith [h_sum_le, h_FS_eq]
  -- Combine quadrature + Taylor + derivative convergence to contradict `hr_lt n`
  have h_main_lower :
      (∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h n t) - ε * ‖h n‖ ≤ ∫ x : ℝ, (Ψ n (x : ℂ)).re := by
    have h_step1 : ∑ t : ↥S, ω t * (-(h n t * (deriv (Ψ n) (t.1 : ℂ)).re) - C₂ * ‖h n‖ ^ 2) ≤
        ∑ t : ↥S, ω t * (Ψ n (t.1 : ℂ)).re :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (htaylor t) (hω_pos t).le
    have h_lin_split :
        ∑ t : ↥S, ω t * (-(h n t * (deriv (Ψ n) (t.1 : ℂ)).re) - C₂ * ‖h n‖ ^ 2) =
          (∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h n t) +
            (∑ t : ↥S, ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re)) -
            C₂ * Ω * ‖h n‖ ^ 2 := by
      have h_b_eq : ∀ t : ↥S, hbNodeCoeff hHB hQ t.1 = -ω t * (deriv G (t.1 : ℂ)).re / L :=
        fun t => by
          rw [hbNodeCoeff_eq_weight_deriv hHB hQ t.2]
      calc ∑ t : ↥S, ω t * (-(h n t * (deriv (Ψ n) (t.1 : ℂ)).re) - C₂ * ‖h n‖ ^ 2)
          = (∑ t : ↥S, ((-ω t * (deriv G (t.1 : ℂ)).re / L) * h n t +
              ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re))) -
              ∑ t : ↥S, ω t * (C₂ * ‖h n‖ ^ 2) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun t _ => by ring
        _ = (∑ t : ↥S, hbNodeCoeff hHB hQ t.1 * h n t) +
              (∑ t : ↥S, ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re)) -
              C₂ * Ω * ‖h n‖ ^ 2 := by
              rw [Finset.sum_add_distrib]
              congr 1
              · congr 1
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [h_b_eq t]
              · rw [← Finset.sum_mul]; dsimp [Ω]; ring
    have h_err1 : -(ε / 2 * ‖h n‖) ≤
        ∑ t : ↥S, ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re) := by
      have habs : |∑ t : ↥S, ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re)| ≤
          (∑ t : ↥S, ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re|) * ‖h n‖ := by
        calc |∑ t : ↥S, ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re)|
            ≤ ∑ t : ↥S, |ω t * h n t * ((deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re)| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ t : ↥S, (ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re|) * ‖h n‖ := by
                refine Finset.sum_le_sum fun t _ => ?_
                rw [abs_mul, abs_mul, abs_of_pos (hω_pos t)]
                calc ω t * |h n t| * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re|
                    = ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re| * |h n t| := by
                        ring
                  _ ≤ ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re| * ‖h n‖ := by
                        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hω_pos t).le (abs_nonneg _))
                        simpa [Real.norm_eq_abs] using norm_le_pi_norm (h n) t
          _ = (∑ t : ↥S, ω t * |(deriv G (t.1 : ℂ)).re / L - (deriv (Ψ n) (t.1 : ℂ)).re|) * ‖h n‖ :=
                (Finset.sum_mul _ _ _).symm
      have h_mul := mul_le_mul_of_nonneg_right hn_slope.le (norm_nonneg (h n))
      linarith [(abs_le.mp (habs.trans h_mul)).1]
    have h_err2 : C₂ * Ω * ‖h n‖ ^ 2 ≤ ε / 2 * ‖h n‖ := by
      have h_mul2 := mul_le_mul_of_nonneg_right hn_C2Ω.le (norm_nonneg (h n))
      linarith [show C₂ * Ω * ‖h n‖ * ‖h n‖ = C₂ * Ω * ‖h n‖ ^ 2 by ring]
    linarith [hquad_lower, h_step1, h_lin_split, h_err1, h_err2]
  have hcontra := hr_lt n
  rw [← hΨ_re_int n] at hcontra
  linarith

/-- **Theorem `se:terminal-stability` (`\eqref{se:multilevel-slope}`):**
For every Hermite–Biehler pair `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`),
`I(h) = ∑_{t ∈ S} b_t h_t + o(‖h‖)` as `h → 0`, with `0 < b_{t_m}` and positive pure
terminal infimum `0 < hbI hHB hQ δ` for all `δ > 0`. -/
theorem hbMultiI_expansion :
    (fun h : ↥(hbTopZeros hHB hQ) → ℝ =>
      hbMultiI hHB hQ h - ∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t)
        =o[𝓝 0] id ∧
      0 < hbNodeCoeff hHB hQ (hbMinZero hHB hQ) ∧
      (∀ δ : ℝ, 0 < δ → 0 < hbI hHB hQ δ) := by
  refine ⟨Asymptotics.isLittleO_iff.mpr fun {ε} hε => ?_, hbNodeCoeff_tm_pos hHB hQ,
    fun δ hδ => (hb_stability hHB hQ).1 δ hδ⟩
  obtain ⟨C_up, δ_up, hC_up, hδ_up, h_up⟩ := hbMultiI_le hHB hQ
  obtain ⟨δ_lo, hδ_lo, h_lo⟩ := hbMultiSet_lower hHB hQ ε hε
  let δ_up2 : ℝ := if C_up = 0 then δ_up else min δ_up (ε / C_up)
  have hδ_up2_pos : 0 < δ_up2 := by
    dsimp [δ_up2]
    split_ifs with h0
    · exact hδ_up
    · exact lt_min hδ_up (div_pos hε (lt_of_le_of_ne hC_up (Ne.symm h0)))
  let δ := min δ_up2 δ_lo
  have hδ_pos : 0 < δ := lt_min hδ_up2_pos hδ_lo
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ_pos, fun {h} hh => ?_⟩
  rw [dist_zero_right] at hh
  have hh_up : ‖h‖ < δ_up := by
    have hh1 : ‖h‖ < δ_up2 := hh.trans_le (min_le_left _ _)
    dsimp [δ_up2] at hh1
    split_ifs at hh1 with h0
    · exact hh1
    · exact hh1.trans_le (min_le_left _ _)
  have hh_lo : ‖h‖ < δ_lo := hh.trans_le (min_le_right _ _)
  obtain ⟨hne, hle_up⟩ := h_up h hh_up
  have hge_lo : (∑ t : ↥(hbTopZeros hHB hQ), hbNodeCoeff hHB hQ t.1 * h t) - ε * ‖h‖ ≤
      hbMultiI hHB hQ h :=
    le_csInf hne (h_lo h hh_lo)
  have h_quad_to_lin : C_up * ‖h‖ ^ 2 ≤ ε * ‖h‖ := by
    by_cases hC0 : C_up = 0
    · rw [hC0, zero_mul]
      exact mul_nonneg hε.le (norm_nonneg _)
    · have hh1 : ‖h‖ < δ_up2 := hh.trans_le (min_le_left _ _)
      have hδ_eq : δ_up2 = min δ_up (ε / C_up) := by dsimp [δ_up2]; simp [hC0]
      rw [hδ_eq] at hh1
      have hC_pos : 0 < C_up := lt_of_le_of_ne hC_up (Ne.symm hC0)
      have hh2 : ‖h‖ < ε / C_up := hh1.trans_le (min_le_right _ _)
      have hh3 : C_up * ‖h‖ ≤ ε := (mul_lt_mul_of_pos_left hh2 hC_pos).le.trans_eq
        (mul_div_cancel₀ ε hC0)
      calc C_up * ‖h‖ ^ 2 = (C_up * ‖h‖) * ‖h‖ := by ring
        _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hh3 (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_le]
  simp only [id_eq]
  exact ⟨by linarith, by linarith⟩

/-- info: 'FormalResearch.ModularBootstrap.Stability.hbMultiI_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbMultiI_expansion

end HBMultilevelExpansion

end FormalResearch.ModularBootstrap.Stability
