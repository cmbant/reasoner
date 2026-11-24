module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Design
public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive

/-!
# The window `W_2` of the two-simple-zero designs (`upper_transfer.tex`, Theorem T2 `ut:T2`)

A *two-simple-zero design* `𝔇` (`TwoZeroDesign n`) has real zeros `p > q`, `q < 0`, and `n` modified pairs at the
sites `u_k = s i` (`k = i + 3`, `u_k < 0`) with half-widths `ε_k = e i > 0`; every other pair is the reference
pair (site `uWKB k`, half-width `gapWKB k / 4`, `η₀ = 1/4`).  Its window is

`W_2(u) = Ai(u)² (u - p)(u - q) / ((u - a₁)²(u - a₂)²) · ∏_{k ≥ 3} ((u - u_k)² + ε_k²)/(u - a_k)²`
`       = -(u - p) · W^{(2)}(u)`,

where `W^{(2)} = airyWindowProd 2 q` is the `f = 2` Airy product of `Upper.Window` (with its removable
singularities at the Airy zeros).  Everything about `W_2` is inherited from `W^{(2)}`:

* `twoZeroW_differentiable`, `twoZeroW_bound` (`‖W_2‖ ≤ C (1+‖u‖)^{-5/2} e(u)`, class `𝒢_{-5/2}`);
* `twoZeroWin d`: `W_2` as an abstract `Upper.Rigidity.Window` with first kept site `u_f = q` (`W_2 ≥ 0` on
  `u ≤ q`, strictly positive below `q`, negative on `(q, p)`, positive above `p`) and the Airy quadrature
  `∫ W_2 = Σ_n W_2(a_n)/Ai'(a_n)²`;
* `tendsto_uAiry_tAiry_add_one`: `u(t(q) + 1) → q`, the position of the threshold `t(q) + 1` of `ut:T2`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window

/-- A two-simple-zero design (`ut:T2`): zeros `p`, `q`; `n` modified pairs with sites `s i` and half-widths
`e i` (the pair `k = i + 3`). -/
structure TwoZeroDesign (n : ℕ) where
  p : ℝ
  q : ℝ
  s : Fin n → ℝ
  e : Fin n → ℝ

namespace TwoZeroDesign

variable {n : ℕ}

/-- The parameter tuple (for the topology of compact families). -/
def toTuple (d : TwoZeroDesign n) : ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) := (d.p, d.q, d.s, d.e)

/-- The hypotheses of `ut:T2` on a design: `p > q`, `q < 0`, modified sites on the band `u_k < 0`, distinct,
with positive widths. -/
def Adm (d : TwoZeroDesign n) : Prop :=
  d.q < d.p ∧ d.q < 0 ∧ (∀ i, d.s i < 0) ∧ Function.Injective d.s ∧ ∀ i, 0 < d.e i

/-- A compact family of designs: its parameter set is compact. -/
def IsCompactFamily (𝒦 : Set (TwoZeroDesign n)) : Prop := IsCompact (toTuple '' 𝒦)

/-- The site `u_k` of the design (`k ≥ 3` modified for `k ≤ n + 2`, reference otherwise). -/
noncomputable def site (d : TwoZeroDesign n) (k : ℕ) : ℝ :=
  if h : 3 ≤ k ∧ k ≤ n + 2 then d.s ⟨k - 3, by omega⟩ else uWKB k

/-- The half-width `ε_k` of the design. -/
noncomputable def width (d : TwoZeroDesign n) (k : ℕ) : ℝ :=
  if h : 3 ≤ k ∧ k ≤ n + 2 then d.e ⟨k - 3, by omega⟩ else (1 / 4) * gapWKB k

lemma site_of_gt (d : TwoZeroDesign n) {k : ℕ} (hk : n + 2 < k) : d.site k = uWKB k := by
  unfold site; simp only [show ¬(3 ≤ k ∧ k ≤ n + 2) from by omega, dite_false]

lemma width_of_gt (d : TwoZeroDesign n) {k : ℕ} (hk : n + 2 < k) : d.width k = (1 / 4) * gapWKB k := by
  unfold width; simp only [show ¬(3 ≤ k ∧ k ≤ n + 2) from by omega, dite_false]

lemma width_ne_zero (d : TwoZeroDesign n) (hd : d.Adm) {k : ℕ} (hk : 2 < k) : d.width k ≠ 0 := by
  unfold width
  split_ifs with h
  · exact (hd.2.2.2.2 _).ne'
  · have := gapWKB_pos (by omega : 1 ≤ k)
    positivity

/-- Tail hypothesis of the Airy product for a profile that is the reference profile beyond a finite index. -/
lemma tail_of_reference {f M : ℕ} {site width : ℕ → ℝ} (hs : ∀ k, M < k → site k = uWKB k)
    (hw : ∀ k, M < k → width k = (1 / 4) * gapWKB k) : AiryProdTailHypothesis f site width := by
  set C₁ : ℝ := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ) with hC₁
  have hC₁p : 0 < C₁ := by have := kappaAiry_pos; positivity
  set B : ℝ := ∑ k ∈ Finset.range (M + 1), ((|site k - uWKB k| + |width k|) * ((k : ℝ) ^ (4 / 3 : ℝ) +
    (k : ℝ) ^ (1 / 3 : ℝ))) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨C₁ + B + 1, by positivity, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : 1 ≤ k := by omega
  have hp43 : 0 < (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hk0 _
  have hp13 : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hk0 _
  by_cases hkM : M < k
  · rw [hs k hkM, hw k hkM, sub_self, abs_zero]
    refine ⟨by positivity, ?_⟩
    have hgap : gapWKB k ≤ C₁ * (k : ℝ) ^ (-(1 / 3 : ℝ)) := gapWKB_le_mul_rpow hk1
    have hgn := (gapWKB_pos hk1).le
    rw [abs_of_nonneg (by positivity)]
    calc (1 / 4) * gapWKB k ≤ C₁ * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by linarith
      _ ≤ (C₁ + B + 1) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hp13.le
  · have hkr : k ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
    have hle := Finset.single_le_sum (f := fun k => ((|site k - uWKB k| + |width k|) *
      ((k : ℝ) ^ (4 / 3 : ℝ) + (k : ℝ) ^ (1 / 3 : ℝ)))) (fun k _ => by positivity) hkr
    have e43 : (k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hk0]; simp
    have e13 : (k : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hk0]; simp
    have p43 : 0 < (k : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hk0 _
    have p13 : 0 < (k : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hk0 _
    constructor
    · calc |site k - uWKB k| = |site k - uWKB k| * ((k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
            rw [e43, mul_one]
        _ = (|site k - uWKB k| * (k : ℝ) ^ (4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
        _ ≤ (C₁ + B + 1) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hp43.le
            nlinarith [abs_nonneg (site k - uWKB k), abs_nonneg (width k), mul_nonneg
              (abs_nonneg (site k - uWKB k)) p13.le, mul_nonneg (abs_nonneg (width k)) p43.le,
              mul_nonneg (abs_nonneg (width k)) p13.le]
    · calc |width k| = |width k| * ((k : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by
            rw [e13, mul_one]
        _ = (|width k| * (k : ℝ) ^ (1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ (C₁ + B + 1) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hp13.le
            nlinarith [abs_nonneg (site k - uWKB k), abs_nonneg (width k), mul_nonneg
              (abs_nonneg (site k - uWKB k)) p13.le, mul_nonneg (abs_nonneg (width k)) p43.le,
              mul_nonneg (abs_nonneg (site k - uWKB k)) p43.le]

lemma tail (d : TwoZeroDesign n) : AiryProdTailHypothesis 2 d.site d.width :=
  tail_of_reference (M := n + 2) (fun _ hk => d.site_of_gt hk) fun _ hk => d.width_of_gt hk

/-- The complex window `W_2(u) = -(u - p) · W^{(2)}(u)`. -/
noncomputable def W (d : TwoZeroDesign n) (u : ℂ) : ℂ :=
  -(u - (d.p : ℂ)) * airyWindowProd 2 d.q d.site d.width u

lemma W_differentiable (d : TwoZeroDesign n) : Differentiable ℂ d.W := by
  unfold W
  exact (differentiable_id.sub_const _).neg.mul
    (airyWindowProd_differentiable 2 (by norm_num) d.q d.site d.width d.tail)

lemma W_bound (d : TwoZeroDesign n) :
    ∃ C > 0, ∀ u : ℂ, ‖d.W u‖ ≤ C * (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * airyEnv u := by
  obtain ⟨C, hC, hbd⟩ := airyWindowProd_bound 2 (by norm_num) d.q d.site d.width d.tail
  refine ⟨C * (1 + |d.p|), by positivity, fun u => ?_⟩
  have h := hbd u
  have hx : 0 < 1 + ‖u‖ := by positivity
  have hxp : (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) = (1 + ‖u‖) * (1 + ‖u‖) ^ (-((2 * ((2 : ℕ) : ℝ) - 1 / 2))) := by
    conv_lhs => rw [show (-(5 / 2 : ℝ)) = 1 + (-((2 * ((2 : ℕ) : ℝ) - 1 / 2))) by norm_num]
    rw [Real.rpow_add hx, Real.rpow_one]
  have hnu : ‖u - (d.p : ℂ)‖ ≤ (1 + |d.p|) * (1 + ‖u‖) := by
    calc ‖u - (d.p : ℂ)‖ ≤ ‖u‖ + ‖(d.p : ℂ)‖ := norm_sub_le _ _
      _ = ‖u‖ + |d.p| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg d.p, norm_nonneg u]
  have henv := airyEnv_pos u
  unfold W
  rw [norm_mul, norm_neg]
  calc ‖u - (d.p : ℂ)‖ * ‖airyWindowProd 2 d.q d.site d.width u‖
      ≤ ((1 + |d.p|) * (1 + ‖u‖)) * (C * (1 + ‖u‖) ^ (-((2 * ((2 : ℕ) : ℝ) - 1 / 2))) * airyEnv u) :=
        mul_le_mul hnu h (norm_nonneg _) (by positivity)
    _ = C * (1 + |d.p|) * (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * airyEnv u := by rw [hxp]; ring

lemma W_integrable (d : TwoZeroDesign n) : Integrable fun x : ℝ => d.W (x : ℂ) := by
  obtain ⟨C, hC, hbd⟩ := d.W_bound
  exact airy_integrable_real d.W_differentiable hC.le (by norm_num) hbd

/-- The Airy quadrature `∫ W_2 = Σ_n W_2(a_n)/Ai'(a_n)²` for the complex window. -/
lemma W_hasSum (d : TwoZeroDesign n) :
    HasSum (fun m : ℕ => d.W (airyZero (m + 1) : ℂ) / (deriv airyAiC (airyZero (m + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, d.W (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := d.W_bound
  exact airy_quadrature d.W_differentiable hC.le (by norm_num) hbd

/-- The real window `W_2` on `ℝ`. -/
noncomputable def Wr (d : TwoZeroDesign n) (u : ℝ) : ℝ := (d.W (u : ℂ)).re

lemma Wr_eq (d : TwoZeroDesign n) (hd : d.Adm) (u : ℝ) :
    ∃ S : ℝ, 0 < S ∧ d.Wr u = (u - d.p) * (u - d.q) * S := by
  obtain ⟨S, hS, h⟩ := airyWindowProd_eq_neg_mul_pos d.q d.tail
    (fun k hk => d.width_ne_zero hd (by omega)) u
  refine ⟨S, hS, ?_⟩
  unfold Wr W
  rw [h]
  have : (-((u : ℂ) - (d.p : ℂ)) * ((-(u - d.q) * S : ℝ) : ℂ)) =
      (((u - d.p) * (u - d.q) * S : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

lemma continuous_Wr (d : TwoZeroDesign n) : Continuous d.Wr :=
  Complex.continuous_re.comp (d.W_differentiable.continuous.comp Complex.continuous_ofReal)

lemma integrable_Wr (d : TwoZeroDesign n) : Integrable d.Wr := d.W_integrable.re

lemma Wr_hasSum (d : TwoZeroDesign n) :
    HasSum (fun i : ℕ => d.Wr (airyNode i) * airyNodeWeight i) (∫ u, d.Wr u) := by
  have h1 := Complex.reCLM.hasSum d.W_hasSum
  have hr : (∫ u, d.Wr u) = ∫ x : ℝ, (d.W (x : ℂ)).re := rfl
  rw [hr]
  have h3 : ∫ x : ℝ, (d.W (x : ℂ)).re = (∫ x : ℝ, d.W (x : ℂ)).re := by
    simpa using integral_re d.W_integrable
  have h2 : Complex.reCLM (∫ x : ℝ, d.W (x : ℂ)) = ∫ x : ℝ, (d.W (x : ℂ)).re := by
    simp only [Complex.reCLM_apply]; exact h3.symm
  rw [h2] at h1
  convert h1 using 2 with i
  have hd : deriv airyAiC (airyZero (i + 1) : ℂ) = (airyAi' (airyZero (i + 1)) : ℂ) :=
    deriv_airyAiC_ofReal _
  have hnode : airyNode i = airyZero (i + 1) := rfl
  simp only [Complex.reCLM_apply, airyNodeWeight, hnode, Wr]
  rw [hd, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  ring

lemma Wr_pos_of_lt (d : TwoZeroDesign n) (hd : d.Adm) {u : ℝ} (hu : u < d.q) : 0 < d.Wr u := by
  obtain ⟨S, hS, h⟩ := d.Wr_eq hd u
  rw [h]
  have h1 : u - d.p < 0 := by linarith [hd.1]
  have h2 : u - d.q < 0 := by linarith
  have := mul_pos_of_neg_of_neg h1 h2
  positivity

lemma Wr_nonneg_of_le (d : TwoZeroDesign n) (hd : d.Adm) {u : ℝ} (hu : u ≤ d.q) : 0 ≤ d.Wr u := by
  rcases hu.lt_or_eq with h | h
  · exact (d.Wr_pos_of_lt hd h).le
  · obtain ⟨S, hS, e⟩ := d.Wr_eq hd u
    rw [e, h]; simp

lemma Wr_neg_of_mem (d : TwoZeroDesign n) (hd : d.Adm) {u : ℝ} (h1 : d.q < u) (h2 : u < d.p) :
    d.Wr u < 0 := by
  obtain ⟨S, hS, h⟩ := d.Wr_eq hd u
  rw [h]
  have := mul_neg_of_neg_of_pos (sub_neg.2 h2) (sub_pos.2 h1)
  nlinarith

lemma Wr_pos_of_gt (d : TwoZeroDesign n) (hd : d.Adm) {u : ℝ} (hu : d.p < u) : 0 < d.Wr u := by
  obtain ⟨S, hS, h⟩ := d.Wr_eq hd u
  rw [h]
  have := mul_pos (sub_pos.2 hu) (sub_pos.2 (hd.1.trans hu))
  positivity

end TwoZeroDesign

/-- The window `W_2` of an admissible two-simple-zero design as an abstract `Window`, first kept site `u_f = q`. -/
noncomputable def twoZeroWin {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) : Window where
  W := d.Wr
  uF := d.q
  continuous := d.continuous_Wr
  integrable := d.integrable_Wr
  nonneg_left := fun _ hu => d.Wr_nonneg_of_le hd hu
  hasSum := d.Wr_hasSum

@[simp] lemma twoZeroWin_W {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) : (twoZeroWin d hd).W = d.Wr := rfl

@[simp] lemma twoZeroWin_uF {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) : (twoZeroWin d hd).uF = d.q := rfl

end FormalResearch.ModularBootstrap.TwoLevel
