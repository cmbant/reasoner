/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJC
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The scalar cubic chart with an abstract phase perturbation (F2a, `fct:comp-cfu`, Steps 2-3)

Paper Lemma `fct:comp-cfu`, Steps 2-3 of the proof.  Let `P` be a parameter space (in the paper `(ℓ, λ, α)`), `Ω ⊂ P` open,
`ℓ : P → ℝ` with values in `(-1/10, 27/10)` (the paper's box `ℓ ∈ [0, 2.6]` is inside) and
`r : P × ℝ → ℝ` (`r(p, z)`, the perturbation of the scaled odd phase `P(x) = x p(x²)`, `p(z) = ℓ - κ z + r(z)`,
`κ = π²/36`) of class `C^18` with all derivatives of order `≤ 18` bounded by `ε` on `Ω × (-1, 6)`.
`cfu_chart_core` constructs, for `ε ≤ ε₀`, and with all `C^16` jet bounds linear in `ε`:

* `B` with `ℓ - (π²/12) B + ρ(B) = 0` (`ρ = r + 2 z r_z`; the critical point `B = b²`), `‖B - 12ℓ/π²‖_{16} ≤ C ε`
  (`step_B`, by `claim_G_pert`);
* `d = (π²/12 - 3 r_z(B))^{1/3}`, `‖d - d*‖_{16} ≤ C ε`, `d* = (π²/12)^{1/3}` (`step_d`, by the `ε`-linear composition
  `JB.comp_small`);
* the Hadamard divided difference `H(p,z) = ∫₀¹ (1-σ) r_{zz}(B + σ(z-B)) dσ` with `‖H‖_{16} ≤ C ε` (`step_H`);
* `R` solving the divided-difference equation `d² R + d z R² + ⅓ z (z-B) R³ + H = 0`, `|R| < 1/50`,
  `‖R‖_{16} ≤ C ε` (`step_R`, by `claim_G`; the paper's `(fct:cfu-div)` up to the sign convention);
* `D = d + (z - B) R`, `‖D - d*‖_{16} ≤ C ε`, the inverse `Z` of `Y = z D²` on `Y ∈ (-1/10, 36/10)`
  (`step_Z`, by `claim_G_pert`) and `V = 1/D(Z(Y))`, `‖V - τ*‖_{16} ≤ C ε`, `τ* = 1/d* = (12/π²)^{1/3}`
  (`step_V`).
* the chart identity `ℓ - κ z + r = A D - z D³/3` (`A = d² B`; `hadH_identity` is the Taylor formula
  `r(z) - r(B) - r_z(B)(z-B) = (z-B)² H`, `chart_alg` the algebra), i.e. `P(x) = Q(W(x))`.

All jets are `JB 16`: iterated Fréchet derivatives with operator norms in the parameter space `P × ℝ`, equivalent
to the paper's `C^k` norms up to constants depending on `k` and on the dimension.  Domains are open boxes slightly
larger than the paper's closed boxes (replacing the paper's Whitney extension).  The constants `C`, `ε₀` depend only on the
fixed numerical data (`π`) and the bound `3` on `ℓ`.  `P` is abstract; the paper's `P` is `ℝ³`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Chart
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- `ρ = r + 2 z ∂_z r`, the derivative of the scaled phase `x ↦ x (ℓ - κ x² + r(x²))` with respect to `x`
(`P_λ'(x) = ℓ - π²/12 z + ρ(z)`). -/
noncomputable def rhoF (r : P × ℝ → ℝ) (q : P × ℝ) : ℝ := r q + 2 * (q.2 * fderiv ℝ r q (0, 1))

lemma step_rho : ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ∀ {r : P × ℝ → ℝ},
    JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε → JC 17 (Ω ×ˢ Ioo (-1 : ℝ) 6) (rhoF r) (c * ε) := by
  refine ⟨1 + 2 * (2 ^ 17 * 6), by positivity, ?_⟩
  intro Ω hΩ ε hε r hr
  have hU : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hU.uniqueDiffOn
  have hrz : JC 17 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => fderiv ℝ r q (0, 1)) ε := JC.deriv_snd (j := 17) hU hr
  have hs : JC 17 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => q.2) 6 :=
    JC.snd hUd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hm := JC.mul hUd (by norm_num) hε hs hrz
  have h2 := JC.const_smul hUd 2 hm
  have h3 := (hr.mono_order (by norm_num : 17 ≤ 18)).add hUd h2
  refine h3.mono ?_
  simp only [abs_two]
  nlinarith

/-- Numerical facts. -/
lemma m0_pos : 0 < Real.pi ^ 2 / 12 := by positivity

lemma twelve_pi_sq : Real.pi ^ 2 / 12 * (12 / Real.pi ^ 2) = 1 := by
  have : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp

lemma B0_bounds {ℓ : ℝ} (h1 : -1 / 10 < ℓ) (h2 : ℓ < 27 / 10) :
    -1 / 5 < 12 / Real.pi ^ 2 * ℓ ∧ 12 / Real.pi ^ 2 * ℓ < 7 / 2 := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hp2 : 98 / 10 < Real.pi ^ 2 := by nlinarith
  have hc : 0 < 12 / Real.pi ^ 2 := by positivity
  have hc1 : 12 / Real.pi ^ 2 < 123 / 100 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
  constructor <;> nlinarith

lemma step_B : ∃ c : ℝ, 0 ≤ c ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {r : P × ℝ → ℝ} {ℓ : P → ℝ}, JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε → JC 16 Ω ℓ 3 →
    (∀ p ∈ Ω, -1 / 10 < ℓ p ∧ ℓ p < 27 / 10) →
    ∃ B : P → ℝ, JC 16 Ω (fun p => B p - 12 / Real.pi ^ 2 * ℓ p) (c * ε) ∧
      (∀ p ∈ Ω, |B p - 12 / Real.pi ^ 2 * ℓ p| < 1 / 10) ∧
      ∀ p ∈ Ω, Real.pi ^ 2 / 12 * B p - ℓ p - rhoF r (p, B p) = 0 := by
  obtain ⟨cρ, hcρ0, hρ⟩ := step_rho (P := P)
  obtain ⟨C0, hC00, hG⟩ := claim_G_pert (Y := P) (k := 16) (by norm_num) (m0 := Real.pi ^ 2 / 12) m0_pos
  set m0 : ℝ := Real.pi ^ 2 / 12 with hm0def
  have hm0 : 0 < m0 := m0_pos
  have hm0lt : m0 < 1 := by
    have := Real.pi_lt_d2
    have := Real.pi_gt_d2
    rw [hm0def, div_lt_one (by norm_num)]
    nlinarith
  set a0 : ℝ := 12 / Real.pi ^ 2 with ha0def
  set bw : ℝ := (Nat.factorial 16 : ℝ) * (|a0| * 3) + 1 with hbwdef
  set cN : ℝ := (Nat.factorial 16 : ℝ) * cρ * (max 1 (max 1 bw)) ^ 16 with hcNdef
  have hcN0 : 0 ≤ cN := by positivity
  refine ⟨C0 * cN, by positivity, (m0 / 2 * (1 / 10) / 2) / (cN + 1), by positivity, ?_⟩
  intro Ω hΩ ε hε0 hε1 r ℓ hr hℓ hℓr
  have hU : IsOpen (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) := hΩ.prod isOpen_Ioo
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) := hU.uniqueDiffOn
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hρ' : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (rhoF r) (cρ * ε) := (hρ hΩ hε0 hr).mono_order (by norm_num)
  have hB0 : JC 16 Ω (fun p => a0 * ℓ p) (|a0| * 3) := by
    have := hℓ.const_smul hΩd a0
    simpa [smul_eq_mul] using this
  have hB0f : JC 16 (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) (fun q : P × ℝ => a0 * ℓ q.1)
      ((Nat.factorial 16 : ℝ) * (|a0| * 3)) := JC.comp_fst hΩd hUd (by positivity) hB0
  have hsnd : JC 16 (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) (fun q : P × ℝ => q.2) 1 :=
    JC.snd hUd le_rfl fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hw := hB0f.add hUd hsnd
  have hu1 : ∀ i, 1 ≤ i → i ≤ 16 → ∀ y ∈ Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10),
      ‖iteratedFDerivWithin ℝ i (fun q : P × ℝ => q.1) (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) y‖ ≤ 1 := by
    intro i hi _ y hy
    exact (norm_iteratedFDerivWithin_clm_le hUd (ContinuousLinearMap.fst ℝ P ℝ) hi hy).trans
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_fst_le p)
  have hmaps : MapsTo (fun q : P × ℝ => (q.1, a0 * ℓ q.1 + q.2)) (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10))
      (Ω ×ˢ Ioo (-1 : ℝ) 6) := by
    intro q hq
    have h1 := B0_bounds (hℓr q.1 hq.1).1 (hℓr q.1 hq.1).2
    have h2 := hq.2
    exact ⟨hq.1, by constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hN0 := JC.comp_pair hUd hWd (g := rhoF r) (u := fun q : P × ℝ => q.1)
    (w := fun q : P × ℝ => a0 * ℓ q.1 + q.2) (b1 := 1) (b2 := bw) (by positivity) hρ'
    contDiffOn_fst hw.1 hu1 (fun i _ hi y hy => hw.2 i hi y hy) hmaps
  have hN := hN0.neg hUd
  have hNε : JC 16 (Ω ×ˢ Ioo (-(1 / 10) : ℝ) (1 / 10)) (fun q : P × ℝ => -rhoF r (q.1, a0 * ℓ q.1 + q.2))
      (cN * ε) := hN.mono (le_of_eq (by simp only [hcNdef]; ring))
  have hεN : cN * ε ≤ m0 / 2 * (1 / 10) / 2 := by
    calc cN * ε ≤ cN * ((m0 / 2 * (1 / 10) / 2) / (cN + 1)) := mul_le_mul_of_nonneg_left hε1 hcN0
      _ = (cN / (cN + 1)) * (m0 / 2 * (1 / 10) / 2) := by ring
      _ ≤ 1 * (m0 / 2 * (1 / 10) / 2) := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
      _ = _ := one_mul _
  obtain ⟨w, hwd, hwb, hwspec⟩ := hG (O := Ω) hΩ (w0 := 1 / 10) (ε := cN * ε) (by positivity)
    (by nlinarith) (by nlinarith) (by nlinarith) hNε.1 hNε.2
  refine ⟨fun p => a0 * ℓ p + w p, ?_, ?_, ?_⟩
  · have : JC 16 Ω w (C0 * (cN * ε)) := ⟨hwd, hwb⟩
    refine (this.congr fun p hp => by simp).mono (le_of_eq (by ring))
  · intro p hp
    have := (hwspec p hp).1
    simp only [add_sub_cancel_left, abs_lt]
    exact ⟨by linarith [this.1], this.2⟩
  · intro p hp
    have h1 := (hwspec p hp).2.1
    simp only [neg_mul] at h1
    have h2 : m0 * (a0 * ℓ p) = ℓ p := by
      rw [hm0def, ha0def]
      have : Real.pi ^ 2 ≠ 0 := by positivity
      field_simp
    have h3 : m0 * w p - rhoF r (p, a0 * ℓ p + w p) = 0 := by linarith
    linarith [h3, h2]

/-- Jets of a fixed smooth function are bounded on a bounded interval inside its (open) domain. -/
lemma exists_JC_Ioo {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℝ} (hg : ContDiffOn ℝ k g V) {a b : ℝ}
    (hab : Icc a b ⊆ V) : ∃ C : ℝ, 0 ≤ C ∧ JC k (Ioo a b) g C := by
  have hcont : ∀ i ≤ k, ∃ C : ℝ, ∀ x ∈ Icc a b, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    intro i hi
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ i g V) V :=
      hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hV.uniqueDiffOn
    have h2 : ContinuousOn (fun x => ‖iteratedFDeriv ℝ i g x‖) (Icc a b) := by
      refine (h1.mono hab).norm.congr fun x hx => ?_
      show ‖iteratedFDeriv ℝ i g x‖ = ‖iteratedFDerivWithin ℝ i g V x‖
      rw [iteratedFDerivWithin_of_isOpen i hV (hab hx)]
    exact isCompact_Icc.exists_bound_of_continuousOn h2 |>.imp fun C hC x hx => by simpa using hC x hx
  choose! C hC using hcont
  refine ⟨∑ i ∈ Finset.range (k + 1), max (C i) 0, by positivity, ?_, ?_⟩
  · exact hg.mono (Ioo_subset_Icc_self.trans hab)
  · intro i hi x hx
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioo hx]
    refine (hC i hi x (Ioo_subset_Icc_self hx)).trans ?_
    refine (le_max_left (C i) 0).trans ?_
    exact Finset.single_le_sum (f := fun i => max (C i) 0) (fun j _ => le_max_right _ _) (Finset.mem_range.mpr (by omega))

/-- The cube root `(π²/12)^{1/3}`. -/
noncomputable def dStar : ℝ := (Real.pi ^ 2 / 12) ^ ((3 : ℝ)⁻¹)

/-- The cubic-root function `s ↦ (π²/12 - 3 s)^{1/3}` giving the scale `d`. -/
noncomputable def dRoot (s : ℝ) : ℝ := (Real.pi ^ 2 / 12 - 3 * s) ^ ((3 : ℝ)⁻¹)

lemma dRoot_zero : dRoot 0 = dStar := by simp [dRoot, dStar]

lemma dRoot_cube {s : ℝ} (hs : 0 ≤ Real.pi ^ 2 / 12 - 3 * s) : dRoot s ^ 3 = Real.pi ^ 2 / 12 - 3 * s := by
  have := Real.rpow_inv_natCast_pow hs (n := 3) (by norm_num)
  simpa [dRoot] using this

lemma dRoot_contDiffOn (k : ℕ) : ContDiffOn ℝ k dRoot (Iio (Real.pi ^ 2 / 12 / 3)) := by
  intro s hs
  have hs' : s < Real.pi ^ 2 / 12 / 3 := hs
  have hne : Real.pi ^ 2 / 12 - 3 * s ≠ 0 := by linarith
  have h1 : ContDiffAt ℝ k (fun x : ℝ => x ^ ((3 : ℝ)⁻¹)) (Real.pi ^ 2 / 12 - 3 * s) :=
    Real.contDiffAt_rpow_const_of_ne hne
  have h2 : ContDiffAt ℝ k (fun s : ℝ => Real.pi ^ 2 / 12 - 3 * s) s := by fun_prop
  exact (h1.comp s h2).contDiffWithinAt

lemma step_d (Bb : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {r : P × ℝ → ℝ} {B : P → ℝ}, JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε → JC 16 Ω B Bb →
    (∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6) →
    ∃ d : P → ℝ, JC 16 Ω (fun p => d p - dStar) (c * ε) ∧
      ∀ p ∈ Ω, 0 < d p ∧ d p ^ 3 = Real.pi ^ 2 / 12 - 3 * fderiv ℝ r (p, B p) (0, 1) := by
  have hm0 := m0_pos
  have hm0' : (0.8 : ℝ) < Real.pi ^ 2 / 12 := by
    have := Real.pi_gt_d2
    nlinarith
  obtain ⟨Cg, hCg0, hCg⟩ := exists_JC_Ioo (k := 16) (V := Iio (Real.pi ^ 2 / 12 / 3)) isOpen_Iio
    (dRoot_contDiffOn 16) (a := -(1 / 20)) (b := 1 / 20) (fun s hs => by
      have : s ≤ 1 / 20 := hs.2
      show s < Real.pi ^ 2 / 12 / 3
      linarith)
  set cs : ℝ := (Nat.factorial 16 : ℝ) * (max 1 (max 1 Bb)) ^ 16 with hcs
  have hcs0 : 0 ≤ cs := by positivity
  refine ⟨(1 + 2 ^ 15 * (Nat.factorial 15 : ℝ)) * Cg * cs, by positivity, 1 / 20 / (cs + 1), by positivity, ?_⟩
  intro Ω hΩ ε hε0 hε1 r B hr hB hBr
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hrz : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => fderiv ℝ r q (0, 1)) ε :=
    (JC.deriv_snd (j := 17) hW hr).mono_order (by norm_num)
  have hid1 : ∀ i, 1 ≤ i → i ≤ 16 → ∀ y ∈ Ω, ‖iteratedFDerivWithin ℝ i (fun p : P => p) Ω y‖ ≤ 1 :=
    fun i hi _ y hy => norm_iteratedFDerivWithin_id_le hΩd hi hy
  have hs := JC.comp_pair hΩd hWd (g := fun q : P × ℝ => fderiv ℝ r q (0, 1)) (u := fun p : P => p) (w := B)
    (b1 := 1) (b2 := Bb) hε0 hrz contDiffOn_id hB.1 hid1 (fun i _ hi y hy => hB.2 i hi y hy)
    (fun p hp => ⟨hp, hBr p hp⟩)
  have hsε : JC 16 Ω (fun p => fderiv ℝ r (p, B p) (0, 1)) (cs * ε) :=
    hs.mono (le_of_eq (by simp only [hcs]; ring))
  have hcsε : cs * ε < 1 / 20 := by
    calc cs * ε ≤ cs * (1 / 20 / (cs + 1)) := mul_le_mul_of_nonneg_left hε1 hcs0
      _ = (cs / (cs + 1)) * (1 / 20) := by ring
      _ < 1 * (1 / 20) := by
        gcongr
        rw [div_lt_one (by positivity)]; linarith
      _ = 1 / 20 := one_mul _
  have hmaps : MapsTo (fun p => fderiv ℝ r (p, B p) (0, 1)) Ω (Ioo (-(1 / 20) : ℝ) (1 / 20)) := by
    intro p hp
    have := abs_lt.mp ((JB.apply_le hsε.2 hp).trans_lt hcsε)
    exact this
  have hcomp := JC.comp_small (j := 15) hΩd isOpen_Ioo (convex_Ioo _ _) (by simp) hCg (f := fun p => fderiv ℝ r (p, B p) (0, 1))
    (ε := cs * ε) (by positivity) (by linarith) hCg0 hsε hmaps
  refine ⟨fun p => dRoot (fderiv ℝ r (p, B p) (0, 1)), ?_, ?_⟩
  · refine (hcomp.congr fun p _ => by rw [dRoot_zero]).mono (le_of_eq (by ring))
  · intro p hp
    have h1 := abs_lt.mp ((JB.apply_le hsε.2 hp).trans_lt hcsε)
    have h2 : 0 ≤ Real.pi ^ 2 / 12 - 3 * fderiv ℝ r (p, B p) (0, 1) := by linarith [h1.1, h1.2]
    refine ⟨Real.rpow_pos_of_pos (by linarith [h1.1, h1.2]) _, dRoot_cube h2⟩

lemma norm_fst_le_one (X Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] : ‖ContinuousLinearMap.fst ℝ X Z‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_fst_le p

lemma norm_snd_le_one (X Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] : ‖ContinuousLinearMap.snd ℝ X Z‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_snd_le p

/-- The Hadamard divided difference `H(p,z) = ∫₀¹ (1-σ) r''(B + σ(z-B)) dσ`
(`r(z) - r(B) - r'(B)(z-B) = (z-B)² H(z)`). -/
noncomputable def hadH (r : P × ℝ → ℝ) (B : P → ℝ) (q : P × ℝ) : ℝ :=
  ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * fderiv ℝ (fun x => fderiv ℝ r x (0, 1)) (q.1, B q.1 + σ * (q.2 - B q.1)) (0, 1)

lemma step_H (Bb : ℝ) (hBb : 0 ≤ Bb) : ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ∀ {r : P × ℝ → ℝ} {B : P → ℝ},
    JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε → JC 16 Ω B Bb → (∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6) →
    JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (hadH r B) (c * ε) := by
  set bB : ℝ := (Nat.factorial 16 : ℝ) * Bb with hbB
  set bw : ℝ := bB + 2 ^ 16 * 1 * ((Nat.factorial 16 : ℝ) * 6 + bB) with hbw
  set cc : ℝ := (Nat.factorial 16 : ℝ) * (max 1 (max 1 bw)) ^ 16 with hcc
  refine ⟨2 ^ 16 * (‖(1 : ℝ)‖ + 1) * cc, by positivity, ?_⟩
  intro Ω hΩ ε hε0 r B hr hB hBr
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hU3d : UniqueDiffOn ℝ ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1) := hWd.prod (uniqueDiffOn_Icc zero_lt_one)
  have hbB0 : 0 ≤ bB := by positivity
  -- the coordinate functions on `X = (P × ℝ) × ℝ`
  have hσ : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => x.2) 1 :=
    JC.snd hU3d le_rfl fun x hx => by
      have := hx.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hz0 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => q.2) 6 :=
    JC.snd hWd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hz : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => x.1.2)
      ((Nat.factorial 16 : ℝ) * 6) :=
    JC.comp_clm hU3d hWd (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ) (norm_fst_le_one _ _) (by norm_num) hz0
      (fun x hx => hx.1)
  set L1 : ((P × ℝ) × ℝ) →L[ℝ] P := (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)
    with hL1
  have hL1n : ‖L1‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      have := norm_fst_le_one P ℝ
      have := norm_fst_le_one (P × ℝ) ℝ
      nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ P ℝ), norm_nonneg (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)])
  have hBx : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => B (L1 x)) bB :=
    JC.comp_clm hU3d hΩd L1 hL1n hBb hB (fun x hx => hx.1.1)
  have hdiff := hz.sub hU3d hBx
  have hmul := JC.mul hU3d zero_le_one (by positivity) hσ hdiff
  have hwx := hBx.add hU3d hmul
  have hrz : JC 17 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => fderiv ℝ r q (0, 1)) ε :=
    JC.deriv_snd (j := 17) hW hr
  have hrzz : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => fderiv ℝ (fun x => fderiv ℝ r x (0, 1)) q (0, 1)) ε :=
    JC.deriv_snd (j := 16) hW hrz
  have hu1 : ∀ i, 1 ≤ i → i ≤ 16 → ∀ y ∈ (Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i (fun x : (P × ℝ) × ℝ => L1 x) ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Icc (0 : ℝ) 1) y‖ ≤ 1 :=
    fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hU3d L1 hi hy).trans hL1n
  have hcomp := JC.comp_pair hU3d hWd (g := fun q : P × ℝ => fderiv ℝ (fun x => fderiv ℝ r x (0, 1)) q (0, 1))
    (u := fun x : (P × ℝ) × ℝ => L1 x)
    (w := fun x : (P × ℝ) × ℝ => B (L1 x) + x.2 * (x.1.2 - B (L1 x))) (b1 := 1) (b2 := bw) hε0 hrzz
    L1.contDiff.contDiffOn hwx.1 hu1 (fun i _ hi y hy => hwx.2 i hi y hy) (by
      intro x hx
      have hp : L1 x ∈ Ω := hx.1.1
      have hB1 := hBr (L1 x) hp
      have hz1 := hx.1.2
      have hσ1 := hx.2
      have := (convex_Ioo (-1 : ℝ) 6).add_smul_sub_mem hB1 hz1 hσ1
      exact ⟨hp, by simpa [smul_eq_mul] using this⟩)
  have hwt := (JC.const hU3d (1 : ℝ)).sub hU3d hσ
  have hF := JC.mul hU3d (by positivity) (by positivity) hwt hcomp
  have hint := JC.integral01 hW (f := fun (q : P × ℝ) (σ : ℝ) =>
    (1 - σ) * fderiv ℝ (fun x => fderiv ℝ r x (0, 1)) (q.1, B q.1 + σ * (q.2 - B q.1)) (0, 1)) hF
  exact hint.mono (le_of_eq (by simp only [hcc]; ring))

lemma dStar_bounds : 93 / 100 < dStar ∧ dStar < 94 / 100 := by
  have hm := m0_pos
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hc : dStar ^ 3 = Real.pi ^ 2 / 12 := by
    have := Real.rpow_inv_natCast_pow (x := Real.pi ^ 2 / 12) hm.le (n := 3) (by norm_num)
    simpa [dStar] using this
  have hpos : 0 < dStar := Real.rpow_pos_of_pos hm _
  have hm1 : (0.82 : ℝ) < Real.pi ^ 2 / 12 := by nlinarith
  have hm2 : Real.pi ^ 2 / 12 < 0.83 := by nlinarith
  constructor
  · by_contra h
    push Not at h
    have : dStar ^ 3 ≤ (93 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le h 3
    nlinarith
  · by_contra h
    push Not at h
    have : (94 / 100 : ℝ) ^ 3 ≤ dStar ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    nlinarith


lemma Rcoef_pos {d z B t : ℝ} (hd : |d - dStar| ≤ 1 / 100) (hz : |z| < 6) (hzB : |z - B| < 7) (ht : |t| < 1 / 50) :
    (1 / 2 : ℝ) ≤ d ^ 2 + 2 * d * z * t + z * (z - B) * t ^ 2 := by
  have hs := dStar_bounds
  have hd1 := abs_le.mp hd
  have hd2 : 92 / 100 ≤ d := by linarith [hs.1]
  have hd3 : d ≤ 95 / 100 := by linarith [hs.2]
  have hz' := abs_lt.mp hz
  have ht' := abs_lt.mp ht
  have h1 : |2 * d * z * t| ≤ 2 * (95 / 100) * 6 * (1 / 50) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by linarith : 0 < d)]
    have := abs_nonneg z
    have := abs_nonneg t
    gcongr
  have h2 : |z * (z - B) * t ^ 2| ≤ 6 * 7 * (1 / 50) ^ 2 := by
    rw [abs_mul, abs_mul, abs_pow]
    have := abs_nonneg z
    have := abs_nonneg (z - B)
    have := abs_nonneg t
    gcongr
  have h3 : (92 / 100 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) hd2 2
  have h4 := neg_abs_le (2 * d * z * t)
  have h5 := neg_abs_le (z * (z - B) * t ^ 2)
  nlinarith

/-- The coefficient `F(q,t) = d² + d z t + ⅓ z (z-B) t²` of the divided-difference equation for `R`. -/
noncomputable def FnR (B d : P → ℝ) (x : (P × ℝ) × ℝ) : ℝ :=
  d x.1.1 ^ 2 + d x.1.1 * x.1.2 * x.2 + 1 / 3 * x.1.2 * (x.1.2 - B x.1.1) * x.2 ^ 2

lemma FnR_jc (Bb dd : ℝ) (hBb : 0 ≤ Bb) (hdd : 0 ≤ dd) : ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Set P}, IsOpen Ω →
    ∀ {B d : P → ℝ}, JC 16 Ω B Bb → JC 16 Ω d dd →
    JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) (FnR B d) K := by
  set bd : ℝ := (Nat.factorial 16 : ℝ) * dd with hbd
  set bB : ℝ := (Nat.factorial 16 : ℝ) * Bb with hbB
  set bz : ℝ := (Nat.factorial 16 : ℝ) * 6 with hbz
  set b1 : ℝ := 2 ^ 16 * bd * bd with hb1
  set b2 : ℝ := 2 ^ 16 * (2 ^ 16 * bd * bz) * 1 with hb2
  set b3 : ℝ := 2 ^ 16 * (2 ^ 16 * (2 ^ 16 * bz * (bz + bB)) * 1) * 1 with hb3
  refine ⟨b1 + b2 + |1 / 3| * b3, by positivity, ?_⟩
  intro Ω hΩ B d hB hd
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hUd : UniqueDiffOn ℝ ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) :=
    (hW.prod isOpen_Ioo).uniqueDiffOn
  have ht : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) (fun x : (P × ℝ) × ℝ => x.2) 1 :=
    JC.snd hUd le_rfl fun x hx => by
      have := hx.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hz0 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => q.2) 6 :=
    JC.snd hWd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hz : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) (fun x : (P × ℝ) × ℝ => x.1.2) bz :=
    JC.comp_clm hUd hWd (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ) (norm_fst_le_one _ _) (by norm_num) hz0
      (fun x hx => hx.1)
  set L1 : ((P × ℝ) × ℝ) →L[ℝ] P := (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)
    with hL1
  have hL1n : ‖L1‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      have := norm_fst_le_one P ℝ
      have := norm_fst_le_one (P × ℝ) ℝ
      nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ P ℝ), norm_nonneg (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)])
  have hBx : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) (fun x : (P × ℝ) × ℝ => B (L1 x)) bB :=
    JC.comp_clm hUd hΩd L1 hL1n hBb hB (fun x hx => hx.1.1)
  have hdx : JC 16 ((Ω ×ˢ Ioo (-1 : ℝ) 6) ×ˢ Ioo (-(1 / 50) : ℝ) (1 / 50)) (fun x : (P × ℝ) × ℝ => d (L1 x)) bd :=
    JC.comp_clm hUd hΩd L1 hL1n hdd hd (fun x hx => hx.1.1)
  have hbz0 : 0 ≤ bz := by positivity
  have hbd0 : 0 ≤ bd := by positivity
  have hbB0 : 0 ≤ bB := by positivity
  have hd2 := JC.mul hUd hbd0 hbd0 hdx hdx
  have hdz := JC.mul hUd hbd0 hbz0 hdx hz
  have hdzt := JC.mul hUd (by positivity) zero_le_one hdz ht
  have hzB := hz.sub hUd hBx
  have hzzB := JC.mul hUd hbz0 (by positivity) hz hzB
  have hzzBt := JC.mul hUd (by positivity) zero_le_one hzzB ht
  have hzzBtt := JC.mul hUd (by positivity) zero_le_one hzzBt ht
  have hc := hzzBtt.const_smul hUd (1 / 3)
  have hsum := (hd2.add hUd hdzt).add hUd hc
  refine (hsum.congr fun x hx => ?_).mono (le_of_eq ?_)
  · simp only [FnR, hL1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  · simp only [hb1, hb2, hb3]

lemma step_R (Bb dd : ℝ) (hBb : 0 ≤ Bb) (hdd : 0 ≤ dd) (cH : ℝ) (hcH : 0 ≤ cH) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {H : P × ℝ → ℝ} {B d : P → ℝ}, JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) H (cH * ε) → JC 16 Ω B Bb → JC 16 Ω d dd →
    (∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6) → (∀ p ∈ Ω, |d p - dStar| ≤ 1 / 100) →
    ∃ R : P × ℝ → ℝ, JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) R (c * ε) ∧
      ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, |R q| < 1 / 50 ∧
        H q + R q * (d q.1 ^ 2 + d q.1 * q.2 * R q + 1 / 3 * q.2 * (q.2 - B q.1) * R q ^ 2) = 0 := by
  obtain ⟨K, hK0, hKjc⟩ := FnR_jc (P := P) Bb dd hBb hdd
  obtain ⟨C, hC0, hG⟩ := claim_G (Y := P × ℝ) (k := 16) (by norm_num) (m := 1 / 2) (K := K) (by norm_num) hK0
  refine ⟨C * cH, by positivity, (1 / 200) / (cH + 1), by positivity, ?_⟩
  intro Ω hΩ ε hε0 hε1 H B d hH hB hd hBr hdr
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hF := hKjc hΩ hB hd
  have hεc : cH * ε < 1 / 100 := by
    calc cH * ε ≤ cH * ((1 / 200) / (cH + 1)) := mul_le_mul_of_nonneg_left hε1 hcH
      _ = (cH / (cH + 1)) * (1 / 200) := by ring
      _ < 1 * (1 / 200) := by
        gcongr
        rw [div_lt_one (by positivity)]; linarith
      _ ≤ 1 / 100 := by norm_num
  have hdE : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, ∀ t ∈ Ioo (-(1 / 50) : ℝ) (1 / 50),
      (1 / 2 : ℝ) ≤ FnR B d (q, t) + t * fderiv ℝ (FnR B d) (q, t) (0, 1) := by
    intro q hq t ht
    have hk0 : ((16 : ℕ) : ℕ∞ω) ≠ 0 := by norm_num
    have hdiff : DifferentiableAt ℝ (FnR B d) (q, t) :=
      (diffAt_of_mem hW hF.1 hq ht).differentiableAt hk0
    have hline := hasDerivAt_line hdiff
    have hpoly : HasDerivAt (fun s : ℝ => FnR B d (q, s))
        (d q.1 * q.2 + 2 / 3 * q.2 * (q.2 - B q.1) * t) t := by
      have h1 : HasDerivAt (fun s : ℝ => d q.1 * q.2 * s) (d q.1 * q.2) t := by
        simpa using (hasDerivAt_id t).const_mul (d q.1 * q.2)
      have h2 : HasDerivAt (fun s : ℝ => 1 / 3 * q.2 * (q.2 - B q.1) * s ^ 2)
          (1 / 3 * q.2 * (q.2 - B q.1) * (2 * t)) t := by
        simpa using (hasDerivAt_pow 2 t).const_mul (1 / 3 * q.2 * (q.2 - B q.1))
      have := (h1.const_add (d q.1 ^ 2)).add h2
      exact this.congr_deriv (by ring)
    rw [hline.unique hpoly]
    have hzabs : |q.2| < 6 := abs_lt.mpr ⟨by linarith [hq.2.1], hq.2.2⟩
    have hzB : |q.2 - B q.1| < 7 :=
      abs_lt.mpr ⟨by linarith [hq.2.1, (hBr q.1 hq.1).2], by linarith [hq.2.2, (hBr q.1 hq.1).1]⟩
    have hk := Rcoef_pos (hdr q.1 hq.1) hzabs hzB (abs_lt.mpr ht)
    have e : FnR B d (q, t) + t * (d q.1 * q.2 + 2 / 3 * q.2 * (q.2 - B q.1) * t) =
        d q.1 ^ 2 + 2 * d q.1 * q.2 * t + q.2 * (q.2 - B q.1) * t ^ 2 := by
      simp only [FnR]; ring
    rw [e]; exact hk
  obtain ⟨R, hRd, hRb, hRs⟩ := hG hW (w0 := 1 / 50) (ε := cH * ε) (by norm_num) (by norm_num) (by positivity)
    (by linarith) (by linarith) (E0 := H) hH.1 hH.2 hF.1 hF.2 hdE
  refine ⟨R, ⟨hRd, hRb.mono (le_of_eq (by ring))⟩, fun q hq => ?_⟩
  obtain ⟨h1, h2, -⟩ := hRs q hq
  refine ⟨abs_lt.mpr ⟨by linarith [h1.1], h1.2⟩, ?_⟩
  simpa [FnR] using h2

lemma step_D (Bb cd cR : ℝ) (hBb : 0 ≤ Bb) (hcd : 0 ≤ cd) (hcR : 0 ≤ cR) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ∀ {B d : P → ℝ} {R : P × ℝ → ℝ},
    JC 16 Ω B Bb → JC 16 Ω (fun p => d p - dStar) (cd * ε) → JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) R (cR * ε) →
    JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => d q.1 + (q.2 - B q.1) * R q - dStar) (c * ε) := by
  set bz : ℝ := 6 + (Nat.factorial 16 : ℝ) * Bb with hbz
  refine ⟨(Nat.factorial 16 : ℝ) * cd + 2 ^ 16 * bz * cR, by positivity, ?_⟩
  intro Ω hΩ ε hε B d R hB hd hR
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have h1 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => d q.1 - dStar) ((Nat.factorial 16 : ℝ) * (cd * ε)) :=
    JC.comp_fst (g := fun p => d p - dStar) hΩd hWd (by positivity) hd
  have hz0 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => q.2) 6 :=
    JC.snd hWd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hB1 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => B q.1) ((Nat.factorial 16 : ℝ) * Bb) :=
    JC.comp_fst hΩd hWd hBb hB
  have h2 := hz0.sub hWd hB1
  have h3 := JC.mul hWd (by positivity) (by positivity) h2 hR
  have h4 := h1.add hWd h3
  refine (h4.congr fun q hq => by ring).mono (le_of_eq ?_)
  simp only [hbz]; ring

/-- `Y = z D²` minus its linearisation `d*² z`: the small nonlinear part of the squared chart. -/
noncomputable def nY (D : P × ℝ → ℝ) (q : P × ℝ) : ℝ := q.2 * (D q - dStar) * (D q - dStar + 2 * dStar)

lemma nY_jc (cD : ℝ) (hcD : 0 ≤ cD) : ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → cD * ε ≤ 1 →
    ∀ {D : P × ℝ → ℝ}, JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => D q - dStar) (cD * ε) →
    JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (nY D) (c * ε) := by
  refine ⟨2 ^ 16 * 6 * (2 ^ 16 * cD * (1 + ‖2 * dStar‖)), by positivity, ?_⟩
  intro Ω hΩ ε hε hcDε D hD
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hz0 : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q : P × ℝ => q.2) 6 :=
    JC.snd hWd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hu2 := hD.add hWd (JC.const hWd (2 * dStar))
  have hprod := JC.mul hWd (by positivity) (by positivity) hD hu2
  have hn := JC.mul hWd (by norm_num) (by positivity) hz0 hprod
  refine (hn.congr fun q _ => by simp only [nY]; ring).mono ?_
  have h1 : cD * ε + ‖2 * dStar‖ ≤ 1 + ‖2 * dStar‖ := by linarith
  have h2 : 2 ^ 16 * (cD * ε) * (cD * ε + ‖2 * dStar‖) ≤ 2 ^ 16 * (cD * ε) * (1 + ‖2 * dStar‖) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc 2 ^ 16 * 6 * (2 ^ 16 * (cD * ε) * (cD * ε + ‖2 * dStar‖))
      ≤ 2 ^ 16 * 6 * (2 ^ 16 * (cD * ε) * (1 + ‖2 * dStar‖)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

lemma dStar_sq_inv : dStar ^ 2 * (dStar ^ 2)⁻¹ = 1 := by
  have : 0 < dStar := lt_trans (by norm_num) dStar_bounds.1
  field_simp

lemma step_Z (cn : ℝ) (hcn : 0 ≤ cn) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {D : P × ℝ → ℝ}, JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (nY D) (cn * ε) →
    ∃ Z : P × ℝ → ℝ, JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => Z y - (dStar ^ 2)⁻¹ * y.2) (c * ε) ∧
      ∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10), Z y ∈ Ioo (-1 : ℝ) 6 ∧
        Z y * D (y.1, Z y) ^ 2 = y.2 := by
  have hs := dStar_bounds
  have hdpos : 0 < dStar := lt_trans (by norm_num) hs.1
  have hd2 : 0 < dStar ^ 2 := by positivity
  have hdlt : dStar ^ 2 < 1 := by nlinarith [hs.2]
  set a : ℝ := (dStar ^ 2)⁻¹ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : 1.13 < a := by
    rw [ha, lt_inv_comm₀ (by norm_num) hd2]; nlinarith [hs.2]
  have ha2 : a < 1.16 := by
    rw [ha, inv_lt_comm₀ hd2 (by norm_num)]; nlinarith [hs.1]
  obtain ⟨CZ, hCZ0, hGP⟩ := claim_G_pert (Y := P × ℝ) (k := 16) (by norm_num) (m0 := dStar ^ 2) hd2
  set bw : ℝ := |a| * ((Nat.factorial 16 : ℝ) * 4) + 1 with hbw
  set cN : ℝ := (Nat.factorial 16 : ℝ) * cn * (max 1 (max 1 bw)) ^ 16 with hcN
  have hcN0 : 0 ≤ cN := by positivity
  refine ⟨CZ * cN, by positivity, (dStar ^ 2 / 2 * (3 / 4) / 2) / (cN + 1), by positivity, ?_⟩
  intro Ω hΩ ε hε0 hε1 D hn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hΩy : IsOpen (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) := hΩ.prod isOpen_Ioo
  have hΩyd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) := hΩy.uniqueDiffOn
  have hUN : IsOpen ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4)) :=
    hΩy.prod isOpen_Ioo
  have hUNd : UniqueDiffOn ℝ ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4)) :=
    hUN.uniqueDiffOn
  have hy0 : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y : P × ℝ => y.2) 4 :=
    JC.snd hΩyd (by norm_num) fun y hy => by
      have := hy.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hy0x : JC 16 ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4))
      (fun x : (P × ℝ) × ℝ => x.1.2) ((Nat.factorial 16 : ℝ) * 4) :=
    JC.comp_clm hUNd hΩyd (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ) (norm_fst_le_one _ _) (by norm_num) hy0
      (fun x hx => hx.1)
  have hwx0 : JC 16 ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4))
      (fun x : (P × ℝ) × ℝ => x.2) 1 :=
    JC.snd hUNd le_rfl fun x hx => by
      have := hx.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hwx := (hy0x.const_smul hUNd a).add hUNd hwx0
  set L1 : ((P × ℝ) × ℝ) →L[ℝ] P := (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)
    with hL1
  have hL1n : ‖L1‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      have := norm_fst_le_one P ℝ
      have := norm_fst_le_one (P × ℝ) ℝ
      nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ P ℝ), norm_nonneg (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)])
  have hu1 : ∀ i, 1 ≤ i → i ≤ 16 → ∀ y ∈ (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4),
      ‖iteratedFDerivWithin ℝ i (fun x : (P × ℝ) × ℝ => L1 x)
        ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4)) y‖ ≤ 1 :=
    fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hUNd L1 hi hy).trans hL1n
  have hrange : ∀ y0 w : ℝ, y0 ∈ Ioo (-(1 / 5) : ℝ) (36 / 10) → w ∈ Ioo (-(3 / 4) : ℝ) (3 / 4) →
      a * y0 + w ∈ Ioo (-1 : ℝ) 6 := by
    intro y0 w hy hw
    constructor <;> nlinarith [hy.1, hy.2, hw.1, hw.2]
  have hN0 := JC.comp_pair hUNd hWd (g := nY D) (u := fun x : (P × ℝ) × ℝ => L1 x)
    (w := fun x : (P × ℝ) × ℝ => a * x.1.2 + x.2) (b1 := 1) (b2 := bw) (by positivity) hn
    L1.contDiff.contDiffOn (by simpa [smul_eq_mul] using hwx.1) hu1
    (fun i _ hi y hy => by simpa [smul_eq_mul] using hwx.2 i hi y hy) (by
      intro x hx
      exact ⟨hx.1.1, hrange _ _ hx.1.2 hx.2⟩)
  have hNε : JC 16 ((Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) ×ˢ Ioo (-(3 / 4) : ℝ) (3 / 4))
      (fun x : (P × ℝ) × ℝ => nY D (L1 x, a * x.1.2 + x.2)) (cN * ε) :=
    hN0.mono (le_of_eq (by simp only [hcN]; ring))
  have hεN : cN * ε ≤ dStar ^ 2 / 2 * (3 / 4) / 2 := by
    calc cN * ε ≤ cN * ((dStar ^ 2 / 2 * (3 / 4) / 2) / (cN + 1)) := mul_le_mul_of_nonneg_left hε1 hcN0
      _ = (cN / (cN + 1)) * (dStar ^ 2 / 2 * (3 / 4) / 2) := by ring
      _ ≤ 1 * (dStar ^ 2 / 2 * (3 / 4) / 2) := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
      _ = _ := one_mul _
  obtain ⟨w, hwd, hwb, hwspec⟩ := hGP (O := Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) hΩy (w0 := 3 / 4)
    (ε := cN * ε) (by positivity) (by nlinarith) (by nlinarith) (by nlinarith) (N := fun x : (P × ℝ) × ℝ =>
      nY D (L1 x, a * x.1.2 + x.2)) hNε.1 hNε.2
  refine ⟨fun y => a * y.2 + w y, ?_, ?_⟩
  · have : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) w (CZ * (cN * ε)) := ⟨hwd, hwb⟩
    exact (this.congr fun y _ => by simp).mono (le_of_eq (by ring))
  · intro y hy
    obtain ⟨hw1, hw2, -⟩ := hwspec y hy
    refine ⟨hrange _ _ hy.2 hw1, ?_⟩
    have h2 : dStar ^ 2 * w y + nY D (y.1, a * y.2 + w y) = 0 := by simpa [hL1] using hw2
    simp only [nY] at h2
    have h3 : dStar ^ 2 * a = 1 := by rw [ha]; exact dStar_sq_inv
    show (a * y.2 + w y) * D (y.1, a * y.2 + w y) ^ 2 = y.2
    linear_combination h2 + y.2 * h3

lemma step_V (cD cZ : ℝ) (hcD : 0 ≤ cD) (hcZ : 0 ≤ cZ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {D Z : P × ℝ → ℝ}, JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => D q - dStar) (cD * ε) →
    JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => Z y - (dStar ^ 2)⁻¹ * y.2) (cZ * ε) →
    (∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10), Z y ∈ Ioo (-1 : ℝ) 6) →
    JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => (D (y.1, Z y))⁻¹ - dStar⁻¹) (c * ε) := by
  have hs := dStar_bounds
  have hdpos : 0 < dStar := lt_trans (by norm_num) hs.1
  set a : ℝ := (dStar ^ 2)⁻¹ with ha
  set bZ : ℝ := cZ + |a| * 4 with hbZ
  set cV1 : ℝ := (Nat.factorial 16 : ℝ) * cD * (max 1 (max 1 bZ)) ^ 16 with hcV1
  set cInv : ℝ := (Nat.factorial 16 : ℝ) * ((Nat.factorial 16 : ℝ) * (max 1 (9 / 10 : ℝ)⁻¹) ^ (16 + 1)) with hcInv
  have hcV10 : 0 ≤ cV1 := by positivity
  refine ⟨2 ^ 16 * cV1 * (2 ^ 16 * cInv * ‖dStar⁻¹‖), by positivity, 1 / 100 / (cV1 + 1), by positivity, ?_⟩
  intro Ω hΩ ε hε0 hε1 D Z hD hZ hZr
  have hΩy : IsOpen (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) := hΩ.prod isOpen_Ioo
  have hΩyd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) := hΩy.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hWd : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6) := hW.uniqueDiffOn
  have hε1' : ε ≤ 1 := by
    have : 1 / 100 / (cV1 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hy0 : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y : P × ℝ => y.2) 4 :=
    JC.snd hΩyd (by norm_num) fun y hy => by
      have := hy.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hZj : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) Z bZ := by
    have h1 := hZ.add hΩyd (hy0.const_smul hΩyd a)
    refine (h1.congr fun y _ => by simp).mono ?_
    have : cZ * ε ≤ cZ := by nlinarith
    simp only [hbZ]; linarith
  have hu1 : ∀ i, 1 ≤ i → i ≤ 16 → ∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10),
      ‖iteratedFDerivWithin ℝ i (fun y : P × ℝ => (ContinuousLinearMap.fst ℝ P ℝ) y)
        (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) y‖ ≤ 1 :=
    fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hΩyd (ContinuousLinearMap.fst ℝ P ℝ) hi hy).trans
      (norm_fst_le_one P ℝ)
  have hg1 := JC.comp_pair hΩyd hWd (g := fun q : P × ℝ => D q - dStar)
    (u := fun y : P × ℝ => (ContinuousLinearMap.fst ℝ P ℝ) y) (w := Z) (b1 := 1) (b2 := bZ) (by positivity) hD
    (ContinuousLinearMap.fst ℝ P ℝ).contDiff.contDiffOn hZj.1 hu1
    (fun i _ hi y hy => hZj.2 i hi y hy) (fun y hy => ⟨hy.1, hZr y hy⟩)
  have hg1' : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => D (y.1, Z y) - dStar) (cV1 * ε) :=
    hg1.mono (le_of_eq (by simp only [hcV1]; ring))
  have hcVε : cV1 * ε ≤ 1 / 100 := by
    calc cV1 * ε ≤ cV1 * (1 / 100 / (cV1 + 1)) := mul_le_mul_of_nonneg_left hε1 hcV10
      _ = (cV1 / (cV1 + 1)) * (1 / 100) := by ring
      _ ≤ 1 * (1 / 100) := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
      _ = 1 / 100 := one_mul _
  have hDp : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => D (y.1, Z y)) (cV1 * ε + ‖dStar‖) := by
    have := hg1'.add hΩyd (JC.const hΩyd dStar)
    exact this.congr fun y _ => by simp
  have hmin : ∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10), (9 / 10 : ℝ) ≤ D (y.1, Z y) := by
    intro y hy
    have h := (abs_le.mp (JB.apply_le hg1'.2 hy)).1
    linarith [hs.1]
  have hb1 : cV1 * ε + ‖dStar‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hdpos]; linarith [hs.2]
  have hinv := JC.inv hΩyd (by norm_num : (0 : ℝ) < 9 / 10) hmin hDp
  have hinv' : JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => (D (y.1, Z y))⁻¹) cInv := by
    refine hinv.mono (le_of_eq ?_)
    have : max 1 (cV1 * ε + ‖dStar‖) = 1 := max_eq_left hb1
    rw [this, one_pow, mul_one]
  have hprod := JC.mul hΩyd (by positivity) (by positivity) hinv' (JC.const hΩyd dStar⁻¹)
  have hfin := JC.mul hΩyd (by positivity) (by positivity) hg1' hprod
  have hneg := hfin.neg hΩyd
  refine (hneg.congr fun y hy => ?_).mono (le_of_eq (by ring))
  have hDpos : 0 < D (y.1, Z y) := by linarith [hmin y hy]
  field_simp
  ring


lemma taylor_two {f f' f'' : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S) (hf : ∀ t ∈ S, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ S, HasDerivAt f' (f'' t) t) (hc : ContinuousOn f'' S) {B z : ℝ} (hB : B ∈ S) (hz : z ∈ S) :
    f z - f B - f' B * (z - B) = (z - B) ^ 2 * ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * f'' (B + σ * (z - B)) := by
  have hseg : uIcc B z ⊆ S := hS.ordConnected.uIcc_subset hB hz
  have hder : ∀ t ∈ uIcc B z, HasDerivAt (fun t => f t + f' t * (z - t)) (f'' t * (z - t)) t := by
    intro t ht
    have h1 := hf t (hseg ht)
    have h2 := (hf' t (hseg ht)).mul ((hasDerivAt_id t).const_sub z)
    have := h1.add h2
    exact this.congr_deriv (by simp)
  have hint : IntervalIntegrable (fun t => f'' t * (z - t)) volume B z := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (hc.mono hseg).mul (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  simp only [sub_self, mul_zero, add_zero] at hftc
  have hsub : ∫ t in B..z, f'' t * (z - t) = (z - B) • ∫ σ in (0 : ℝ)..1, f'' ((z - B) * σ + B) * (z - ((z - B) * σ + B)) := by
    have := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) (fun t => f'' t * (z - t)) (z - B) B
    simpa using this.symm
  have hconv : ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * f'' (B + σ * (z - B)) =
      ∫ σ in (0 : ℝ)..1, (1 - σ) * f'' (B + σ * (z - B)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rw [hconv]
  have : f z - f B - f' B * (z - B) = ∫ t in B..z, f'' t * (z - t) := by linarith [hftc]
  rw [this, hsub, smul_eq_mul]
  have h3 : ∀ σ : ℝ, f'' ((z - B) * σ + B) * (z - ((z - B) * σ + B)) = (z - B) * ((1 - σ) * f'' (B + σ * (z - B))) := by
    intro σ
    have : (z - B) * σ + B = B + σ * (z - B) := by ring
    rw [this]; ring
  simp_rw [h3]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma hadH_identity {Ω : Set P} (hΩ : IsOpen Ω) {r : P × ℝ → ℝ} (hr : ContDiffOn ℝ 18 r (Ω ×ˢ Ioo (-1 : ℝ) 6))
    {B : P → ℝ} (hBr : ∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6) {q : P × ℝ} (hq : q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6) :
    r q - r (q.1, B q.1) - fderiv ℝ r (q.1, B q.1) (0, 1) * (q.2 - B q.1) =
      (q.2 - B q.1) ^ 2 * hadH r B q := by
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hrz : ContDiffOn ℝ 17 (fun x : P × ℝ => fderiv ℝ r x (0, 1)) (Ω ×ˢ Ioo (-1 : ℝ) 6) :=
    (hr.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hrzz : ContDiffOn ℝ 16 (fun x : P × ℝ => fderiv ℝ (fun x : P × ℝ => fderiv ℝ r x (0, 1)) x (0, 1))
      (Ω ×ˢ Ioo (-1 : ℝ) 6) := (hrz.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hp : q.1 ∈ Ω := hq.1
  have h1 : ∀ s ∈ Ioo (-1 : ℝ) 6, HasDerivAt (fun s => r (q.1, s)) (fderiv ℝ r (q.1, s) (0, 1)) s := fun s hs =>
    hasDerivAt_line (((hr.contDiffAt (hW.mem_nhds (show (q.1, s) ∈ Ω ×ˢ Ioo (-1 : ℝ) 6 from ⟨hp, hs⟩))).differentiableAt (by norm_num)))
  have h2 : ∀ s ∈ Ioo (-1 : ℝ) 6, HasDerivAt (fun s => fderiv ℝ r (q.1, s) (0, 1))
      (fderiv ℝ (fun x : P × ℝ => fderiv ℝ r x (0, 1)) (q.1, s) (0, 1)) s := fun s hs =>
    hasDerivAt_line (((hrz.contDiffAt (hW.mem_nhds (show (q.1, s) ∈ Ω ×ˢ Ioo (-1 : ℝ) 6 from ⟨hp, hs⟩))).differentiableAt (by norm_num)))
  have h3 : ContinuousOn (fun s => fderiv ℝ (fun x : P × ℝ => fderiv ℝ r x (0, 1)) (q.1, s) (0, 1))
      (Ioo (-1 : ℝ) 6) := by
    have : ContinuousOn (fun x : P × ℝ => fderiv ℝ (fun x : P × ℝ => fderiv ℝ r x (0, 1)) x (0, 1))
        (Ω ×ˢ Ioo (-1 : ℝ) 6) := hrzz.continuousOn
    exact this.comp (by fun_prop) (fun s hs => ⟨hp, hs⟩)
  exact taylor_two (convex_Ioo (-1 : ℝ) 6) h1 h2 h3 (hBr q.1 hp) hq.2

/-- Algebra of the chart identity `p(z) = A D - z D³/3` (`A = d² B`, `D = d + (z-B) R`). -/
lemma chart_alg {κ ℓ B d R H z r0 rz0 rq : ℝ}
    (E1 : 3 * κ * B - ℓ - r0 - 2 * B * rz0 = 0) (E2 : d ^ 3 - 3 * κ + 3 * rz0 = 0)
    (E3 : H + R * (d ^ 2 + d * z * R + 1 / 3 * z * (z - B) * R ^ 2) = 0)
    (E4 : rq - (r0 + rz0 * (z - B) + (z - B) ^ 2 * H) = 0) :
    ℓ - κ * z + rq = d ^ 2 * B * (d + (z - B) * R) - z * (d + (z - B) * R) ^ 3 / 3 := by
  linear_combination (-1) * E1 + (z - B) ^ 2 * E3 + (z / 3 - B) * E2 + E4

/-- `D(q) = d + (z - B) R`, the chart coefficient `W(x) = x D(x²)` (`D_λ(z) = d_λ + (z - B_λ) R_λ(z)`). -/
noncomputable def Dfun (B d : P → ℝ) (R : P × ℝ → ℝ) (q : P × ℝ) : ℝ := d q.1 + (q.2 - B q.1) * R q

theorem cfu_chart_core : ∃ cB cd cR cD cZ cV : ℝ, 0 ≤ cB ∧ 0 ≤ cd ∧ 0 ≤ cR ∧ 0 ≤ cD ∧ 0 ≤ cZ ∧ 0 ≤ cV ∧
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ {Ω : Set P}, IsOpen Ω → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε0 →
    ∀ {r : P × ℝ → ℝ} {ℓ : P → ℝ}, JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε → JC 16 Ω ℓ 3 →
    (∀ p ∈ Ω, -1 / 10 < ℓ p ∧ ℓ p < 27 / 10) →
    ∃ (B d : P → ℝ) (R Z : P × ℝ → ℝ),
      JC 16 Ω (fun p => B p - 12 / Real.pi ^ 2 * ℓ p) (cB * ε) ∧
      (∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6 ∧ Real.pi ^ 2 / 12 * B p - ℓ p - rhoF r (p, B p) = 0) ∧
      JC 16 Ω (fun p => d p - dStar) (cd * ε) ∧
      (∀ p ∈ Ω, 0 < d p ∧ d p ^ 3 = Real.pi ^ 2 / 12 - 3 * fderiv ℝ r (p, B p) (0, 1)) ∧
      JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) R (cR * ε) ∧
      (∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, |R q| < 1 / 50 ∧
        hadH r B q + R q * (d q.1 ^ 2 + d q.1 * q.2 * R q + 1 / 3 * q.2 * (q.2 - B q.1) * R q ^ 2) = 0) ∧
      JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => Dfun B d R q - dStar) (cD * ε) ∧
      JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => Z y - (dStar ^ 2)⁻¹ * y.2) (cZ * ε) ∧
      (∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10), Z y ∈ Ioo (-1 : ℝ) 6 ∧
        Z y * Dfun B d R (y.1, Z y) ^ 2 = y.2) ∧
      JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => (Dfun B d R (y.1, Z y))⁻¹ - dStar⁻¹) (cV * ε) ∧
      (∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + r q =
        d q.1 ^ 2 * B q.1 * Dfun B d R q - q.2 * Dfun B d R q ^ 3 / 3) := by
  obtain ⟨cρ, hcρ, -⟩ := step_rho (P := P)
  obtain ⟨cB, hcB, eB, heB, hB⟩ := step_B (P := P)
  set a0 : ℝ := 12 / Real.pi ^ 2 with ha0
  set Bb : ℝ := cB + |a0| * 3 with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  obtain ⟨cd, hcd, ed, hed, hd⟩ := step_d (P := P) Bb
  set dd : ℝ := cd + ‖dStar‖ with hdd
  have hdd0 : 0 ≤ dd := by positivity
  obtain ⟨cH, hcH, hH⟩ := step_H (P := P) Bb hBb0
  obtain ⟨cR, hcR, eR, heR, hR⟩ := step_R (P := P) Bb dd hBb0 hdd0 cH hcH
  obtain ⟨cD, hcD, hDc⟩ := step_D (P := P) Bb cd cR hBb0 hcd hcR
  obtain ⟨cn, hcn, hnY⟩ := nY_jc (P := P) cD hcD
  obtain ⟨cZ, hcZ, eZ, heZ, hZ⟩ := step_Z (P := P) cn hcn
  obtain ⟨cV, hcV, eV, heV, hV⟩ := step_V (P := P) cD cZ hcD hcZ
  refine ⟨cB, cd, cR, cD, cZ, cV, hcB, hcd, hcR, hcD, hcZ, hcV,
    min (min (min eB ed) (min eR eZ)) (min (min eV 1) (min (1 / 100 / (cd + 1)) (1 / (cD + 1)))),
    lt_min (lt_min (lt_min heB hed) (lt_min heR heZ)) (lt_min (lt_min heV one_pos)
      (lt_min (by positivity) (by positivity))), ?_⟩
  intro Ω hΩ ε hε0 hε r ℓ hr hℓ hℓr
  have hεB : ε ≤ eB := hε.trans (by simp)
  have hεd : ε ≤ ed := hε.trans (by simp)
  have hεR : ε ≤ eR := hε.trans (by simp)
  have hεZ : ε ≤ eZ := hε.trans (by simp)
  have hεV : ε ≤ eV := hε.trans (by simp)
  have hε1 : ε ≤ 1 := hε.trans (by simp)
  have hεcd : ε ≤ 1 / 100 / (cd + 1) := hε.trans (by simp)
  have hεcD : ε ≤ 1 / (cD + 1) := hε.trans (by simp)
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  obtain ⟨B, hBjc, hBr1, hBeq⟩ := hB hΩ hε0 hεB hr hℓ hℓr
  have hB0 : JC 16 Ω (fun p => a0 * ℓ p) (|a0| * 3) := by
    have := hℓ.const_smul hΩd a0
    simpa [smul_eq_mul] using this
  have hBfull : JC 16 Ω B Bb := by
    have h := hBjc.add hΩd hB0
    refine (h.congr fun p _ => by ring).mono ?_
    have : cB * ε ≤ cB := by nlinarith
    simp only [hBb]; linarith
  have hBrange : ∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6 := by
    intro p hp
    have h1 := B0_bounds (hℓr p hp).1 (hℓr p hp).2
    have h2 := abs_lt.mp (hBr1 p hp)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨d, hdjc, hdspec⟩ := hd hΩ hε0 hεd hr hBfull hBrange
  have hdfull : JC 16 Ω d dd := by
    have h := hdjc.add hΩd (JC.const hΩd dStar)
    refine (h.congr fun p _ => by ring).mono ?_
    have : cd * ε ≤ cd := by nlinarith
    simp only [hdd]; linarith
  have hdr : ∀ p ∈ Ω, |d p - dStar| ≤ 1 / 100 := by
    intro p hp
    refine (JB.apply_le hdjc.2 hp).trans ?_
    calc cd * ε ≤ cd * (1 / 100 / (cd + 1)) := mul_le_mul_of_nonneg_left hεcd hcd
      _ = (cd / (cd + 1)) * (1 / 100) := by ring
      _ ≤ 1 * (1 / 100) := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
      _ = 1 / 100 := one_mul _
  have hHjc := hH hΩ hε0 hr hBfull hBrange
  obtain ⟨R, hRjc, hRspec⟩ := hR hΩ hε0 hεR hHjc hBfull hdfull hBrange hdr
  have hDjc : JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => Dfun B d R q - dStar) (cD * ε) :=
    hDc hΩ hε0 hBfull hdjc hRjc
  have hcDε : cD * ε ≤ 1 := by
    calc cD * ε ≤ cD * (1 / (cD + 1)) := mul_le_mul_of_nonneg_left hεcD hcD
      _ = cD / (cD + 1) := by ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hn := hnY hΩ hε0 hcDε hDjc
  obtain ⟨Z, hZjc, hZspec⟩ := hZ hΩ hε0 hεZ hn
  have hVjc := hV hΩ hε0 hεV hDjc hZjc (fun y hy => (hZspec y hy).1)
  refine ⟨B, d, R, Z, hBjc, fun p hp => ⟨hBrange p hp, hBeq p hp⟩, hdjc, hdspec, hRjc, hRspec, hDjc, hZjc, hZspec,
    hVjc, fun q hq => ?_⟩
  have h4 := hadH_identity hΩ hr.1 hBrange hq
  have e1 := hBeq q.1 hq.1
  have e2 := (hdspec q.1 hq.1).2
  have e3 := (hRspec q hq).2
  unfold rhoF at e1
  exact chart_alg (κ := Real.pi ^ 2 / 36) (r0 := r (q.1, B q.1)) (rz0 := fderiv ℝ r (q.1, B q.1) (0, 1))
    (rq := r q) (by linarith) (by linarith) e3 (by linarith)

end Chart

/-- info: 'FormalResearch.SignUncertainty.step_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_rho

/-- info: 'FormalResearch.SignUncertainty.step_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_B

/-- info: 'FormalResearch.SignUncertainty.step_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_d

/-- info: 'FormalResearch.SignUncertainty.step_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_H

/-- info: 'FormalResearch.SignUncertainty.step_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_R

/-- info: 'FormalResearch.SignUncertainty.step_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_Z

/-- info: 'FormalResearch.SignUncertainty.step_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_V

/-- info: 'FormalResearch.SignUncertainty.hadH_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadH_identity

/-- info: 'FormalResearch.SignUncertainty.chart_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chart_alg

/-- info: 'FormalResearch.SignUncertainty.cfu_chart_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cfu_chart_core

end FormalResearch.SignUncertainty
