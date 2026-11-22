module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.SoftPhaseInputs
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk

/-!
# Paper J, Layer 2: the upper soft window of `thm:smo-BSr` as a `WindowPhase` (L2.S6, finding F-S6-6)

Source: Paper J `app_thmA.tex`, `thm:smo-BSr` ("Soft windows"), proof of `thm:smo-spec` ("Density": the slope on `I_pm` is `partial_alpha mu_0(0, 0) > 0`).
Inputs: `SoftPhaseInputs` (regularity of `mu_{2r}`, `X_s^+(t)`; uniform norm bound), `SoftLabels` (`PropThaW2` (3)); both in `Charts/SoftPhaseInputs.lean`.

## Proved here (axiom-pinned)

* `softSigma_sum`, `label_sum`: the phase sum `sum_{j<=M} h^j Sigma_j` is `pi sum_{s<=M/2} h^{2s} mu_{2s}`, and `mu_0 + sum_{s=1}^{n} h^{2s} mu_{2s} = sum_{s<=n}`.
* `softSigma_reg`: `Sigma_{+,j} in C^{2M+1}(I_+ x [-t0, t0])` by composition of `muS_reg` with `(X, t) -> (X_s^+(t) - X, t)` (`bandHi_reg`).
* `softSigma_zero`: `Sigma_{+,0}(X, 0) = S_0(X)` on `I_+ cap [X_s^-, X_s^+]` from the chart's `mu0_S0`.
* `softSigma_slope`: `partial_X Sigma_{+,0}(X, 0) <= -pi cmu0` on the open window, from the chart's `mu0_slope`.
* `softSigma_rule` and **`softUpWindow`**: the labelled rule `eq:smo-BSr2` on `I_+` for `T`, from `SoftLabels` (the terms `h^{2s} mu_{2s}`, `2s > M`, that `PropThaW2` carries beyond the phase are bounded by `Cmu h^{M+1}`: `muS_bd`),
  hence a `WindowPhase T K t0 M` on `[X_s^+(mu, 0) - w, X_s^+(mu, 0) + w]`.

## Differences from the paper

The labelled rule is taken as the premise `SoftLabels` (`PropThaW2` (3) after Step 0, with error `O(h^{M+1})`); the structure `SoftPhaseInputs` holds the regularity facts that the paper states in
`thm:smo-BSr` and the frozen chart does not contain.  `hq : M <= q` (`q = 2 Kidx`, `Kidx = (M+1)/2`).

## Not formalised

The lower window (`negFamily`, reversal of eigen-systems), the proofs of the `SoftPhaseInputs` fields, `SoftLabels` from `PropThaW2` and Step 0.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Two finite sums -/

/-- `sum_{j<=M} h^j Sigma_j = pi sum_{s<=M/2} h^{2s} mu_{2s}` for `Sigma_j = pi mu_{j/2}` (`j` even), `0` (`j` odd). -/
lemma softSigma_sum (f : ℕ → ℝ) (h : ℝ) (M : ℕ) :
    ∑ j ∈ range (M + 1), h ^ j * (if j % 2 = 0 then Real.pi * f (j / 2) else 0) =
      Real.pi * ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s := by
  have hE : ∀ a : ℕ, ∑ j ∈ range (2 * a + 1), h ^ j * (if j % 2 = 0 then Real.pi * f (j / 2) else 0) =
      Real.pi * ∑ s ∈ range (a + 1), h ^ (2 * s) * f s := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [show 2 * (a + 1) + 1 = (2 * a + 1) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ (fun s => h ^ (2 * s) * f s) (a + 1)]
      have h1 : ¬ ((2 * a + 1) % 2 = 0) := by omega
      have h2 : (2 * a + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * a + 1 + 1) / 2 = a + 1 := by omega
      rw [if_neg h1, if_pos h2, h3]
      ring
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' M
  · have : 2 * a / 2 = a := by omega
    rw [this]
    exact hE a
  · have : (2 * a + 1) / 2 = a := by omega
    rw [this, Finset.sum_range_succ, hE a]
    have h1 : ¬ ((2 * a + 1) % 2 = 0) := by omega
    rw [if_neg h1]
    ring

/-- `mu_0 + sum_{s=1}^n h^{2s} mu_{2s} = sum_{s<=n} h^{2s} mu_{2s}`. -/
lemma label_sum (f : ℕ → ℝ) (h : ℝ) (n : ℕ) :
    f 0 + ∑ s ∈ Icc 1 n, h ^ (2 * s) * f s = ∑ s ∈ range (n + 1), h ^ (2 * s) * f s := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ _ (n + 1), ← ih]; ring

/-! ### The window -/

section Soft

variable {T : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M Kidx : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart (frozenFamily T Kidx) (paramSet K t0) m q U V Lm}

/-- `Sigma_{+,j} in C^{2M+1}` on `I_+ x [-t0, t0]`: composition of `muS_reg` with `(X, t) -> (X_s^+(t) - X, t)`. -/
lemma softSigma_reg (SI : SoftPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 M C) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) :
    JetRegJ (softSigma C μ j) (Icc ((frozenFamily T Kidx).bandHi (μ, 0) - SI.w) ((frozenFamily T Kidx).bandHi (μ, 0) + SI.w)) t0 (2 * M + 1) := by
  unfold JetRegJ
  by_cases hjo : j % 2 = 0
  · set rect : Set (ℝ × ℝ) := Icc ((frozenFamily T Kidx).bandHi (μ, 0) - SI.w) ((frozenFamily T Kidx).bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0 with hrect
    have hg : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => C.muS (j / 2) (μ, p.2) p.1)
        (Icc (-(SI.w + SI.ρ)) (SI.w + SI.ρ) ×ˢ Icc (-t0) t0) := SI.muS_reg μ hμ (j / 2) (by omega)
    have hband : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => (frozenFamily T Kidx).bandHi (μ, p.2)) rect :=
      (SI.bandHi_reg μ hμ).comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    have hφ : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => ((frozenFamily T Kidx).bandHi (μ, p.2) - p.1, p.2)) rect :=
      (hband.sub contDiff_fst.contDiffOn).prodMk contDiff_snd.contDiffOn
    have hmaps : MapsTo (fun p : ℝ × ℝ => ((frozenFamily T Kidx).bandHi (μ, p.2) - p.1, p.2)) rect
        (Icc (-(SI.w + SI.ρ)) (SI.w + SI.ρ) ×ˢ Icc (-t0) t0) := by
      intro p hp
      have h1 := SI.bandHi_close μ hμ p.2 hp.2
      have h2 := hp.1
      have h3 := abs_le.mp h1
      refine ⟨⟨?_, ?_⟩, hp.2⟩ <;> simp only <;> linarith [h2.1, h2.2, h3.1, h3.2]
    have hcomp := contDiffOn_const (c := Real.pi).mul (hg.comp hφ hmaps)
    refine hcomp.congr (fun p _ => ?_)
    simp [softSigma, hjo]
  · have : (fun p : ℝ × ℝ => softSigma C μ j p.1 p.2) = fun _ => 0 := by
      funext p; simp [softSigma, hjo]
    rw [this]
    exact contDiffOn_const

/-- The hypothesis `(mu, 0) in paramSet K t0`. -/
lemma mem_paramSet_zero {μ : Par} (hμ : μ ∈ K) (ht0 : 0 < t0) : (μ, (0 : ℝ)) ∈ paramSet K t0 :=
  ⟨hμ, ⟨by linarith, ht0.le⟩⟩

/-- The band end of the frozen family at `t = 0` is that of `T`. -/
lemma frozen_bandHi_zero (T : SymbolFamily Par) (Kidx : ℕ) (μ : Par) : (frozenFamily T Kidx).bandHi (μ, 0) = T.bandHi μ := by
  rw [frozen_bandHi]
  unfold SymbolFamily.bandHi
  simp

/-- `Sigma_{+,0}(X, 0) = S_0(X)` on `I_+ cap [X_s^-, X_s^+]`, from the chart's `mu0_S0`. -/
lemma softSigma_zero (SI : SoftPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) {μ : Par} (hμ : μ ∈ K) {X : ℝ}
    (hX : X ∈ Icc ((frozenFamily T Kidx).bandHi (μ, 0) - SI.w) ((frozenFamily T Kidx).bandHi (μ, 0) + SI.w))
    (hband : X ∈ Icc (T.bandLo μ) (T.bandHi μ)) : softSigma C μ 0 X 0 = actionS0 T μ X := by
  have hb := frozen_bandHi_zero T Kidx μ
  have hle : X ≤ (frozenFamily T Kidx).bandHi (μ, 0) := by rw [hb]; exact hband.2
  have hδ : (frozenFamily T Kidx).bandHi (μ, 0) - X ≤ C.δ0 := by
    have := SI.window_in_chart
    have := SI.ρ_nonneg
    linarith [hX.1]
  have h := C.mu0_S0 (μ, 0) (mem_paramSet_zero hμ ht0) X hle hδ
  have e : softSigma C μ 0 X 0 = Real.pi * C.muS 0 (μ, 0) ((frozenFamily T Kidx).bandHi (μ, 0) - X) := by
    simp [softSigma]
  rw [e, h, ← actionS0_frozen_zero T Kidx μ X]
  rfl

/-- The slope of `Sigma_{+,0}(., 0)` on the open window, from the chart's `mu0_slope`. -/
lemma softSigma_slope (SI : SoftPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo ((frozenFamily T Kidx).bandHi (μ, 0) - SI.w) ((frozenFamily T Kidx).bandHi (μ, 0) + SI.w),
      deriv (fun X' => softSigma C μ 0 X' 0) X ≤ -c := by
  refine ⟨Real.pi * C.cmu0, mul_pos Real.pi_pos C.consts_pos5.1, fun μ hμ X hX => ?_⟩
  have hμ0 := mem_paramSet_zero hμ ht0
  have hd : Differentiable ℝ (C.muS 0 (μ, 0)) := (C.mu0_deriv (μ, 0) hμ0).1.differentiable (by norm_num)
  have h1 : HasDerivAt (fun X' : ℝ => (frozenFamily T Kidx).bandHi (μ, 0) - X') (-1) X := by
    simpa using (hasDerivAt_id X).const_sub ((frozenFamily T Kidx).bandHi (μ, 0))
  have h2 := (hd ((frozenFamily T Kidx).bandHi (μ, 0) - X)).hasDerivAt.comp X h1
  have h3 := h2.const_mul Real.pi
  have key : (fun X' => softSigma C μ 0 X' 0) =
      fun X' => Real.pi * (C.muS 0 (μ, 0) ∘ fun X'' : ℝ => (frozenFamily T Kidx).bandHi (μ, 0) - X'') X' := by
    funext X'; simp [softSigma]
  rw [key, h3.deriv]
  have hα : |(frozenFamily T Kidx).bandHi (μ, 0) - X| ≤ C.δ0 := by
    have := SI.window_in_chart
    have := SI.ρ_nonneg
    rw [abs_le]
    constructor <;> linarith [hX.1, hX.2, SI.w_pos]
  have hs := (C.mu0_slope (μ, 0) hμ0 _ hα).1
  nlinarith [Real.pi_pos]

/-- **The labelled rule `eq:smo-BSr2` on `I_+`**, from `SoftLabels` (see the module docstring). -/
lemma softSigma_rule (SI : SoftPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) (hq : M ≤ q)
    (hlab : SoftLabels T Kidx K M C) :
    ∃ Cr h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (T.jacobiMat μ N) Xs Um →
        ∀ k : Fin (N + 1), Xs k ∈ Icc ((frozenFamily T Kidx).bandHi (μ, 0) - SI.w) ((frozenFamily T Kidx).bandHi (μ, 0) + SI.w) →
          |∑ j ∈ range (M + 1), T.step N ^ j * softSigma C μ j (Xs k) (T.step N) - Real.pi * T.step N * (((k : ℕ) : ℝ) + 1 / 2)|
            ≤ Cr * T.step N ^ (M + 1) := by
  obtain ⟨Cc, h0, hh0, hl⟩ := hlab
  have hCmu0 := C.consts_pos2.1
  refine ⟨Real.pi * (|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu), min (min h0 t0) 1, lt_min (lt_min hh0 ht0) one_pos, ?_⟩
  intro μ hμ N hN Xs Um hE k hk
  have hpos : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
  have hN0 : T.step N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hNt : T.step N ≤ t0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN1 : T.step N ≤ 1 := hN.trans (min_le_right _ _)
  set h := T.step N with hh
  set b := (frozenFamily T Kidx).bandHi (μ, h) with hbdef
  have hcl := SI.bandHi_close μ hμ h ⟨by linarith, hNt⟩
  have hαδ : |Xs k - b| ≤ C.δ0 := by
    have h1 := SI.window_in_chart
    have h2 := abs_le.mp hcl
    rw [abs_le]
    constructor <;> linarith [hk.1, hk.2]
  have hlk := hl μ hμ N hN0 Xs Um hE k hαδ
  -- the sums
  set f : ℕ → ℝ := fun s => C.muS s (μ, h) (b - Xs k) with hf
  have hA : ∑ j ∈ range (M + 1), h ^ j * softSigma C μ j (Xs k) h = Real.pi * ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s := by
    rw [← softSigma_sum f h M]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [softSigma, hf, hbdef]
  have hL : C.muS 0 (μ, h) (b - Xs k) + ∑ s ∈ Icc 1 (q / 2), h ^ (2 * s) * C.muS s (μ, h) (b - Xs k)
      = ∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s := label_sum f h (q / 2)
  have hsplit : ∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s =
      ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s + ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s :=
    (Finset.sum_range_add_sum_Ico _ (by omega : M / 2 + 1 ≤ q / 2 + 1)).symm
  have hmem : (μ, h) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have htail : |∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s| ≤ ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu * h ^ (M + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), |h ^ (2 * s) * f s| ≤ C.Cmu * h ^ (M + 1) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      have hbd := C.muS_bd s (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (μ, h) hmem (b - Xs k) (by rw [abs_sub_comm]; exact hαδ)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hpos.le _)]
      calc h ^ (2 * s) * |f s| ≤ h ^ (M + 1) * C.Cmu :=
            mul_le_mul (pow_le_pow_of_le_one hpos.le hN1 (by omega)) hbd (abs_nonneg _) (by positivity)
        _ = C.Cmu * h ^ (M + 1) := by ring
    calc ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), |h ^ (2 * s) * f s|
        ≤ ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), C.Cmu * h ^ (M + 1) := Finset.sum_le_sum hterm
      _ = ((q / 2 + 1 - (M / 2 + 1) : ℕ) : ℝ) * (C.Cmu * h ^ (M + 1)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ((q / 2 : ℕ) + 1 : ℝ) * (C.Cmu * h ^ (M + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (q / 2 + 1 - (M / 2 + 1) : ℕ) ≤ q / 2 + 1 := by omega
          exact_mod_cast this
      _ = _ := by ring
  -- combine
  have hlk' : |∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h| ≤ Cc * h ^ (M + 1) := by
    rw [← hL]; exact hlk
  have hmain : |∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h| ≤
      (|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu) * h ^ (M + 1) := by
    have e : ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h =
        (∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h) -
          ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s := by
      rw [hsplit]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : Cc * h ^ (M + 1) ≤ |Cc| * h ^ (M + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith [hlk', htail]
  rw [hA]
  have e2 : Real.pi * ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - Real.pi * h * (((k : ℕ) : ℝ) + 1 / 2) =
      Real.pi * (∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h) := by ring
  rw [e2, abs_mul, abs_of_pos Real.pi_pos]
  calc Real.pi * |∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (((k : ℕ) : ℝ) + 1 / 2) * h|
      ≤ Real.pi * ((|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu) * h ^ (M + 1)) := mul_le_mul_of_nonneg_left hmain Real.pi_pos.le
    _ = _ := by ring

/-- **The upper soft window as a `WindowPhase`** (`thm:smo-BSr`, "Soft windows"): on `[X_s^+(mu, 0) - w, X_s^+(mu, 0) + w]`, from `SoftPhaseInputs` and the labels `SoftLabels`. -/
def softUpWindow (SI : SoftPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) (hq : M ≤ q)
    (hlab : SoftLabels T Kidx K M C) :
    WindowPhase T K t0 M (fun μ => (frozenFamily T Kidx).bandHi (μ, 0) - SI.w) (fun μ => (frozenFamily T Kidx).bandHi (μ, 0) + SI.w) where
  Sigma := softSigma C
  Sigma_reg := fun μ hμ j hj => softSigma_reg SI hμ hj
  Sigma_bdd := SI.Sigma_bdd
  Sigma_zero := fun μ hμ X hX hb => softSigma_zero SI ht0 hμ hX hb
  slope := softSigma_slope SI ht0
  rule := softSigma_rule SI ht0 hq hlab

end Soft

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_rule

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_reg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_zero

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_slope

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softUpWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softUpWindow

end FormalResearch.JacobiEigenvectors.TheoremA
