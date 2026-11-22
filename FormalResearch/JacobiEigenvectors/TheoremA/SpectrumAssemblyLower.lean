module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.NegTransport
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblySoft

/-!
# Paper J, Layer 2: the lower soft window of `thm:smo-BSr` as a `WindowPhase` (L2.S6, the lower edge, `WS false`)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-BSr` ("At the lower edge apply the same to the matrix `-(-1)^n J~_h^{(t)} (-1)^n` (bonds `a_n`, diagonal `-B_n`), whose spectrum is `-X_k(t)` with index `N - k` from the top, and
put `Sigma_- := pi L - Sigma~_+(-X, t, h)`; since `(N+1) h = L`, `pi L - pi h (N - k + 1/2) = pi h (k + 1/2)`, and `pi L - Sigma~_{+,0} = S_0^{(t)}` on the band").  `NegTransport.lean` is the eigen-system reversal;
this file is the phase bookkeeping.  The chart of the lower edge is `CI.softLoL : SoftEdgeChart (negFamily (frozenFamily F Kidx)) ..` (`ChartInputs`), so every statement below is about
`Fz := negFamily (frozenFamily T Kidx)` itself (no rewriting of the family), `C : SoftEdgeChart Fz (paramSet K t0) m q U V Lm`.

## Proved here (axiom-pinned)

* `softSigmaG_reg`, `softSigmaG_slope`, `softSigma_rule_core`: the generic-in-`Fz` versions of `softSigma_reg`, `softSigma_slope` and of the core of `softSigma_rule` (from the labelled rule at one eigenvalue to the
  phase sum with label `kk`); the frozen-specific lemmas of `SpectrumAssemblySoft.lean` are the same proofs.
* `softLoSigma L C mu j X t := (if j = 0 then pi L else 0) - Sigma~_{+,j}(-X, t)` (`Sigma_-` of the paper; the constant `pi L` is the order-`0` term since `(N+1) h = L` exactly).
* `actionS0_neg`: `S_0(negFamily G, X') = pi L - S_0(G, -X')` (from `arccos(-w) = pi - arccos w`), under integrability of the integrand; `actionS0_integrable` gives it from `HypOn T K`, `DM T K 0`.
* `softLoSigma_reg` (`C^{2M+1}` on the lower window by composition with the reflection `(X, t) -> (-X, t)`), `softLoSigma_bdd` (the uniform norm bound, from `SoftPhaseInputs.Sigma_bdd` via the isometry
  `reflX`), `softLoSigma_zero` (`Sigma_{-,0}(X, 0) = S_0(X)` on the band, from the chart's own `mu0_S0` and `actionS0_neg`), `softLoSigma_slope` (`d_X Sigma_{-,0} <= -pi cmu0`, from `mu0_slope`) and
  `softLoSigma_rule` (the labelled rule `eq:smo-BSr2` on `I_-` for `T`, from `SoftLabelsLo` through `IsEigenSystem.neg_frozen`, `negX_rev`, `pi L - pi h (N - k + 1/2) = pi h (k + 1/2)`).
* **`softLoWindow`**: the lower soft window `WindowPhase T K t0 M (X_s^-(mu) - w) (X_s^-(mu) + w)`, from `SoftPhaseInputs` of the chart `softLoL` and the labels `SoftLabelsLo`.  This is `WS false` of `thmSmoSpec`.

## Differences from the paper

* The window is `{|X - X_s^-(mu)| <= w}` (`X_s^-` of `T` at `t = 0`), the half-width `w` and the closeness `rho` of `X_s^-(t)` to `X_s^-(0)` being fields of `SoftPhaseInputs` of the lower chart (paper: `delta_0/4`, `delta_0/16`).
* `SoftLabelsLo` is the lower analogue of `SoftLabels`: `PropThaW2` (3) for the chart `softLoL` (family `negFamily (frozenFamily T Kidx)`) at `p = (mu, step N)`, i.e. for the eigen-systems of the matrix
  `(negFamily (frozenFamily T Kidx)).jacobiMat (mu, step N) N` (which is `negFamily T`'s matrix `-D J_h D`, `negFrozen_jacobiMat_at_step`), after Step 0, with error `O(h^{M+1})`.  It is an *input* from `PropThaW2` (L2.C7),
  not proved here (Step 0 for the lower end is Step 0 of the gauge family, `X_N >= X_s^- - C h^2`).
* The integrability of the `S_0` integrand is needed for `arccos(-w) = pi - arccos w` under the integral: `softLoWindow` takes `HypOn T K` and `DM T K 0` (the paper's `(H1)`--`(H3)`, `(D_0)`), as `actionS0_mem_Icc` does.

## Not formalised

The proofs of the `SoftPhaseInputs` fields of the lower chart and of `SoftLabelsLo` from `PropThaW2` and Step 0 (Layer 4 / L2.C7).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Generic-in-`Fz` versions of the upper-window lemmas -/

section Generic

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ} {M : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart Fz P m q U V Lm}

/-- `softSigma_reg` for an arbitrary soft family `Fz`. -/
lemma softSigmaG_reg (SI : SoftPhaseInputs Fz P K t0 M C) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) :
    JetRegJ (softSigma C μ j) (Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w)) t0 (2 * M + 1) := by
  unfold JetRegJ
  by_cases hjo : j % 2 = 0
  · set rect : Set (ℝ × ℝ) := Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0 with hrect
    have hg : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => C.muS (j / 2) (μ, p.2) p.1)
        (Icc (-(SI.w + SI.ρ)) (SI.w + SI.ρ) ×ˢ Icc (-t0) t0) := SI.muS_reg μ hμ (j / 2) (by omega)
    have hband : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Fz.bandHi (μ, p.2)) rect :=
      (SI.bandHi_reg μ hμ).comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    have hφ : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => (Fz.bandHi (μ, p.2) - p.1, p.2)) rect :=
      (hband.sub contDiff_fst.contDiffOn).prodMk contDiff_snd.contDiffOn
    have hmaps : MapsTo (fun p : ℝ × ℝ => (Fz.bandHi (μ, p.2) - p.1, p.2)) rect
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

/-- The core of `softSigma_rule`: from the labelled rule at one eigenvalue (label `kk`, soft coordinate `x`) to the phase sum.  The terms `h^{2s} mu_{2s}`, `2s > M`, that the label carries are
bounded by `Cmu h^{M+1}` (`muS_bd`). -/
lemma softSigma_rule_core (hq : M ≤ q) {μ : Par} {h : ℝ} (hpos : 0 < h) (h1 : h ≤ 1) (hmem : (μ, h) ∈ P) {Cc kk x : ℝ}
    (hαδ : |x - Fz.bandHi (μ, h)| ≤ C.δ0)
    (hlk : |(C.muS 0 (μ, h) (Fz.bandHi (μ, h) - x) + ∑ s ∈ Finset.Icc 1 (q / 2), h ^ (2 * s) * C.muS s (μ, h) (Fz.bandHi (μ, h) - x))
      - (kk + 1 / 2) * h| ≤ Cc * h ^ (M + 1)) :
    |∑ j ∈ range (M + 1), h ^ j * softSigma C μ j x h - Real.pi * h * (kk + 1 / 2)|
      ≤ Real.pi * (|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu) * h ^ (M + 1) := by
  set b := Fz.bandHi (μ, h) with hbdef
  set f : ℕ → ℝ := fun s => C.muS s (μ, h) (b - x) with hf
  have hA : ∑ j ∈ range (M + 1), h ^ j * softSigma C μ j x h = Real.pi * ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s := by
    rw [← softSigma_sum f h M]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [softSigma, hf, hbdef]
  have hL : C.muS 0 (μ, h) (b - x) + ∑ s ∈ Icc 1 (q / 2), h ^ (2 * s) * C.muS s (μ, h) (b - x)
      = ∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s := label_sum f h (q / 2)
  have hsplit : ∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s =
      ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s + ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s :=
    (Finset.sum_range_add_sum_Ico _ (by omega : M / 2 + 1 ≤ q / 2 + 1)).symm
  have htail : |∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s| ≤ ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu * h ^ (M + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), |h ^ (2 * s) * f s| ≤ C.Cmu * h ^ (M + 1) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      have hbd := C.muS_bd s (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (μ, h) hmem (b - x) (by rw [abs_sub_comm]; exact hαδ)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hpos.le _)]
      calc h ^ (2 * s) * |f s| ≤ h ^ (M + 1) * C.Cmu :=
            mul_le_mul (pow_le_pow_of_le_one hpos.le h1 (by omega)) hbd (abs_nonneg _) (by positivity)
        _ = C.Cmu * h ^ (M + 1) := by ring
    calc ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), |h ^ (2 * s) * f s|
        ≤ ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), C.Cmu * h ^ (M + 1) := Finset.sum_le_sum hterm
      _ = ((q / 2 + 1 - (M / 2 + 1) : ℕ) : ℝ) * (C.Cmu * h ^ (M + 1)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ((q / 2 : ℕ) + 1 : ℝ) * (C.Cmu * h ^ (M + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg C.consts_pos2.1 (by positivity))
          have : (q / 2 + 1 - (M / 2 + 1) : ℕ) ≤ q / 2 + 1 := by omega
          exact_mod_cast this
      _ = _ := by ring
  have hlk' : |∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h| ≤ Cc * h ^ (M + 1) := by
    rw [← hL]; exact hlk
  have hmain : |∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h| ≤
      (|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu) * h ^ (M + 1) := by
    have e : ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h =
        (∑ s ∈ range (q / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h) -
          ∑ s ∈ Finset.Ico (M / 2 + 1) (q / 2 + 1), h ^ (2 * s) * f s := by
      rw [hsplit]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : Cc * h ^ (M + 1) ≤ |Cc| * h ^ (M + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith [hlk', htail]
  rw [hA]
  have e2 : Real.pi * ∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - Real.pi * h * (kk + 1 / 2) =
      Real.pi * (∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h) := by ring
  rw [e2, abs_mul, abs_of_pos Real.pi_pos]
  calc Real.pi * |∑ s ∈ range (M / 2 + 1), h ^ (2 * s) * f s - (kk + 1 / 2) * h|
      ≤ Real.pi * ((|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu) * h ^ (M + 1)) := mul_le_mul_of_nonneg_left hmain Real.pi_pos.le
    _ = _ := by ring

end Generic

/-! ### The reflection `(X, t) -> (-X, t)` as a linear isometry of `R x R` -/

/-- The reflection `(X, t) -> (-X, t)`, a linear isometry equivalence of `R x R` (sup norm). -/
def reflX : (ℝ × ℝ) ≃ₗᵢ[ℝ] (ℝ × ℝ) where
  toLinearEquiv :=
    { toFun := fun p => (-p.1, p.2)
      invFun := fun p => (-p.1, p.2)
      map_add' := fun p r => by ext <;> simp <;> ring
      map_smul' := fun c p => by ext <;> simp
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  norm_map' := fun p => by simp [Prod.norm_def]

@[simp] lemma reflX_apply (p : ℝ × ℝ) : reflX p = (-p.1, p.2) := rfl

lemma reflX_preimage (a b t0 : ℝ) :
    reflX ⁻¹' (Icc a b ×ˢ Icc (-t0) t0) = Icc (-b) (-a) ×ˢ Icc (-t0) t0 := by
  ext p
  simp only [Set.mem_preimage, reflX_apply, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-! ### The action of the gauge family -/

section Action

/-- **`S_0` of the gauge family**: `S_0(negFamily G, X') = pi L - S_0(G, -X')` (`arccos(-w) = pi - arccos w`), under integrability of the integrand of `S_0(G, -X')`. -/
lemma actionS0_neg (G : SymbolFamily Par) (μ : Par) (X' : ℝ)
    (hint : IntervalIntegrable (fun u => Real.arccos ((-X' - G.B 0 μ u) / (2 * Real.sqrt (E0 G.L (G.G 0 μ) u)))) MeasureTheory.volume 0 G.L) :
    actionS0 (negFamily G) μ X' = Real.pi * G.L - actionS0 G μ (-X') := by
  unfold actionS0
  have hpt : ∀ u : ℝ, Real.arccos ((X' - (negFamily G).B 0 μ u) / (2 * Real.sqrt (E0 (negFamily G).L ((negFamily G).G 0 μ) u))) =
      Real.pi - Real.arccos ((-X' - G.B 0 μ u) / (2 * Real.sqrt (E0 G.L (G.G 0 μ) u))) := by
    intro u
    rw [← Real.arccos_neg]
    congr 1
    simp only [negFamily]
    ring
  have e1 : ∫ u in (0 : ℝ)..(negFamily G).L, Real.arccos ((X' - (negFamily G).B 0 μ u) / (2 * Real.sqrt (E0 (negFamily G).L ((negFamily G).G 0 μ) u))) =
      ∫ u in (0 : ℝ)..G.L, (Real.pi - Real.arccos ((-X' - G.B 0 μ u) / (2 * Real.sqrt (E0 G.L (G.G 0 μ) u)))) :=
    intervalIntegral.integral_congr (fun u _ => hpt u)
  rw [e1, intervalIntegral.integral_sub intervalIntegrable_const hint]
  simp [mul_comm]

/-- The `S_0` integrand of a family under `(H1)`--`(H3)` and `(D_0)` is interval integrable (`intervalIntegrable_arccos_action`). -/
lemma actionS0_integrable (T : SymbolFamily Par) (K : Set Par) (hH : HypOn T K) (hD : DM T K 0) {μ : Par} (hμ : μ ∈ K) (X : ℝ) :
    IntervalIntegrable (fun u => Real.arccos ((X - T.B 0 μ u) / (2 * Real.sqrt (E0 T.L (T.G 0 μ) u)))) MeasureTheory.volume 0 T.L := by
  obtain ⟨g, hg⟩ := hH
  have hyp := hg μ hμ
  have hr := hD.reg 0 (Nat.zero_le _)
  have h2 : (2 : WithTop ℕ∞) ≤ ((regBudget 0 - 10 * (0 / 2) : ℕ) : WithTop ℕ∞) := by
    have : (2 : ℕ) ≤ regBudget 0 - 10 * (0 / 2) := by unfold regBudget; omega
    exact_mod_cast this
  have hG2 : ContDiffOn ℝ 2 (T.G 0 μ) (Icc 0 T.L) := (hr.1.1 μ hμ).of_le h2
  have hB2 : ContDiffOn ℝ 2 (T.B 0 μ) (Icc 0 T.L) := (hr.2.1 μ hμ).of_le h2
  exact intervalIntegrable_arccos_action T.L_pos hyp hG2 hB2 X

/-- The action at `t = 0` of the gauge family of the frozen family is that of the gauge family of `T`. -/
lemma actionS0_negFrozen_zero (T : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (X : ℝ) :
    actionS0 (negFamily (frozenFamily T Kidx)) (μ, 0) X = actionS0 (negFamily T) μ X := by
  unfold actionS0
  simp [frozenFamily, negFamily]

/-- `S_0(negFamily T, X') = pi L - S_0(T, -X')` under `(H1)`--`(H3)`, `(D_0)`. -/
lemma actionS0_neg_of_hyp (T : SymbolFamily Par) (K : Set Par) (hH : HypOn T K) (hD : DM T K 0) {μ : Par} (hμ : μ ∈ K) (X' : ℝ) :
    actionS0 (negFamily T) μ X' = Real.pi * T.L - actionS0 T μ (-X') :=
  actionS0_neg T μ X' (actionS0_integrable T K hH hD hμ (-X'))

/-- The band ends of the frozen family at `t = 0`: `X_s^-(frozen, (mu, 0)) = X_s^-(T, mu)`. -/
lemma frozen_bandLo_zero (T : SymbolFamily Par) (Kidx : ℕ) (μ : Par) : (frozenFamily T Kidx).bandLo (μ, 0) = T.bandLo μ := by
  rw [frozen_bandLo]
  unfold SymbolFamily.bandLo
  simp

/-- `X_s^+` of the gauge chart family at `t = 0` is `-X_s^-(T)`. -/
lemma negFrozen_bandHi_zero (T : SymbolFamily Par) (Kidx : ℕ) (μ : Par) :
    (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) = -T.bandLo μ := by
  rw [negFrozen_bandHi, frozen_bandLo_zero]

end Action

/-! ### The lower phase -/

section Lower

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ} {M : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart Fz P m q U V Lm}

/-- **`Sigma_{-,j}(mu; X, t) = [j = 0] pi L - Sigma~_{+,j}(mu; -X, t)`**: the phase coefficients of the lower soft edge (`Sigma_- = pi L - Sigma~_+(-X, t, h)`, `(N + 1) h = L`). -/
def softLoSigma (L : ℝ) (C : SoftEdgeChart Fz P m q U V Lm) (μ : Par) (j : ℕ) (X t : ℝ) : ℝ :=
  (if j = 0 then Real.pi * L else 0) - softSigma C μ j (-X) t

/-- `Sigma_{-,j} in C^{2M+1}` on `I_- x [-t0, t0]`. -/
lemma softLoSigma_reg (L : ℝ) (SI : SoftPhaseInputs Fz P K t0 M C) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) :
    JetRegJ (softLoSigma L C μ j) (Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w)) t0 (2 * M + 1) := by
  have h := softSigmaG_reg SI hμ hj
  unfold JetRegJ at h ⊢
  have hr : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => softSigma C μ j (-p.1) p.2)
      (Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0) := by
    have hsub := h.comp (reflX.toContinuousLinearEquiv : ℝ × ℝ →L[ℝ] ℝ × ℝ).contDiff.contDiffOn
      (s := Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0)
      (t := Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0) (fun p hp => by
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, reflX_apply, Set.mem_prod, Set.mem_Icc] at hp ⊢
        exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2⟩)
    refine hsub.congr (fun p _ => ?_)
    simp
  have := contDiffOn_const (c := (if j = 0 then Real.pi * L else 0)).sub hr
  exact this.congr (fun p _ => by simp [softLoSigma])

/-- The uniform `C^{2M+1}` bound of the lower phase coefficients, from that of the upper ones (`reflX` is an isometry; the constant `pi L` only enters in order `0`). -/
lemma softLoSigma_bdd (L : ℝ) (SI : SoftPhaseInputs Fz P K t0 M C) (ht0 : 0 < t0) :
    ∃ Cb : ℝ, ∀ μ ∈ K, ∀ j ≤ M, ∀ i ≤ 2 * M + 1,
      ∀ p ∈ Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0,
        ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => softLoSigma L C μ j q.1 q.2)
          (Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0) p‖ ≤ Cb := by
  obtain ⟨Cb, hCb⟩ := SI.Sigma_bdd
  refine ⟨Cb + |Real.pi * L|, fun μ hμ j hj i hi p hp => ?_⟩
  set S' : Set (ℝ × ℝ) := Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0 with hS'
  set S : Set (ℝ × ℝ) := Icc (-Fz.bandHi (μ, 0) - SI.w) (-Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0 with hS
  have hpre : reflX ⁻¹' S' = S := by
    rw [hS', hS, reflX_preimage]
    congr 2 <;> ring
  have hUD : UniqueDiffOn ℝ S' := UniqueDiffOn.prod (uniqueDiffOn_Icc (by linarith [SI.w_pos])) (uniqueDiffOn_Icc (by linarith))
  have hUD' : UniqueDiffOn ℝ S := by
    rw [← hpre]
    exact reflX.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.2 hUD
  have hpS : reflX p ∈ S' := by
    rw [← Set.mem_preimage, hpre]; exact hp
  have hnorm := reflX.norm_iteratedFDerivWithin_comp_right (fun q : ℝ × ℝ => softSigma C μ j q.1 q.2) hUD hpS i
  rw [hpre] at hnorm
  have hbd : ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => softSigma C μ j q.1 q.2) S' (reflX p)‖ ≤ Cb := hCb μ hμ j hj i hi _ hpS
  have hcd : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) ((fun q : ℝ × ℝ => softSigma C μ j q.1 q.2) ∘ ⇑reflX) S := by
    rw [← hpre]
    exact (reflX.toContinuousLinearEquiv.contDiffOn_comp_iff (f := fun q : ℝ × ℝ => softSigma C μ j q.1 q.2)
      (s := S')).2 (softSigmaG_reg SI hμ hj)
  have hfun : (fun q : ℝ × ℝ => softLoSigma L C μ j q.1 q.2) =
      (fun _ => (if j = 0 then Real.pi * L else 0)) - ((fun q : ℝ × ℝ => softSigma C μ j q.1 q.2) ∘ ⇑reflX) := by
    funext q
    simp [softLoSigma]
  have hc : |(if j = 0 then Real.pi * L else 0)| ≤ |Real.pi * L| := by
    split_ifs
    · exact le_rfl
    · rw [abs_zero]; exact abs_nonneg _
  rw [hfun]
  cases i with
  | zero =>
    rw [norm_iteratedFDerivWithin_zero]
    have hb0 : |softSigma C μ j (-p.1) p.2| ≤ Cb := by
      have := hbd
      rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
      simpa using this
    simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs]
    calc |(if j = 0 then Real.pi * L else 0) - softSigma C μ j (reflX p).1 (reflX p).2|
        ≤ |(if j = 0 then Real.pi * L else 0)| + |softSigma C μ j (reflX p).1 (reflX p).2| := abs_sub _ _
      _ ≤ Cb + |Real.pi * L| := by simp only [reflX_apply] at hb0 ⊢; linarith
  | succ i' =>
    have hcd1 : ContDiffWithinAt ℝ ((i' + 1 : ℕ) : WithTop ℕ∞) ((fun q : ℝ × ℝ => softSigma C μ j q.1 q.2) ∘ ⇑reflX) S p :=
      (hcd p hp).of_le (by exact_mod_cast hi)
    rw [iteratedFDerivWithin_sub_apply (contDiffWithinAt_const) hcd1 hUD' hp, iteratedFDerivWithin_succ_const, Pi.zero_apply, zero_sub, norm_neg, hnorm]
    linarith [abs_nonneg (Real.pi * L)]

end Lower

/-! ### The lower soft window -/

section LowerWindow

variable {T : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M Kidx : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart (negFamily (frozenFamily T Kidx)) (paramSet K t0) m q U V Lm}

/-- **The labelled soft rule at the lower edge** (`PropThaW2` (3) for the chart `softLoL` of the family `negFamily (frozenFamily T Kidx)` at `p = (mu, step N)`, in the form of `eq:smo-BSr2`): for every eigenvalue `X'_i`
of `-D J_h D` (the matrix of the chart family at `(mu, h)`, `negFrozen_jacobiMat_at_step`) within `delta_0` of `X_s^+(mu, h)` of the gauge family (`= -X_s^-(mu, h)`),
`mu_0(alpha) + sum_{s=1}^{q/2} h^{2s} mu_{2s}(alpha) = (i + 1/2) h + O(h^{M+1})` with `alpha = X_s^+(negFamily; mu, h) - X'_i`, `i` the index from the top of `-D J_h D`.  The lower analogue of `SoftLabels`;
an input from `PropThaW2` (and Step 0 for the gauge family), not proved here. -/
def SoftLabelsLo (T : SymbolFamily Par) (Kidx : ℕ) (K : Set Par) (M : ℕ) {P : Set (Par × ℝ)} {m q : ℕ}
    {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ} (C : SoftEdgeChart (negFamily (frozenFamily T Kidx)) P m q U V Lm) : Prop :=
  ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      IsEigenSystem ((negFamily (frozenFamily T Kidx)).jacobiMat (μ, T.step N) N) Xs Um →
      ∀ i : Fin (N + 1), |Xs i - (negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N)| ≤ C.δ0 →
        |(C.muS 0 (μ, T.step N) ((negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N) - Xs i) +
            ∑ s ∈ Finset.Icc 1 (q / 2), T.step N ^ (2 * s) * C.muS s (μ, T.step N) ((negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N) - Xs i))
          - ((i : ℕ) + 1 / 2) * T.step N| ≤ Cc * T.step N ^ (M + 1)

/-- `Sigma_{-,0}(X, 0) = S_0(X)` on `I_- cap [X_s^-, X_s^+]`: from the chart's `mu0_S0` for the gauge family at `-X`, `actionS0_neg` and `arccos(-w) = pi - arccos w`. -/
lemma softLoSigma_zero (SI : SoftPhaseInputs (negFamily (frozenFamily T Kidx)) (paramSet K t0) K t0 M C) (ht0 : 0 < t0)
    (hH : HypOn T K) (hD : DM T K 0) {μ : Par} (hμ : μ ∈ K) {X : ℝ}
    (hX : X ∈ Icc (T.bandLo μ - SI.w) (T.bandLo μ + SI.w)) (hband : X ∈ Icc (T.bandLo μ) (T.bandHi μ)) :
    softLoSigma T.L C μ 0 X 0 = actionS0 T μ X := by
  have hb := negFrozen_bandHi_zero T Kidx μ
  have hmem := mem_paramSet_zero hμ ht0
  have hle : -X ≤ (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) := by rw [hb]; linarith [hband.1]
  have hδ : (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) - (-X) ≤ C.δ0 := by
    have := SI.window_in_chart
    have := SI.ρ_nonneg
    rw [hb]; linarith [hX.2]
  have h := C.mu0_S0 (μ, 0) hmem (-X) hle hδ
  have hS : Real.pi * C.muS 0 (μ, 0) ((negFamily (frozenFamily T Kidx)).bandHi (μ, 0) - -X) =
      actionS0 (negFamily (frozenFamily T Kidx)) (μ, 0) (-X) := h
  have e : softSigma C μ 0 (-X) 0 = Real.pi * C.muS 0 (μ, 0) ((negFamily (frozenFamily T Kidx)).bandHi (μ, 0) - -X) := by
    simp [softSigma]
  unfold softLoSigma
  rw [if_pos rfl, e, hS, actionS0_negFrozen_zero, actionS0_neg_of_hyp T K hH hD hμ, neg_neg]
  ring

/-- The slope `partial_X Sigma_{-,0}(X, 0) <= -pi cmu0` on the open window, from the chart's `mu0_slope`. -/
lemma softLoSigma_slope (SI : SoftPhaseInputs (negFamily (frozenFamily T Kidx)) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo (T.bandLo μ - SI.w) (T.bandLo μ + SI.w),
      deriv (fun X' => softLoSigma T.L C μ 0 X' 0) X ≤ -c := by
  refine ⟨Real.pi * C.cmu0, mul_pos Real.pi_pos C.consts_pos5.1, fun μ hμ X hX => ?_⟩
  have hμ0 := mem_paramSet_zero hμ ht0
  have hb := negFrozen_bandHi_zero T Kidx μ
  have hd : Differentiable ℝ (C.muS 0 (μ, 0)) := (C.mu0_deriv (μ, 0) hμ0).1.differentiable (by norm_num)
  have h1 : HasDerivAt (fun X' : ℝ => (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) + X') 1 X := by
    simpa using (hasDerivAt_id X).const_add ((negFamily (frozenFamily T Kidx)).bandHi (μ, 0))
  have h2 := (hd ((negFamily (frozenFamily T Kidx)).bandHi (μ, 0) + X)).hasDerivAt.comp X h1
  have h3 := (h2.const_mul Real.pi).const_sub (Real.pi * T.L)
  have key : (fun X' => softLoSigma T.L C μ 0 X' 0) =
      fun X' => Real.pi * T.L - Real.pi * (C.muS 0 (μ, 0) ∘ fun X'' : ℝ => (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) + X'') X' := by
    funext X'; simp [softLoSigma, softSigma]
  rw [key, h3.deriv]
  have hα : |(negFamily (frozenFamily T Kidx)).bandHi (μ, 0) + X| ≤ C.δ0 := by
    have := SI.window_in_chart
    have := SI.ρ_nonneg
    rw [abs_le, hb]
    constructor <;> linarith [hX.1, hX.2, SI.w_pos]
  have hs := (C.mu0_slope (μ, 0) hμ0 _ hα).1
  nlinarith [Real.pi_pos]

/-- **The labelled rule `eq:smo-BSr2` on `I_-`**, from `SoftLabelsLo` through the eigen-system reversal (`IsEigenSystem.neg_frozen`): `k` is the index of `X_k` from the top of `J_h`, `N - k` that of `-X_k` for `-D J_h D`. -/
lemma softLoSigma_rule (SI : SoftPhaseInputs (negFamily (frozenFamily T Kidx)) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) (hq : M ≤ q)
    (hlab : SoftLabelsLo T Kidx K M C) :
    ∃ Cr h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (T.jacobiMat μ N) Xs Um →
        ∀ k : Fin (N + 1), Xs k ∈ Icc (T.bandLo μ - SI.w) (T.bandLo μ + SI.w) →
          |∑ j ∈ range (M + 1), T.step N ^ j * softLoSigma T.L C μ j (Xs k) (T.step N) - Real.pi * T.step N * (((k : ℕ) : ℝ) + 1 / 2)|
            ≤ Cr * T.step N ^ (M + 1) := by
  obtain ⟨Cc, h0, hh0, hl⟩ := hlab
  refine ⟨Real.pi * (|Cc| + ((q / 2 : ℕ) + 1 : ℝ) * C.Cmu), min (min h0 t0) 1, lt_min (lt_min hh0 ht0) one_pos, ?_⟩
  intro μ hμ N hN Xs Um hE k hk
  have hpos : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
  have hN0 : T.step N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hNt : T.step N ≤ t0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN1 : T.step N ≤ 1 := hN.trans (min_le_right _ _)
  have hb0 := negFrozen_bandHi_zero T Kidx μ
  have hcl := SI.bandHi_close μ hμ (T.step N) ⟨by linarith, hNt⟩
  have hE' := hE.neg_frozen (Kidx := Kidx)
  have hαδ : |negX Xs (Fin.rev k) - (negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N)| ≤ C.δ0 := by
    have h1 := SI.window_in_chart
    have h2 := abs_le.mp hcl
    have h3 : -SI.w ≤ Xs k - T.bandLo μ ∧ Xs k - T.bandLo μ ≤ SI.w := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    rw [negX_rev, abs_le]
    rw [hb0] at h2
    constructor <;> linarith [h3.1, h3.2, h2.1, h2.2]
  have hlk := hl μ hμ N hN0 (negX Xs) (negU Um) hE' (Fin.rev k) hαδ
  simp only [negX_rev] at hlk
  have hmem : (μ, T.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have hαδ' : |-Xs k - (negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N)| ≤ C.δ0 := by
    rw [negX_rev] at hαδ; exact hαδ
  have hcore := softSigma_rule_core hq hpos hN1 hmem hαδ' hlk
  -- the constant and the reversal of the label
  have hsum : ∑ j ∈ range (M + 1), T.step N ^ j * softLoSigma T.L C μ j (Xs k) (T.step N) =
      Real.pi * T.L - ∑ j ∈ range (M + 1), T.step N ^ j * softSigma C μ j (-Xs k) (T.step N) := by
    unfold softLoSigma
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  have hL : T.L = ((N : ℝ) + 1) * T.step N := by
    have := step_mul_succ T N
    linarith
  have hrev : ((Fin.rev k : ℕ) : ℝ) = (N : ℝ) - ((k : ℕ) : ℝ) := by
    have h1 : (Fin.rev k : ℕ) + (k : ℕ) = N := by
      have := k.isLt
      simp only [Fin.val_rev]; omega
    have h2 := congrArg (Nat.cast (R := ℝ)) h1
    push_cast at h2
    linarith
  rw [hsum]
  have e : Real.pi * T.L - ∑ j ∈ range (M + 1), T.step N ^ j * softSigma C μ j (-Xs k) (T.step N) -
      Real.pi * T.step N * (((k : ℕ) : ℝ) + 1 / 2) =
      -(∑ j ∈ range (M + 1), T.step N ^ j * softSigma C μ j (-Xs k) (T.step N) -
        Real.pi * T.step N * (((Fin.rev k : ℕ) : ℝ) + 1 / 2)) := by
    rw [hL, hrev]; ring
  rw [e, abs_neg]
  exact hcore

/-- **The lower soft window as a `WindowPhase`** (`thm:smo-BSr`, lower edge; the `WS false` of `thmSmoSpec`): on `[X_s^-(mu) - w, X_s^-(mu) + w]`, from `SoftPhaseInputs` of the chart `softLoL`, the labels `SoftLabelsLo`
and the paper's hypotheses `(H1)`--`(H3)`, `(D_0)` (integrability of the `S_0` integrand). -/
def softLoWindow (SI : SoftPhaseInputs (negFamily (frozenFamily T Kidx)) (paramSet K t0) K t0 M C) (ht0 : 0 < t0) (hq : M ≤ q)
    (hH : HypOn T K) (hD : DM T K 0) (hlab : SoftLabelsLo T Kidx K M C) :
    WindowPhase T K t0 M (fun μ => T.bandLo μ - SI.w) (fun μ => T.bandLo μ + SI.w) where
  Sigma := fun μ j X t => softLoSigma T.L C μ j X t
  Sigma_reg := fun μ hμ j hj => by
    have e : -(negFamily (frozenFamily T Kidx)).bandHi (μ, 0) = T.bandLo μ := by rw [negFrozen_bandHi_zero, neg_neg]
    have := softLoSigma_reg T.L SI hμ hj
    rw [e] at this
    exact this
  Sigma_bdd := by
    obtain ⟨Cb, hCb⟩ := softLoSigma_bdd T.L SI ht0
    refine ⟨Cb, fun μ hμ j hj i hi p hp => ?_⟩
    have e : -(negFamily (frozenFamily T Kidx)).bandHi (μ, 0) = T.bandLo μ := by rw [negFrozen_bandHi_zero, neg_neg]
    have := hCb μ hμ j hj i hi p (by rw [e]; exact hp)
    rw [e] at this
    exact this
  Sigma_zero := fun μ hμ X hX hb => softLoSigma_zero SI ht0 hH hD hμ hX hb
  slope := softLoSigma_slope SI ht0
  rule := softLoSigma_rule SI ht0 hq hlab

end LowerWindow

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoWindow

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_rule

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_zero

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_slope

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_reg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_bdd

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_neg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_rule_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_rule_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigmaG_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigmaG_reg

end FormalResearch.JacobiEigenvectors.TheoremA
