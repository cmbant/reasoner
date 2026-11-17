module

public import FormalResearch.Special.LatticeOffsetGamma
public import FormalResearch.Special.LatticeTailC
public import FormalResearch.Special.TraceCoreDecomp
public import FormalResearch.Special.TraceCoreAsymp

/-!
# `thm:tracecore`: trace functionals over a calibrated phase lattice (Gamma phase)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `thm:tracecore` (with `lem:latticesum` (o), (ii),
`lem:traceperturb`, `def:admissible`).  Setting of `latticesum_gamma` (`ϰ = nc`, `b`, `c_*`, `L^{c_*/2} ≤ X ≤ L^{c_*}`,
`F_±`, `Θ` with `|Θ - G| ≤ L^{-b}`, `S = {x_r}`), `δ, κ > 0`, `0 < b₁ < min(b, ϰ min(δ,¼))` (stated as `b₁ < b`,
`b₁ < ϰ min(δ,¼)`).  Let `C` be Hermitian with `0 ≤ C ≤ 1` on a finite index set, `U` orthonormal columns indexed by
the lattice `S` (the paper's `u_r`; `Uᴴ U = 1`), `λ_r = ⟨u_r, C u_r⟩` (`blockLam`), `D`, `C'` as in `TraceBlock`, and
`a > 0`, `σ ∈ (0,1]`, `M ≥ 0`.  Suppose

* (TC) `X ε_λ + ‖C - D - C'‖₁ + ε_op ≤ L^{-a}` where `ε_λ ≥ max_r |λ_r - ν(2πx_r)|` and `ε_op ≥ μ(1-μ)` for every
  eigenvalue `μ` of `C'` (the eigenvalue form of `‖C'(1-C')‖ ≤ ε_op`: for the positive semidefinite
  `C'(1-C')` its operator norm is its largest eigenvalue `max μ(1-μ)`);
* (FM_σ) `∑_j (μ_j(1-μ_j))^{σ/2} ≤ M log L` over the eigenvalues `μ_j` of `C` (`Tr[C(1-C)]^{σ/2} ≤ M log L`).

Then for every `(σ,δ,κ)`-admissible `h` with constant `C_h` and all `L ≥ L₀`,
`|Tr h(C) - ∫_ℝ h(ν(2πs)) [ℓ_Σ - ϰ Re ψ(½+is)]/π ds| ≤ C L^{-b_h}`, `b_h = min(σ a/3, b₁)`; the density
`[ℓ_Σ - ϰ Re ψ(½+is)]/π` is `gdens nc ℓ_Σ s`.  `C, L₀` depend only on `nc, b, c_*, b₁, δ, κ, F_±, σ, a, M, C_h`.

Proof (as in the paper): `tracecore_decomp` (block form, `traceperturb` via Lidskii, calibration, small occupations),
the level count (o) and the rate-`πσ` tail (`sum_exp_rate_le`) for `∑ e^{-πσ|x_r|} ≤ C ϰ log L`, and
`latticesum_gamma` (ii) applied to `s ↦ h(ν(2πs))`.

Not formalised / differences: the Gamma-function identification of the phase (`argGammaHalf`); the operator norm in
(TC) is replaced by its eigenvalue form (equivalent); the smooth cutoff `χ₀` by a piecewise linear one, and
`ε_ρ = ρ^{σ/2}(1+|log ρ|)` by `K_ρ ∼ ρ^{5σ/12}` (all that the exponent `b_h` needs); admissibility (a) is
used in the form of `def:admissible`.  The case distinctions of the paper's `O(L^{-σ a/2} log² L)` are absorbed into
the exponent `σ a/3`.
-/

@[expose] public section

universe u

namespace FormalResearch.Special.TraceCore

open Matrix FormalResearch.MatrixAnalysis FormalResearch.Special.Lattice Set MeasureTheory
open scoped ComplexOrder MatrixOrder

/-- **`thm:tracecore`** for the Gamma phase. -/
theorem tracecore_gamma (nc : ℕ) (hnc : 1 ≤ nc) {b cs b1 Fm Fp δ κ σ a Mfm Ch : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hδ : 0 < δ) (hκ : 0 < κ) (hb1 : 0 < b1)
    (hb1b : b1 < b) (hb1δ : b1 < nc * min δ (1 / 4)) (hFm : 0 < Fm) (hFmp : Fm ≤ Fp)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 0 < a) (hM : 0 ≤ Mfm) (hCh : 0 ≤ Ch) :
    ∃ K0 L0 : ℝ, 0 < K0 ∧ 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      ∀ {h : ℝ → ℂ}, Admissible σ δ κ Ch h →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℂ) (hC : C.IsHermitian),
        C.PosSemidef → (1 - C).PosSemidef →
        ∀ (U : Matrix ι S ℂ), Uᴴ * U = 1 →
        ∀ epl epo : ℝ, 0 ≤ epl → 0 ≤ epo → (∀ x : S, |blockLam U C x - nuR (2 * Real.pi * x)| ≤ epl) →
        (∀ i, (blockC'_isHermitian hC U).eigenvalues i * (1 - (blockC'_isHermitian hC U).eigenvalues i) ≤ epo) →
        X * epl + tnorm (C - (blockD U (blockLam U C) + blockC' U C)) + epo ≤ L ^ (-a) →
        ∑ i, ddf (hC.eigenvalues i) ^ (σ / 2) ≤ Mfm * Real.log L →
        ‖traceFn h hC - ∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤
          K0 * L ^ (-min (σ * a / 3) b1) := by
  have hncpos : (0 : ℝ) < nc := by exact_mod_cast hnc
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  have hpi := Real.pi_pos
  obtain ⟨Cl, Ll, hCl, hLl, Hl⟩ := latticesum_gamma nc hnc hb hcs0 hcs hδ hκ hb1 hb1b hb1δ hFm hFmp
  -- rate-`πσ` tail constant
  have hγ : 0 < Real.pi * σ := by positivity
  set R : ℝ := 2 * ((2 * nc / Real.pi + 2) / (1 - Real.exp (-(Real.pi * σ)))) with hR
  have hden : 0 < 1 - Real.exp (-(Real.pi * σ)) := by
    have : Real.exp (-(Real.pi * σ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨C1, hC1, hE1⟩ := asym_E1 (σ := σ) (a := a) (Ch := Ch) (Q := Mfm + R) hσ ha hCh (by positivity)
  obtain ⟨C2, hC2, hE2⟩ := asym_E2 (σ := σ) (a := a) (Ch := Ch) (Q := 4 * nc) hσ hσ1 ha hCh (by positivity)
  set Λ : ℝ := max 1 (Real.log 16 / a) with hΛ
  refine ⟨C1 + C2 + Cl * Ch + 1, max Ll (Real.exp Λ + 1), by positivity,
    lt_of_lt_of_le hLl (le_max_left _ _), ?_⟩
  intro L hLL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS h H ι _ _ C hC hC0 hC1' U hU epl epo hepl hepo0 hlam hepo hTC hFM
  have hLLl : Ll ≤ L := (le_max_left _ _).trans hLL
  have hLΛ : Real.exp Λ + 1 ≤ L := (le_max_right _ _).trans hLL
  have hL1 : 1 < L := by linarith [Real.exp_pos Λ]
  have hL0 : 0 < L := by linarith
  have hlogL : Λ ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 (by linarith)
  have hlog1 : 1 ≤ Real.log L := le_trans (le_max_left _ _) hlogL
  have hLa16 : 16 ≤ L ^ a := by
    have h1 : Real.log 16 / a ≤ Real.log L := le_trans (le_max_right _ _) hlogL
    have h2 : Real.log 16 ≤ Real.log L * a := by
      have := (div_le_iff₀ ha).1 h1; linarith
    rw [Real.rpow_def_of_pos hL0]
    have : (16 : ℝ) = Real.exp (Real.log 16) := (Real.exp_log (by norm_num)).symm
    rw [this]; exact Real.exp_le_exp.2 h2
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow hL1.le (by positivity)) hX
  have hXpos : 0 < X := by linarith
  have hle : -X ≤ X := by linarith
  have hLna : 0 < L ^ (-a) := Real.rpow_pos_of_pos hL0 _
  have hLna16 : L ^ (-a) ≤ 1 / 16 := by
    rw [Real.rpow_neg hL0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hLa16
  -- lattice facts (o) and (ii)
  obtain ⟨⟨hcount, -⟩, hsum⟩ := Hl L hLLl F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hmem : ∀ x ∈ S, x ∈ Icc (-X) X := fun x hx => ((hS x).mp hx).1
  have hcard : (S.card : ℝ) ≤ 4 * nc * X * Real.log L := by
    have h0 := hcount (-X) X le_rfl hle le_rfl
    rw [Finset.filter_true_of_mem hmem] at h0
    exact card_le_four hncr hX1 hlog1 h0
  -- TC consequences
  have htn := tnorm_nonneg (C - (blockD U (blockLam U C) + blockC' U C))
  have hXel : 0 ≤ X * epl := mul_nonneg hXpos.le hepl
  have hXel' : X * epl ≤ L ^ (-a) := by linarith
  have htn' : tnorm (C - (blockD U (blockLam U C) + blockC' U C)) ≤ L ^ (-a) := by linarith
  have hepoL : epo ≤ L ^ (-a) := by linarith
  -- apply the decomposition
  set ρ : ℝ := 2 * L ^ (-a) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ8 : ρ ≤ 1 / 8 := by rw [hρ]; linarith
  have hdec := tracecore_decomp H hσ hσ1 hCh hρ0 hρ8 hC hC0 hC1' hU (fun x : S => (x : ℝ))
    (epo := epo) hepo (by rw [hρ]; linarith)
  -- sums over the lattice
  have hrate : ∑ x : S, Real.exp (-(Real.pi * σ) * |(x : ℝ)|) ≤ R * Real.log L := by
    rw [Finset.sum_coe_sort S (fun x => Real.exp (-(Real.pi * σ) * |x|))]
    have hc0 : 0 ≤ 2 * (nc : ℝ) * Real.log L / Real.pi := by positivity
    have := sum_exp_rate_le S (c := 2 * nc * Real.log L / Real.pi) (γ := Real.pi * σ) hγ hc0 hmem hcount
    refine this.trans ?_
    rw [hR]
    have hcc : 2 * (nc : ℝ) * Real.log L / Real.pi + 2 ≤ (2 * nc / Real.pi + 2) * Real.log L := by
      have : 2 * (nc : ℝ) * Real.log L / Real.pi = 2 * nc / Real.pi * Real.log L := by ring
      rw [this]; nlinarith
    have := div_le_div_of_nonneg_right hcc hden.le
    calc 2 * ((2 * nc * Real.log L / Real.pi + 2) / (1 - Real.exp (-(Real.pi * σ))))
        ≤ 2 * (((2 * nc / Real.pi + 2) * Real.log L) / (1 - Real.exp (-(Real.pi * σ)))) := by linarith
      _ = 2 * ((2 * nc / Real.pi + 2) / (1 - Real.exp (-(Real.pi * σ)))) * Real.log L := by ring
  have hcalsum : ∑ x : S, |blockLam U C x - nuR (2 * Real.pi * x)| ≤ 4 * nc * Real.log L * L ^ (-a) := by
    calc ∑ x : S, |blockLam U C x - nuR (2 * Real.pi * x)| ≤ ∑ _x : S, epl := Finset.sum_le_sum fun x _ => hlam x
      _ = S.card * epl := by simp
      _ ≤ (4 * nc * X * Real.log L) * epl := mul_le_mul_of_nonneg_right hcard hepl
      _ = 4 * nc * Real.log L * (X * epl) := by ring
      _ ≤ 4 * nc * Real.log L * L ^ (-a) := mul_le_mul_of_nonneg_left hXel' (by positivity)
  -- first part of the error
  have hK0 : 0 ≤ Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) := by positivity
  have hE1' : Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) *
      ((∑ i, ddf (hC.eigenvalues i) ^ (σ / 2)) + ∑ x : S, Real.exp (-(Real.pi * σ) * |(x : ℝ)|)) ≤
      C1 * L ^ (-(σ * a / 3)) := by
    refine le_trans ?_ (hE1 L hL1)
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have := add_mul Mfm R (Real.log L)
    linarith
  have hΛ0 : 0 ≤ Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) + Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ) := by
    positivity
  have hE2' : (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) + Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ)) *
      (tnorm (C - (blockD U (blockLam U C) + blockC' U C)) +
        ∑ x : S, |blockLam U C x - nuR (2 * Real.pi * x)|) ≤ C2 * L ^ (-(σ * a / 3)) := by
    refine le_trans ?_ (hE2 L hL1 hlog1 hLa16)
    refine mul_le_mul_of_nonneg_left ?_ hΛ0
    have e : L ^ (-a) * (1 + 4 * (nc : ℝ) * Real.log L) = L ^ (-a) + 4 * nc * Real.log L * L ^ (-a) := by
      ring
    linarith
  -- lattice part
  obtain ⟨g, hgd, hgv, hgb⟩ := H.ext
  have hlat := hsum g Ch hCh hgd hgb
  have hlat' : ‖∑ x : S, h (nuR (2 * Real.pi * x)) -
      ∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤ Cl * Ch * L ^ (-b1) := by
    have e1 : ∑ x : S, h (nuR (2 * Real.pi * x)) = ∑ x ∈ S, g (x : ℂ) := by
      rw [Finset.sum_coe_sort S (fun x => h (nuR (2 * Real.pi * x)))]
      exact Finset.sum_congr rfl fun x _ => (hgv x).symm
    have e2 : (∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)) =
        ∫ s : ℝ, g (s : ℂ) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [hgv]
    rw [e1, e2]
    exact hlat
  -- conclusion
  have hbh : min (σ * a / 3) b1 ≤ σ * a / 3 := min_le_left _ _
  have hbh1 : min (σ * a / 3) b1 ≤ b1 := min_le_right _ _
  have hpow1 : L ^ (-(σ * a / 3)) ≤ L ^ (-min (σ * a / 3) b1) :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)
  have hpow2 : L ^ (-b1) ≤ L ^ (-min (σ * a / 3) b1) :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)
  have hsplit : ‖traceFn h hC - ∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤
      ‖traceFn h hC - ∑ x : S, h (nuR (2 * Real.pi * x))‖ +
        ‖∑ x : S, h (nuR (2 * Real.pi * x)) -
          ∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ := by
    have := norm_add_le (traceFn h hC - ∑ x : S, h (nuR (2 * Real.pi * x)))
      (∑ x : S, h (nuR (2 * Real.pi * x)) -
        ∫ s : ℝ, h (nuR (2 * Real.pi * s)) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ))
    rwa [sub_add_sub_cancel] at this
  have hP : 0 < L ^ (-min (σ * a / 3) b1) := Real.rpow_pos_of_pos hL0 _
  have hCl0 : 0 ≤ Cl * Ch := by positivity
  calc _ ≤ _ := hsplit
    _ ≤ (C1 * L ^ (-(σ * a / 3)) + C2 * L ^ (-(σ * a / 3))) + Cl * Ch * L ^ (-b1) := by
        have := hdec.trans (add_le_add hE1' hE2')
        linarith
    _ ≤ (C1 * L ^ (-min (σ * a / 3) b1) + C2 * L ^ (-min (σ * a / 3) b1)) +
          Cl * Ch * L ^ (-min (σ * a / 3) b1) := by
        have a1 := mul_le_mul_of_nonneg_left hpow1 hC1.le
        have a2 := mul_le_mul_of_nonneg_left hpow1 hC2.le
        have a3 := mul_le_mul_of_nonneg_left hpow2 hCl0
        linarith
    _ ≤ _ := by
        have : (C1 + C2 + Cl * Ch + 1) * L ^ (-min (σ * a / 3) b1) =
            C1 * L ^ (-min (σ * a / 3) b1) + C2 * L ^ (-min (σ * a / 3) b1) +
              Cl * Ch * L ^ (-min (σ * a / 3) b1) + L ^ (-min (σ * a / 3) b1) := by ring
        linarith

/-- info: 'FormalResearch.Special.TraceCore.tracecore_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracecore_gamma

end FormalResearch.Special.TraceCore
