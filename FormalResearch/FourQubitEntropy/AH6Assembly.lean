import FormalResearch.FourQubitEntropy.AH6Binary
import FormalResearch.FourQubitEntropy.AH6Cubic

/-!
# Assembly of the joint scalar majorant from its ingredients

`lem:seven-joint-scalar-majorant`, proof in `joint_entropy_analytic_proof.tex`.  Everything is a statement about
real functions of `e`; the hypotheses are exactly the ingredients proved elsewhere:

* `hK`: the kernel minorant `k₀ q(e)² ≤ (P(e) - g(e)) L(e)` for `e > 0` (`kmin`);
* `hη`: `η₃ > 0`, and `η₂, η₃` are the Hermite coefficients (`eta2R`, `eta3R`), with the binary minorant
  `phiB_minorant`;
* `hΠ`: the factorisation `R(e) = (e - e₀)² Π(e)` of the degree-twenty polynomial with `Π(e) > 0` for `e ≥ 0`;
* positivity of `L`, `k₀`.

The conclusion is `(f(λ) + f(μ))/2 ≤ H(λ,μ)` for all `λ, μ ≥ 0`, `H(λ,μ) = P(e) + v A(e) + v² B(e)`,
`e = 4(λ+μ)`, `v = 16(λ-μ)²` (`majorant_of_data`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

open Filter Topology

/-- The data of the majorant. -/
structure MajData where
  P : ℝ → ℝ
  q : ℝ → ℝ
  k0 : ℝ
  gam : ℝ
  e0 : ℝ
  A : ℝ → ℝ
  B : ℝ → ℝ
  Pi : ℝ → ℝ

namespace MajData

variable (D : MajData)

noncomputable def L (e : ℝ) : ℝ := 1 + D.gam * (e - D.e0)
noncomputable def U (e : ℝ) : ℝ := 8 * D.k0 * D.q e ^ 2
noncomputable def V (e : ℝ) : ℝ := 1 / 2 + 8 * e * D.A e
noncomputable def W (e : ℝ) : ℝ := eta2R + 8 * e ^ 3 * D.B e

/-- `R = 27η₃²U² + 4eLUW³ + 4η₃e²L²V³ - e²L²V²W² - 18η₃eLUVW`. -/
noncomputable def R (e : ℝ) : ℝ :=
  27 * eta3R ^ 2 * D.U e ^ 2 + 4 * e * D.L e * D.U e * D.W e ^ 3 +
    4 * eta3R * e ^ 2 * D.L e ^ 2 * D.V e ^ 3 - e ^ 2 * D.L e ^ 2 * D.V e ^ 2 * D.W e ^ 2 -
    18 * eta3R * e * D.L e * D.U e * D.V e * D.W e

/-- The cubic `F(e, v)`. -/
noncomputable def F (e v : ℝ) : ℝ :=
  e ^ 5 * D.U e + e ^ 4 * D.L e * D.V e * v + e ^ 2 * D.L e * D.W e * v ^ 2 + eta3R * D.L e * v ^ 3

/-- The polynomial `H(λ, μ)`. -/
noncomputable def H (l m : ℝ) : ℝ :=
  D.P (4 * (l + m)) + 16 * (l - m) ^ 2 * D.A (4 * (l + m)) + (16 * (l - m) ^ 2) ^ 2 * D.B (4 * (l + m))

end MajData

section

variable (D : MajData)

theorem F_nonneg_of_ne (heta : 0 < eta3R) (hk0 : 0 < D.k0) (hL : ∀ e, 0 ≤ e → 0 < D.L e)
    (hR : ∀ e, D.R e = (e - D.e0) ^ 2 * D.Pi e) (hPi : ∀ e, 0 ≤ e → 0 < D.Pi e)
    {e : ℝ} (he : 0 < e) (hne : e ≠ D.e0) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ D.F e v := by
  have hLe := hL e he.le
  have hU : 0 ≤ D.U e := by unfold MajData.U; positivity
  have hdisc : disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e) (e ^ 4 * D.L e * D.V e)
      (e ^ 5 * D.U e) = -(e ^ 10 * D.L e ^ 2 * D.R e) := by
    unfold disc3 MajData.R; ring
  have hRpos : 0 < D.R e := by
    rw [hR e]
    have : 0 < (e - D.e0) ^ 2 := by
      have : e - D.e0 ≠ 0 := sub_ne_zero.2 hne
      positivity
    exact mul_pos this (hPi e he.le)
  have hneg : disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e) (e ^ 4 * D.L e * D.V e)
      (e ^ 5 * D.U e) < 0 := by
    rw [hdisc]
    have : 0 < e ^ 10 * D.L e ^ 2 * D.R e := by positivity
    linarith
  have := cubic_nonneg (mul_pos heta hLe) (by positivity : 0 ≤ e ^ 5 * D.U e) hneg v hv
  unfold MajData.F
  nlinarith [this]

theorem F_nonneg (heta : 0 < eta3R) (hk0 : 0 < D.k0) (hL : ∀ e, 0 ≤ e → 0 < D.L e)
    (hR : ∀ e, D.R e = (e - D.e0) ^ 2 * D.Pi e) (hPi : ∀ e, 0 ≤ e → 0 < D.Pi e)
    (hq : Continuous D.q) (hA : Continuous D.A) (hB : Continuous D.B)
    {e : ℝ} (he : 0 < e) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ D.F e v := by
  by_cases hne : e = D.e0
  · have hcont : Continuous (fun e => D.F e v) := by
      unfold MajData.F MajData.U MajData.L MajData.V MajData.W
      fun_prop
    have hT : Tendsto (fun e => D.F e v) (𝓝[≠] D.e0) (𝓝 (D.F D.e0 v)) :=
      (hcont.tendsto _).mono_left nhdsWithin_le_nhds
    have hpos : 0 < D.e0 := hne ▸ he
    have hev : ∀ᶠ e' in 𝓝[≠] D.e0, 0 ≤ D.F e' v := by
      have h1 : ∀ᶠ e' in 𝓝[≠] D.e0, 0 < e' :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hpos)
      have h2 : ∀ᶠ e' in 𝓝[≠] D.e0, e' ≠ D.e0 := self_mem_nhdsWithin
      filter_upwards [h1, h2] with e' h1' h2'
      exact F_nonneg_of_ne D heta hk0 hL hR hPi h1' h2' hv
    rw [hne]
    exact ge_of_tendsto hT hev
  · exact F_nonneg_of_ne D heta hk0 hL hR hPi he hne hv

/-- **The entropy gap dominates the cubic.** -/
theorem gap_lb (hL : ∀ e, 0 ≤ e → 0 < D.L e)
    (hK : ∀ e : ℝ, 0 < e → D.k0 * D.q e ^ 2 ≤ (D.P e - Real.negMulLog (e / 8)) * D.L e)
    {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    D.F (4 * (l + m)) (16 * (l - m) ^ 2) ≤
      8 * (4 * (l + m)) ^ 5 * D.L (4 * (l + m)) *
        (D.H l m - (Real.negMulLog l + Real.negMulLog m) / 2) := by
  set e : ℝ := 4 * (l + m) with he
  set v : ℝ := 16 * (l - m) ^ 2 with hv
  have hlm : 0 < l + m := by linarith
  have he0 : 0 < e := by rw [he]; linarith
  have hs : |(l - m) / (l + m)| < 1 := by
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hlm]; linarith
    · rw [div_lt_iff₀ hlm]; linarith
  set s : ℝ := (l - m) / (l + m) with hsdef
  have havg := avg_identity hl hm
  have hM : (l + m) / 2 = e / 8 := by rw [he]; ring
  rw [← hsdef, hM] at havg
  have hphi := phiB_minorant hs
  have hz : s ^ 2 = v / e ^ 2 := by
    rw [hsdef, hv, he]; field_simp; ring
  have hLe := hL e he0.le
  have hKe := hK e he0
  set X : ℝ := phiB s with hX
  have hHdef : D.H l m = D.P e + v * D.A e + v ^ 2 * D.B e := by
    unfold MajData.H; rw [he, hv]
  rw [hHdef, havg]
  have hΦ : e ^ 6 * D.L e * (s ^ 2 / 2 + eta2R * (s ^ 2) ^ 2 + eta3R * (s ^ 2) ^ 3) ≤ e ^ 6 * D.L e * X :=
    mul_le_mul_of_nonneg_left hphi (by positivity)
  have hΦeq : e ^ 6 * D.L e * (s ^ 2 / 2 + eta2R * (s ^ 2) ^ 2 + eta3R * (s ^ 2) ^ 3) =
      e ^ 4 * D.L e * (1 / 2) * v + e ^ 2 * D.L e * eta2R * v ^ 2 + eta3R * D.L e * v ^ 3 := by
    rw [hz]; field_simp
  have hK8 : 8 * e ^ 5 * (D.k0 * D.q e ^ 2) ≤ 8 * e ^ 5 * ((D.P e - Real.negMulLog (e / 8)) * D.L e) :=
    mul_le_mul_of_nonneg_left hKe (by positivity)
  have hFeq : D.F e v = 8 * e ^ 5 * (D.k0 * D.q e ^ 2) + 8 * e ^ 5 * D.L e * v * D.A e +
      8 * e ^ 5 * D.L e * v ^ 2 * D.B e +
      (e ^ 4 * D.L e * (1 / 2) * v + e ^ 2 * D.L e * eta2R * v ^ 2 + eta3R * D.L e * v ^ 3) := by
    unfold MajData.F MajData.U MajData.V MajData.W; ring
  rw [hFeq, ← hΦeq]
  nlinarith [hΦ, hK8]

end

section

variable (D : MajData)

/-- **Majorant on the open quadrant.** -/
theorem majorant_pos (heta : 0 < eta3R) (hk0 : 0 < D.k0) (hL : ∀ e, 0 ≤ e → 0 < D.L e)
    (hK : ∀ e : ℝ, 0 < e → D.k0 * D.q e ^ 2 ≤ (D.P e - Real.negMulLog (e / 8)) * D.L e)
    (hR : ∀ e, D.R e = (e - D.e0) ^ 2 * D.Pi e) (hPi : ∀ e, 0 ≤ e → 0 < D.Pi e)
    (hq : Continuous D.q) (hA : Continuous D.A) (hB : Continuous D.B)
    {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    (Real.negMulLog l + Real.negMulLog m) / 2 ≤ D.H l m := by
  have hlm : 0 < l + m := by linarith
  have he0 : 0 < 4 * (l + m) := by linarith
  have hF := F_nonneg D heta hk0 hL hR hPi hq hA hB he0 (v := 16 * (l - m) ^ 2) (by positivity)
  have hg := gap_lb D hL hK hl hm
  have hLe := hL _ he0.le
  have : 0 ≤ 8 * (4 * (l + m)) ^ 5 * D.L (4 * (l + m)) *
      (D.H l m - (Real.negMulLog l + Real.negMulLog m) / 2) := le_trans hF hg
  have hpos : 0 < 8 * (4 * (l + m)) ^ 5 * D.L (4 * (l + m)) := by positivity
  have := nonneg_of_mul_nonneg_right this hpos
  linarith

/-- **Majorant on the closed quadrant**, by continuity. -/
theorem majorant_all (heta : 0 < eta3R) (hk0 : 0 < D.k0) (hL : ∀ e, 0 ≤ e → 0 < D.L e)
    (hK : ∀ e : ℝ, 0 < e → D.k0 * D.q e ^ 2 ≤ (D.P e - Real.negMulLog (e / 8)) * D.L e)
    (hR : ∀ e, D.R e = (e - D.e0) ^ 2 * D.Pi e) (hPi : ∀ e, 0 ≤ e → 0 < D.Pi e)
    (hq : Continuous D.q) (hA : Continuous D.A) (hB : Continuous D.B) (hP : Continuous D.P)
    {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) :
    (Real.negMulLog l + Real.negMulLog m) / 2 ≤ D.H l m := by
  have hcont : Continuous (fun t : ℝ => D.H (l + t) (m + t) -
      (Real.negMulLog (l + t) + Real.negMulLog (m + t)) / 2) := by
    unfold MajData.H
    have := Real.continuous_negMulLog
    fun_prop
  have hT : Tendsto (fun t : ℝ => D.H (l + t) (m + t) -
      (Real.negMulLog (l + t) + Real.negMulLog (m + t)) / 2) (𝓝[>] 0)
      (𝓝 (D.H l m - (Real.negMulLog l + Real.negMulLog m) / 2)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ D.H (l + t) (m + t) -
      (Real.negMulLog (l + t) + Real.negMulLog (m + t)) / 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have := majorant_pos D heta hk0 hL hK hR hPi hq hA hB (l := l + t) (m := m + t)
      (by have : (0 : ℝ) < t := ht; linarith) (by have : (0 : ℝ) < t := ht; linarith)
    linarith
  have := ge_of_tendsto hT hev
  linarith

end

end FormalResearch.FourQubitEntropy.AH6
