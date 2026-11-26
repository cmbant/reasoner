module

public import FormalResearch.SignUncertainty.CtChartData

/-!
# The CFU chart `T(s;β) = s U(s²;β)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Steps 2-3.  **Proved.**
`Z(y;β)` solves `Z V(Z;β)² = y` (parametric scalar IFT), `U = 1/V(Z;β)`, `T(s;β) = s U(s²;β)`, with
`Φ(T(s;β); β) = -(a(β) s + s³/3)` (`chart_identity`), `Z(d(β)²β; β) = β` (`saddle_Z`), conjugation symmetry.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The scalar equation `z V(z;β)² - y = 0`, `p = (z, (y, β))`. -/
noncomputable def G2 (p : ℂ × (ℂ × ℂ)) : ℂ := p.1 * Vf (p.1, p.2.2) ^ 2 - p.2.1

lemma G2_base : G2 (0, (0, 0)) = 0 := by simp [G2]

lemma contDiffAt_G2 : ContDiffAt ℂ ∞' G2 (0, (0, 0)) := by
  unfold G2
  have hV : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => Vf (p.1, p.2.2)) (0, (0, 0)) :=
    ContDiffAt.comp (g := Vf) (f := fun p : ℂ × (ℂ × ℂ) => (p.1, p.2.2)) (0, (0, 0)) (by simpa using contDiffAt_Vf)
      (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffAt
  exact (contDiff_fst.contDiffAt.mul (hV.pow 2)).sub (contDiff_fst.comp contDiff_snd).contDiffAt

lemma hasDerivAt_G2_base : HasDerivAt (fun z : ℂ => G2 (z, (0, 0))) (((CtCfu.d0 : ℝ) : ℂ) ^ 2) 0 := by
  have hW : ContDiffAt ℂ ∞' (fun z : ℂ => Vf (z, 0)) 0 :=
    ContDiffAt.comp (g := Vf) (f := fun z : ℂ => (z, (0 : ℂ))) 0 (by simpa using contDiffAt_Vf)
      (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd := (hW.differentiableAt (by simp)).hasDerivAt.pow 2
  have h := (hasDerivAt_id' (0 : ℂ)).mul hd
  have e : (fun z : ℂ => G2 (z, (0, 0))) = fun z => z * Vf (z, 0) ^ 2 := by
    funext z; simp [G2]
  rw [e]
  refine h.congr_deriv ?_
  have : Vf (0, 0) = ((CtCfu.d0 : ℝ) : ℂ) := Vf_zero
  simp [this]

lemma G2_sym : ∀ᶠ p in 𝓝 ((0 : ℂ), ((0 : ℂ), (0 : ℂ))),
    G2 (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (G2 p) := by
  have ht : Tendsto (fun p : ℂ × (ℂ × ℂ) => (p.1, p.2.2)) (𝓝 ((0 : ℂ), ((0 : ℂ), (0 : ℂ)))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousAt.tendsto
  filter_upwards [ht.eventually Vf_conj] with p hp
  unfold G2
  have hp' : Vf (starRingEnd ℂ p.1, starRingEnd ℂ p.2.2) = starRingEnd ℂ (Vf (p.1, p.2.2)) := hp
  simp only [conj2, map_sub, map_mul, map_pow, hp']

theorem exists_Zf : ∃ Z : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' Z (0, 0) ∧ Z (0, 0) = 0 ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), G2 (Z q, q) = 0) ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Z (conj2 q) = starRingEnd ℂ (Z q)) ∧
    ∀ᶠ β in 𝓝 (0 : ℂ), Z (dC β ^ 2 * β, β) = β := by
  have hd0 : ((CtCfu.d0 : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 d0C_ne
  obtain ⟨ξ, h1, h2, h3, ⟨U, hU, V, hV, huniq⟩, h5⟩ := scalar_ift_conj (g := G2) (x0 := 0) (q0 := ((0 : ℂ), (0 : ℂ)))
    (g1 := ((CtCfu.d0 : ℝ) : ℂ) ^ 2) contDiffAt_G2 G2_base hasDerivAt_G2_base hd0 (by simp) (by simp [conj2]) G2_sym
  refine ⟨ξ, h1, h2, h3, h5, ?_⟩
  have hq : Tendsto (fun β : ℂ => (dC β ^ 2 * β, β)) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have hc : ContinuousAt dC 0 := contDiffAt_dC.continuousAt
    have : ContinuousAt (fun β : ℂ => (dC β ^ 2 * β, β)) 0 := ((hc.pow 2).mul continuousAt_id).prodMk continuousAt_id
    simpa using this.tendsto
  filter_upwards [hq.eventually hV, hU] with β hβV hβU
  have hβU' : β ∈ U := hβU
  have hz : G2 (β, (dC β ^ 2 * β, β)) = 0 := by
    unfold G2
    simp only [Vf_diag]
    ring
  exact (huniq _ hβV β hβU' hz).symm

/-- `Z(y;β)`: `T(s;β)² = Z(s²;β)`. -/
noncomputable def Zf : ℂ × ℂ → ℂ := Classical.choose exists_Zf

lemma contDiffAt_Zf : ContDiffAt ℂ ∞' Zf (0, 0) := (Classical.choose_spec exists_Zf).1
lemma Zf_zero : Zf (0, 0) = 0 := (Classical.choose_spec exists_Zf).2.1
lemma Zf_eq : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Zf q * Vf (Zf q, q.2) ^ 2 = q.1 := by
  filter_upwards [(Classical.choose_spec exists_Zf).2.2.1] with q hq
  have hq' : Zf q * Vf (Zf q, q.2) ^ 2 - q.1 = 0 := hq
  linear_combination hq'
lemma Zf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Zf (conj2 q) = starRingEnd ℂ (Zf q) :=
  (Classical.choose_spec exists_Zf).2.2.2.1
/-- **The saddle**: `Z(d²β; β) = β`. -/
lemma saddle_Z : ∀ᶠ β in 𝓝 (0 : ℂ), Zf (dC β ^ 2 * β, β) = β := (Classical.choose_spec exists_Zf).2.2.2.2

/-- `U(y;β) = 1/V(Z(y;β);β)`. -/
noncomputable def Uf (q : ℂ × ℂ) : ℂ := 1 / Vf (Zf q, q.2)

/-- The chart `T(s;β) = s U(s²;β)`. -/
noncomputable def Tf (p : ℂ × ℂ) : ℂ := p.1 * Uf (p.1 ^ 2, p.2)

lemma Vf_Zf_zero : Vf (Zf (0, 0), 0) = ((CtCfu.d0 : ℝ) : ℂ) := by rw [Zf_zero]; exact Vf_zero

lemma contDiffAt_VZ : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => Vf (Zf q, q.2)) (0, 0) := by
  have h := contDiffAt_Zf
  have hV : ContDiffAt ℂ ∞' Vf (Zf (0, 0), (0, 0).2) := by simpa [Zf_zero] using contDiffAt_Vf
  exact ContDiffAt.comp (g := Vf) (f := fun q : ℂ × ℂ => (Zf q, q.2)) (0, 0) hV (h.prodMk contDiff_snd.contDiffAt)

lemma contDiffAt_Uf : ContDiffAt ℂ ∞' Uf (0, 0) := by
  unfold Uf
  exact contDiffAt_const.div contDiffAt_VZ (by simpa [Vf_Zf_zero] using d0C_ne)

lemma Uf_zero : Uf (0, 0) = 1 / ((CtCfu.d0 : ℝ) : ℂ) := by unfold Uf; simp [Vf_Zf_zero]

lemma Vf_Zf_ne : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Vf (Zf q, q.2) ≠ 0 := by
  have hc : ContinuousAt (fun q : ℂ × ℂ => Vf (Zf q, q.2)) (0, 0) := contDiffAt_VZ.continuousAt
  exact hc.eventually_ne (by simpa [Vf_Zf_zero] using d0C_ne)

lemma contDiffAt_Tf : ContDiffAt ℂ ∞' Tf (0, 0) := by
  unfold Tf
  have hU : ContDiffAt ℂ ∞' Uf ((fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0)) := by simpa using contDiffAt_Uf
  exact contDiff_fst.contDiffAt.mul
    (ContDiffAt.comp (g := Uf) (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) hU
      ((contDiff_fst.pow 2).prodMk contDiff_snd).contDiffAt)

/-- The phase `Φ(x; L) = x L - x³ ñ(x²) = x (L - p(x²))`. -/
noncomputable def PhiC (x β : ℂ) : ℂ := x * (LC β - pC (x ^ 2))

lemma tendsto_sq : Tendsto (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
  have : ContinuousAt (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) := (continuous_fst.pow 2).continuousAt.prodMk continuous_snd.continuousAt
  simpa using this.tendsto

lemma tendsto_Zq : Tendsto (fun p : ℂ × ℂ => (Zf (p.1 ^ 2, p.2), p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
  have h1 : Tendsto (fun p : ℂ × ℂ => Zf (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
    have := contDiffAt_Zf.continuousAt.tendsto
    rw [Zf_zero] at this
    exact this.comp tendsto_sq
  exact h1.prodMk_nhds continuous_snd.continuousAt.tendsto

/-- **The chart identity** (`ct:cfu` Step 2): `Φ(T(s;β); β) = -(a(β) s + s³/3)`. -/
theorem chart_identity : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    PhiC (Tf p) p.2 = -(aC p.2 * p.1 + p.1 ^ 3 / 3) := by
  filter_upwards [tendsto_sq.eventually Zf_eq, tendsto_Zq.eventually key_identity, tendsto_sq.eventually Vf_Zf_ne]
    with p h1 h2 h3
  obtain ⟨s, β⟩ := p
  simp only at h1 h2 h3
  set z := Zf (s ^ 2, β) with hz
  set V := Vf (z, β) with hV
  have hTU : Tf (s, β) = s / V := by
    unfold Tf Uf
    simp only
    rw [← hz, ← hV]; ring
  have hT2 : (s / V) ^ 2 = z := by
    field_simp
    linear_combination -h1
  unfold PhiC
  rw [hTU, hT2]
  simp only at h2 ⊢
  rw [h2]
  field_simp
  linear_combination (-s) * h1

/-- At the saddle, `U(d²β; β) = 1/d(β)`. -/
lemma Uf_saddle : ∀ᶠ β in 𝓝 (0 : ℂ), Uf (dC β ^ 2 * β, β) = 1 / dC β := by
  filter_upwards [saddle_Z] with β hβ
  unfold Uf
  simp only
  rw [hβ, Vf_diag]

lemma Uf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Uf (conj2 q) = starRingEnd ℂ (Uf q) := by
  have hq : Tendsto (fun q : ℂ × ℂ => (Zf q, q.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    have h1 := contDiffAt_Zf.continuousAt.tendsto
    rw [Zf_zero] at h1
    exact h1.prodMk_nhds continuous_snd.continuousAt.tendsto
  filter_upwards [Zf_conj, hq.eventually Vf_conj] with q h1 h2
  unfold Uf
  simp only [conj2] at h1 ⊢
  rw [map_div₀, map_one]
  have : Vf (Zf (starRingEnd ℂ q.1, starRingEnd ℂ q.2), starRingEnd ℂ q.2) = starRingEnd ℂ (Vf (Zf q, q.2)) := by
    rw [h1]; exact h2
  rw [this]

/-- Reality of the chart: `T(s̄; β̄) = conj T(s; β)`. -/
lemma Tf_conj : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Tf (conj2 p) = starRingEnd ℂ (Tf p) := by
  filter_upwards [tendsto_sq.eventually Uf_conj] with p hp
  unfold Tf
  simp only [conj2] at hp ⊢
  rw [map_mul]
  have : Uf ((starRingEnd ℂ p.1) ^ 2, starRingEnd ℂ p.2) = starRingEnd ℂ (Uf (p.1 ^ 2, p.2)) := by
    simpa [conj2, map_pow] using hp
  rw [this]

/-- info: 'FormalResearch.SignUncertainty.CtChart.chart_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chart_identity

end FormalResearch.SignUncertainty.CtChart
