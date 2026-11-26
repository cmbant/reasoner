module

public import FormalResearch.SignUncertainty.CtChartTheta

/-!
# The amplitude/phase decomposition of the CFU chart (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3.  **Proved** (complex-smooth near `(0,0)`, in the
`β = b²` parametrisation; `a = -d(β)²β = -y_*(β)`).
With `y = s²`, `h(y;β) = U(y;β) ϑ(Z(y;β))` (so `θ(T(s;β)) = s h(s²;β)`), `ψ̂(β) = h(y_*(β);β)`, `h̃ = hadY h`, `Q_geo = hadY μ`,
`X = s (s² - y_*) h̃`, and `Q_ε := Q_geo e^{iX} + i s h̃ E₁(iX)`:
`μ(s²;β) = 1 + (s² - y_*) Q_geo`, `θ(T) - sψ̂ = s (s² - y_*) h̃`, `μ e^{iX} = 1 + (s² - y_*) Q_ε`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

open CtOuter

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `h(y;β) = U(y;β) ϑ(Z(y;β))`. -/
noncomputable def hF (ϑ : ℂ → ℂ) (q : ℂ × ℂ) : ℂ := Uf q * ϑ (Zf q)

/-- `ψ̂(β) = h(y_*(β);β)`. -/
noncomputable def psiHat (ϑ : ℂ → ℂ) (β : ℂ) : ℂ := hF ϑ (ysF β, β)

/-- `h̃ = (h - h(y_*))/(y - y_*)`. -/
noncomputable def htil (ϑ : ℂ → ℂ) : ℂ × ℂ → ℂ := hadY (hF ϑ)

/-- `Q_geo = (μ - 1)/(y - y_*)`. -/
noncomputable def Qgeo : ℂ × ℂ → ℂ := hadY muf

/-- The phase `X = s (s² - y_*) h̃(s²;β)` (`p = (s, β)`). -/
noncomputable def Xph (ϑ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ := p.1 * (p.1 ^ 2 - ysF p.2) * htil ϑ (p.1 ^ 2, p.2)

/-- `Q_ε(s;β) = Q_geo e^{iX} + i s h̃ E₁(iX)`. -/
noncomputable def Qeps (ϑ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  Qgeo (p.1 ^ 2, p.2) * Complex.exp (Complex.I * Xph ϑ p) +
    Complex.I * p.1 * htil ϑ (p.1 ^ 2, p.2) * E1 (Complex.I * Xph ϑ p)

lemma contDiffAt_hF {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ContDiffAt ℂ ∞' (hF ϑ) (0, 0) := by
  unfold hF
  refine contDiffAt_Uf.mul ?_
  exact ContDiffAt.comp (g := ϑ) (f := Zf) (0, 0) (by simpa [Zf_zero] using hA.contDiffAt) contDiffAt_Zf

lemma sq_prod_cd : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) :=
  ((contDiff_fst.pow 2).prodMk contDiff_snd).contDiffAt

lemma contDiffAt_comp_sq {F : ℂ × ℂ → ℂ} (h : ContDiffAt ℂ ∞' F (0, 0)) :
    ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => F (p.1 ^ 2, p.2)) (0, 0) :=
  ContDiffAt.comp (g := F) (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (0, 0) (by simpa using h) sq_prod_cd

lemma contDiffAt_htil {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ContDiffAt ℂ ∞' (htil ϑ) (0, 0) :=
  contDiffAt_hadY (contDiffAt_hF hA)

lemma contDiffAt_Qgeo : ContDiffAt ℂ ∞' Qgeo (0, 0) := contDiffAt_hadY contDiffAt_muf

lemma contDiffAt_Xph {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ContDiffAt ℂ ∞' (Xph ϑ) (0, 0) := by
  unfold Xph
  have hy : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => ysF p.2) (0, 0) :=
    ContDiffAt.comp (g := ysF) (f := fun p : ℂ × ℂ => p.2) (0, 0) (by simpa using contDiffAt_ysF)
      contDiff_snd.contDiffAt
  exact contDiff_fst.contDiffAt.mul (((contDiff_fst.pow 2).contDiffAt).sub hy) |>.mul (contDiffAt_comp_sq (contDiffAt_htil hA))

lemma contDiffAt_Qeps {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ContDiffAt ℂ ∞' (Qeps ϑ) (0, 0) := by
  unfold Qeps
  have hX := contDiffAt_Xph hA
  have hIX : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => Complex.I * Xph ϑ p) (0, 0) := contDiffAt_const.mul hX
  have hexp : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => Complex.exp (Complex.I * Xph ϑ p)) (0, 0) :=
    (Complex.contDiff_exp.contDiffAt).comp (0, 0) hIX
  have hE : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => E1 (Complex.I * Xph ϑ p)) (0, 0) :=
    ContDiffAt.comp (g := E1) (f := fun p : ℂ × ℂ => Complex.I * Xph ϑ p) (0, 0)
      (contDiffAt_E1 _) hIX
  exact ((contDiffAt_comp_sq contDiffAt_Qgeo).mul hexp).add
    ((((contDiffAt_const.mul contDiff_fst.contDiffAt)).mul (contDiffAt_comp_sq (contDiffAt_htil hA))).mul hE)

lemma tendsto_sq_eq : Tendsto (fun p : ℂ × ℂ => (p.1 ^ 2, p.2)) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
  tendsto_sq

/-- `μ(s²;β) = 1 + (s² - y_*) Q_geo(s²;β)`. -/
lemma muf_decomp : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    muf (p.1 ^ 2, p.2) = 1 + (p.1 ^ 2 - ysF p.2) * Qgeo (p.1 ^ 2, p.2) := by
  have h1 := hadY_identity contDiffAt_muf
  have h2 : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), muf (ysF q.2, q.2) = 1 := by
    have := saddle_mu
    exact (continuous_snd.tendsto ((0 : ℂ), (0 : ℂ))).eventually this
  have h3 := tendsto_sq.eventually (h1.and h2)
  filter_upwards [h3] with p hp
  obtain ⟨e1, e2⟩ := hp
  rw [e2] at e1
  unfold Qgeo
  linear_combination e1

/-- `h(s²;β) - ψ̂(β) = (s² - y_*) h̃(s²;β)`. -/
lemma hF_decomp {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    hF ϑ (p.1 ^ 2, p.2) - psiHat ϑ p.2 = (p.1 ^ 2 - ysF p.2) * htil ϑ (p.1 ^ 2, p.2) := by
  have h1 := hadY_identity (contDiffAt_hF hA)
  filter_upwards [tendsto_sq.eventually h1] with p hp
  simpa [psiHat, htil] using hp

/-- The exact amplitude decomposition `μ(s²;β) e^{iX} = 1 + (s² - y_*) Q_ε(s;β)`. -/
theorem amp_decomp (ϑ : ℂ → ℂ) : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    muf (p.1 ^ 2, p.2) * Complex.exp (Complex.I * Xph ϑ p) = 1 + (p.1 ^ 2 - ysF p.2) * Qeps ϑ p := by
  filter_upwards [muf_decomp] with p hp
  have hE := exp_sub_one_eq (Complex.I * Xph ϑ p)
  unfold Qeps
  have hX : Xph ϑ p = p.1 * (p.1 ^ 2 - ysF p.2) * htil ϑ (p.1 ^ 2, p.2) := rfl
  rw [hp]
  have : Complex.exp (Complex.I * Xph ϑ p) = 1 + Complex.I * Xph ϑ p * E1 (Complex.I * Xph ϑ p) := by
    linear_combination hE
  rw [this, hX]
  ring

lemma Tf_zero : Tf (0, 0) = 0 := by simp [Tf]

lemma Tf_sq : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Tf p ^ 2 = Zf (p.1 ^ 2, p.2) := by
  filter_upwards [tendsto_sq.eventually (Zf_eq.and Vf_Zf_ne)] with p hp
  obtain ⟨e1, e2⟩ := hp
  unfold Tf Uf
  simp only
  field_simp
  linear_combination -e1

lemma tendsto_Tf : Tendsto Tf (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
  have := contDiffAt_Tf.continuousAt
  rw [ContinuousAt, Tf_zero] at this
  exact this

/-- `θ(T(s;β)) = s h(s²;β)`, where `θ = thOdd ε = τ ϑ(τ²)` near `0`. -/
lemma theta_T {ε : ℝ} {ϑ : ℂ → ℂ} (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2)) :
    ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), thOdd ε (Tf p) = p.1 * hF ϑ (p.1 ^ 2, p.2) := by
  filter_upwards [tendsto_Tf.eventually hϑ, Tf_sq] with p h1 h2
  rw [h1, h2]
  unfold hF Uf Tf
  simp only [Uf]
  ring

/-- `θ(T) - s ψ̂ = s (s² - y_*) h̃`. -/
theorem theta_T_decomp {ε : ℝ} {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2)) :
    ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
      thOdd ε (Tf p) - p.1 * psiHat ϑ p.2 = p.1 * (p.1 ^ 2 - ysF p.2) * htil ϑ (p.1 ^ 2, p.2) := by
  filter_upwards [theta_T hϑ, hF_decomp hA] with p h1 h2
  rw [h1]
  linear_combination p.1 * h2

/-- `ψ̂(β) = ϑ(β)/d(β)`. -/
lemma psiHat_eq (ϑ : ℂ → ℂ) : ∀ᶠ β in 𝓝 (0 : ℂ), psiHat ϑ β = ϑ β / dC β := by
  filter_upwards [saddle_Z, Uf_saddle] with β h1 h2
  unfold psiHat hF
  have e : (ysF β, β) = (dC β ^ 2 * β, β) := rfl
  rw [e, h2, h1]
  ring

/-- info: 'FormalResearch.SignUncertainty.CtChart.amp_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_decomp

/-- info: 'FormalResearch.SignUncertainty.CtChart.theta_T_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_T_decomp

end FormalResearch.SignUncertainty.CtChart
