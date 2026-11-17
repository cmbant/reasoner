module

public import FormalResearch.Special.DiscreteAiryLimitSetup

/-!
# The discrete-to-Airy limit at a simple turn (composition of the D2A machinery)

**Setting (abstract `SimpleTurnData`).**  Smooth coefficient data `u ∈ C³`, `A ∈ C²` near `c₀` with
`u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0` (P3 `A:804-818`, W1 `est:266-282`: a simple turning point of the symmetric
Jacobi recurrence `a_{k+1} y_{k+1} + a_k y_{k-1} = c_k y_k` with `a_k ≈ A(q_k - h/2)`, `c_k ≈ 2A(q_k)u(q_k)`,
`q_k = q₀ + kh`).  `ζ = langerZeta u c₀` is the Langer coordinate (`ζ ζ'² = Φ(u-1)`, `ζ(c₀) = 0`, `ζ'(c₀) = (2u')^{1/3}`),
`g = langerAmp u A c₀` the amplitude (`g² A ζ' Sh(ζ ζ'²) = 1`), `X_k = h^{-2/3} ζ(q_k)` (`h = δ³`) and
`ψ_k = g(q_k) Ai(X_k)`.

**`discrete_airy_limit`** (this file) composes M1-M7b (`DiscreteJacobi*`, `AiryShift*`, `Langer*`,
`AiryParametrix*`, `AiryRecessive*`, `AiryWindow*`) through the verification layer `DiscreteAiryLimit{Data,Lattice,
Defect,Hyp,Fields,Setup}`: for coefficient sequences with `|a_k - A(q_k-h/2)| ≤ E h²`, `|c_k - 2A(q_k)u(q_k)| ≤ E h²`
(the paper's `A_k = a₀(s) + O(h²)`), on the lattice window `J ≤ m ≤ N` with `X_J ≈ -A₀`, `X_m ≈ 0`, `q_{N+1} ≈ c₀ + r/2`:

* **recessive form** (the recessive-branch counterpart of Geronimo/GBVA Thm 3.8, on a bounded oscillatory window and the
  forbidden side up to `q ≤ c₀ + r/2`; see *Not formalised* for what is not replaced): there is an exact solution `f` of the recurrence on the
  rows `J+1..N` with `f = ψ` at the last two sites and `|f_k - ψ_k| ≤ C δ³ ψ_k` on the forbidden side `X ≥ 0` and
  `|f_k - ψ_k| ≤ C δ³ W` on the oscillatory window `X ∈ [-A₀, 0]` (`δ³ = h`; `W` bounds `|ψ|`);
* **physical form** (P3 `thm:general-rank-airy`(i), W1 `eq:airyfactor`): every exact solution `Y` of the rows with
  `|Y_N|, |Y_{N+1}| ≤ Y_max` is `Y = κ f + μ f₂` with `|μ| ≤ C_μ Y_max e^{-ξ(X_N)}` (`ξ(X_N) ≥ ξ₀/δ³`) and
  `|Y_k - κ ψ_k| ≤ C δ³ |κ| W + C_osc |μ|/δ` on `X ∈ [-A₀, 0]`, `≤ C δ³ |κ| ψ_k + C_top |μ|/(δ airyWt X_k)` on `X ≥ 0`.

`dal_conclusion_window` (`DiscreteAiryLimitWindow`) is the corollary on a bounded window `X_k ≤ Z` with the
exponentially small `μ`-terms absorbed: `|Y_k - κ g(q_k) Ai(X_k)| ≤ C δ³ |κ| W + δⁿ` for `|Y_N|, |Y_{N+1}| ≤ δ^{-p}`,
which is the paper's `Y = κ g [Ai + O(h)]` when `|κ| ≥ δ^s`.  The Hahn/centred-Racah instance of both is in
`DiscreteAiryLimitHahn` (`discrete_airy_hahn_racah`, `discrete_airy_hahn_racah_window`).

**Numerics (mpmath, 30 digits, not a Lean claim).**  `A = 1 + 0.3q + 0.2q²`, `u = cosh√(q + 0.4q²)`, `c₀ = 0`,
`a_k = A(q_k - h/2)`, `c_k = 2A(q_k)u(q_k)`, solved backward from `q = 0.5`: the relative error of the recessive solution
against `g Ai(h^{-2/3}ζ)` on `X ≥ -1` is `0.0249, 0.0255, 0.0256, 0.0263 × h` for `h = 1/N`, `N = 50, 100, 200, 400`,
and the absolute error on `X ∈ [-6, -1]` is `≈ 0.017 h`, i.e. `O(h)` as the theorem states.  For the closed-form Hahn chain
(`P = 1, Q = 0, β₀ = 0, a = b = ½, x = 0.6, τ = 1`, `q_* = 0.8`, `A_k = ½ r_k √(1-(kh)²)`, `B_k = ab/(k(k+1))`,
`N = 100, 200, 400, 800`): relative error on `X ≥ 0` `= 0.252, 0.263, 0.274, 0.284 × h` and absolute error on
`X ∈ [-5, 0]` `= 0.274, 0.264, 0.257, 0.253 × h`.

**Claim class: proved** (no hypothesis beyond the stated smoothness and perturbation sizes; all constants existential,
`ζ`, `g` are the M3 coordinate and amplitude).  Hypothesis `|Y_N|, |Y_{N+1}| ≤ Y_max` is the polynomial bound `(R)`
(`T:889-892`) at the fixed point `N`, left to the caller (for the Hahn/Racah chains, `DiscreteAiryLimitHahn`).

**Exported window position.**  The statement records `q_k ∈ [c₀ - r, c₀ + r]` on `[J, N+1]`, `c₀ - Dδ² ≤ q_J ≤ c₀`,
`c₀ ≤ q_m < c₀ + h`, `c₀ + r/4 ≤ q_N`, `q_{N+1} ≤ c₀ + r/2` and `X_J ≤ -A₀` (`turnX u c₀ q₀ δ J ≤ -A₀`), so the
oscillatory window `[J, m]` reaches at least `X = -A₀` and the forbidden side `[m, N+1]` is non-empty (`X_N ≥ c₁r/(4δ²)`).

**Not formalised / scope.**  This does **not** replace Geronimo/GBVA in full.  It is the recessive-plus-bounded-window
form for one fixed `(u, A, c₀)`: this theorem has no non-recessive canonical `Ai`/`Bi` pair and no oscillatory side beyond
`X ≥ -A₀` (both are in `DiscreteAiryOsc*`, `dao_turn_conclusion`, and in the unified `DiscreteAiryPhys*`, `discrete_airy_full`: whole
macroscopic oscillatory side, `Cδ³` in the Olver-type weights, pair `g Ai`, `g Bi`; those statements pick their own radius `r`, so
they are not formally derived from this one), not uniform over families of data; here the closed forms of the Hahn/Racah instance are not identified with the actual
3j/6j chains (done in `DiscreteAiryLimitChains*`) and `(R)` is a hypothesis (derived in `DiscreteAiryLimitHyper*` up to one
normalisation, proved for the actual chains in `DiscreteAiryLimitChains*`).  The scalar `κ` (a normalisation fixed by the Darboux/Wigner-`d` bulk matching, T:336,
A:925-1054, est:309-318) is produced by the recessive selection and is not identified; `κ ≠ 0` is not proved.  The
oscillatory side beyond a bounded window `X ≥ -A₀` with the `M/E` weights of GBVA (covered in the amplitude-adapted `O(δ³)`
form by `DiscreteAiryOsc*`); the `h²` coefficient `ϖ` (the abstract second-order bracket for Langer-form data is `airy2_turn_full`, `DiscreteAirySecond*`; its Hahn/Racah instance, S4, is not formalised); constants are not tracked (the window constant is `e^{O(A₀²)}`, see `AiryWindowMain`); the
uniformity in the family parameters (everything is for one fixed `(u, A, c₀)`).
-/

@[expose] public section

open FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The lattice variable `X_k = h^{-2/3} ζ(q_k)` of the simple turn `(u, c₀)` (`h = δ³`). -/
noncomputable abbrev turnX (u : ℝ → ℝ) (c0 q₀ δ : ℝ) : ℤ → ℝ := dalX (langerZeta u c0) q₀ δ

/-- The parametrix `ψ_k = g(q_k) Ai(X_k)` of the simple turn `(u, A, c₀)`. -/
noncomputable abbrev turnPsi (u A : ℝ → ℝ) (c0 q₀ δ : ℝ) : ℤ → ℝ :=
  dalPsi (langerAmp u A c0) (langerZeta u c0) q₀ δ

/-- `ξ(X) ≥ (2/3)(c₁ r/4)^{3/2}/δ³` when `X ≥ c₁ r/(4δ²)`. -/
lemma dal_xi_large {X a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hX : a / δ ^ 2 ≤ X) :
    2 / 3 * a ^ (3 / 2 : ℝ) / δ ^ 3 ≤ airyXi X := by
  unfold airyXi
  have h0 : 0 ≤ a / δ ^ 2 := by positivity
  have h1 : a / δ ^ 2 ≤ max X 0 := hX.trans (le_max_left _ _)
  have h2 : (a / δ ^ 2) ^ (3 / 2 : ℝ) ≤ (max X 0) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow h0 h1 (by norm_num)
  have h3 : (a / δ ^ 2) ^ (3 / 2 : ℝ) = a ^ (3 / 2 : ℝ) / δ ^ 3 := by
    rw [Real.div_rpow ha (by positivity)]
    congr 1
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]
    norm_num
  calc 2 / 3 * a ^ (3 / 2 : ℝ) / δ ^ 3 = 2 / 3 * (a ^ (3 / 2 : ℝ) / δ ^ 3) := by ring
    _ = 2 / 3 * (a / δ ^ 2) ^ (3 / 2 : ℝ) := by rw [h3]
    _ ≤ 2 / 3 * (max X 0) ^ (3 / 2 : ℝ) := by gcongr

/-- The conclusion of the discrete-to-Airy limit for the lattice data `(a, c)`, the parametrix `ψ` and the Langer
variable `X` on the window `J ≤ m ≤ N`: the exact recessive solution `f` and the physical form of every exact solution
`Y` with `|Y_N|, |Y_{N+1}| ≤ Y_max` (see the module docstring). -/
def DalConclusion (a c ψ X : ℤ → ℝ) (J m N : ℤ) (δ C Cosc Ctop W Cmu ξ0 : ℝ) : Prop :=
  ξ0 / δ ^ 3 ≤ airyXi (X N) ∧ (∀ k ∈ Finset.Icc J (N + 1), |ψ k| ≤ W) ∧
  (∀ k ∈ Finset.Icc m (N + 1), 0 ≤ X k) ∧
  (∃ f : ℤ → ℝ, (∀ k ∈ Finset.Icc (J + 1) N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
    (∀ k ∈ Finset.Icc m (N + 1), |f k - ψ k| ≤ C * δ ^ 3 * ψ k) ∧
    (∀ k ∈ Finset.Icc J m, |f k - ψ k| ≤ C * δ ^ 3 * W)) ∧
  ∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Finset.Icc (J + 1) N, jac a c Y k = 0) →
    |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) ∧
      (∀ k ∈ Finset.Icc J m, |Y k - κ * ψ k| ≤ C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
      (∀ k ∈ Finset.Icc m (N + 1), |Y k - κ * ψ k| ≤
        C * δ ^ 3 * |κ| * ψ k + Ctop * |μ| / δ / airyWt (X k))

/-- Enlarging constants in the three-term bounds. -/
lemma dal_up0 {e C C' d w : ℝ} (h : e ≤ C * d * w) (hC : C ≤ C') (hd : 0 ≤ d) (hw : 0 ≤ w) :
    e ≤ C' * d * w :=
  h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hd) hw)

lemma dal_up1 {e C C' d K w Co Co' q : ℝ} (h : e ≤ C * d * K * w + Co * q) (hC : C ≤ C') (hCo : Co ≤ Co')
    (hd : 0 ≤ d) (hK : 0 ≤ K) (hw : 0 ≤ w) (hq : 0 ≤ q) : e ≤ C' * d * K * w + Co' * q :=
  h.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hd) hK) hw)
    (mul_le_mul_of_nonneg_right hCo hq))

lemma dal_up2 {e C C' d K w Co Co' m δ v : ℝ} (h : e ≤ C * d * K * w + Co * m / δ / v) (hC : C ≤ C')
    (hCo : Co ≤ Co') (hd : 0 ≤ d) (hK : 0 ≤ K) (hw : 0 ≤ w) (hm : 0 ≤ m) (hδ : 0 < δ) (hv : 0 < v) :
    e ≤ C' * d * K * w + Co' * m / δ / v := by
  refine h.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hd) hK) hw) ?_)
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCo hm) hδ.le) hv.le

/-- **The discrete-to-Airy limit at a simple turn.**  See the module docstring. -/
theorem discrete_airy_limit {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E A0 : ℝ) (hE : 0 ≤ E) (hA0p : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧
      0 < W ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < D ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - D * δ ^ 2 ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J ≤ c0 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        turnX u c0 q₀ δ J ≤ -A0 ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DalConclusion a c (turnPsi u A c0 q₀ δ) (turnX u c0 q₀ δ) J m N δ C Cosc Ctop W Cmu ξ0 := by
  obtain ⟨r, c1, c2, gmin, gmax, Amin, Amax, LA, Lg, Lu, U, T, hrr0, hU, hsub, hζ, hAU, hgU, hrel, heik⟩ :=
    dal_turn_data hu h1 h2 hA hA0 hr0
  obtain ⟨δ1, D, W, ca, B, κ1, κ2, C0, Λ, S, Sg, Qq, w0, hδ1, hδ11, hD, hW, hca, hB, hκ1, hκ12, hC0, hΛ,
    hS, hSg, hQq, hw0, H⟩ := dal_window_hyp T hU hsub hζ hAU hgU hrel heik E A0 hE hA0p
  have hc1 := T.c1_pos
  have hr := T.r_pos
  have hAmax : 0 < Amax := lt_of_lt_of_le T.Amin_pos T.Amin_le
  obtain ⟨δ2, hδ2, C2, hC2, Hphys⟩ :=
    discrete_airy_window_physical c1 B ca κ1 κ2 C0 Λ S Sg Qq w0 hc1 hca hC0 hΛ hS hSg hQq hw0
  obtain ⟨δ3, hδ3, C3, hC3, Hrec⟩ :=
    discrete_airy_window c1 B ca κ1 κ2 C0 Λ S Sg Qq hc1 hca hC0 hΛ hS hSg hQq
  have hosc0 : 0 < 2 / (ca * w0) * windowExp c1 ca Sg Qq S := by
    have := windowExp_pos c1 ca Sg Qq S
    positivity
  have hξ0 : 0 < 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) := by positivity
  have hκ2p : 0 < κ2 := lt_of_lt_of_le hκ1 hκ12
  refine ⟨r, min δ1 (min δ2 δ3), max C2 C3, max 1 (2 / (ca * w0) * windowExp c1 ca Sg Qq S),
    max 1 (secondConst c1 ca κ1 κ2), W, 3 * κ2 * (Amax + E), 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ), D, hr, hrr0,
    lt_min hδ1 (lt_min hδ2 hδ3), (min_le_left _ _).trans hδ11, lt_max_of_lt_left hC2,
    lt_max_of_lt_left one_pos, lt_max_of_lt_left one_pos, hW, by positivity, hξ0, hD, ?_⟩
  intro δ q₀ hδ hδ0
  have hδ1' : δ ≤ δ1 := hδ0.trans (min_le_left _ _)
  have hδ2' : δ ≤ δ2 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3' : δ ≤ δ3 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ11' : δ ≤ 1 := hδ1'.trans hδ11
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hXN, hXJ, Hh⟩ := H δ q₀ hδ hδ1'
  refine ⟨J, m, N, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hXJ, ?_⟩
  intro a c ha hc
  have hh := Hh a c ha hc
  have h3 : 0 ≤ δ ^ 3 := by positivity
  unfold DalConclusion
  refine ⟨dal_xi_large (by positivity) hδ hXN, hh.psiabs, hh.Xnn, ?_⟩
  constructor
  · obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := Hrec (dalX (langerZeta u c0) q₀ δ)
      (turnPsi u A c0 q₀ δ) a c J m N δ W hJm hmN hδ3' hh.lat hh.cmp hh.gap hh.span hh.alow hh.hyp hh.lipa
      hh.defT hh.defW hh.psim hh.junction
    refine ⟨f, hf1, hf2, hf3, fun k hk => ?_, fun k hk => ?_⟩
    · exact dal_up0 (by simpa [mul_assoc] using hf4 k hk) (le_max_right C2 C3) h3 (hh.cmp.pos hk).le
    · exact dal_up0 (by simpa [mul_assoc] using hf5 k hk) (le_max_right C2 C3) h3 hW.le
  · intro Y Ymax hY hYN hYN1
    obtain ⟨κ, μ, hμ, hosc, htop⟩ := Hphys (dalX (langerZeta u c0) q₀ δ) (turnPsi u A c0 q₀ δ) a c Y J m N δ W Ymax
      hJm hmN hδ2' hh.lat hh.cmp hh.gap hh.span hh.alow hh.hyp hh.lipa hh.defT hh.defW hh.psim hh.junction
      hh.psilow hY hYN hYN1
    have hYm : 0 ≤ Ymax := (abs_nonneg _).trans hYN
    have haN : a (N + 1) ≤ Amax + E := by
      have hk : N + 1 ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
      have h5 := (abs_le.1 (ha (N + 1) hk)).2
      have h6 := (T.Ab _ (dal_mid hwin hδ (N + 1) hk)).2
      have h7 : E * δ ^ 6 ≤ E := by
        have : δ ^ 6 ≤ 1 := pow_le_one₀ hδ.le hδ11'
        nlinarith
      linarith
    refine ⟨κ, μ, ?_, fun k hk => ?_, fun k hk => ?_⟩
    · refine hμ.trans ?_
      have hex := Real.exp_pos (-airyXi (dalX (langerZeta u c0) q₀ δ N))
      have h8 : 3 * κ2 * a (N + 1) ≤ 3 * κ2 * (Amax + E) := by
        have : 0 ≤ 3 * κ2 := by positivity
        exact mul_le_mul_of_nonneg_left haN this
      calc 3 * κ2 * a (N + 1) * Ymax * Real.exp (-airyXi (dalX (langerZeta u c0) q₀ δ N))
          = (3 * κ2 * a (N + 1)) * (Ymax * Real.exp (-airyXi (dalX (langerZeta u c0) q₀ δ N))) := by ring
        _ ≤ (3 * κ2 * (Amax + E)) * (Ymax * Real.exp (-airyXi (dalX (langerZeta u c0) q₀ δ N))) :=
          mul_le_mul_of_nonneg_right h8 (by positivity)
        _ = _ := by ring
    · exact dal_up1 (hosc k hk) (le_max_left C2 C3) (le_max_right _ _) h3 (abs_nonneg _) hW.le (by positivity)
    · exact dal_up2 (htop k hk) (le_max_left C2 C3) (le_max_right _ _) h3 (abs_nonneg _) (hh.cmp.pos hk).le
        (abs_nonneg _) hδ (airyWt_pos _)

/-- info: 'FormalResearch.Special.discrete_airy_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_limit

end FormalResearch.Special
