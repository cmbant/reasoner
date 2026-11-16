module

public import FormalResearch.Special.DiscreteAiryLimitHyperDecay
public import FormalResearch.Special.DiscreteAiryLimitWindow

/-!
# Discrete-to-Airy limit for the closed-form Hahn / centred Racah chains with hypothesis `(R)` discharged

Part of the wiring layer `DiscreteAiryLimit*`.  `discrete_airy_hahn_racah` and `discrete_airy_hahn_racah_window` assume
`|Y_N|, |Y_{N+1}| ≤ Y_max` (resp. `≤ δ^{-p}`), the forbidden-side bound `(R)` of P3 `thm:general-rank-airy`(ii)
(`T:889-892`).  Here `(R)` is replaced by explicit data, following P3 `rem:airy2-R`(b) (T:965) and
`prop:forbidden-decay`(a): `Y` solves the closed-form recurrence `jac (hrAk …) (hrCk …) Y = 0` on the **whole chain**
`[J+1, k_max]`, up to the hard edge `((k_max+1)h)² ∈ Dom`, `ẽ(((k_max+1)h)²) = 0` (so `A_{k_max+1} = 0`; Hahn: `(k_max+1)h = 1`), and
is bounded at **one site `k₁` of the forbidden side**, `m ≤ k₁ ≤ N`.  Then:

* `N + 1 ≤ k_max` (the matching sites lie on the chain; derived from the hard edge, not assumed);
* `|Y_k| ≤ |Y_{k₁}|` for all `k₁ ≤ k ≤ k_max` (monotone decay to the hard edge: exact hyperbolicity
  beyond the turn, `hr_hardedge_decay`), in particular `|Y_N|, |Y_{N+1}| ≤ |Y_{k₁}|`, which is `(R)`.

`discrete_airy_hahn_racah_hardedge` exports this next to the full `DalConclusion` of `discrete_airy_hahn_racah` (apply its
last component, the physical form, with `Y_max = |Y_{k₁}|`).  `discrete_airy_hahn_racah_hardedge_window` is the bounded-window
form `Y_k = κ g (Ai + O(h)) + O(δⁿ)` on `X ≤ Z`, with the sole normalisation hypothesis `|Y_{k₁}| ≤ δ^{-p}`.

**Claim class: proved** (no hypothesis beyond those stated; constants existential).

**The one normalisation hypothesis.**  The decay runs *from* `k₁` *to* the hard edge, so the bound `|Y_{k₁}| ≤ δ^{-p}` at an
early site of the forbidden side (`m ≤ k₁ ≤ N`; the paper takes `k₁` = the first rank with `N^{2/3}ζ ≥ 1`) is genuinely needed and
is not derived: a bound at the hard edge does not bound `Y` at `k₁`.  In the paper it comes from `thm:general-rank-airy`(i)
(`Y` normalised in the bulk by Darboux matching, so `κ` is identified) or, independently, from `3j`/`6j` orthogonality
(`Σ Y_k² ≤ δ^{-2p}` gives `|Y_{k₁}| ≤ δ^{-p}` at once).  Neither normalisation is formalised here (`κ` is not identified, as in
`DiscreteAiryLimit`).  Claiming a bound `|Y_{k₁}| ≤ δ^{-p}` for the actual `3j/6j` chain would need the identification of the
closed forms with the actual chains (done in `DiscreteAiryLimitChains*`).

**Scope / not formalised** (as in `DiscreteAiryLimitHahn`): the closed forms are not identified with the actual `3j`/`6j` chains here (see `DiscreteAiryLimitChains*`);
`κ` unidentified, `κ ≠ 0` unproved; recessive-plus-bounded-window form only; one fixed `(P,Q,a,b,τ,x)`; the quantum-`6j` variant;
the sharper exponential decay `prop:forbidden-decay`(b) is not used (monotone decay suffices for `(R)`).
-/

@[expose] public section

open FormalResearch.DiscreteAiry FormalResearch.Racah.P3

namespace FormalResearch.Special

/-- The hard edge lies beyond the matching window: if `ẽ(e²) = 0` (`e ≥ 0`) and `1 - Pq² > 0`, `1 - Qq² > 0` on
`[q_* - r₀, q_* + r₀]` and at `q_*`, then `e > q_* + r₀`. -/
lemma hr_edge_beyond {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) {qs r0 e : ℝ} (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hr0 : 0 < r0)
    (hdom : ∀ q ∈ Set.Icc (qs - r0) (qs + r0), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2)
    (he0 : 0 ≤ e) (hz : etilde P Q (e ^ 2) = 0) : qs + r0 < e := by
  by_contra hle
  push Not at hle
  have hpos : 0 < 1 - P * e ^ 2 ∧ 0 < 1 - Q * e ^ 2 := by
    rcases le_or_gt e qs with h1 | h1
    · have : e ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ he0 h1 2
      exact ⟨by nlinarith [mul_le_mul_of_nonneg_left this hP],
        by nlinarith [mul_le_mul_of_nonneg_left this hQ]⟩
    · exact hdom e ⟨by linarith, hle⟩
  unfold etilde at hz
  have := Real.sqrt_pos.2 (mul_pos hpos.1 hpos.2)
  linarith

/-- **Discrete-to-Airy limit for the closed-form Hahn / centred Racah chains, `(R)` replaced by hard-edge data.**
See the module docstring.  Conclusion: the window data and `DalConclusion` of `discrete_airy_hahn_racah`, and for every
solution `Y` on the chain `[J+1, k_max]` with the hard edge, the matching sites lie on the chain (`N + 1 ≤ k_max`) and `Y`
decays monotonically in absolute value from every site `k₁ ∈ [m, N]` to the hard edge. -/
theorem discrete_airy_hahn_racah_hardedge {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cosc ∧
      0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < D ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ qs ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ J ≤ -A0 ∧
        DalConclusion (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3))
          (turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
          J m N δ C Cosc Ctop W Cmu ξ0 ∧
        ∀ (kmax : ℕ) (k1 : ℤ) (Y : ℤ → ℝ),
          (((kmax : ℝ) + 1) * δ ^ 3) ^ 2 ∈ Dom P Q →
          etilde P Q ((((kmax : ℝ) + 1) * δ ^ 3) ^ 2) = 0 → m ≤ k1 → k1 ≤ N →
          (∀ k ∈ Finset.Icc (J + 1) (kmax : ℤ),
            jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          N + 1 ≤ (kmax : ℤ) ∧ ∀ k : ℤ, k1 ≤ k → k ≤ (kmax : ℤ) → |Y k| ≤ |Y k1| := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hrr0, hδ0', hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_limit (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) hr0 (hrE P Q a b qs) A0
      (hrE_nonneg P Q a b qs) hA0
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hκ' : 0 < (1 - τ * x) / qs ^ 2 := div_pos hκ (by positivity)
  have hρ0 : 0 ≤ hrRho P Q a b qs := by unfold hrRho; positivity
  have hδC0 : 0 < 2 * ((1 - τ * x) / qs ^ 2) * qs / (hrRho P Q a b qs + 1) :=
    div_pos (mul_pos (mul_pos two_pos hκ') hqs) (by linarith)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (min (qs / (2 * hrM a b))
      (2 * ((1 - τ * x) / qs ^ 2) * qs / (hrRho P Q a b qs + 1))))) :=
    lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) hδC0)))
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (min (qs / (2 * hrM a b))
      (2 * ((1 - τ * x) / qs ^ 2) * qs / (hrRho P Q a b qs + 1)))))), C, Cosc, Ctop, W, Cmu, ξ0, D, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro δ hδ hδδ0
  have hδ1' : δ ≤ δ0' := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 :=
    hδi'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδM2 : δ ≤ qs / (2 * hrM a b) :=
    hδi'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hδC : δ ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs / (hrRho P Q a b qs + 1) :=
    hδi'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  -- the two smallness conditions of `hr_hardedge_decay`
  have hhM : δ ^ 3 * (2 * hrM a b) ≤ qs := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * hrM a b)).1 hδM2
    calc δ ^ 3 * (2 * hrM a b) ≤ δ * (2 * hrM a b) :=
          mul_le_mul_of_nonneg_right h3δ (by positivity)
      _ ≤ qs := this
  have hhC : δ ^ 3 * hrRho P Q a b qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs := by
    have := (le_div_iff₀ (by linarith : 0 < hrRho P Q a b qs + 1)).1 hδC
    nlinarith [mul_le_mul_of_nonneg_right h3δ hρ0]
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hXJ, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  have hδqq : δ ^ 3 ≤ qs / 2 := h3δ.trans hδq
  have hδM' : δ ≤ 3 * qs / (4 * hrM a b) := hδM
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM' hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  have hJ1 : 1 ≤ J := hr_J_pos hr4 hδ hδqq (by omega) hwin
  refine ⟨J, m, N, hJ1, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    hXJ, Hc _ _ hpa hpc, ?_⟩
  · have h1 := hwin k hk
    rw [e2] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  intro kmax k1 Y hedge hedge0 hmk1 hk1N hY
  have he0 : 0 ≤ ((kmax : ℝ) + 1) * δ ^ 3 := by positivity
  have hbey := hr_edge_beyond hP hQ hα hβ hr0 hdom he0 hedge0
  have hN1 : N + 1 ≤ (kmax : ℤ) := by
    have hq := hqN1
    rw [e2] at hq
    push_cast at hq
    have h5 : ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 < ((kmax : ℝ) + 1) * δ ^ 3 := by linarith
    have h6 := lt_of_mul_lt_mul_right h5 h3.le
    have h7 : (N : ℝ) < kmax := by linarith
    have h8 : N < (kmax : ℤ) := by exact_mod_cast h7
    omega
  refine ⟨hN1, ?_⟩
  lift k1 to ℕ using (by omega)
  have hmk : (m : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hmk1
  have hk1' : qs ≤ ((k1 : ℝ) + 1 / 2) * δ ^ 3 := by
    have := hqm1
    rw [e2] at this
    nlinarith
  exact hr_hardedge_decay hP hQ a b τ x qs (δ ^ 3) hqs h3 hτ hκ hturn hhM hhC kmax k1 hedge hedge0 hk1'
    (by omega) Y (fun k hk => hY k (by rw [Finset.mem_Icc] at hk ⊢; omega))

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah_hardedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_racah_hardedge

/-- **Bounded-window form with `(R)` discharged** (`Y = κ g [Ai + O(h)] + O(δⁿ)` on `X ≤ Z`): for every solution `Y` of the
closed-form recurrence on the whole chain `[J+1, k_max]` with the hard edge `ẽ(((k_max+1)h)²) = 0`, `((k_max+1)h)² ∈ Dom`, bounded
at one forbidden-side site `m ≤ k₁ ≤ N` by `|Y_{k₁}| ≤ δ^{-p}`, the matching sites are on the chain, `|Y_N|, |Y_{N+1}| ≤ δ^{-p}`
(the bound `(R)`), and `|Y_k - κ ψ_k| ≤ C δ³ |κ| W + δⁿ` on `[J, N+1] ∩ {X ≤ Z}`.  The single normalisation hypothesis is
`|Y_{k₁}| ≤ δ^{-p}` (see the module docstring); `κ` is not identified. -/
theorem discrete_airy_hahn_racah_hardedge_window {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ)
    (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 Z : ℝ) (hA0 : 0 < A0) (hZ : 0 ≤ Z)
    (n p : ℕ) :
    ∃ (r δ0 C W D : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < W ∧ 0 < D ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ qs ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ J ≤ -A0 ∧
        ∀ (kmax : ℕ) (k1 : ℤ) (Y : ℤ → ℝ),
          (((kmax : ℝ) + 1) * δ ^ 3) ^ 2 ∈ Dom P Q →
          etilde P Q ((((kmax : ℝ) + 1) * δ ^ 3) ^ 2) = 0 → m ≤ k1 → k1 ≤ N →
          (∀ k ∈ Finset.Icc (J + 1) (kmax : ℤ),
            jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          |Y k1| ≤ (δ ^ p)⁻¹ →
          N + 1 ≤ (kmax : ℤ) ∧ |Y N| ≤ (δ ^ p)⁻¹ ∧ |Y (N + 1)| ≤ (δ ^ p)⁻¹ ∧
          ∃ κ : ℝ, ∀ k ∈ Finset.Icc J (N + 1), turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ≤ Z →
            |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ k| ≤
              C * δ ^ 3 * |κ| * W + δ ^ n := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hrq, hδ0, hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah_hardedge hP hQ a b τ x qs hqs hτ hκ hα hβ hturn A0 hA0
  obtain ⟨δ1, hδ1, hδ11, Hw⟩ :=
    dal_conclusion_window C Cosc Ctop W Cmu ξ0 Z hC.le hCosc hCtop hCmu hξ0 hZ n p
  refine ⟨r, min δ0 δ1, C, W, D, hr, hrq, lt_min hδ0 hδ1, (min_le_left _ _).trans hδ01, hC, hW, hD, ?_⟩
  intro δ hδ hδδ
  obtain ⟨J, m, N, hJ1, hJm, hmN, hloc, hp1, hp2, hp3, hp4, hXJ, Hc, Hdec⟩ :=
    H δ hδ (hδδ.trans (min_le_left _ _))
  refine ⟨J, m, N, hJ1, hJm, hmN, hloc, hp1, hp2, hp3, hp4, hXJ, ?_⟩
  intro kmax k1 Y hedge hedge0 hmk1 hk1N hY hYk1
  obtain ⟨hN1, hdec⟩ := Hdec kmax k1 Y hedge hedge0 hmk1 hk1N hY
  have hYN : |Y N| ≤ (δ ^ p)⁻¹ := (hdec N hk1N (by omega)).trans hYk1
  have hYN1 : |Y (N + 1)| ≤ (δ ^ p)⁻¹ := (hdec (N + 1) (by omega) hN1).trans hYk1
  refine ⟨hN1, hYN, hYN1, ?_⟩
  exact Hw _ _ _ _ J m N δ hδ (hδδ.trans (min_le_right _ _)) hJm hmN Hc Y
    (fun k hk => hY k (by rw [Finset.mem_Icc] at hk ⊢; omega)) hYN hYN1

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah_hardedge_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_racah_hardedge_window

end FormalResearch.Special
