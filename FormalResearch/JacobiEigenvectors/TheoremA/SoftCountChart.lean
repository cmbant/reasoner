module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCount
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountHyps
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6

/-!
# Paper J, Layer 2 (L2.C7): the counting step on the soft chart (`soft_count_chart`)

Source: app_thmA, proof of prop:tha-W2, Step 6 (counting, *Order*) and the existence clause of item (3).

Proved here (axiom-pinned), under `SoftCountHyps CL CR Cs0` (the sign facts (ii), (iii) of Step 6) and the usual chart premises:
* `mu0_gap`: `cmu0 (b - a) <= mu_0(b) - mu_0(a)` on `[-delta_0, delta_0]` (`mu0_slope`, mean value theorem);
  `softMu0_strictAnti`: `X |-> mu_0(bandHi - X)` is strictly decreasing and continuous on `|X - bandHi| <= delta_0`.
* `muTilde_sub_le2`: `|mu-tilde - mu_0| <= (q/2) C_mu h^2` for `h <= 1`.
* `soft_count_chart`: the conjuncts (3) and the existence clause of `PropThaW2`: for an eigen-system obeying Step 0, every
  eigenvalue `X_i` with `|X_i - bandHi| <= delta_0` has `|mu-tilde(X_i) - (i + 1/2) h| <= Cc h^{m+1} Lm(h)` (label = index), and for every
  `k <= N` whose nominal point (`mu-tilde(X) = (k + 1/2) h`, `|X - bandHi| <= delta_0 / 2`) exists, the eigenvalue of index `k`
  exists and lies in `|X - bandHi| <= delta_0`.
  Inputs: `soft_window_label` (hypothesis (i) of `lem:tha-count`), `casD_zero_exists_eig`/`casD_eig_zero` (zero of `casD` = eigenvalue),
  `propThaCount` and `order_label_real` (through `count_label`), `bondA_pos_all` (positive bonds).

Differences from the paper: `Phi = pi mu_0`, `eps = pi h/8`, `I = {|X - bandHi| <= delta_0}` (see `SoftCountHyps`); the
threshold `h0` makes `Cs0 h^2 <= delta_0` (so that Step 0 puts every eigenvalue below `bandHi + delta_0`) and
`h/2 + K h^2 <= cmu0 delta_0 / 2` (so that the bracketing interval of an existing nominal point lies in `Phi(I)`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Chart

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- the quantitative slope of `mu_0` on `[-delta_0, delta_0]`. -/
lemma mu0_gap {p : Par × ℝ} (hp : p ∈ P) {a b : ℝ} (ha : -CL.δ0 ≤ a) (hb : b ≤ CL.δ0) (hab : a ≤ b) :
    CL.cmu0 * (b - a) ≤ CL.muS 0 p b - CL.muS 0 p a := by
  have hdiff : Differentiable ℝ (CL.muS 0 p) := (CL.mu0_deriv p hp).1.differentiable (by norm_num)
  have hD : Convex ℝ (Set.Icc (-CL.δ0) CL.δ0) := convex_Icc _ _
  have hδ := CL.consts_pos.1
  exact hD.mul_sub_le_image_sub_of_le_deriv (f := CL.muS 0 p) (C := CL.cmu0) hdiff.continuous.continuousOn
    hdiff.differentiableOn
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (CL.mu0_slope p hp x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)).1)
    a (Set.mem_Icc.mpr ⟨ha, by linarith⟩) b (Set.mem_Icc.mpr ⟨by linarith, hb⟩) hab

lemma softMu0_strictAnti {p : Par × ℝ} (hp : p ∈ P) :
    StrictAntiOn (softMu0 CL p) (Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0)) := by
  intro x hx y hy hxy
  have hc := CL.consts_pos5.1
  have := mu0_gap CL hp (a := Fz.bandHi p - y) (b := Fz.bandHi p - x) (by linarith [hy.2]) (by linarith [hx.1]) (by linarith)
  unfold softMu0
  nlinarith

lemma softMu0_continuousOn {p : Par × ℝ} (hp : p ∈ P) (s : Set ℝ) : ContinuousOn (softMu0 CL p) s := by
  have h1 : Continuous (CL.muS 0 p) := (CL.mu0_deriv p hp).1.continuous
  exact (h1.comp (continuous_const.sub continuous_id)).continuousOn

/-- `|mu-tilde - mu_0| <= (q/2) C_mu h^2` (`h <= 1`). -/
lemma muTilde_sub_le2 {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hh1 : Fz.step N ≤ 1) :
    |CL.muTilde p X N - CL.muS 0 p (Fz.bandHi p - X)| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
  have hh := SoftEdgeChart.step_pos (F := Fz) N
  have hα := CL.abs_alpha_le hX
  unfold SoftEdgeCore.muTilde
  rw [add_sub_cancel_left]
  have hterm : ∀ r ∈ Finset.Icc 1 (q / 2), |Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)| ≤ Fz.step N ^ 2 * CL.Cmu := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh.le _)]
    have h1 : Fz.step N ^ (2 * r) ≤ Fz.step N ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by omega)
    have h2 : |CL.muS r p (Fz.bandHi p - X)| ≤ CL.Cmu :=
      CL.muS_bd r (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hr).2⟩) p hp _ hα
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  calc |∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)|
      ≤ ∑ r ∈ Finset.Icc 1 (q / 2), |Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ 2 * CL.Cmu := Finset.sum_le_sum hterm
    _ = ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
      rw [Finset.sum_const, Nat.card_Icc]; simp; ring

end Chart

/-- the bracketing interval of an existing nominal point lies in `Phi(I)`. -/
lemma bracket_of_nominal {M : ℝ → ℝ} {c δ h K k cm x : ℝ} (hMc : ContinuousOn M (Set.Icc (c - δ) (c + δ)))
    (hδ : 0 ≤ δ) (hh : 0 < h) (hg1 : M x + cm * (δ / 2) ≤ M (c - δ)) (hg2 : M (c + δ) ≤ M x - cm * (δ / 2))
    (hx : |M x - ((k : ℝ) + 1 / 2) * h| ≤ K * h ^ 2) (hpar : h / 2 + K * h ^ 2 ≤ cm * (δ / 2)) :
    Set.Icc (Real.pi * h * k) (Real.pi * h * (k + 1)) ⊆ (fun X => Real.pi * M X) '' Set.Icc (c - δ) (c + δ) := by
  have hpi := Real.pi_pos
  have hab : c - δ ≤ c + δ := by linarith
  have hΦc : ContinuousOn (fun X => Real.pi * M X) (Set.Icc (c - δ) (c + δ)) := continuousOn_const.mul hMc
  refine Set.Subset.trans ?_ (intermediate_value_Icc' hab hΦc)
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  apply Set.Icc_subset_Icc
  · show Real.pi * M (c + δ) ≤ Real.pi * h * k
    have : M (c + δ) ≤ h * k := by nlinarith
    nlinarith
  · show Real.pi * h * (k + 1) ≤ Real.pi * M (c - δ)
    have : h * (k + 1) ≤ M (c - δ) := by nlinarith
    nlinarith

section Main

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

lemma abs_window_aux {a b j h : ℝ} (h1 : |a - b| ≤ h / 16) (h2 : |a - j| ≤ h / 16) : |b - j| ≤ h / 8 := by
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `Phi = pi mu_0`: the window of the nominal action is `h/8` wide, given the `h^2` and `Cw h^{m+1} Lm` bounds. -/
lemma soft_window_M {p : Par × ℝ} (hp : p ∈ P) {N : ℕ} (hs1 : Fz.step N ≤ 1) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0)
    {Cw : ℝ} {j : ℕ} (hKh : ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 ≤ Fz.step N / 16)
    (hCwb : Cw * Fz.step N ^ (m + 1) * Lm (Fz.step N) ≤ Fz.step N / 16)
    (hj : |CL.muTilde p X N - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Cw * Fz.step N ^ (m + 1) * Lm (Fz.step N)) :
    |softMu0 CL p X - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Fz.step N / 8 := by
  have h1 := muTilde_sub_le2 CL hp hX hs1 (N := N)
  exact abs_window_aux (h1.trans hKh) (hj.trans hCwb)

/-- the bracketing intervals of the nominal windows lie in `Phi(I)`. -/
lemma soft_bracket {p : Par × ℝ} (hp : p ∈ P) {N : ℕ} (hs1 : Fz.step N ≤ 1)
    (hpar : Fz.step N / 2 + ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 ≤ CL.cmu0 * (CL.δ0 / 2)) (k : ℕ)
    (hex : ∃ X, |X - Fz.bandHi p| ≤ CL.δ0 / 2 ∧ CL.muTilde p X N = ((k : ℝ) + 1 / 2) * Fz.step N) :
    Set.Icc (Real.pi * Fz.step N * k) (Real.pi * Fz.step N * (k + 1)) ⊆
      (fun X => Real.pi * softMu0 CL p X) '' Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := by
  obtain ⟨X, hX, hμ⟩ := hex
  have hδ := CL.consts_pos.1
  have hh := SoftEdgeChart.step_pos (F := Fz) N
  have hX' : |X - Fz.bandHi p| ≤ CL.δ0 := hX.trans (by linarith)
  have hxk : |softMu0 CL p X - ((k : ℝ) + 1 / 2) * Fz.step N| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
    have h1 := muTilde_sub_le2 CL hp hX' hs1 (N := N)
    rw [hμ] at h1
    rw [abs_sub_comm]
    exact h1
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  have hcm := CL.consts_pos5.1
  have hg1 : softMu0 CL p X + CL.cmu0 * (CL.δ0 / 2) ≤ softMu0 CL p (Fz.bandHi p - CL.δ0) := by
    have := mu0_gap CL hp (a := Fz.bandHi p - X) (b := CL.δ0) (by linarith) le_rfl (by linarith)
    have e : Fz.bandHi p - (Fz.bandHi p - CL.δ0) = CL.δ0 := by ring
    unfold softMu0
    rw [e]
    nlinarith
  have hg2 : softMu0 CL p (Fz.bandHi p + CL.δ0) ≤ softMu0 CL p X - CL.cmu0 * (CL.δ0 / 2) := by
    have := mu0_gap CL hp (a := -CL.δ0) (b := Fz.bandHi p - X) (by linarith) (by linarith) (by linarith)
    have e : Fz.bandHi p - (Fz.bandHi p + CL.δ0) = -CL.δ0 := by ring
    unfold softMu0
    rw [e]
    nlinarith
  exact bracket_of_nominal (softMu0_continuousOn CL hp _) hδ.le hh hg1 hg2 hxk hpar

/-- the counting step at a fixed `(p, N)`: all inputs are explicit facts. -/
lemma soft_count_fixed {p : Par × ℝ} (hp : p ∈ P) {N : ℕ} (hN1 : 1 ≤ N)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < Fz.bondA p N n)
    (σ σ' : ℝ) (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hsg : ∀ X : ℝ, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ, Real.pi * softMu0 CL p X = Real.pi * Fz.step N * k →
      SignType.sign (casD Fz p N X) = SignType.sign (σ * (-1) ^ k))
    (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (Fz.jacobiMat p N) Xs Um)
    (hsg' : ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ,
      |Real.pi * softMu0 CL p (Xs i) - Real.pi * Fz.step N * ((k : ℝ) + 1 / 2)| ≤ Real.pi * Fz.step N / 8 →
        ∀ κ' : ℝ, (∀ n ≤ N, pSol Fz p N (Xs i) n = κ' * qSol Fz p N (Xs i) (N - n)) →
          SignType.sign κ' = SignType.sign (σ' * (-1) ^ k))
    (hcap : ∀ i, Xs i ≤ Fz.bandHi p + CL.δ0)
    (hlab : ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∃ j : ℕ,
      |softMu0 CL p (Xs i) - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Fz.step N / 8)
    (hbr : ∀ k : ℕ, (∃ X, |X - Fz.bandHi p| ≤ CL.δ0 / 2 ∧ CL.muTilde p X N = ((k : ℝ) + 1 / 2) * Fz.step N) →
      Set.Icc (Real.pi * Fz.step N * k) (Real.pi * Fz.step N * (k + 1)) ⊆
        (fun X => Real.pi * softMu0 CL p X) '' Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0)) :
    (∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∀ j : ℕ,
      |softMu0 CL p (Xs i) - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Fz.step N / 8 → (i : ℕ) = j) ∧
    (∀ k : ℕ, (∃ X, |X - Fz.bandHi p| ≤ CL.δ0 / 2 ∧ CL.muTilde p X N = ((k : ℝ) + 1 / 2) * Fz.step N) →
      ∃ i : Fin (N + 1), (i : ℕ) = k ∧ |Xs i - Fz.bandHi p| ≤ CL.δ0) := by
  have hδ := CL.consts_pos.1
  have hcm := CL.consts_pos5.1
  have hI : ∀ x : ℝ, x ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) ↔ |x - Fz.bandHi p| ≤ CL.δ0 := fun x => by
    rw [abs_le, Set.mem_Icc]
    constructor
    · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hMend : softMu0 CL p (Fz.bandHi p + CL.δ0) ≤ 0 := by
    have := mu0_gap CL hp (a := -CL.δ0) (b := 0) (by linarith) hδ.le (by linarith)
    have e : Fz.bandHi p - (Fz.bandHi p + CL.δ0) = -CL.δ0 := by ring
    unfold softMu0
    rw [e]
    rw [CL.mu0_zero p hp] at this
    nlinarith
  obtain ⟨hA, hB⟩ := count_label Fz p N hN1 hpos (Fz.bandHi p) CL.δ0 (softMu0 CL p) (softMu0_continuousOn CL hp _)
    (softMu0_strictAnti CL hp) hMend
    ⟨σ, hσ, fun X hX k hk => hsg X ((hI X).mp hX) k hk⟩
    ⟨σ', hσ', fun X hX k h0 hw κ' hκ => by
      obtain ⟨i, rfl⟩ := casD_zero_exists_eig hpos hN1 h0 Xs Um hE
      exact hsg' i ((hI _).mp hX) k hw κ' hκ⟩
    Xs Um hE hcap (fun i hi => hlab i ((hI _).mp hi))
  refine ⟨fun i hi j hj => hA i ((hI _).mpr hi) j hj, ?_⟩
  intro k hex
  obtain ⟨i, hi, hik, -⟩ := hB k (hbr k hex)
  exact ⟨i, hik, (hI _).mp hi⟩

/-- **the counting step on the soft chart** (Step 6): label = index, and existence of the eigenvalue of every nominal window. -/
theorem soft_count_chart (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) (hS : SoftCountHyps CL CR Cs0) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) →
        (∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 →
          |(CL.muS 0 p (Fz.bandHi p - Xs i) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs i))
              - ((i : ℕ) + 1 / 2) * Fz.step N| ≤ Cc * Fz.step N ^ (m + 1) * Lm (Fz.step N)) ∧
        (∀ k : ℕ, k ≤ N → (∃ X, |X - Fz.bandHi p| ≤ CL.δ0 / 2 ∧
            CL.muS 0 p (Fz.bandHi p - X) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - X)
              = ((k : ℝ) + 1 / 2) * Fz.step N) →
          ∃ i : Fin (N + 1), (i : ℕ) = k ∧ |Xs i - Fz.bandHi p| ≤ CL.δ0) := by
  obtain ⟨h1S, h1Sp, HS⟩ := hS
  obtain ⟨Cw, hw0, hw0p, HW⟩ := soft_window_label CL CR hM hf hm hLm Cs0
  have hδ := CL.consts_pos.1
  have hcm := CL.consts_pos5.1
  have hCmu := CL.consts_pos2.1
  have hK : 0 ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu := mul_nonneg (Nat.cast_nonneg _) hCmu
  obtain ⟨hL0, hL0p, HLs⟩ := CL.Lm_small (1 / (16 * (|Cw| + 1))) (by positivity)
  have hLpos := Fz.L_pos
  obtain ⟨h0, h0p, h0le⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, h ≤ h0 → h ≤ h1S ∧ h ≤ hw0 ∧ h ≤ 1 ∧ h ≤ Fz.L / 2 ∧
      h ≤ CL.softH1 ∧ h ≤ CR.softH1 ∧ h ≤ CL.δ0 / (|Cs0| + 1) ∧ h ≤ hL0 ∧
      h ≤ 1 / (16 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1)) ∧
      h ≤ CL.cmu0 * CL.δ0 / (4 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1)) := by
    refine ⟨min h1S (min hw0 (min 1 (min (Fz.L / 2) (min CL.softH1 (min CR.softH1 (min (CL.δ0 / (|Cs0| + 1))
      (min hL0 (min (1 / (16 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1)))
        (CL.cmu0 * CL.δ0 / (4 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1))))))))))), ?_, fun h hh => by
        simpa only [le_min_iff] using hh⟩
    simp only [lt_min_iff]
    exact ⟨h1Sp, hw0p, one_pos, by positivity, CL.softH1_pos, CR.softH1_pos, by positivity, hL0p, by positivity,
      by positivity⟩
  refine ⟨Cw, h0, h0p, ?_⟩
  intro p hp N hN hstep Xs Um hE hs0
  obtain ⟨hs1S, hsw, hs1, hsL, hsH1, hsH1R, hsδ, hsL0, hsK1, hsK2⟩ := h0le _ hstep
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hN0 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by
    by_contra hc
    have hN0' : N = 0 := by omega
    subst hN0'
    have e : Fz.step 0 = Fz.L := by simp [SymbolFamily.step, FormalResearch.JB.stepSize]
    rw [e] at hsL
    linarith
  have hpos := bondA_pos_all CL CR hM hp (X := Fz.bandHi p) (by rw [sub_self, abs_zero]; exact hδ.le) hN0 hsH1 hsH1R
  have hCs : |Cs0| * Fz.step N ^ 2 ≤ CL.δ0 := by
    have h1 : Fz.step N * (|Cs0| + 1) ≤ CL.δ0 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < |Cs0| + 1)).mp hsδ
      linarith
    have h2 : Fz.step N ^ 2 ≤ Fz.step N := by nlinarith
    nlinarith [abs_nonneg Cs0]
  have hcap : ∀ i, Xs i ≤ Fz.bandHi p + CL.δ0 := fun i => by
    have := hs0 i
    have h3 : Cs0 * Fz.step N ^ 2 ≤ |Cs0| * Fz.step N ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    linarith
  have hCwb : Cw * Fz.step N ^ (m + 1) * Lm (Fz.step N) ≤ Fz.step N / 16 := by
    have hLm1 : 1 ≤ Lm (Fz.step N) := hLm _ hh hs1
    have h_a : Fz.step N ^ (m + 1) ≤ Fz.step N ^ 2 := pow_le_pow_of_le_one hh.le hs1 (by omega)
    have h_b : Fz.step N * Lm (Fz.step N) ≤ 1 / (16 * (|Cw| + 1)) := HLs _ hh hsL0
    have h_c : |Cw| * (1 / (16 * (|Cw| + 1))) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cw]
    calc Cw * Fz.step N ^ (m + 1) * Lm (Fz.step N) ≤ |Cw| * (Fz.step N ^ (m + 1) * Lm (Fz.step N)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cw| * (Fz.step N * (Fz.step N * Lm (Fz.step N))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc Fz.step N ^ (m + 1) * Lm (Fz.step N) ≤ Fz.step N ^ 2 * Lm (Fz.step N) :=
                mul_le_mul_of_nonneg_right h_a (by linarith)
            _ = Fz.step N * (Fz.step N * Lm (Fz.step N)) := by ring
      _ ≤ |Cw| * (Fz.step N * (1 / (16 * (|Cw| + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left h_b hh.le
      _ = Fz.step N * (|Cw| * (1 / (16 * (|Cw| + 1)))) := by ring
      _ ≤ Fz.step N * (1 / 16) := mul_le_mul_of_nonneg_left h_c hh.le
      _ = Fz.step N / 16 := by ring
  have hKh : ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 ≤ Fz.step N / 16 := by
    set K : ℝ := ((q / 2 : ℕ) : ℝ) * CL.Cmu with hKdef
    have h1 : Fz.step N * (16 * (K + 1)) ≤ 1 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (K + 1))).mp hsK1
      linarith
    have h2 : K * Fz.step N ≤ 1 / 16 := by nlinarith
    nlinarith
  have hpar : Fz.step N / 2 + ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 ≤ CL.cmu0 * (CL.δ0 / 2) := by
    set K : ℝ := ((q / 2 : ℕ) : ℝ) * CL.Cmu with hKdef
    have h1 : Fz.step N * (4 * (K + 1)) ≤ CL.cmu0 * CL.δ0 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (K + 1))).mp hsK2
      linarith
    have h2 : K * Fz.step N ^ 2 ≤ K * Fz.step N := by
      nlinarith [mul_nonneg (mul_nonneg hK hh.le) (sub_nonneg.2 hs1)]
    nlinarith
  obtain ⟨⟨σ, hσ, hsg⟩, ⟨σ', hσ', hsg'⟩⟩ := HS p hp N hN hs1S
  have hlab : ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∃ j : ℕ,
      |CL.muTilde p (Xs i) N - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Cw * Fz.step N ^ (m + 1) * Lm (Fz.step N) := by
    intro i hi
    obtain ⟨-, j, hj⟩ := HW p hp N hN hsw Xs Um hE hs0 i hi
    exact ⟨j, hj⟩
  obtain ⟨hA, hB⟩ := soft_count_fixed CL hp hN1 hpos σ σ' hσ hσ' hsg Xs Um hE (fun i hi k hw κ' hκ => hsg' Xs Um hE hs0 i hi k hw κ' hκ)
    hcap (fun i hi => by
      obtain ⟨j, hj⟩ := hlab i hi
      exact ⟨j, soft_window_M CL hp hs1 hi hKh hCwb hj⟩)
    (fun k hex => soft_bracket CL hp hs1 hpar k hex)
  refine ⟨fun i hi => ?_, fun k _ hex => hB k hex⟩
  obtain ⟨j, hj⟩ := hlab i hi
  have hij := hA i hi j (soft_window_M CL hp hs1 hi hKh hCwb hj)
  rw [hij]
  exact hj

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_count_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_count_chart

end FormalResearch.JacobiEigenvectors.TheoremA

end
