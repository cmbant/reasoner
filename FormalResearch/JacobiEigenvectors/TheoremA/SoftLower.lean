module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftPC
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftGrowth

/-!
# Paper J, Layer 2 (L2.C6, R4): the lower half of `|lambda_L| ~ lambda kappa_bal`

Source: Paper J `app_thmA.tex` Step 3, "(S3) bounds `|(M_1)_{11}|` above; it is also bounded below": (i) the Weber sequence is `>= c E M` and grows by `r_W >= 1 + gamma/2` (`eq:tha-S4grow`), (ii) the dominant member of
the first PC pair has `r_2 <= 1 + C h`, (iii) the Casoratian of the PC pair is `asymp omega_*` and its first member is `<= C E M`, hence
`|W_{j_1}(psi-hat^{Web}, psi-hat^{(2)})| >= (gamma/2) a_{j_1} |psi-hat^{Web}_{j_1} psi-hat^{(2)}_{j_1}| >= c omega_*`.

## Proved here

* `A_ne_zero_rows`: the bonds `A_n` of the chain do not vanish on `0 <= n < N_R` (`(S1)` of the three patches).
* `soft_patch1_err`: the engine bound for patch 1 on the two rows `j_1, j_1 + 1` of the overlap, for an exact solution with the Weber seed.
* `soft_f_growth`: `|f_{j_1}| >= c_3 E` and `|f_{j_1+1}| >= (1 + C_2 h) |f_{j_1}| + (gamma/2) c_3 E` for the Weber comparison sequence `f = phi^{(1)}_1`, `E = lambda W M`.
* `soft_lamL_lower`: there are `c_lam, h_0 > 0` with `c_lam lambda kappa_bal <= |lambda_L|` for `h <= h_0`, uniformly in `(p, X, N)`.

## Differences from the paper

* The paper's `r_W >= 1 + gamma/2` is obtained here from the growth of the **exact** solution `psi` (`growth_ratio`) and the engine bound for patch 1 on the rows `j_1, j_1 + 1` (rescaled chain), rather than from the corrector
  bound of `phi^{(1)}_1` alone.  The exact solution is constructed (`exists_seeded`), as the paper's `psi^L`.
* The comparison `M_{j_1+1} <= C_M M_{j_1}` ("`M^2_Web ~ h^{1/2}` there") and the dominant-member ratio `r_2 <= 1 + C_2 h` are chart fields (`ratioM`, `ratio2`).
* `|g_{j_1}|` is **not** bounded below separately: the quotient `|cas(phi^{(1)}_1, phi^{(2)}_2)| / |cas(phi^{(1)}_2, phi^{(2)}_2)|` is bounded below directly, the factor `|g_{j_1}| a_{j_1}` cancelling.

## Not formalised

The derivation of the chart fields `grow_gap`, `collar_lbW`, `ratio2`, `ratioM` from the geometry and the special-function facts.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-- the real algebra of the growth of the Weber comparison sequence across the overlap bond. -/
lemma f1_lower {γ c E eps K C2h a0 a1 p0 p1 : ℝ} (hγ : 0 < γ) (hE : 0 < E) (hsmall : eps * (1 + γ + K) * E ≤ γ * c / 4 * E)
    (hC : C2h ≤ γ / 4) (hc : c * E ≤ a0) (hp0 : a0 - eps * E ≤ p0) (hp1 : p1 - eps * K * E ≤ a1)
    (hgr : (1 + γ) * p0 ≤ p1) (ha0 : 0 ≤ a0) (hc0 : 0 ≤ c) :
    (1 + C2h) * a0 + γ / 2 * c * E ≤ a1 := by
  have hmul1 : (1 + γ) * (a0 - eps * E) ≤ (1 + γ) * p0 := mul_le_mul_of_nonneg_left hp0 (by linarith)
  have hmul2 : 0 ≤ a0 * (γ / 4 - C2h) := mul_nonneg ha0 (by linarith)
  have hmul3 : γ / 4 * (c * E) ≤ γ / 4 * a0 := mul_le_mul_of_nonneg_left hc (by linarith)
  have hA : (1 + γ) * a0 - eps * (1 + γ + K) * E ≤ a1 := by linarith
  have hB : (1 + C2h) * a0 + γ / 2 * c * E ≤ (1 + γ) * a0 - eps * (1 + γ + K) * E := by
    have e1 : (1 + γ) * a0 - (1 + C2h) * a0 = (γ - C2h) * a0 := by ring
    have : γ / 2 * c * E + eps * (1 + γ + K) * E ≤ (γ - C2h) * a0 := by
      have e2 : (γ - C2h) * a0 = 3 * γ / 4 * a0 + a0 * (γ / 4 - C2h) := by ring
      have e3 : γ / 2 * c * E = γ / 2 * (c * E) := by ring
      linarith
    linarith
  linarith

lemma c2h_le {C2 γ h : ℝ} (hC2 : 0 ≤ C2) (hγ : 0 < γ) (hh : h ≤ γ / (4 * (C2 + 1))) : C2 * h ≤ γ / 4 := by
  have h1 := mul_le_mul_of_nonneg_left hh hC2
  have h2 : C2 * (γ / (4 * (C2 + 1))) ≤ γ / 4 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

lemma c2h_le_one {C2 h : ℝ} (hC2 : 0 ≤ C2) (hh : h ≤ 1 / (C2 + 1)) : C2 * h ≤ 1 := by
  have h1 := mul_le_mul_of_nonneg_left hh hC2
  have h2 : C2 * (1 / (C2 + 1)) ≤ 1 := by
    rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]
    linarith
  linarith

section Lower

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the bonds of the chain do not vanish on `0 <= n < N_R`. -/
lemma A_ne_zero_rows {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    (hh : Fz.step N ≤ C.softH1) {lam : ℝ} (hV : ((C.chain p X N).rescale1 lam).PreValid C.cs (Fz.step N) m) :
    ∀ n : ℤ, 0 ≤ n → n < (C.chain p X N).NR → (C.chain p X N).A n ≠ 0 := by
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hh hV
  have hP3' : ((C.chain p X N).rescale1 lam).P = 3 := hP3
  have hjl : (C.chain p X N).jj 3 = (C.chain p X N).NR - 1 := by
    have := hV.jj_last
    change (C.chain p X N).jj (C.chain p X N).P = (C.chain p X N).NR - 1 at this
    rw [hP3] at this; exact this
  have hjj0 : (C.chain p X N).jj 0 = 0 := hV.jj0
  have hj23 : (C.chain p X N).jj 2 < (C.chain p X N).jj 3 := hV.jj_mono 2 (by rw [hP3']; norm_num)
  intro n hn0 hnN
  by_cases h1 : n ≤ (C.chain p X N).jj 1
  · exact hV.A_ne_zero (p := 1) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := n)
      (mem_Icc.mpr ⟨by show (C.chain p X N).jj (1 - 1) ≤ n; rw [show (1 - 1 : ℕ) = 0 from rfl, hjj0]; exact hn0, h1⟩)
  · by_cases h2 : n ≤ (C.chain p X N).jj 2
    · exact hV.A_ne_zero (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := n)
        (mem_Icc.mpr ⟨by show (C.chain p X N).jj (2 - 1) ≤ n; simp only [show (2 - 1 : ℕ) = 1 from rfl]; omega, h2⟩)
    · exact hV.A_ne_zero (p := 3) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']⟩) (j := n)
        (mem_Icc.mpr ⟨by show (C.chain p X N).jj (3 - 1) ≤ n; simp only [show (3 - 1 : ℕ) = 2 from rfl]; omega, by show n ≤ (C.chain p X N).jj 3; omega⟩)

lemma psiHat_one' (D : LadderData) (h : ℝ) (j : ℤ) : D.psiHat h 1 j = D.phi h 0 1 j := by
  unfold LadderData.psiHat Engine.psiHat
  rw [cvec_one]
  simp

/-- **the engine bound for patch 1 on the overlap rows `j_1, j_1 + 1`** for an exact solution with the Weber seed (chain weights, `lambda` times the engine constant). -/
lemma soft_patch1_err {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hstep : Fz.step N ≤ min (softH0 C) C.softH1)
    {ψ : ℤ → ℝ} (hJ : JacSol Fz p N X (C.chain p X N).NR ψ) (hseed0 : ψ 0 = C.psiHatL p X N 0)
    {k : ℤ} (hk : k = (C.chain p X N).jj 1 ∨ k = (C.chain p X N).jj 1 + 1) :
    |ψ k - (C.chain p X N).phi (Fz.step N) 0 1 k| ≤
      softLam C p X N * (softC C 3 * (Fz.step N ^ m * Lm (Fz.step N))) * ((C.chain p X N).W k * (C.chain p X N).M k) := by
  have hstep0 : Fz.step N ≤ softH0 C := hstep.trans (min_le_left _ _)
  have hstep1 : Fz.step N ≤ C.softH1 := hstep.trans (min_le_right _ _)
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid C.csT (Fz.step N) m := C.soft_valid hf hp hX hN hstep1 hVpre
  obtain ⟨hP3, hs0, -⟩ := C.shape p hp X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, -⟩ := C.soft_pos hp hX hN hstep1 hVpre
  have hθ : (C.chain p X N).theta (Fz.step N) ≤ C.Csum * Lm (Fz.step N) := C.theta_le p hp X hX N hN
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hstep1' : Fz.step N ≤ 1 := hstep0.trans (softH0_le_one C)
  have hsmall := soft_small C hm hstep_pos hstep0 hθ
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  have hsol := sol_chain_rows (C.chain p X N) hs0 (C.A_bond p hp X hX N hN) (C.Q_diag p hp X hX N hN) le_rfl hJ
  have hseed : ∀ j ∈ Icc (0 : ℤ) (C.chain p X N).s0, ψ j = (C.chain p X N).phi (Fz.step N) 0 1 j := by
    intro j hj
    rw [hs0] at hj
    have hj0' : j = 0 := by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      omega
    subst hj0'
    rw [hseed0, psiHatL_of_le C p X N (uNode_zero_le C hp (le_trans hstep0 (softH0_le_eta C))),
      chain_phi_one_eq C hp hX hN]
  have hst := LadderData.stability_rescale1 (C.chain p X N) C.csT (Fz.step N) m (softLam C p X N) hlam.ne' hV ψ hsol hseed hsmall
  obtain ⟨c1, -, -⟩ := hst
  have hp1 : 1 ∈ Icc 1 (C.chain p X N).P := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hkw : k ∈ Icc (eqLo (C.chain p X N).s0 (C.chain p X N).jj 1) ((C.chain p X N).jj 1 + 1) := by
    have : eqLo (C.chain p X N).s0 (C.chain p X N).jj 1 = 0 := by unfold eqLo; simp [hs0]
    rw [this]
    rcases hk with rfl | rfl
    · exact mem_Icc.mpr ⟨hj0, by omega⟩
    · exact mem_Icc.mpr ⟨by omega, le_rfl⟩
  have h1 := c1 1 hp1 k hkw
  rw [psiHat_one', hP3, abs_of_pos hlam] at h1
  refine le_trans h1 ?_
  have hBT := soft_engine_le C 3 hstep_pos hstep1' hθ
  have hkm : 0 ≤ k ∧ k ≤ (C.chain p X N).NR := by rcases hk with rfl | rfl <;> omega
  have hW := hV.W_pos k (mem_Icc.mpr hkm)
  have hM := hV.M_pos k (mem_Icc.mpr hkm)
  have hWM : 0 ≤ (C.chain p X N).W k * (C.chain p X N).M k := mul_nonneg hW.le hM.le
  calc softLam C p X N * (mvC C.cs.cm C.cs.CE (softK C) C.softLamC 3 * (2 * C.cs.KD * C.cs.Kw * Fz.step N ^ m * (C.chain p X N).theta (Fz.step N))
          * (C.chain p X N).W k * (C.chain p X N).M k)
      = softLam C p X N * ((mvC C.cs.cm C.cs.CE (softK C) C.softLamC 3 * (2 * C.cs.KD * C.cs.Kw * Fz.step N ^ m * (C.chain p X N).theta (Fz.step N)))
          * ((C.chain p X N).W k * (C.chain p X N).M k)) := by ring
    _ ≤ softLam C p X N * ((softC C 3 * (Fz.step N ^ m * Lm (Fz.step N))) * ((C.chain p X N).W k * (C.chain p X N).M k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBT hWM) hlam.le
    _ = _ := by ring

/-- the growth rate `gamma = nu_1 / (C_A + 1)` of the exact solution on the left forbidden side. -/
def softGam : ℝ := C.nu1 / (C.CA + 1)

lemma softGam_pos : 0 < softGam C := by
  obtain ⟨hCA, hnu, -⟩ := C.consts_pos3
  unfold softGam
  positivity

/-- the smallness level `(gamma c_3 / 4) / (softC_3 (1 + gamma + C_w C_M) + 1)` for `h Lm(h)`. -/
def softEε : ℝ := (softGam C * C.c3W / 4) / (softC C 3 * (1 + softGam C + C.tCw * C.CM) + 1)

lemma softEε_pos : 0 < softEε C := by
  have h3 := C.consts_pos3
  have := softC_nonneg C 3
  have := softGam_pos C
  have hCw : 0 < C.tCw := Real.exp_pos _
  unfold softEε
  have := h3.2.2.1; have := h3.2.2.2.2
  positivity

/-- the smallness `softC_3 h^m Lm(h) (1 + gamma + C_w C_M) <= gamma c_3 / 4`: `h <= h_1(softEε)`. -/
def softHε : ℝ := softHL C (softEε C)

lemma softHε_pos : 0 < softHε C := softHL_pos C _

/-- the smallness threshold of `soft_lamL_lower`. -/
def softH3 : ℝ :=
  min (min (softH0 C) C.softH1) (min (softHε C) (min (softGam C / (4 * (C.C2 + 1))) (1 / (C.C2 + 1))))

lemma softH3_pos : 0 < softH3 C := by
  have h3 := C.consts_pos3
  have hC2 := h3.2.2.2.1
  unfold softH3
  exact lt_min (lt_min (softH0_pos C) C.softH1_pos) (lt_min (softHε_pos C) (lt_min (by have := softGam_pos C; positivity) (by positivity)))

lemma final_quot {c lam κ A gg θ Y Nn Dn : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hc : 0 ≤ c) (hDpos : 0 < Dn)
    (hnum : A * (gg * θ) ≤ Nn) (hY : Dn ≤ A * (gg * Y)) (hθ : c * lam * Y = θ) (hA : 0 ≤ A) (hgg : 0 ≤ gg) :
    c * (lam * κ) ≤ κ * (Nn / Dn) := by
  have h1 : c * lam * Dn ≤ Nn := by
    calc c * lam * Dn ≤ c * lam * (A * (gg * Y)) := mul_le_mul_of_nonneg_left hY (by positivity)
      _ = A * (gg * (c * lam * Y)) := by ring
      _ = A * (gg * θ) := by rw [hθ]
      _ ≤ Nn := hnum
  have h2 : c * lam ≤ Nn / Dn := by rw [le_div_iff₀ hDpos]; exact h1
  calc c * (lam * κ) = κ * (c * lam) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hκ.le

/-- the real algebra of the Casoratian quotient. -/
lemma cas_quot_lower {A f0 f1 g0 g1 u0 u1 ρ θ K Kp w Cr R : ℝ} (hA : 0 < A) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2)
    (hr2 : |g1| ≤ ρ * |g0|) (hf : ρ * |f0| + θ ≤ |f1|) (hu0 : |u0| ≤ K * w) (hu1 : |u1| ≤ K * (Cr * w))
    (hK : 0 ≤ K) (hKp : K ≤ Kp) (hw : 0 < w) (hR : R = Cr + 2) (hCr : 0 ≤ Cr) (hD : u0 * g1 - g0 * u1 ≠ 0) :
    A * (|g0| * θ) ≤ |A * (f1 * g0 - f0 * g1)| ∧ |A * (u1 * g0 - u0 * g1)| ≤ A * (|g0| * (Kp * w * R)) ∧
      0 < |A * (u1 * g0 - u0 * g1)| := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : |f1| * |g0| - |f0| * |g1| ≤ |f1 * g0 - f0 * g1| := by
      have := abs_sub_abs_le_abs_sub (f1 * g0) (f0 * g1)
      rwa [abs_mul, abs_mul] at this
    have h2 : |f0| * |g1| ≤ |f0| * (ρ * |g0|) := mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
    have h3 := mul_le_mul_of_nonneg_right hf (abs_nonneg g0)
    have h4 : |g0| * θ ≤ |f1 * g0 - f0 * g1| := by linarith
    rw [abs_mul, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left h4 hA.le
  · have h1 : |u1 * g0 - u0 * g1| ≤ |u1| * |g0| + |u0| * |g1| := by
      calc |u1 * g0 - u0 * g1| ≤ |u1 * g0| + |u0 * g1| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul]
    have h2 : |u1| * |g0| ≤ K * (Cr * w) * |g0| := mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
    have h3 : |u0| * |g1| ≤ K * w * (2 * |g0|) := by
      refine mul_le_mul hu0 ?_ (abs_nonneg _) (by positivity)
      calc |g1| ≤ ρ * |g0| := hr2
        _ ≤ 2 * |g0| := mul_le_mul_of_nonneg_right hρ (abs_nonneg _)
    have e : K * (Cr * w) * |g0| + K * w * (2 * |g0|) = |g0| * (K * w * R) := by rw [hR]; ring
    have h5 : |g0| * (K * w * R) ≤ |g0| * (Kp * w * R) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hR0 : 0 ≤ R := by rw [hR]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKp hw.le) hR0
    have h4 : |u1 * g0 - u0 * g1| ≤ |g0| * (Kp * w * R) := by linarith
    have : |A * (u1 * g0 - u0 * g1)| = A * |u1 * g0 - u0 * g1| := by rw [abs_mul, abs_of_pos hA]
    rw [this]
    exact mul_le_mul_of_nonneg_left h4 hA.le
  · refine abs_pos.mpr (mul_ne_zero hA.ne' ?_)
    intro h0
    apply hD
    linarith

/-- **the Weber comparison sequence grows across the overlap bond** (`app_thmA` Step 3 (i)): `|f_{j_1}| >= c_3 E` and `|f_{j_1+1}| >= (1 + C_2 h) |f_{j_1}| + (gamma/2) c_3 E`,
`E = lambda W_{j_1} M_{j_1}`, `f = phi^{(1)}_1`.  (The exact solution `psi` of `eq:tha-S4grow` is constructed here.) -/
theorem soft_f_growth {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hstep : Fz.step N ≤ softH3 C) :
    C.c3W * (softLam C p X N * ((C.chain p X N).W ((C.chain p X N).jj 1) * (C.chain p X N).M ((C.chain p X N).jj 1)))
        ≤ |(C.chain p X N).phi (Fz.step N) 0 1 ((C.chain p X N).jj 1)| ∧
      (1 + C.C2 * Fz.step N) * |(C.chain p X N).phi (Fz.step N) 0 1 ((C.chain p X N).jj 1)|
        + softGam C / 2 * C.c3W * (softLam C p X N * ((C.chain p X N).W ((C.chain p X N).jj 1) * (C.chain p X N).M ((C.chain p X N).jj 1)))
        ≤ |(C.chain p X N).phi (Fz.step N) 0 1 ((C.chain p X N).jj 1 + 1)| := by
  obtain ⟨hCA, hnu, hc3, hC2, hCM⟩ := C.consts_pos3
  have hK0 := softK_nonneg C
  have hCε := softC_nonneg C 3
  have hCw : 0 < C.tCw := Real.exp_pos _
  set γ : ℝ := softGam C with hγdef
  have hγ : 0 < γ := softGam_pos C
  set Dε : ℝ := softC C 3 * (1 + γ + C.tCw * C.CM) + 1 with hDεdef
  have hDε : 0 < Dε := by positivity
  have hstepA : Fz.step N ≤ min (softH0 C) C.softH1 := hstep.trans (min_le_left _ _)
  have hstepE : Fz.step N ≤ softHε C := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hstepC : Fz.step N ≤ γ / (4 * (C.C2 + 1)) := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hstepC1 : Fz.step N ≤ 1 / (C.C2 + 1) := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hstep0 : Fz.step N ≤ softH0 C := hstepA.trans (min_le_left _ _)
  have hstep1 : Fz.step N ≤ C.softH1 := hstepA.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hstep1.trans C.softH1_le_one
  have hhη : Fz.step N ≤ C.η / 2 := hstep1.trans C.softH1_le_eta
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid C.csT (Fz.step N) m := C.soft_valid hf hp hX hN hstep1 hVpre
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hstep1 hVpre
  obtain ⟨-, hs0, -⟩ := C.shape p hp X hX N hN
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  have hκ := kappaBal_pos (C.aOf p X N)
  have hη := C.consts_pos.2.1
  have hArows := A_ne_zero_rows C hp hX hN hstep1 hVpre
  have hAeq := C.A_bond p hp X hX N hN
  have hjNR : (C.chain p X N).jj 1 < (C.chain p X N).NR := by omega
  -- the bonds on `0 <= n <= j_1`
  have hApos : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chain p X N).jj 1 → 0 < Fz.bondA p N n := by
    intro n hn0 hn1
    have hne := hArows n hn0 (by omega)
    rw [hAeq n (mem_Icc.mpr ⟨by omega, by omega⟩)] at hne
    exact lt_of_le_of_ne (bondA_nonneg' Fz p N n) (Ne.symm hne)
  have hAle : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chain p X N).jj 1 → Fz.bondA p N n ≤ C.CA + 1 := fun n _ _ => by
    linarith [C.bondA_le p hp N hN n]
  have hgap : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chain p X N).jj 1 →
      Fz.bondA p N n + Fz.bondA p N (n - 1) + C.nu1 ≤ Fz.diagQ p N X n := by
    intro n hn0 hn1
    refine C.grow_gap p hp X hX N hN n hn0 ?_
    have : uNode (Fz.step N) n ≤ uNode (Fz.step N) ((C.chain p X N).jj 1) := SoftEdgeChart.uNode_mono_le hh0.le hn1
    linarith
  -- the seed and the exact solution
  have hseedpos := C.seed_posW p hp X hX N hN
  have hu0 : uNode (Fz.step N) 0 ≤ C.uc p - C.η / 2 := uNode_zero_le C hp (hstep0.trans (softH0_le_eta C))
  have hs : C.psiHatL p X N 0 = (C.chain p X N).phi (Fz.step N) 0 1 0 := by
    rw [psiHatL_of_le C p X N hu0, chain_phi_one_eq C hp hX hN]
  have hs' : 0 < C.psiHatL p X N 0 := by
    rw [psiHatL_of_le C p X N hu0]; exact hseedpos
  obtain ⟨ψ, hψ0, hψsol⟩ := exists_seeded (Fz.bondA p N) (Fz.diagQ p N X) (C.chain p X N).NR
    (fun n hn0 hnN => by
      have hne := hArows n hn0 hnN
      rwa [hAeq n (mem_Icc.mpr ⟨by omega, by omega⟩)] at hne) (C.psiHatL p X N 0)
  have hJ : JacSol Fz p N X (C.chain p X N).NR ψ := hψsol
  have hA0 : Fz.bondA p N (-1) = 0 := by
    unfold SymbolFamily.bondA
    rw [if_neg (by omega)]
  have hgr := growth_ratio (Fz.bondA p N) (Fz.diagQ p N X) ψ ((C.chain p X N).jj 1) (C.CA + 1) C.nu1 hA0 hApos hAle hnu hgap
    (fun n hn0 hn1 => hψsol n hn0 (by omega)) (by rw [hψ0]; exact hs')
  obtain ⟨hψj, hψj1⟩ := hgr ((C.chain p X N).jj 1) hj0 le_rfl
  -- the errors
  have e0 := soft_patch1_err C hf hm hp hX hN hstepA hJ hψ0 (k := (C.chain p X N).jj 1) (Or.inl rfl)
  have e1 := soft_patch1_err C hf hm hp hX hN hstepA hJ hψ0 (k := (C.chain p X N).jj 1 + 1) (Or.inr rfl)
  set j := (C.chain p X N).jj 1 with hjdef
  have hjmem : j ∈ Icc (0 : ℤ) (C.chain p X N).NR := mem_Icc.mpr ⟨hj0, by omega⟩
  have hj1mem : j + 1 ∈ Icc (0 : ℤ) (C.chain p X N).NR := mem_Icc.mpr ⟨by omega, by omega⟩
  have hW0 : 0 < (C.chain p X N).W j := hV.W_pos j hjmem
  have hW1 : 0 < (C.chain p X N).W (j + 1) := hV.W_pos (j + 1) hj1mem
  have hM0 : 0 < (C.chain p X N).M j := hV.M_pos j hjmem
  have hM1 : 0 < (C.chain p X N).M (j + 1) := hV.M_pos (j + 1) hj1mem
  have hwr : (C.chain p X N).W (j + 1) ≤ C.tCw * (C.chain p X N).W j := C.soft_Wratio hp hX hN hstep1 hVpre
  have hmr : (C.chain p X N).M (j + 1) ≤ C.CM * (C.chain p X N).M j := C.ratioM p hp X hX N hN
  have hWM1 : (C.chain p X N).W (j + 1) * (C.chain p X N).M (j + 1) ≤ C.tCw * C.CM * ((C.chain p X N).W j * (C.chain p X N).M j) := by
    calc _ ≤ (C.tCw * (C.chain p X N).W j) * (C.CM * (C.chain p X N).M j) := mul_le_mul hwr hmr hM1.le (by positivity)
      _ = _ := by ring
  have hWM0 : 0 < (C.chain p X N).W j * (C.chain p X N).M j := mul_pos hW0 hM0
  set lam := softLam C p X N with hlamdef
  set E : ℝ := lam * ((C.chain p X N).W j * (C.chain p X N).M j) with hEdef
  have hEpos : 0 < E := mul_pos hlam hWM0
  -- the lower bound of the Weber comparison sequence at `j_1`
  obtain ⟨-, -, hNW0, hNWu, hNWv⟩ := C.shapeW p hp X hX N hN
  have hjuW : uNode (Fz.step N) j ≤ C.uc p - C.η / 2 := by linarith
  have hjW : j ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR := by
    refine mem_Icc.mpr ⟨hj0, ?_⟩
    by_contra hcon
    have : uNode (Fz.step N) ((C.chainW p X N).NR + 1) ≤ uNode (Fz.step N) j := SoftEdgeChart.uNode_mono_le hh0.le (by omega)
    linarith
  have hWj : (C.chain p X N).W j = softEnvWebW C p X N j / lam := chain_W_one C hp hX hN (mem_Icc.mpr ⟨hj0, le_rfl⟩)
  have hMj := C.M1_def p hp X hX N hN j (mem_Icc.mpr ⟨hj0, le_rfl⟩)
  have hWw := C.W_defW p hp X hX N hN j hjW
  have hMw := C.M_defW p hp X hX N hN j hjW
  have hEeq : E = (C.chainW p X N).W j * (C.chainW p X N).M j := by
    rw [hEdef, hWj, hMj, hWw, hMw]
    unfold softEnvWebW
    field_simp
  have hflow : C.c3W * E ≤ |(C.chain p X N).phi (Fz.step N) 0 1 j| := by
    have := C.collar_lbW p hp X hX N hN j hjW hjuW
    rw [chain_phi_one_eq C hp hX hN, hEeq, ← mul_assoc]
    exact this
  -- the Weber sequence grows across the overlap bond
  set f0 := (C.chain p X N).phi (Fz.step N) 0 1 j with hf0def
  set f1 := (C.chain p X N).phi (Fz.step N) 0 1 (j + 1) with hf1def
  set ε' : ℝ := softC C 3 * (Fz.step N ^ m * Lm (Fz.step N)) with hε'def
  have e0' : |ψ j - f0| ≤ ε' * E := by
    refine le_trans e0 (le_of_eq ?_)
    rw [hEdef]; ring
  have e1' : |ψ (j + 1) - f1| ≤ ε' * (C.tCw * C.CM) * E := by
    refine le_trans e1 ?_
    have hε0 : 0 ≤ ε' := mul_nonneg hCε (powLm_nonneg C hh0 hh1)
    calc lam * ε' * ((C.chain p X N).W (j + 1) * (C.chain p X N).M (j + 1))
        ≤ lam * ε' * (C.tCw * C.CM * ((C.chain p X N).W j * (C.chain p X N).M j)) :=
          mul_le_mul_of_nonneg_left hWM1 (mul_nonneg hlam.le hε0)
      _ = _ := by rw [hEdef]; ring
  have hε'0 : 0 ≤ ε' := mul_nonneg hCε (powLm_nonneg C hh0 hh1)
  have hεt : Fz.step N * Lm (Fz.step N) ≤ softEε C := softHL_spec C (softEε_pos C) hh0 hstepE
  have hε'le : ε' ≤ softC C 3 * softEε C :=
    mul_le_mul_of_nonneg_left ((pow_Lm_le C hm hh0 hh1).trans hεt) hCε
  have hsmallε : ε' * (1 + γ + C.tCw * C.CM) ≤ γ * C.c3W / 4 := by
    have h1 : softC C 3 * (1 + γ + C.tCw * C.CM) ≤ Dε := by rw [hDεdef]; linarith
    have h2 : softEε C * Dε = γ * C.c3W / 4 := by
      have : softEε C = (γ * C.c3W / 4) / Dε := rfl
      rw [this, div_mul_cancel₀ _ hDε.ne']
    have hpos : 0 ≤ 1 + γ + C.tCw * C.CM := by positivity
    have hEε := softEε_pos C
    calc ε' * (1 + γ + C.tCw * C.CM) ≤ (softC C 3 * softEε C) * (1 + γ + C.tCw * C.CM) :=
          mul_le_mul_of_nonneg_right hε'le hpos
      _ = softEε C * (softC C 3 * (1 + γ + C.tCw * C.CM)) := by ring
      _ ≤ softEε C * Dε := mul_le_mul_of_nonneg_left h1 hEε.le
      _ = _ := h2
  have hC2h : C.C2 * Fz.step N ≤ γ / 4 := c2h_le hC2 hγ hstepC
  have hC2h1 : C.C2 * Fz.step N ≤ 1 := c2h_le_one hC2 hstepC1
  have hf1lb : (1 + C.C2 * Fz.step N) * |f0| + γ / 2 * C.c3W * E ≤ |f1| := by
    have hp0 : |f0| - ε' * E ≤ ψ j := by
      have := abs_sub_abs_le_abs_sub f0 (ψ j)
      rw [abs_sub_comm, abs_of_pos hψj] at this
      linarith
    have hp1 : ψ (j + 1) - ε' * (C.tCw * C.CM) * E ≤ |f1| := by
      have h3 := le_abs_self (ψ (j + 1) - f1)
      have h4 := le_abs_self f1
      linarith
    exact f1_lower hγ hEpos (mul_le_mul_of_nonneg_right hsmallε hEpos.le) hC2h hflow hp0 hp1 hψj1 (abs_nonneg _) hc3.le
  exact ⟨hflow, hf1lb⟩

/-- **(R4) the lower half of (c)**: `c_lam lambda kappa_bal <= |lambda_L|` for `h <= h_0`, uniformly. -/
theorem soft_lamL_lower {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m) :
    ∃ clam h0 : ℝ, 0 < clam ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 →
      clam * (softLam C p X N * kappaBal (C.aOf p X N)) ≤ |C.lamL p X N| := by
  obtain ⟨hCA, hnu, hc3, hC2, hCM⟩ := C.consts_pos3
  have hK0 := softK_nonneg C
  have hCw : 0 < C.tCw := Real.exp_pos _
  have hγ := softGam_pos C
  set R : ℝ := C.tCw * C.CM + 2 with hRdef
  have hR : 0 < R := by positivity
  set Kp : ℝ := softK C + 1 with hKpdef
  have hKp : 0 < Kp := by positivity
  refine ⟨softGam C * C.c3W / (2 * Kp * R), softH3 C, by positivity, softH3_pos C, ?_⟩
  intro p hp X hX N hN hstep
  obtain ⟨hflow, hf1lb⟩ := soft_f_growth C hf hm hp hX hN hstep
  have hstepA : Fz.step N ≤ min (softH0 C) C.softH1 := hstep.trans (min_le_left _ _)
  have hstepC : Fz.step N ≤ softGam C / (4 * (C.C2 + 1)) := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hstepC1 : Fz.step N ≤ 1 / (C.C2 + 1) := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hstep1 : Fz.step N ≤ C.softH1 := hstepA.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid C.csT (Fz.step N) m := C.soft_valid hf hp hX hN hstep1 hVpre
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hstep1 hVpre
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  have hκ := kappaBal_pos (C.aOf p X N)
  have hArows := A_ne_zero_rows C hp hX hN hstep1 hVpre
  set lam := softLam C p X N with hlamdef
  have hC2h1 : C.C2 * Fz.step N ≤ 1 := c2h_le_one hC2 hstepC1
  have hjNR : (C.chain p X N).jj 1 < (C.chain p X N).NR := by omega
  set j := (C.chain p X N).jj 1 with hjdef
  have hjmem : j ∈ Icc (0 : ℤ) (C.chain p X N).NR := mem_Icc.mpr ⟨hj0, by omega⟩
  have hj1mem : j + 1 ∈ Icc (0 : ℤ) (C.chain p X N).NR := mem_Icc.mpr ⟨by omega, by omega⟩
  have hW0 : 0 < (C.chain p X N).W j := hV.W_pos j hjmem
  have hM0 : 0 < (C.chain p X N).M j := hV.M_pos j hjmem
  have hM1 : 0 < (C.chain p X N).M (j + 1) := hV.M_pos (j + 1) hj1mem
  have hwr : (C.chain p X N).W (j + 1) ≤ C.tCw * (C.chain p X N).W j := C.soft_Wratio hp hX hN hstep1 hVpre
  have hmr : (C.chain p X N).M (j + 1) ≤ C.CM * (C.chain p X N).M j := C.ratioM p hp X hX N hN
  have hWM1 : (C.chain p X N).W (j + 1) * (C.chain p X N).M (j + 1) ≤ C.tCw * C.CM * ((C.chain p X N).W j * (C.chain p X N).M j) := by
    calc _ ≤ (C.tCw * (C.chain p X N).W j) * (C.CM * (C.chain p X N).M j) := mul_le_mul hwr hmr hM1.le (by positivity)
      _ = _ := by ring
  have hWM0 : 0 < (C.chain p X N).W j * (C.chain p X N).M j := mul_pos hW0 hM0
  have hAeq := C.A_bond p hp X hX N hN
  have hphi2 : ∀ (α : Fin 2) (k : ℤ), ((C.chain p X N).rescale1 lam).phi (Fz.step N) α 2 k = (C.chain p X N).phi (Fz.step N) α 2 k :=
    fun α k => LadderData.phi_rescale1_of_ne _ _ _ α (by norm_num) k
  have hp2 : 2 ∈ Icc 1 ((C.chain p X N).rescale1 lam).P := mem_Icc.mpr ⟨by norm_num, by show 2 ≤ (C.chain p X N).P; omega⟩
  have hwin0 : j ∈ Icc (((C.chain p X N).rescale1 lam).jj (2 - 1)) (((C.chain p X N).rescale1 lam).jj 2 + 1) :=
    mem_Icc.mpr ⟨le_rfl, by show j ≤ (C.chain p X N).jj 2 + 1; omega⟩
  have hwin1 : j + 1 ∈ Icc (((C.chain p X N).rescale1 lam).jj (2 - 1)) (((C.chain p X N).rescale1 lam).jj 2 + 1) :=
    mem_Icc.mpr ⟨by show j ≤ j + 1; omega, by show j + 1 ≤ (C.chain p X N).jj 2 + 1; omega⟩
  have hu0 : |(C.chain p X N).phi (Fz.step N) 0 2 j| ≤ softK C * ((C.chain p X N).W j * (C.chain p X N).M j) := by
    have h := (hV.phi_bd hp2 hwin0).1
    rw [hphi2] at h
    have h' : |(C.chain p X N).phi (Fz.step N) 0 2 j| ≤ softK C * (C.chain p X N).W j * (C.chain p X N).M j := h
    linarith
  have hu1 : |(C.chain p X N).phi (Fz.step N) 0 2 (j + 1)| ≤ softK C * ((C.chain p X N).W (j + 1) * (C.chain p X N).M (j + 1)) := by
    have h := (hV.phi_bd hp2 hwin1).1
    rw [hphi2] at h
    have h' : |(C.chain p X N).phi (Fz.step N) 0 2 (j + 1)| ≤ softK C * (C.chain p X N).W (j + 1) * (C.chain p X N).M (j + 1) := h
    linarith
  have hne := hV.det_ne_zero hp2 (j := j) (mem_Icc.mpr ⟨le_rfl, by show j ≤ (C.chain p X N).jj 2; omega⟩)
  rw [hphi2, hphi2, hphi2, hphi2] at hne
  have hr2 : |(C.chain p X N).phi (Fz.step N) 1 2 (j + 1)| ≤ (1 + C.C2 * Fz.step N) * |(C.chain p X N).phi (Fz.step N) 1 2 j| :=
    C.ratio2 p hp X hX N hN
  have hAj : 0 < (C.chain p X N).A j := by
    have hne0 := hArows j hj0 hjNR
    rw [hAeq j (mem_Icc.mpr ⟨by omega, by omega⟩)] at hne0 ⊢
    exact lt_of_le_of_ne (bondA_nonneg' Fz p N j) (Ne.symm hne0)
  have hAne' : (C.chain p X N).A j ≠ 0 := hAj.ne'
  have hlamL := lamL_eq_kappa_mul_transMat C p X N hAne'
  rw [LadderData.transMat_zero_zero_eq_cas_div ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1)
    (C.chain p X N).jj 1 (C.chain p X N).A hAne'] at hlamL
  unfold cas at hlamL
  set g0 := (C.chain p X N).phi (Fz.step N) 1 2 j with hg0def
  set g1 := (C.chain p X N).phi (Fz.step N) 1 2 (j + 1) with hg1def
  set u0 := (C.chain p X N).phi (Fz.step N) 0 2 j with hu0def
  set u1 := (C.chain p X N).phi (Fz.step N) 0 2 (j + 1) with hu1def
  set A := (C.chain p X N).A j with hAdef
  have hρ : 1 + C.C2 * Fz.step N ≤ 2 := by linarith
  have hρ0 : 0 ≤ 1 + C.C2 * Fz.step N := by positivity
  have hu1' : |(C.chain p X N).phi (Fz.step N) 0 2 (j + 1)| ≤ softK C * (C.tCw * C.CM * ((C.chain p X N).W j * (C.chain p X N).M j)) :=
    le_trans hu1 (mul_le_mul_of_nonneg_left hWM1 hK0)
  obtain ⟨hnum, hY, hDpos⟩ := cas_quot_lower hAj hρ0 hρ hr2 hf1lb hu0 hu1' hK0 (show softK C ≤ Kp by rw [hKpdef]; linarith) hWM0 hRdef
    (by positivity) hne
  have hθ0 : softGam C * C.c3W / (2 * Kp * R) * lam * (Kp * ((C.chain p X N).W j * (C.chain p X N).M j) * R)
      = softGam C / 2 * C.c3W * (lam * ((C.chain p X N).W j * (C.chain p X N).M j)) := by
    field_simp
  have hab := hlamL
  rw [← hlamL] at hab
  have hlamabs : |C.lamL p X N| = kappaBal (C.aOf p X N) *
      (|(C.chain p X N).A j * ((C.chain p X N).phi (Fz.step N) 0 1 (j + 1) * (C.chain p X N).phi (Fz.step N) 1 2 j
          - (C.chain p X N).phi (Fz.step N) 0 1 j * (C.chain p X N).phi (Fz.step N) 1 2 (j + 1))| /
        |(C.chain p X N).A j * ((C.chain p X N).phi (Fz.step N) 0 2 (j + 1) * (C.chain p X N).phi (Fz.step N) 1 2 j
          - (C.chain p X N).phi (Fz.step N) 0 2 j * (C.chain p X N).phi (Fz.step N) 1 2 (j + 1))|) := by
    rw [hlamL, abs_mul, abs_of_pos hκ, abs_div]
  rw [hlamabs]
  exact final_quot hκ hlam (by positivity) hDpos hnum hY hθ0 hAj.le (abs_nonneg _)

end Lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_lamL_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_lamL_lower

end FormalResearch.JacobiEigenvectors.TheoremA

end
