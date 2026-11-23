module

public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.ProfWinDef
public import FormalResearch.ModularBootstrap.Upper.Ramped.AiryProfile

/-!
# Profile windows: the class `𝒟x` of displaced designs (`sr:P`, `sr:Sigma` Step 5)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (the design `𝔇 = (f; d; N, η_*;` finitely many
displacements`)` of §2, `sr:P`, and the sign law there), `upper_transfer.tex` (`ut:V`, `ut:R`),
`CFT/notes/n2_ramped_comb.tex` (`rem:profile`).

* `profWin` (`Assembly.ProfWinDef`): the abstract `Window` of an arbitrary admissible profile
  `(u_k, ε_k)`, all `ε_k ≠ 0`, first site `u_1 = a_1 - d`; `designWin` is the case
  `(designSiteU N, designWidthU N η)`.  Its facts `profWin_pi_zero`, `profWin_pi_succ`, `profWin_V_eq` and the
  sign law `profWin_pi_pos`, `profWin_pi_neg`, `profWin_pi_eq_zero` (`Π_n > 0, < 0, = 0` according as
  `a_n <, >, = u_f`) are there.
* For `d = -κ ≤ 0` the two-sided comparison `profPi0 ≤ profPi (-κ) ≤ (1 + κ/Δ₁) profPi0`
  (`profPi_ge_profPi0`, `profPi_neg_le`): the form `Π_n(d) = Π_n(0)(1 + κ/|a_n - a_1|)` that `profV_identity`
  (stated for `d ≥ 0`) does not give.
* `dispSite N e`: the sites of `D(N, ·, ·)` displaced by `e k` (`e k = 0` outside `[2, N]`).
* **`displacedClass`**: the class `𝒟x` of the displaced designs of `sr:P`: `N ≥ 1`, `0 < η_* ≤ 1/4`,
  sites `u_k = a_k + e_k` (`2 ≤ k ≤ N`, kept on the band `u_k < 0`), `u_k = u_k^W` for `k > N`, widths
  `ε_k = η_* gap_k` (`k ≤ N`), `gap_k/4` beyond, `|d| < d_0`.  This is the class for which `Σ3` (property
  `sr:P`, `DesignPropertyP S.μS displacedClass`) has to be proved.  `designClass` is the case `e = 0`
  (with all `d`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### Comparison of `Π_n(d)` and `Π_n(0)` for `d = -κ ≤ 0` -/

lemma abs_airyZero_sub_one_ge {n : ℕ} (hn : 2 ≤ n) :
    airyZero 1 - airyZero 2 ≤ |airyZero n - airyZero 1| := by
  have h12 : airyZero n ≤ airyZero 2 := by
    rcases hn.eq_or_lt with rfl | h2n
    · exact le_rfl
    · exact (airyZero_lt_of_lt (by omega) h2n).le
  rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < n)])]
  linarith

lemma gapOne_pos : 0 < airyZero 1 - airyZero 2 := sub_pos.2 (airyZero_strictAnti le_rfl)

lemma abs_airyZero_sub_one_pos {n : ℕ} (hn : 2 ≤ n) : 0 < |airyZero n - airyZero 1| :=
  lt_of_lt_of_le gapOne_pos (abs_airyZero_sub_one_ge hn)

/-- For `d = -κ ≤ 0`: `Π_n(0) ≤ Π_n(d)` (`Π_n(d) = Π_n(0)(1 + κ/|a_n - a_1|)`). -/
lemma profPi_ge_profPi0 {uSite epsU : ℕ → ℝ} (hH : AiryProdTailHypothesis 1 uSite epsU) {κ : ℝ}
    (hκ : 0 ≤ κ) {n : ℕ} (hn : 2 ≤ n) :
    profPi0 uSite epsU n ≤ profPi uSite epsU (-κ) n := by
  unfold profPi
  have h0 := profPi0_nonneg uSite epsU hH hn
  have e : 1 - -κ / |airyZero n - airyZero 1| = 1 + κ / |airyZero n - airyZero 1| := by
    rw [neg_div, sub_neg_eq_add]
  rw [e]
  nlinarith [mul_nonneg h0 (div_nonneg hκ (abs_nonneg (airyZero n - airyZero 1)))]

/-- For `d = -κ`, `κ ≥ 0`: `Π_n(d) ≤ (1 + κ/Δ₁) Π_n(0)` with `Δ₁ = a_1 - a_2`. -/
lemma profPi_neg_le {uSite epsU : ℕ → ℝ} (hH : AiryProdTailHypothesis 1 uSite epsU) {κ : ℝ}
    (hκ : 0 ≤ κ) {n : ℕ} (hn : 2 ≤ n) :
    profPi uSite epsU (-κ) n ≤ (1 + κ / (airyZero 1 - airyZero 2)) * profPi0 uSite epsU n := by
  unfold profPi
  have h0 := profPi0_nonneg uSite epsU hH hn
  have hΔ := gapOne_pos
  have hge := abs_airyZero_sub_one_ge hn
  have : κ / |airyZero n - airyZero 1| ≤ κ / (airyZero 1 - airyZero 2) :=
    div_le_div_of_nonneg_left hκ hΔ hge
  have h2 : 1 - -κ / |airyZero n - airyZero 1| ≤ 1 + κ / (airyZero 1 - airyZero 2) := by
    rw [neg_div, sub_neg_eq_add]; linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

/-! ### The displaced designs -/

/-- The sites of `D(N, ·, ·)` displaced by `e k`: `u_k = designSiteU N k + e k`. -/
noncomputable def dispSite (N : ℕ) (e : ℕ → ℝ) (k : ℕ) : ℝ := designSiteU N k + e k

lemma dispSite_of_eq_zero {N : ℕ} {e : ℕ → ℝ} {k : ℕ} (h : e k = 0) :
    dispSite N e k = designSiteU N k := by
  unfold dispSite; rw [h, add_zero]

/-- **The class `𝒟x` of the displaced designs** (`sr:P`, `sr:Sigma` Step 5): `D(N, η_*, d)` with finitely many
displaced sites `u_k = a_k + e_k` (`2 ≤ k ≤ N`, `e_k = 0` elsewhere, on the band `u_k < 0`), `N ≥ 1`,
`0 < η_* ≤ 1/4`, `|d| < d₀`.  `designClass` is the case `e = 0` (there with all `d ∈ ℝ`).  This is the class
for which property `sr:P` (`DesignPropertyP S.μS displacedClass`, task `Σ3`) is to be proved. -/
def displacedClass : Set Window :=
  {D | ∃ (N : ℕ) (η : ℝ) (e : ℕ → ℝ) (d : ℝ) (hη : 0 < η)
      (hH : AiryProdTailHypothesis 1 (dispSite N e) (designWidthU N η)),
      1 ≤ N ∧ η ≤ 1 / 4 ∧ (∀ k, (k < 2 ∨ N < k) → e k = 0) ∧
      (∀ k, 2 ≤ k → k ≤ N → airyZero k + e k < 0) ∧ |d| < designRadius ∧
      D = profWin (dispSite N e) (designWidthU N η) hH
        (fun _ hk => designWidthU_ne_zero N hη hk) d}

lemma profWin_mem_displacedClass {N : ℕ} {η : ℝ} (hη : 0 < η) {e : ℕ → ℝ}
    (hH : AiryProdTailHypothesis 1 (dispSite N e) (designWidthU N η)) {d : ℝ} (hN : 1 ≤ N)
    (hη1 : η ≤ 1 / 4) (he : ∀ k, (k < 2 ∨ N < k) → e k = 0)
    (hband : ∀ k, 2 ≤ k → k ≤ N → airyZero k + e k < 0) (hd : |d| < designRadius) :
    profWin (dispSite N e) (designWidthU N η) hH
      (fun _ hk => designWidthU_ne_zero N hη hk) d ∈ displacedClass :=
  ⟨N, η, e, d, hη, hH, hN, hη1, he, hband, hd, rfl⟩

/-- The displaced designs with `e = 0` are the designs `designWin`. -/
lemma profWin_dispSite_zero (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hH : AiryProdTailHypothesis 1 (dispSite N (fun _ => 0) ) (designWidthU N η)) (d : ℝ) :
    (profWin (dispSite N (fun _ => 0)) (designWidthU N η) hH
      (fun _ hk => designWidthU_ne_zero N hη hk) d).W = (designWin N hη d).W := by
  funext u
  have : dispSite N (fun _ => 0) = designSiteU N := by
    funext k; exact dispSite_of_eq_zero rfl
  rw [profWin_W, designWin, profWin_W, this]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.profPi_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms profPi_neg_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.profWin_mem_displacedClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms profWin_mem_displacedClass

end FormalResearch.ModularBootstrap.Upper.Assembly
