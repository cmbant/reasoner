module

public import FormalResearch.Special.DiscreteLgDefect
public import FormalResearch.Special.DiscreteLgMarch

/-!
# Discrete Liouville-Green (Darboux) theorem for a Jacobi chain in the oscillatory bulk

**Statement** (`dlg_bulk`).  Let `A, θ, w, Θ` be a bulk datum on an open interval `U` (`DlgData`: `Θ' = θ`, amplitude relation `A w² sin θ = 1`, `C²` bounds),
`q_k = q₀ + k h` lattice sites in `U` for `k ∈ [J, N+1]` with `(N - J) h ≤ L`, and coefficients with
`|a_k - A(q_k - h/2)| ≤ E h²`, `|c_k - 2A(q_k) cos θ(q_k)| ≤ E h²`.  Then for `0 < h ≤ h₀(lo, hi, M, E, L)`, **every** solution `Y` of the rows
`a_{k+1}Y_{k+1} + a_k Y_{k-1} = c_k Y_k` (`k ∈ [J+1, N]`) has an amplitude and a phase constant `R ≥ 0`, `φ₀ ∈ ℝ` with

`|Y_k - R w(q_k) cos(Θ(q_k)/h - φ₀)| ≤ C h R w(q_k)`   for all `k ∈ [J, N+1]`,

and `R ≍ |Y_m| + |Y_{m+1}|` for any base bond `m ∈ [J, N]` (constants `C, h₀` depend only on `lo, hi, M, E, L`: uniform in the datum).
This is the first-order discrete Liouville-Green / Darboux asymptotics (for Wigner-`d`/Hahn/Racah chains: Hilb/Darboux in the bulk), with **explicit**
phase `Θ(q_k)/h` (no `o(1)` in the phase beyond the `O(h)` relative error), valid on any compact interior interval of the oscillatory region,
not only in a Langer chart around a turning point.

**Proof.**  `φ = w cos P`, `ψ = w sin P` is an approximate fundamental pair: row defects `70 hi R⁴ h²` and Casoratian `1 + O(h)` (`DiscreteLgDefect`);
the constant-weight Grönwall march (`DiscreteLgMarch`, from `voc_march_up/down`) gives total drift `Λ = O((N-J) h²) = O(h)` of the Cramer
coefficients.

**Claim class: proved.**  **Not formalised:** the `h²`-correction of the phase (second-order Liouville-Green, `ϖ`); smooth `(A, u)` to `DlgData`
conversion is in `DiscreteLgSmooth`; the matching with the Airy turning layer is `DiscreteLgMatch`.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma dlg_polar (α β : ℝ) : ∃ R φ0 : ℝ, 0 ≤ R ∧ |α| ≤ R ∧ |β| ≤ R ∧ R ≤ |α| + |β| ∧
    ∀ P : ℝ, α * Real.cos P + β * Real.sin P = R * Real.cos (P - φ0) := by
  refine ⟨‖(⟨α, β⟩ : ℂ)‖, Complex.arg ⟨α, β⟩, norm_nonneg _, Complex.abs_re_le_norm (⟨α, β⟩ : ℂ),
    Complex.abs_im_le_norm (⟨α, β⟩ : ℂ), Complex.norm_le_abs_re_add_abs_im (⟨α, β⟩ : ℂ), fun P => ?_⟩
  have h1 := Complex.norm_mul_cos_arg (⟨α, β⟩ : ℂ)
  have h2 := Complex.norm_mul_sin_arg (⟨α, β⟩ : ℂ)
  simp only at h1 h2
  rw [Real.cos_sub]
  linear_combination (-Real.cos P) * h1 + (-Real.sin P) * h2

lemma dlg_cross {Ym Ym1 p0 p1 hi : ℝ} (hp0 : |p0| ≤ hi) (hp1 : |p1| ≤ hi) :
    |Ym * p1 - Ym1 * p0| ≤ hi * (|Ym| + |Ym1|) := by
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 : |Ym| * |p1| ≤ |Ym| * hi := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
  have h2 : |Ym1| * |p0| ≤ |Ym1| * hi := mul_le_mul_of_nonneg_left hp0 (abs_nonneg _)
  linarith

lemma dlg_rep_size {α β p q hi R : ℝ} (hα : |α| ≤ R) (hβ : |β| ≤ R) (hp : |p| ≤ hi) (hq : |q| ≤ hi) :
    |α * p + β * q| ≤ 2 * hi * R := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 : |α| * |p| ≤ R * hi := mul_le_mul hα hp (abs_nonneg _) ((abs_nonneg _).trans hα)
  have h2 : |β| * |q| ≤ R * hi := mul_le_mul hβ hq (abs_nonneg _) ((abs_nonneg _).trans hβ)
  linarith

/-- Size of the Cramer coefficients at one bond in terms of `Y`. -/
lemma dlg_cramer_size {a Y φ ψ : ℤ → ℝ} {m : ℤ} {hi E : ℝ} (hD : 1 / 2 ≤ cas a φ ψ m) (ham : |a (m + 1)| ≤ hi + E)
    (hφ0 : |φ m| ≤ hi) (hφ1 : |φ (m + 1)| ≤ hi) (hψ0 : |ψ m| ≤ hi) (hψ1 : |ψ (m + 1)| ≤ hi) :
    |vocA a Y φ ψ m| ≤ 2 * ((hi + E) * (hi * (|Y m| + |Y (m + 1)|))) ∧
      |vocB a Y φ ψ m| ≤ 2 * ((hi + E) * (hi * (|Y m| + |Y (m + 1)|))) := by
  have hpos : 0 < cas a φ ψ m := by linarith
  have hnn : 0 ≤ hi + E := (abs_nonneg _).trans ham
  constructor
  · unfold vocA
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hcr : |cas a Y ψ m| ≤ (hi + E) * (hi * (|Y m| + |Y (m + 1)|)) := by
      unfold cas
      rw [abs_mul]
      exact mul_le_mul ham (dlg_cross hψ0 hψ1) (abs_nonneg _) hnn
    have : 0 ≤ (hi + E) * (hi * (|Y m| + |Y (m + 1)|)) := (abs_nonneg _).trans hcr
    nlinarith
  · unfold vocB
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hcr : |cas a φ Y m| ≤ (hi + E) * (hi * (|Y m| + |Y (m + 1)|)) := by
      unfold cas
      rw [abs_mul]
      have e : φ m * Y (m + 1) - φ (m + 1) * Y m = Y (m + 1) * φ m - Y m * φ (m + 1) := by ring
      rw [e]
      have := dlg_cross (Ym := Y (m + 1)) (Ym1 := Y m) hφ1 hφ0
      refine mul_le_mul ham (this.trans (le_of_eq (by ring))) (abs_nonneg _) hnn
    have : 0 ≤ (hi + E) * (hi * (|Y m| + |Y (m + 1)|)) := (abs_nonneg _).trans hcr
    nlinarith

/-- **Cartesian form** (abstract sequences).  Let `φ = W cos P`, `ψ = W sin P` (`0 ≤ W ≤ hi`) have Casoratian `≥ 1/2` on the bonds `[J, N]` and let the
Cramer coefficients of `Y` at the bond `m` drift by at most `n₀ · 2Λ` (`n₀ = |α_m| + |β_m|`).  Then `Y = α_m φ + β_m ψ` up to `2Λ n₀ W` on `[J, N+1]`, and
`n₀ ≤ 4 (hi + E) hi (|Y_m| + |Y_{m+1}|)`, `|Y_m| + |Y_{m+1}| ≤ 4 hi n₀`. -/
theorem dlg_amp_cart {a Y W P : ℤ → ℝ} {J N m : ℤ} {hi E Λ : ℝ}
    (hJm : J ≤ m) (hmN : m ≤ N) (hW0 : ∀ k ∈ Icc J (N + 1), 0 ≤ W k) (hW : ∀ k ∈ Icc J (N + 1), W k ≤ hi)
    (hcas : ∀ k ∈ Icc J N, 1 / 2 ≤ cas a (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k)
    (ham : |a (m + 1)| ≤ hi + E)
    (hd : ∀ k ∈ Icc J N,
      |vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k -
          vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
        |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k -
          vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| ≤
        (|vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
          |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m|) * (2 * Λ)) :
    (∀ k ∈ Icc J (N + 1),
      |Y k - (vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * (W k * Real.cos (P k)) +
          vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * (W k * Real.sin (P k)))| ≤
        (|vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
          |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m|) * (2 * Λ) * W k) ∧
    |vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
        |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| ≤
      4 * (hi + E) * hi * (|Y m| + |Y (m + 1)|) ∧
    |Y m| + |Y (m + 1)| ≤ 4 * hi * (|vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
        |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m|) := by
  set φ : ℤ → ℝ := fun i => W i * Real.cos (P i) with hφdef
  set ψ : ℤ → ℝ := fun i => W i * Real.sin (P i) with hψdef
  have hφb : ∀ k ∈ Icc J (N + 1), |φ k| ≤ W k := fun k hk => by
    simp only [hφdef]
    rw [abs_mul, abs_of_nonneg (hW0 k hk)]
    exact mul_le_of_le_one_right (hW0 k hk) (Real.abs_cos_le_one _)
  have hψb : ∀ k ∈ Icc J (N + 1), |ψ k| ≤ W k := fun k hk => by
    simp only [hψdef]
    rw [abs_mul, abs_of_nonneg (hW0 k hk)]
    exact mul_le_of_le_one_right (hW0 k hk) (Real.abs_sin_le_one _)
  have hne : ∀ k ∈ Icc J N, cas a φ ψ k ≠ 0 := fun k hk => by
    have := hcas k hk
    intro h0; rw [h0] at this; norm_num at this
  have hmI : m ∈ Icc J N := by rw [Finset.mem_Icc]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hk' := hk
    rw [Finset.mem_Icc] at hk'
    obtain ⟨b, hb, hYk⟩ : ∃ b ∈ Icc J N, Y k = vocA a Y φ ψ b * φ k + vocB a Y φ ψ b * ψ k := by
      by_cases hkN : k ≤ N
      · exact ⟨k, by rw [Finset.mem_Icc]; omega, (voc_repr a Y φ ψ k (hne k (by rw [Finset.mem_Icc]; omega))).1⟩
      · have hk1 : k = N + 1 := by omega
        subst hk1
        exact ⟨N, by rw [Finset.mem_Icc]; omega, (voc_repr a Y φ ψ N (hne N (by rw [Finset.mem_Icc]; omega))).2⟩
    have hdb := hd b hb
    have e : Y k - (vocA a Y φ ψ m * φ k + vocB a Y φ ψ m * ψ k) =
        (vocA a Y φ ψ b - vocA a Y φ ψ m) * φ k + (vocB a Y φ ψ b - vocB a Y φ ψ m) * ψ k := by rw [hYk]; ring
    have t1 : |(vocA a Y φ ψ b - vocA a Y φ ψ m) * φ k| ≤ |vocA a Y φ ψ b - vocA a Y φ ψ m| * W k :=
      dlg_mul_le (le_refl _) (hφb k hk)
    have t2 : |(vocB a Y φ ψ b - vocB a Y φ ψ m) * ψ k| ≤ |vocB a Y φ ψ b - vocB a Y φ ψ m| * W k :=
      dlg_mul_le (le_refl _) (hψb k hk)
    have hWk := hW0 k hk
    show |Y k - (vocA a Y φ ψ m * φ k + vocB a Y φ ψ m * ψ k)| ≤ _
    rw [e]
    calc _ ≤ |(vocA a Y φ ψ b - vocA a Y φ ψ m) * φ k| + |(vocB a Y φ ψ b - vocB a Y φ ψ m) * ψ k| := abs_add_le _ _
      _ ≤ (|vocA a Y φ ψ b - vocA a Y φ ψ m| + |vocB a Y φ ψ b - vocB a Y φ ψ m|) * W k := by linarith
      _ ≤ ((|vocA a Y φ ψ m| + |vocB a Y φ ψ m|) * (2 * Λ)) * W k := mul_le_mul_of_nonneg_right hdb hWk
  · have hDm := hcas m hmI
    have wm := hW m (by rw [Finset.mem_Icc]; omega)
    have wm1 := hW (m + 1) (by rw [Finset.mem_Icc]; omega)
    obtain ⟨hα, hβ⟩ := dlg_cramer_size (a := a) (Y := Y) (φ := φ) (ψ := ψ) hDm ham
      ((hφb m (by rw [Finset.mem_Icc]; omega)).trans wm) ((hφb (m + 1) (by rw [Finset.mem_Icc]; omega)).trans wm1)
      ((hψb m (by rw [Finset.mem_Icc]; omega)).trans wm) ((hψb (m + 1) (by rw [Finset.mem_Icc]; omega)).trans wm1)
    nlinarith
  · have hYm := voc_repr a Y φ ψ m (hne m hmI)
    have hq := hψb (m + 1) (by rw [Finset.mem_Icc]; omega)
    have hq0 := hψb m (by rw [Finset.mem_Icc]; omega)
    have hp := hφb (m + 1) (by rw [Finset.mem_Icc]; omega)
    have hp0 := hφb m (by rw [Finset.mem_Icc]; omega)
    have wm := hW m (by rw [Finset.mem_Icc]; omega)
    have wm1 := hW (m + 1) (by rw [Finset.mem_Icc]; omega)
    have hαR : |vocA a Y φ ψ m| ≤ |vocA a Y φ ψ m| + |vocB a Y φ ψ m| := by linarith [abs_nonneg (vocB a Y φ ψ m)]
    have hβR : |vocB a Y φ ψ m| ≤ |vocA a Y φ ψ m| + |vocB a Y φ ψ m| := by linarith [abs_nonneg (vocA a Y φ ψ m)]
    have b0 : |Y m| ≤ 2 * hi * (|vocA a Y φ ψ m| + |vocB a Y φ ψ m|) := by
      rw [hYm.1]
      exact dlg_rep_size hαR hβR ((hp0).trans wm) ((hq0).trans wm)
    have b1 : |Y (m + 1)| ≤ 2 * hi * (|vocA a Y φ ψ m| + |vocB a Y φ ψ m|) := by
      rw [hYm.2]
      exact dlg_rep_size hαR hβR ((hp).trans wm1) ((hq).trans wm1)
    have hn0 : 0 ≤ |vocA a Y φ ψ m| + |vocB a Y φ ψ m| := by positivity
    have hhi0 : 0 ≤ hi := (hW0 m (by rw [Finset.mem_Icc]; omega)).trans wm
    nlinarith

/-- **Amplitude and phase of an exact solution** (abstract sequences), polar form of `dlg_amp_cart`: there are `R ≥ 0`, `φ₀` with
`|Y_k - R W_k cos(P_k - φ₀)| ≤ 4 Λ R W_k`, `R ≤ 4 (hi + E) hi (|Y_m| + |Y_{m+1}|)` and `|Y_m| + |Y_{m+1}| ≤ 8 hi R`. -/
theorem dlg_amp_phase {a Y W P : ℤ → ℝ} {J N m : ℤ} {hi E Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hJm : J ≤ m) (hmN : m ≤ N) (hW0 : ∀ k ∈ Icc J (N + 1), 0 ≤ W k) (hW : ∀ k ∈ Icc J (N + 1), W k ≤ hi)
    (hcas : ∀ k ∈ Icc J N, 1 / 2 ≤ cas a (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k)
    (ham : |a (m + 1)| ≤ hi + E)
    (hd : ∀ k ∈ Icc J N,
      |vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k -
          vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
        |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) k -
          vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| ≤
        (|vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
          |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m|) * (2 * Λ)) :
    ∃ R φ0 : ℝ, 0 ≤ R ∧ (∀ k ∈ Icc J (N + 1), |Y k - R * W k * Real.cos (P k - φ0)| ≤ 4 * Λ * R * W k) ∧
      R ≤ 4 * (hi + E) * hi * (|Y m| + |Y (m + 1)|) ∧ |Y m| + |Y (m + 1)| ≤ 8 * hi * R := by
  obtain ⟨c1, c2, c3⟩ := dlg_amp_cart hJm hmN hW0 hW hcas ham hd
  obtain ⟨R, φ0, hR0, hαR, hβR, hRn, hpol⟩ := dlg_polar
    (vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m)
    (vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m)
  have hn : |vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| +
      |vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m| ≤ 2 * R := by linarith
  have hhi : 0 ≤ hi := by
    have := hW m (by rw [Finset.mem_Icc]; omega)
    exact (hW0 m (by rw [Finset.mem_Icc]; omega)).trans this
  refine ⟨R, φ0, hR0, fun k hk => ?_, by linarith, ?_⟩
  · have hmain : vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * (W k * Real.cos (P k)) +
        vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * (W k * Real.sin (P k)) =
        R * W k * Real.cos (P k - φ0) := by
      have := hpol (P k)
      calc _ = W k * (vocA a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * Real.cos (P k) +
            vocB a Y (fun i => W i * Real.cos (P i)) (fun i => W i * Real.sin (P i)) m * Real.sin (P k)) := by ring
        _ = R * W k * Real.cos (P k - φ0) := by rw [this]; ring
    rw [← hmain]
    refine (c1 k hk).trans ?_
    have hWk := hW0 k hk
    calc _ ≤ ((2 * R) * (2 * Λ)) * W k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) hWk
      _ = 4 * Λ * R * W k := by ring
  · nlinarith [mul_le_mul_of_nonneg_left hn hhi]

/-- Row defects and Casoratian of the bulk pair on a window (packaging of `dlg_row_defect`, `dlg_cas_bound`). -/
lemma dlg_pair_ok {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M E : ℝ} (D : DlgData A θ w Θ U lo hi M) (hE : 0 ≤ E)
    {q0 h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hh96 : 96 * dlgR lo hi M E ^ 4 * h ≤ 1) {a c : ℤ → ℝ} {J N : ℤ}
    (hU : ∀ k ∈ Icc J (N + 1), dlgQ q0 h k ∈ U)
    (hA : ∀ k ∈ Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2)
    (hCc : ∀ k ∈ Icc (J + 1) N, |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) :
    (∀ k ∈ Icc (J + 1) N, |jac a c (dlgPhi w Θ q0 h) k| ≤ 70 * hi * dlgR lo hi M E ^ 4 * h ^ 2 ∧
      |jac a c (dlgPsi w Θ q0 h) k| ≤ 70 * hi * dlgR lo hi M E ^ 4 * h ^ 2) ∧
    ∀ k ∈ Icc J N, 1 / 2 ≤ cas a (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) k := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [Finset.mem_Icc] at hk
    exact dlg_row_defect D hE hh h1 (hU k (by rw [Finset.mem_Icc]; omega)) (hU (k + 1) (by rw [Finset.mem_Icc]; omega))
      (hU (k - 1) (by rw [Finset.mem_Icc]; omega)) (hA (k + 1) (by rw [Finset.mem_Icc]; omega))
      (hA k (by rw [Finset.mem_Icc]; omega)) (hCc k (by rw [Finset.mem_Icc]; omega))
  · rw [Finset.mem_Icc] at hk
    have := dlg_cas_bound D hE hh h1 (hU k (by rw [Finset.mem_Icc]; omega)) (hU (k + 1) (by rw [Finset.mem_Icc]; omega))
      (hA (k + 1) (by rw [Finset.mem_Icc]; omega))
    rw [abs_le] at this
    linarith [this.1]

/-- The hypotheses of `dlg_amp_cart` for the bulk pair (Casoratian, step bound for `a_{m+1}`, and the Grönwall drift `Λ = 280 hi² R⁴ L h`). -/
lemma dlg_bulk_core (lo hi M E L : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧ 1120 * hi ^ 2 * dlgR lo hi M E ^ 4 * L ≤ C ∧ 4 * (hi + E) * hi ≤ C ∧ 8 * hi ≤ C ∧
      ∀ {A θ w Θ : ℝ → ℝ} {U : Set ℝ}, DlgData A θ w Θ U lo hi M →
      ∀ (q0 h : ℝ) (a c Y : ℤ → ℝ) (J N m : ℤ), 0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Icc J (N + 1), dlgQ q0 h k ∈ U) →
        (∀ k ∈ Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) →
        (∀ k ∈ Icc J N, 1 / 2 ≤ cas a (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
          (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) k) ∧ |a (m + 1)| ≤ hi + E ∧
        (∀ k ∈ Icc J N,
          |vocA a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) k -
            vocA a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) m| +
          |vocB a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) k -
            vocB a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) m| ≤
          (|vocA a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) m| +
            |vocB a Y (fun i => w (dlgQ q0 h i) * Real.cos (dlgP Θ q0 h i))
              (fun i => w (dlgQ q0 h i) * Real.sin (dlgP Θ q0 h i)) m|) * (2 * (280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h))) := by
  have hRd := dlgR_ge_one hlo hhi hM hE
  set Rd := dlgR lo hi M E with hRddef
  have hRd4 : 1 ≤ Rd ^ 4 := one_le_pow₀ hRd
  have hRd0 : 0 < Rd ^ 4 := by linarith
  set h0 : ℝ := min 1 (min (1 / (96 * Rd ^ 4)) (1 / (1120 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1)))) with hh0
  set C : ℝ := 1120 * hi ^ 2 * Rd ^ 4 * L + 4 * (hi + E) * hi + 8 * hi + 1 with hC
  have hh0pos : 0 < h0 := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hC0 : 0 < C := by rw [hC]; positivity
  have p1 : 0 ≤ 1120 * hi ^ 2 * Rd ^ 4 * L := by positivity
  have p2 : 0 ≤ 4 * (hi + E) * hi := by positivity
  have p3 : 0 ≤ 8 * hi := by positivity
  refine ⟨h0, C, hh0pos, min_le_left _ _, hC0, by rw [hC]; linarith, by rw [hC]; linarith, by rw [hC]; linarith, ?_⟩
  intro A θ w Θ U D q0 h a c Y J N m hh hh0' hJm hmN hlen hU hA hCc hY
  have hh1 : h ≤ 1 := hh0'.trans (min_le_left _ _)
  have hh96 : h ≤ 1 / (96 * Rd ^ 4) := hh0'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1120 : h ≤ 1 / (1120 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1)) :=
    hh0'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh96' : 96 * Rd ^ 4 * h ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hh96 (by positivity : (0 : ℝ) ≤ 96 * Rd ^ 4)
    have e : 96 * Rd ^ 4 * (1 / (96 * Rd ^ 4)) = 1 := by field_simp
    linarith
  obtain ⟨hdef, hcas⟩ := dlg_pair_ok D hE hh hh1 hh96' hU hA hCc
  have hwk : ∀ k ∈ Icc J (N + 1), 0 ≤ w (dlgQ q0 h k) ∧ w (dlgQ q0 h k) ≤ hi := fun k hk =>
    ⟨(D.lo_pos.trans_le (D.wb _ (hU k hk)).1).le, (D.wb _ (hU k hk)).2⟩
  have hφb' : ∀ k ∈ Icc J (N + 1), |dlgPhi w Θ q0 h k| ≤ hi := fun k hk => by
    unfold dlgPhi
    rw [abs_mul, abs_of_nonneg (hwk k hk).1]
    exact (mul_le_of_le_one_right (hwk k hk).1 (Real.abs_cos_le_one _)).trans (hwk k hk).2
  have hψb' : ∀ k ∈ Icc J (N + 1), |dlgPsi w Θ q0 h k| ≤ hi := fun k hk => by
    unfold dlgPsi
    rw [abs_mul, abs_of_nonneg (hwk k hk).1]
    exact (mul_le_of_le_one_right (hwk k hk).1 (Real.abs_sin_le_one _)).trans (hwk k hk).2
  set Λ : ℝ := 280 * hi ^ 2 * Rd ^ 4 * L * h with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛ4 : Λ ≤ 1 / 4 := by
    have h1 : 280 * hi ^ 2 * Rd ^ 4 * L * h ≤ 280 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1) * h := by
      have a1 : hi ^ 2 ≤ hi ^ 2 + 1 := by linarith
      have a2 : L ≤ L + 1 := by linarith
      have : hi ^ 2 * L ≤ (hi ^ 2 + 1) * (L + 1) := mul_le_mul a1 a2 hL (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 280 * Rd ^ 4 * h)]
    have h2 : 280 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1) * h ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hh1120 (by positivity : (0 : ℝ) ≤ 280 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1))
      have e : 280 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1) * (1 / (1120 * (hi ^ 2 + 1) * Rd ^ 4 * (L + 1))) = 1 / 4 := by
        field_simp; ring
      linarith
    linarith
  have hmarch := dlg_march_const (a := a) (c := c) (Y := Y) (φ := dlgPhi w Θ q0 h) (ψ := dlgPsi w Θ q0 h)
    (J := J) (N := N) (m := m) hJm hmN
    (γ := 1 / 2) (ε := 70 * hi * Rd ^ 4 * h ^ 2) (W := hi) (Λ := Λ) (by norm_num) (by positivity) hhi hY
    (fun k hk => (hcas k hk).trans (le_abs_self _)) (fun k hk => hφb' k hk) (fun k hk => hψb' k hk)
    (fun k hk => (hdef k hk).1) (fun k hk => (hdef k hk).2)
    (by
      have e : 2 * hi * (70 * hi * Rd ^ 4 * h ^ 2) / (1 / 2) = 280 * hi ^ 2 * Rd ^ 4 * h ^ 2 := by field_simp; ring
      rw [e]
      have e2 : ((N - J : ℤ) : ℝ) * (280 * hi ^ 2 * Rd ^ 4 * h ^ 2) = (((N - J : ℤ) : ℝ) * h) * (280 * hi ^ 2 * Rd ^ 4 * h) := by ring
      rw [e2, hΛdef]
      calc (((N - J : ℤ) : ℝ) * h) * (280 * hi ^ 2 * Rd ^ 4 * h) ≤ L * (280 * hi ^ 2 * Rd ^ 4 * h) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 280 * hi ^ 2 * Rd ^ 4 * L * h := by ring)
  have hexp : Real.exp Λ - 1 ≤ 2 * Λ := dlg_exp_small hΛ0 hΛ4
  have hmI : m ∈ Icc J N := by rw [Finset.mem_Icc]; omega
  have ham : |a (m + 1)| ≤ hi + E := by
    have hq1 := hU m (by rw [Finset.mem_Icc]; omega)
    have hq2 := hU (m + 1) (by rw [Finset.mem_Icc]; omega)
    have hmid := dlg_mid_mem D.convex hq1 (by rw [dlgQ_succ] at hq2; exact hq2 : dlgQ q0 h m + h ∈ U)
    have hAm := hA (m + 1) (by rw [Finset.mem_Icc]; omega)
    have e : dlgQ q0 h (m + 1) - h / 2 = dlgQ q0 h m + h / 2 := by rw [dlgQ_succ]; ring
    rw [e] at hAm
    have hAb := (D.Ab _ hmid).2
    have hApos := (D.Ab _ hmid).1
    have hh2' : E * h ^ 2 ≤ E := mul_le_of_le_one_right hE (pow_le_one₀ hh.le hh1)
    have := (abs_sub_abs_le_abs_sub (a (m + 1)) (A (dlgQ q0 h m + h / 2)))
    rw [abs_of_pos (D.lo_pos.trans_le hApos)] at this
    linarith
  refine ⟨hcas, ham, fun k hk => (hmarch k hk).trans (mul_le_mul_of_nonneg_left hexp (by positivity))⟩

/-- **Discrete Liouville-Green (Darboux) theorem in the oscillatory bulk, Cartesian form**: every exact solution is `α φ + β ψ` with the Cramer
coefficients `(α, β)` at any base bond `m`, up to `C h (|α| + |β|) w`; `|α| + |β| ≍ |Y_m| + |Y_{m+1}|`. -/
theorem dlg_bulk_cart (lo hi M E L : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧
      ∀ {A θ w Θ : ℝ → ℝ} {U : Set ℝ}, DlgData A θ w Θ U lo hi M →
      ∀ (q0 h : ℝ) (a c Y : ℤ → ℝ) (J N m : ℤ), 0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Icc J (N + 1), dlgQ q0 h k ∈ U) →
        (∀ k ∈ Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) →
        (∀ k ∈ Icc J (N + 1),
          |Y k - (vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m * dlgPhi w Θ q0 h k +
              vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m * dlgPsi w Θ q0 h k)| ≤
            C * h * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| +
              |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) * w (dlgQ q0 h k)) ∧
        |vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| + |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| ≤
          C * (|Y m| + |Y (m + 1)|) ∧
        |Y m| + |Y (m + 1)| ≤ C * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| +
          |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) := by
  obtain ⟨h0, C, hh0, hh01, hC0, hCa, hCb, hCd, H⟩ := dlg_bulk_core lo hi M E L hlo hhi hM hE hL
  refine ⟨h0, C, hh0, hh01, hC0, ?_⟩
  intro A θ w Θ U D q0 h a c Y J N m hh hh0' hJm hmN hlen hU hA hCc hY
  obtain ⟨hcas, ham, hd⟩ := H D q0 h a c Y J N m hh hh0' hJm hmN hlen hU hA hCc hY
  have hwk : ∀ k ∈ Icc J (N + 1), 0 ≤ w (dlgQ q0 h k) ∧ w (dlgQ q0 h k) ≤ hi := fun k hk =>
    ⟨(D.lo_pos.trans_le (D.wb _ (hU k hk)).1).le, (D.wb _ (hU k hk)).2⟩
  obtain ⟨c1, c2, c3⟩ := dlg_amp_cart (a := a) (Y := Y) (W := fun k => w (dlgQ q0 h k)) (P := dlgP Θ q0 h)
    (J := J) (N := N) (m := m) (hi := hi) (E := E)
    (Λ := 280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h) hJm hmN
    (fun k hk => (hwk k hk).1) (fun k hk => (hwk k hk).2) hcas ham hd
  have hhi0 : 0 ≤ 4 * (hi + E) * hi := by positivity
  refine ⟨fun k hk => (c1 k hk).trans ?_, c2.trans (mul_le_mul_of_nonneg_right hCb (by positivity)), ?_⟩
  · have hn0 : 0 ≤ |vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| + |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| := by
      positivity
    have hwk0 := (hwk k hk).1
    have p0 : 0 ≤ 560 * hi ^ 2 * dlgR lo hi M E ^ 4 * L := by
      have := dlgR_ge_one hlo hhi hM hE
      positivity
    have key : 560 * hi ^ 2 * dlgR lo hi M E ^ 4 * L ≤ C := by linarith
    have e : (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| + |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) *
        (2 * (280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h)) * w (dlgQ q0 h k) =
        (560 * hi ^ 2 * dlgR lo hi M E ^ 4 * L) * (h * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| +
          |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) * w (dlgQ q0 h k)) := by ring
    have hnn : 0 ≤ h * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| +
        |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) * w (dlgQ q0 h k) :=
      mul_nonneg (mul_nonneg hh.le hn0) hwk0
    have := mul_le_mul_of_nonneg_right key hnn
    refine le_trans (le_of_eq e) ?_
    have e2 : C * h * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| + |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) *
        w (dlgQ q0 h k) = C * (h * (|vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m| +
          |vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m|) * w (dlgQ q0 h k)) := by ring
    rw [e2]
    exact this
  · have : 4 * hi ≤ C := by linarith
    exact c3.trans (mul_le_mul_of_nonneg_right this (by positivity))

/-- **Discrete Liouville-Green (Darboux) theorem in the oscillatory bulk** (amplitude-phase form).  See the module docstring. -/
theorem dlg_bulk (lo hi M E L : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧
      ∀ {A θ w Θ : ℝ → ℝ} {U : Set ℝ}, DlgData A θ w Θ U lo hi M →
      ∀ (q0 h : ℝ) (a c Y : ℤ → ℝ) (J N m : ℤ), 0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Icc J (N + 1), dlgQ q0 h k ∈ U) →
        (∀ k ∈ Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) →
        ∃ R φ0 : ℝ, 0 ≤ R ∧
          (∀ k ∈ Icc J (N + 1), |Y k - R * w (dlgQ q0 h k) * Real.cos (dlgP Θ q0 h k - φ0)| ≤
            C * h * R * w (dlgQ q0 h k)) ∧
          R ≤ C * (|Y m| + |Y (m + 1)|) ∧ |Y m| + |Y (m + 1)| ≤ C * R := by
  obtain ⟨h0, C, hh0, hh01, hC0, hCa, hCb, hCd, H⟩ := dlg_bulk_core lo hi M E L hlo hhi hM hE hL
  refine ⟨h0, C, hh0, hh01, hC0, ?_⟩
  intro A θ w Θ U D q0 h a c Y J N m hh hh0' hJm hmN hlen hU hA hCc hY
  obtain ⟨hcas, ham, hd⟩ := H D q0 h a c Y J N m hh hh0' hJm hmN hlen hU hA hCc hY
  have hwk : ∀ k ∈ Icc J (N + 1), 0 ≤ w (dlgQ q0 h k) ∧ w (dlgQ q0 h k) ≤ hi := fun k hk =>
    ⟨(D.lo_pos.trans_le (D.wb _ (hU k hk)).1).le, (D.wb _ (hU k hk)).2⟩
  have hRd := dlgR_ge_one hlo hhi hM hE
  have hΛ0 : 0 ≤ 280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h := by positivity
  obtain ⟨R, φ0, hR0, hpt, hR1, hR2⟩ := dlg_amp_phase (a := a) (Y := Y) (W := fun k => w (dlgQ q0 h k))
    (P := dlgP Θ q0 h) (J := J) (N := N) (m := m) (hi := hi) (E := E)
    (Λ := 280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h) hΛ0 hJm hmN
    (fun k hk => (hwk k hk).1) (fun k hk => (hwk k hk).2) hcas ham hd
  have p2 : 0 ≤ 4 * (hi + E) * hi := by positivity
  refine ⟨R, φ0, hR0, fun k hk => (hpt k hk).trans ?_, hR1.trans (mul_le_mul_of_nonneg_right hCb (by positivity)),
    hR2.trans (mul_le_mul_of_nonneg_right hCd hR0)⟩
  have hwk0 := (hwk k hk).1
  have e : 4 * (280 * hi ^ 2 * dlgR lo hi M E ^ 4 * L * h) * R * w (dlgQ q0 h k) =
      (1120 * hi ^ 2 * dlgR lo hi M E ^ 4 * L) * (h * R * w (dlgQ q0 h k)) := by ring
  show _ ≤ C * h * R * _
  rw [e]
  have : 0 ≤ h * R * w (dlgQ q0 h k) := mul_nonneg (mul_nonneg hh.le hR0) hwk0
  have := mul_le_mul_of_nonneg_right hCa this
  linarith

/-- info: 'FormalResearch.Special.dlg_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk

/-- info: 'FormalResearch.Special.dlg_bulk_cart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk_cart

/-- info: 'FormalResearch.Special.dlg_amp_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_amp_phase

end FormalResearch.Special
