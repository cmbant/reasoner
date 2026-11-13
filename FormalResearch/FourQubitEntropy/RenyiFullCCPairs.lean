module

public import FormalResearch.FourQubitEntropy.RenyiFullCCBinary
public import FormalResearch.FourQubitEntropy.RenyiFullSliverProof
public import FormalResearch.FourQubitEntropy.RenyiFullCCCells
public import FormalResearch.FourQubitEntropy.RenyiFullNU

/-!
# Capped cubic lemma: the two pair charts `21/50 ≤ p ≤ 47/100`

Paper E, `lem:fqe-capped-cubic`, paragraph *The two pairs*.  For the ordered charts
`λ_S = ((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)` and `λ_B = ((1-u)/2, (1-u)/2, (u+δ)/2, (u-δ)/2)` and `v = δ²`:

* `renyi_group2`: Jensen's inequality for the logarithm,
  `H_q((1-u)a, u b) ≤ h(u) + (1-w) H_q(a) + w H_q(b)`, `w = u^q/((1-u)^q + u^q)`;
* `entS_cc`: `H_{q_s}(λ_S) ≤ 1 + h(u) - (1+2u) v`; `entB_cc`: `H_{q_s}(λ_B) ≤ 1 + h(u) - (3-2u) v` (CG3).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Filter Topology

/-- Jensen for the logarithm: grouping of two two-point blocks. -/
theorem renyi_group2 {q a0 a1 b0 b1 u : ℝ} (hq : 1 < q) (hu0 : 0 < u) (hu1 : u < 1)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hsa : a0 + a1 = 1)
    (hsb : b0 + b1 = 1) :
    renyiSpec q ![(1 - u) * a0, (1 - u) * a1, u * b0, u * b1] ≤
      -Real.log ((1 - u) ^ q + u ^ q) / ((q - 1) * Real.log 2) +
      ((1 - u) ^ q / ((1 - u) ^ q + u ^ q)) * renyiSpec q ![a0, a1] +
      (u ^ q / ((1 - u) ^ q + u ^ q)) * renyiSpec q ![b0, b1] := by
  have hq0 : 0 < q := by linarith
  have hr : 0 < (q - 1) * Real.log 2 := mul_pos (by linarith) log_two_pos'
  have h1u : 0 < 1 - u := by linarith
  have hM1 : 0 < (1 - u) ^ q := Real.rpow_pos_of_pos h1u q
  have hM2 : 0 < u ^ q := Real.rpow_pos_of_pos hu0 q
  set M := (1 - u) ^ q + u ^ q with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  have hSa : 0 < a0 ^ q + a1 ^ q := by
    have := PaperECritical.sum_rpow_pos_of_prob (u := ![a0, a1]) (by intro i; fin_cases i <;> simpa) (by simp [Fin.sum_univ_two, hsa]) hq0
    simpa [Fin.sum_univ_two] using this
  have hSb : 0 < b0 ^ q + b1 ^ q := by
    have := PaperECritical.sum_rpow_pos_of_prob (u := ![b0, b1]) (by intro i; fin_cases i <;> simpa) (by simp [Fin.sum_univ_two, hsb]) hq0
    simpa [Fin.sum_univ_two] using this
  set A := a0 ^ q + a1 ^ q with hA
  set B := b0 ^ q + b1 ^ q with hB
  have hsum : ∑ i, (![(1 - u) * a0, (1 - u) * a1, u * b0, u * b1] : Fin 4 → ℝ) i ^ q =
      (1 - u) ^ q * A + u ^ q * B := by
    simp only [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [Real.mul_rpow h1u.le ha0, Real.mul_rpow h1u.le ha1, Real.mul_rpow hu0.le hb0,
      Real.mul_rpow hu0.le hb1, hA, hB]
    ring
  rw [renyiSpec_eq_neg hq, hsum, renyiSpec_eq_neg hq (l := ![a0, a1]),
    renyiSpec_eq_neg hq (l := ![b0, b1])]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hA, ← hB]
  -- Jensen: log (w' A + w B) ≥ w' log A + w log B
  have hw1 : 0 ≤ (1 - u) ^ q / M := by positivity
  have hw2 : 0 ≤ u ^ q / M := by positivity
  have hw12 : (1 - u) ^ q / M + u ^ q / M = 1 := by
    rw [← add_div]; exact div_self hMpos.ne'
  have hJ := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hSa) (Set.mem_Ioi.2 hSb) hw1 hw2 hw12
  simp only [smul_eq_mul] at hJ
  have hlog : Real.log ((1 - u) ^ q * A + u ^ q * B) =
      Real.log M + Real.log ((1 - u) ^ q / M * A + u ^ q / M * B) := by
    rw [← Real.log_mul hMpos.ne' (by positivity)]
    congr 1
    field_simp
  rw [hlog]
  have key : -(Real.log M + Real.log ((1 - u) ^ q / M * A + u ^ q / M * B)) ≤
      -Real.log M - ((1 - u) ^ q / M * Real.log A + u ^ q / M * Real.log B) := by linarith
  have e : -Real.log M / ((q - 1) * Real.log 2) +
      (1 - u) ^ q / M * (-Real.log A / ((q - 1) * Real.log 2)) +
      u ^ q / M * (-Real.log B / ((q - 1) * Real.log 2)) =
      (-Real.log M - ((1 - u) ^ q / M * Real.log A + u ^ q / M * Real.log B)) / ((q - 1) * Real.log 2) := by
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right key hr.le

/-! ### Weight estimates -/

theorem qBQ_le : qBQ ≤ 8 / 5 := by unfold qBQ; norm_num
theorem three_halves_le_qBQ : (3 / 2 : ℝ) ≤ qBQ := by unfold qBQ; norm_num

/-- Chart `S`: the weight of the first block is at least `(1-u)²/((1-u)² + u² + u(1-u)/4)`. -/
theorem wS_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) :
    (1 - u) ^ 2 / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) ≤
      (1 - u) ^ qBQ / ((1 - u) ^ qBQ + u ^ qBQ) := by
  have h1u : 0 < 1 - u := by linarith
  set ρ := u / (1 - u) with hρ
  have hρ0 : 0 < ρ := div_pos hu0 h1u
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one h1u]; linarith
  have hu : u = (1 - u) * ρ := by rw [hρ]; field_simp
  have hpow : u ^ qBQ = (1 - u) ^ qBQ * ρ ^ qBQ := by
    conv_lhs => rw [hu]
    exact Real.mul_rpow h1u.le hρ0.le
  have h32 : ρ ^ qBQ ≤ ρ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 three_halves_le_qBQ
  have hsq := rpow_three_halves_eq_nu hρ0.le
  have hs0 := Real.sqrt_nonneg ρ
  have hss : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
  have hsle : Real.sqrt ρ ≤ ρ + 1 / 4 := by nlinarith [sq_nonneg (Real.sqrt ρ - 1 / 2)]
  have hT : ρ ^ qBQ ≤ ρ * (ρ + 1 / 4) := by
    rw [hsq] at h32
    nlinarith [mul_le_mul_of_nonneg_left hsle hρ0.le]
  have hA : 0 < (1 - u) ^ qBQ := Real.rpow_pos_of_pos h1u _
  have hM : (1 - u) ^ qBQ + u ^ qBQ ≤ (1 - u) ^ qBQ * (1 + ρ * (ρ + 1 / 4)) := by
    rw [hpow]; nlinarith [mul_le_mul_of_nonneg_left hT hA.le]
  have hMpos : 0 < (1 - u) ^ qBQ + u ^ qBQ := by rw [hpow]; have := Real.rpow_pos_of_pos hρ0 qBQ; positivity
  have hD : 0 < (1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4 := by positivity
  have e : (1 - u) ^ 2 / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) = 1 / (1 + ρ * (ρ + 1 / 4)) := by
    rw [hρ]; field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) hMpos]
  nlinarith [hM]

theorem M_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 3 / 32) :
    (1 - u) ^ qBQ + u ^ qBQ ≤ 1 - u := by
  have h1u : 0 < 1 - u := by linarith
  have a1 : (1 - u) ^ qBQ ≤ (1 - u) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge h1u (by linarith) three_halves_le_qBQ
  have a2 : u ^ qBQ ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hu0 (by linarith) three_halves_le_qBQ
  rw [rpow_three_halves_eq_nu h1u.le] at a1
  rw [rpow_three_halves_eq_nu hu0.le] at a2
  have s1 : Real.sqrt (1 - u) ≤ 1 - u / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith [sq_nonneg u]
  have s2 : Real.sqrt u ≤ 1 / 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have b1 : (1 - u) * Real.sqrt (1 - u) ≤ (1 - u) * (1 - u / 2) := mul_le_mul_of_nonneg_left s1 h1u.le
  have b2 : u * Real.sqrt u ≤ u * (1 / 3) := mul_le_mul_of_nonneg_left s2 hu0.le
  nlinarith

/-- Chart `B`: the weight of the second block is at least `u² (3 - 2u)`. -/
theorem wB_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 3 / 32) :
    u ^ 2 * (3 - 2 * u) ≤ u ^ qBQ / ((1 - u) ^ qBQ + u ^ qBQ) := by
  have h1u : 0 < 1 - u := by linarith
  have hM := M_le hu0 hu1
  have hMpos : 0 < (1 - u) ^ qBQ + u ^ qBQ := by
    have := Real.rpow_pos_of_pos h1u qBQ; have := Real.rpow_pos_of_pos hu0 qBQ; linarith
  have h1 : u ^ (8 / 5 : ℝ) ≤ u ^ qBQ := Real.rpow_le_rpow_of_exponent_ge hu0 (by linarith) qBQ_le
  have h2 : u ^ 2 * ((1 - u) * (3 - 2 * u)) ≤ u ^ (8 / 5 : ℝ) := by
    have hb : 0 < u ^ 2 * ((1 - u) * (3 - 2 * u)) := by
      have : 0 < 3 - 2 * u := by linarith
      positivity
    have key : (u ^ 2 * ((1 - u) * (3 - 2 * u))) ^ 5 ≤ u ^ 8 := by
      have hp := cc_wB_poly hu0.le hu1
      have h8 : 0 < u ^ 8 := by positivity
      have e : (u ^ 2 * ((1 - u) * (3 - 2 * u))) ^ 5 = u ^ 8 * (u ^ 2 * ((1 - u) * (3 - 2 * u)) ^ 5) := by ring
      rw [e]
      nlinarith
    have := le_rpow_of_pow_le hb hu0 (m := 8) (n := 5) (by norm_num) key
    have e : ((8 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 8 / 5 := by norm_num
    rwa [e] at this
  rw [le_div_iff₀ hMpos]
  have hu2 : 0 < u ^ 2 * (3 - 2 * u) := by
    have : 0 < 3 - 2 * u := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hM hu2.le]

/-! ### The entropy of the two charts (CG3) -/

theorem binH_symm (q u : ℝ) : binH q (1 - u) = binH q u := by
  unfold binH
  rw [sub_sub_cancel, add_comm]

/-- Entropy of an imbalanced pair, deficit form: `H(((1+ρ)/2,(1-ρ)/2)) = binH ((1-ρ)/2)`. -/
theorem renyiSpec_pair {ρ : ℝ} : renyiSpec qBQ ![(1 + ρ) / 2, (1 - ρ) / 2] = binH qBQ ((1 - ρ) / 2) := by
  have e : (![(1 + ρ) / 2, (1 - ρ) / 2] : Fin 2 → ℝ) = ![(1 + ρ) / 2, 1 - (1 + ρ) / 2] := by
    congr 1; ext i; fin_cases i ; simp ; ring
  rw [e, renyiSpec_binary, ← binH_symm]
  congr 1; ring

theorem renyiSpec_half : renyiSpec qBQ ![(1 / 2 : ℝ), 1 / 2] = 1 := by
  have e : (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) = ![1 / 2, 1 - 1 / 2] := by
    congr 1; ext i; fin_cases i ; simp ; norm_num
  rw [e, renyiSpec_binary, binH_half]

theorem binH_eq_neg_log' (u : ℝ) :
    binH qBQ u = -Real.log ((1 - u) ^ qBQ + u ^ qBQ) / ((qBQ - 1) * Real.log 2) := by
  rw [binH_eq_neg_log, add_comm]

/-- **(CG3), chart `S`.** -/
theorem entS_cc {u δ : ℝ} (hu : 3 / 100 ≤ u) (hu2 : u ≤ 4 / 15) (hδ0 : 0 ≤ δ)
    (hδ : δ ^ 2 ≤ 2 / 3 * (1 - u) ^ 2) :
    renyiSpec qS ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤
      1 + binH qBQ u - (1 + 2 * u) * δ ^ 2 := by
  have hqq : qS = qBQ := by unfold qS qBQ; rfl
  rw [hqq]
  have h1u : 0 < 1 - u := by linarith
  set ρ := δ / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hδ0 h1u.le
  have hδρ : δ = (1 - u) * ρ := by rw [hρ]; field_simp
  have hρ2 : ρ ^ 2 ≤ 2 / 3 := by
    have : (1 - u) ^ 2 * ρ ^ 2 ≤ (1 - u) ^ 2 * (2 / 3) := by
      rw [hδρ] at hδ; nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hρ56 : ρ ≤ 5 / 6 := by nlinarith
  have hvec : (![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] : Fin 4 → ℝ) =
      ![(1 - u) * ((1 + ρ) / 2), (1 - u) * ((1 - ρ) / 2), u * (1 / 2), u * (1 / 2)] := by
    ext i; fin_cases i <;> simp [hδρ] <;> ring
  rw [hvec]
  have hg := renyi_group2 (q := qBQ) (a0 := (1 + ρ) / 2) (a1 := (1 - ρ) / 2) (b0 := 1 / 2) (b1 := 1 / 2)
    (u := u) (by unfold qBQ; norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by ring) (by norm_num)
  rw [renyiSpec_half, renyiSpec_pair, ← binH_eq_neg_log'] at hg
  -- the pair bound
  have hq2 := bin_quartic2 (u := (1 - ρ) / 2) (by linarith) (by linarith)
  have hRHS : 4 * ((1 - ρ) / 2) * (1 - (1 - ρ) / 2) - 3 / 8 * ((1 - ρ) / 2 * (1 - (1 - ρ) / 2) *
      (1 - 2 * ((1 - ρ) / 2)) ^ 2) = 1 - ρ ^ 2 - 3 / 32 * ((1 - ρ ^ 2) * ρ ^ 2) := by ring
  rw [hRHS] at hq2
  -- weights
  have hu0 : 0 < u := by linarith
  have hw := wS_lower hu0 (by linarith : u ≤ 1 / 2)
  have hMpos : 0 < (1 - u) ^ qBQ + u ^ qBQ := by
    have := Real.rpow_pos_of_pos h1u qBQ; have := Real.rpow_pos_of_pos hu0 qBQ; linarith
  set M := (1 - u) ^ qBQ + u ^ qBQ with hM
  have hw12 : (1 - u) ^ qBQ / M + u ^ qBQ / M = 1 := by
    rw [← add_div]; exact div_self hMpos.ne'
  have hw'0 : 0 ≤ (1 - u) ^ qBQ / M := by
    have := Real.rpow_pos_of_pos h1u qBQ; positivity
  have hH : binH qBQ ((1 - ρ) / 2) ≤ 1 - 33 / 32 * ρ ^ 2 := by
    have h13 : 0 ≤ ρ ^ 2 * (2 / 3 - ρ ^ 2) := mul_nonneg (sq_nonneg ρ) (by linarith)
    nlinarith [hq2, h13]
  have hDn : 0 < (1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4 := by positivity
  have hpoly : (1 + 2 * u) ≤ (33 / 32) / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) := by
    rw [le_div_iff₀ hDn]
    nlinarith [mul_nonneg (sq_nonneg u) (show (0 : ℝ) ≤ 4 / 15 - u by linarith), sq_nonneg u]
  have hkey : (1 + 2 * u) * δ ^ 2 ≤ (1 - u) ^ qBQ / M * (33 / 32 * ρ ^ 2) := by
    have e1 : δ ^ 2 = (1 - u) ^ 2 * ρ ^ 2 := by rw [hδρ]; ring
    have h2 : (1 - u) ^ 2 / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) * (33 / 32 * ρ ^ 2) ≤
        (1 - u) ^ qBQ / M * (33 / 32 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    have h3 : (1 + 2 * u) * δ ^ 2 ≤ (1 - u) ^ 2 / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) * (33 / 32 * ρ ^ 2) := by
      have : (1 - u) ^ 2 / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) * (33 / 32 * ρ ^ 2) =
          (33 / 32) / ((1 - u) ^ 2 + u ^ 2 + u * (1 - u) / 4) * ((1 - u) ^ 2 * ρ ^ 2) := by
        field_simp
      rw [this, e1]
      exact mul_le_mul_of_nonneg_right hpoly (by positivity)
    linarith
  have hfin : (1 - u) ^ qBQ / M * binH qBQ ((1 - ρ) / 2) ≤ (1 - u) ^ qBQ / M * (1 - 33 / 32 * ρ ^ 2) :=
    mul_le_mul_of_nonneg_left hH hw'0
  nlinarith [hg, hfin, hkey, hw12]

/-- **(CG3), chart `B`.** -/
theorem entB_cc {u δ : ℝ} (hu : 3 / 100 ≤ u) (hu2 : u ≤ 3 / 32) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) :
    renyiSpec qS ![(1 - u) / 2, (1 - u) / 2, (u + δ) / 2, (u - δ) / 2] ≤
      1 + binH qBQ u - (3 - 2 * u) * δ ^ 2 := by
  have hqq : qS = qBQ := by unfold qS qBQ; rfl
  rw [hqq]
  have hu0 : 0 < u := by linarith
  have h1u : 0 < 1 - u := by linarith
  set ρ := δ / u with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hδ0 hu0.le
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hu0]; exact hδu
  have hδρ : δ = u * ρ := by rw [hρ]; field_simp
  have hvec : (![(1 - u) / 2, (1 - u) / 2, (u + δ) / 2, (u - δ) / 2] : Fin 4 → ℝ) =
      ![(1 - u) * (1 / 2), (1 - u) * (1 / 2), u * ((1 + ρ) / 2), u * ((1 - ρ) / 2)] := by
    ext i; fin_cases i <;> simp [hδρ] <;> ring
  rw [hvec]
  have hg := renyi_group2 (q := qBQ) (a0 := 1 / 2) (a1 := 1 / 2) (b0 := (1 + ρ) / 2) (b1 := (1 - ρ) / 2)
    (u := u) (by unfold qBQ; norm_num) hu0 (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by norm_num) (by ring)
  rw [renyiSpec_half, renyiSpec_pair, ← binH_eq_neg_log'] at hg
  have hc := bin_cubic (u := (1 - ρ) / 2) (by linarith) (by linarith)
  have hRHS : 4 * ((1 - ρ) / 2) * (1 - (1 - ρ) / 2) = 1 - ρ ^ 2 := by ring
  rw [hRHS] at hc
  have hMpos : 0 < (1 - u) ^ qBQ + u ^ qBQ := by
    have := Real.rpow_pos_of_pos h1u qBQ; have := Real.rpow_pos_of_pos hu0 qBQ; linarith
  have hw := wB_lower hu0 hu2
  set M := (1 - u) ^ qBQ + u ^ qBQ with hM
  have hw12 : (1 - u) ^ qBQ / M + u ^ qBQ / M = 1 := by
    rw [← add_div]; exact div_self hMpos.ne'
  have hw0 : 0 ≤ u ^ qBQ / M := by
    have := Real.rpow_pos_of_pos hu0 qBQ; positivity
  have hkey : (3 - 2 * u) * δ ^ 2 ≤ u ^ qBQ / M * ρ ^ 2 := by
    have e1 : δ ^ 2 = u ^ 2 * ρ ^ 2 := by rw [hδρ]; ring
    rw [e1]
    have := mul_le_mul_of_nonneg_right hw (sq_nonneg ρ)
    nlinarith [this]
  have hfin : u ^ qBQ / M * binH qBQ ((1 - ρ) / 2) ≤ u ^ qBQ / M * (1 - ρ ^ 2) :=
    mul_le_mul_of_nonneg_left hc hw0
  nlinarith [hg, hfin, hkey, hw12]

end FormalResearch.FourQubitEntropy.RenyiFull
