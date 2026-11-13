module

public import FormalResearch.Racah.P2AnalyticNLO6jDeriv
public import FormalResearch.Racah.P2AnalyticBridge6j

/-!
# First `6j` correction, canonical sector (Weyl P2, `thm:6jclosedcorrection`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jclosedcorrection` (`eq:6jclosedg`,
`eq:6jPf`, `eq:6jQf`), `eq:grec`, `eq:glocalforcing`, `eq:kappaClosedMatch`, `eq:gexceptional`.

Route (as for `thm:3jNLO`): the true `t`-derivative of the carrier,
`e_d = W(x) q_d` with `W = √(((1-x)/2)^p((1+x)/2)^q)`, satisfies (`q6_rank`, the carrier recurrence
differentiated in `t`) the same inhomogeneous rank recurrence as
`H_f + μ d_f` (`nlo6H_rec`: ladders differentiated once in `x` and the Wigner ODE), the starts
agree (`nlo6_seed_alg` for `m > 0`, a direct computation for `m = n = 0`), so
`rec_seq_ext` gives `e_d = H_{m+d} + μ d_{m+d}` for all `d` (`nlo6_e_eq`).

## Results

* `nlo6_e_eq`: `W(x) q_d = H_{m+d} + μ d_{m+d}` (canonical sector, `x ∈ (-1,1)`).
* `hasDerivAt_G6c_closed`: `∂_t G6c(·,t)|_{t=0} = P_f d' + Q_f d` (`nlo6G`), canonical sector.
* `a6_one_closed` (**`eq:6jclosedg`**, all four chambers): `a_{f,1} = ∂_t G6|_{t=0}` is the closed form,
  on every strict-triangle shape.
* `G6even_one_eq_closed`: `G_{f,2}(A,B,C) = G6closed f m n A B C = P_f ∂_x d + Q_f d` on the cone.
* `Phi6_nlo_expansion`, `Phi6_nlo_expansion_cone` (**`thm:6jclosedcorrection` with remainder**):
  `|Φ_f - d^f_{nm}(arccos x) - G_{f,2}| ≤ C S⁻⁴` uniformly on compact strict-triangle shape sets
  (resp. `≤ C H⁻⁴` on `T_δ`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set

lemma nlo6_wdx_zero_zero_zero {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : wignerSmallDx 0 0 0 y = 1 := by
  have h := dZero6c_start_eq_wignerD 0 0 0 0 (by simp) (by simp) hy
  unfold dZero6c at h
  simp [ptilde6_zero] at h
  simpa using h.symm

lemma nlo6_wdx_one_zero_zero {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : wignerSmallDx 1 0 0 y = y := by
  unfold wignerSmallDx
  rw [wignerSmallD_one_zero_zero, Real.cos_arccos hy.1 hy.2]


/-! ### Sequences along the rank -/

/-- `d_{m+k} = d^{m+k}_{nm}(arccos x)` and its `x`-derivative. -/
noncomputable def nlo6D (m n : ℚ) (x : ℝ) (k : ℕ) : ℝ := wignerSmallDx (m + (k : ℚ)) n m x

noncomputable def nlo6D' (m n : ℚ) (x : ℝ) (k : ℕ) : ℝ := deriv (wignerSmallDx (m + (k : ℚ)) n m) x

/-- `H_{m+k} = G_{m+k,2} - ρ(2f+1)f(f+1)/6 · d_{m+k}`, `f = m+k`. -/
noncomputable def nlo6Hs (m n : ℚ) (ρ w x : ℝ) (k : ℕ) : ℝ :=
  nlo6Hr (((m + (k : ℚ) : ℚ)) : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x
    (nlo6D m n x k) (nlo6D' m n x k)

/-- Pure algebra of one induction step. -/
lemma nlo6_step (F R1 R2 S T ρ w x μ e0 e1 e2 H0 H1 H2 D0 D1 D2 : ℝ)
    (hq : F * R2 * e2 = (2 * F + 1) * (F * (F + 1) * x - T) * e1 -
        (2 * F + 1) * (F * (F + 1)) * (2 * (F * (F + 1)) + 1 - S) / 8 * w * D1 -
        (F + 1) * R1 * (e0 - 2 * ρ * F ^ 2 * D0))
    (hH : (2 * F + 1) * (F * (F + 1) * x - T) * H1 =
      (F + 1) * (R1 * H0 - 2 * ρ * F ^ 2 * (R1 * D0)) + F * (R2 * H2) +
        (2 * F + 1) * (F * (F + 1)) * (2 * (F * (F + 1)) + 1 - S) * w / 8 * D1)
    (hW : (2 * F + 1) * (F * (F + 1) * x - T) * D1 = (F + 1) * (R1 * D0) + F * (R2 * D2)) :
    F * R2 * (e2 - (H2 + μ * D2)) =
      (2 * F + 1) * (F * (F + 1) * x - T) * (e1 - (H1 + μ * D1)) -
        (F + 1) * R1 * (e0 - (H0 + μ * D0)) := by
  linear_combination hq + hH + μ * hW


/-- The rank ladder recurrence along the sequence `d_{m+k}`. -/
lemma nlo6D_rec (m n : ℚ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (j : ℕ) (L : ℝ)
    (hL : L = ((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ)) :
    (2 * L + 1) * (L * (L + 1) * x - (m : ℝ) * n) * nlo6D m n x (j + 1) =
      (L + 1) * (rootR m n L * nlo6D m n x j) +
        L * (rootR m n (L + 1) * nlo6D m n x (j + 1 + 1)) := by
  subst hL
  have h := wignerSmallDx_rank_rec (m + ((j + 1 : ℕ) : ℚ)) n m hx
  have e1 : m + ((j + 1 : ℕ) : ℚ) - 1 = m + (j : ℚ) := by push_cast; ring
  have e2 : m + ((j + 1 : ℕ) : ℚ) + 1 = m + ((j + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [e1, e2] at h
  simp only [wigR_eq_rootR] at h
  have hR2 : rootR (m : ℝ) (n : ℝ) (((m + ((j + 1 + 1 : ℕ) : ℚ) : ℚ) : ℝ)) =
      rootR (m : ℝ) (n : ℝ) ((((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ)) + 1) := by
    congr 1; push_cast; ring
  rw [hR2] at h
  exact h

/-- The inhomogeneous rank recurrence along the sequence `H_{m+k}` (`nlo6H_rec`, in sequence form). -/
lemma nlo6Hs_rec (m n : ℚ) (ρ w : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (j : ℕ) (L : ℝ)
    (hL : L = ((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ)) :
    (2 * L + 1) * (L * (L + 1) * x - (m : ℝ) * n) * nlo6Hs m n ρ w x (j + 1) =
      (L + 1) * (rootR m n L * nlo6Hs m n ρ w x j -
          2 * ρ * L ^ 2 * (rootR m n L * nlo6D m n x j)) +
        L * (rootR m n (L + 1) * nlo6Hs m n ρ w x (j + 1 + 1)) +
        (2 * L + 1) * (L * (L + 1)) * (2 * (L * (L + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) *
          w / 8 * nlo6D m n x (j + 1) := by
  subst hL
  have h := nlo6H_rec (m + ((j + 1 : ℕ) : ℚ)) m n ρ w hx
  have e1 : m + ((j + 1 : ℕ) : ℚ) - 1 = m + (j : ℚ) := by push_cast; ring
  have e2 : m + ((j + 1 : ℕ) : ℚ) + 1 = m + ((j + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [e1, e2] at h
  simp only [wigR_eq_rootR] at h
  have hR2 : rootR (m : ℝ) (n : ℝ) (((m + ((j + 1 + 1 : ℕ) : ℚ) : ℚ) : ℝ)) =
      rootR (m : ℝ) (n : ℝ) ((((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ)) + 1) := by
    congr 1; push_cast; ring
  rw [hR2] at h
  exact h


/-- Scalar sector `m = n = 0`: `d_0 = 1`, `d_0' = 0`. -/
lemma nlo6_scalar_D0 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : nlo6D 0 0 x 0 = 1 ∧ nlo6D' 0 0 x 0 = 0 := by
  have heq : wignerSmallDx 0 0 0 =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact nlo6_wdx_zero_zero_zero ⟨hy.1.le, hy.2.le⟩
  constructor
  · simpa [nlo6D] using nlo6_wdx_zero_zero_zero ⟨hx.1.le, hx.2.le⟩
  · simp only [nlo6D', Nat.cast_zero, add_zero]
    rw [heq.deriv_eq]; simp

/-- Scalar sector: `d_1 = x`, `d_1' = 1`. -/
lemma nlo6_scalar_D1 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : nlo6D 0 0 x 1 = x ∧ nlo6D' 0 0 x 1 = 1 := by
  have heq : wignerSmallDx 1 0 0 =ᶠ[nhds x] fun y => y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact nlo6_wdx_one_zero_zero ⟨hy.1.le, hy.2.le⟩
  constructor
  · simpa [nlo6D] using nlo6_wdx_one_zero_zero ⟨hx.1.le, hx.2.le⟩
  · simp only [nlo6D', Nat.cast_one, zero_add]
    rw [heq.deriv_eq]; simp

lemma nlo6_scalar_H0 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (ρ w : ℝ) : nlo6Hs 0 0 ρ w x 0 = 0 := by
  obtain ⟨h1, h2⟩ := nlo6_scalar_D0 hx
  unfold nlo6Hs
  rw [h1, h2]
  simp [nlo6Hr, nlo6G, nlo6P, nlo6Q]

lemma nlo6_scalar_H1 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (ρ w : ℝ) :
    nlo6Hs 0 0 ρ w x 1 = -w / 8 := by
  obtain ⟨h1, h2⟩ := nlo6_scalar_D1 hx
  have hu : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold nlo6Hs
  rw [h1, h2]
  simp only [Rat.cast_zero, Nat.cast_one, zero_add, Rat.cast_one]
  unfold nlo6Hr nlo6G nlo6P nlo6Q
  field_simp
  ring

/-- **The `t`-derivative of the carrier is `H + μ d`** (canonical sector): for `x ∈ (-1,1)`,
`W(x) q_d = H_{m+d} + μ d_{m+d}`, `ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`,
`μ = nlo6Mu p q ρ w x`. -/
theorem nlo6_e_eq (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (α β ρ w : ℝ) (hρ : ρ = ((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8)
    (hw : w = 1 / (α * β)) (d : ℕ) :
    Real.sqrt (((1 - x) / 2) ^ p * ((1 + x) / 2) ^ q) * q6 m n d α β ((1 - x) / 2) =
      nlo6Hs m n ρ w x d + nlo6Mu (p : ℝ) (q : ℝ) ρ w x * nlo6D m n x d := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  obtain ⟨f1, f2, f3⟩ := floor_labels m n p q hp hq
  have hp' : (m : ℝ) - n = p := by exact_mod_cast hp
  have hq' : (m : ℝ) + n = q := by exact_mod_cast hq
  have hm0 : (0 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  set μ : ℝ := nlo6Mu (p : ℝ) (q : ℝ) ρ w x with hμ
  set s : ℝ := Real.sqrt (((1 - x) / 2) ^ p * ((1 + x) / 2) ^ q) with hs
  have hd : ∀ j : ℕ, s * ptilde6 m n ((1 - x) / 2) 0 0 0 j = nlo6D m n x j := by
    intro j
    have := dZero6c_eq_wignerD m n p q hp hq hxI j
    unfold dZero6c at this
    rw [f1, f2] at this
    exact this
  have hR_pos : ∀ k : ℝ, (m : ℝ) < k → 0 < rootR (m : ℝ) (n : ℝ) k := fun k hk =>
    rootR_pos_canon p q hp hq hk
  have hscalar : m = 0 → m = 0 ∧ n = 0 ∧ p = 0 ∧ q = 0 := by
    intro h0
    subst h0
    have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
    have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    have hn : n = 0 := by linarith
    have hp0 : p = 0 := by
      have : (p : ℚ) = 0 := by linarith
      exact_mod_cast this
    have hq0 : q = 0 := by
      have : (q : ℚ) = 0 := by linarith
      exact_mod_cast this
    exact ⟨rfl, hn, hp0, hq0⟩
  have hμ0 : m = 0 → μ = 0 := by
    intro h0
    obtain ⟨-, -, hp0, hq0⟩ := hscalar h0
    rw [hμ, hp0, hq0]; simp [nlo6Mu, nlo6cc]
  -- the two starts
  have hst0 : nlo6Hs m n ρ w x 0 + μ * nlo6D m n x 0 = 0 := by
    by_cases h0 : m = 0
    · obtain ⟨-, hn, -, -⟩ := hscalar h0
      have := hμ0 h0
      subst h0 hn
      rw [this, nlo6_scalar_H0 hx]; simp
    · have hmpos : (0 : ℝ) < m := lt_of_le_of_ne hm0 (by exact_mod_cast Ne.symm h0)
      have hlad := wignerSmallDx_rank_lower m n m hx
      have hR0 : wigR m n m = 0 := by unfold wigR; simp
      rw [hR0, zero_mul] at hlad
      have hseed := nlo6_seed_alg x (m : ℝ) (n : ℝ) ρ w (wignerSmallDx m n m x)
        (deriv (wignerSmallDx m n m) x) hx.1 hx.2 hmpos (by linear_combination -hlad)
      rw [hp', hq'] at hseed
      simpa [nlo6Hs, nlo6D, nlo6D', hμ] using hseed
  have hst1 : s * q6 m n 1 α β ((1 - x) / 2) -
      (nlo6Hs m n ρ w x 1 + μ * nlo6D m n x 1) = 0 := by
    by_cases h0 : m = 0
    · obtain ⟨-, hn, hp0, hq0⟩ := hscalar h0
      have := hμ0 h0
      subst h0 hn hp0 hq0
      rw [this, nlo6_scalar_H1 hx, q6_one_of_eq, hw]
      simp [hs]
    · have hmpos : (0 : ℝ) < m := lt_of_le_of_ne hm0 (by exact_mod_cast Ne.symm h0)
      have hR : 0 < rootR (m : ℝ) (n : ℝ) ((m : ℝ) + 1) := hR_pos _ (by linarith)
      have hmR : (m : ℝ) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + 1) ≠ 0 := (mul_pos hmpos hR).ne'
      have hq1 := q6_one_of_ne m n α β ((1 - x) / 2) hmR
      have hH := nlo6H_rec m m n ρ w hx
      have hW := wignerSmallDx_rank_rec m n m hxI
      have hR0 : wigR m n m = 0 := by unfold wigR; simp
      rw [hR0] at hH hW
      rw [wigR_eq_rootR] at hH hW
      simp only [Rat.cast_add, Rat.cast_one] at hH hW
      have eH : nlo6Hs m n ρ w x 1 = nlo6Hr ((m : ℝ) + 1) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
          ((m : ℝ) * n) ρ w x (wignerSmallDx (m + 1) n m x)
          (deriv (wignerSmallDx (m + 1) n m) x) := by simp [nlo6Hs, nlo6D, nlo6D']
      have eD : nlo6D m n x 1 = wignerSmallDx (m + 1) n m x := by simp [nlo6D]
      have eH0 : nlo6Hs m n ρ w x 0 = nlo6Hr (m : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
          ((m : ℝ) * n) ρ w x (wignerSmallDx m n m x) (deriv (wignerSmallDx m n m) x) := by
        simp [nlo6Hs, nlo6D, nlo6D']
      have eD0 : nlo6D m n x 0 = wignerSmallDx m n m x := by simp [nlo6D]
      have hd0 := hd 0
      rw [eD0] at hd0
      rw [eH0, eD0] at hst0
      rw [eH, eD]
      refine (mul_eq_zero.mp (?_ : (m : ℝ) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + 1) *
        (s * q6 m n 1 α β ((1 - x) / 2) -
          (nlo6Hr ((m : ℝ) + 1) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x
            (wignerSmallDx (m + 1) n m x) (deriv (wignerSmallDx (m + 1) n m) x) +
            μ * wignerSmallDx (m + 1) n m x)) = 0)).resolve_left hmR
      linear_combination s * hq1 - (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) * x - m * n) * hst0 -
        ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) *
          (2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 * w) * hd0 +
        hH + μ * hW +
        ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) *
          (2 * ((m : ℝ) * ((m : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 *
            (s * ptilde6 m n ((1 - x) / 2) 0 0 0 0)) * hw
  -- the recurrence
  have hrec : ∀ (j : ℕ) (L : ℝ), L = ((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) →
      L * rootR (m : ℝ) (n : ℝ) (L + 1) *
          (s * q6 m n (j + 2) α β ((1 - x) / 2) -
            (nlo6Hs m n ρ w x (j + 1 + 1) + μ * nlo6D m n x (j + 1 + 1))) =
        (2 * L + 1) * (L * (L + 1) * x - (m : ℝ) * n) *
            (s * q6 m n (j + 1) α β ((1 - x) / 2) -
              (nlo6Hs m n ρ w x (j + 1) + μ * nlo6D m n x (j + 1))) -
          (L + 1) * rootR (m : ℝ) (n : ℝ) L *
            (s * q6 m n j α β ((1 - x) / 2) - (nlo6Hs m n ρ w x j + μ * nlo6D m n x j)) := by
    intro j L hL
    have hLF : (m : ℝ) + j + 1 = L := by rw [hL]; push_cast; ring
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hLpos : 0 < L := by rw [← hLF]; linarith
    have hR2 := hR_pos (L + 1) (by linarith)
    have hFR : ((m : ℝ) + j + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + j + 1 + 1) ≠ 0 := by
      rw [hLF]; exact (mul_pos hLpos hR2).ne'
    have hq0 := q6_rank m n j α β ((1 - x) / 2) hFR
    rw [hLF] at hq0
    have hH := nlo6Hs_rec m n ρ w hx j L hL
    have hW := nlo6D_rec m n hxI j L hL
    have hd1 := hd (j + 1)
    have hd0 := hd j
    have hqe : L * rootR (m : ℝ) (n : ℝ) (L + 1) * (s * q6 m n (j + 2) α β ((1 - x) / 2)) =
        (2 * L + 1) * (L * (L + 1) * x - (m : ℝ) * n) * (s * q6 m n (j + 1) α β ((1 - x) / 2)) -
          (2 * L + 1) * (L * (L + 1)) * (2 * (L * (L + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 *
            w * nlo6D m n x (j + 1) -
          (L + 1) * rootR (m : ℝ) (n : ℝ) L *
            (s * q6 m n j α β ((1 - x) / 2) - 2 * ρ * L ^ 2 * nlo6D m n x j) := by
      rw [hρ, hw] at *
      linear_combination s * hq0 -
        ((2 * L + 1) * (L * (L + 1)) * (2 * (L * (L + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / 8 *
          (1 / (α * β))) * hd1 +
        ((L + 1) * rootR (m : ℝ) (n : ℝ) L * (L ^ 2 / 4 * ((α ^ 2)⁻¹ + (β ^ 2)⁻¹))) * hd0
    exact nlo6_step L (rootR (m : ℝ) (n : ℝ) L) (rootR (m : ℝ) (n : ℝ) (L + 1))
      ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x μ
      (s * q6 m n j α β ((1 - x) / 2)) (s * q6 m n (j + 1) α β ((1 - x) / 2))
      (s * q6 m n (j + 2) α β ((1 - x) / 2))
      (nlo6Hs m n ρ w x j) (nlo6Hs m n ρ w x (j + 1)) (nlo6Hs m n ρ w x (j + 1 + 1))
      (nlo6D m n x j) (nlo6D m n x (j + 1)) (nlo6D m n x (j + 1 + 1)) hqe hH hW
  obtain ⟨Lr, hLr⟩ : ∃ Lr : ℕ → ℝ, ∀ j, Lr j = ((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) :=
    ⟨fun j => ((m + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ), fun _ => rfl⟩
  have hδ := rec_seq_ext
    (fun j => s * q6 m n j α β ((1 - x) / 2) - (nlo6Hs m n ρ w x j + μ * nlo6D m n x j))
    (fun _ => (0 : ℝ))
    (fun j => Lr j * rootR (m : ℝ) (n : ℝ) (Lr j + 1))
    (fun j => (2 * Lr j + 1) * (Lr j * (Lr j + 1) * x - (m : ℝ) * n))
    (fun j => (Lr j + 1) * rootR (m : ℝ) (n : ℝ) (Lr j))
    (by simp only [q6_zero, mul_zero, zero_sub]; linarith)
    hst1
    (by
      intro j
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hLF : Lr j = (m : ℝ) + j + 1 := by rw [hLr]; push_cast; ring
      have hLpos : 0 < Lr j := by rw [hLF]; linarith
      have hR2 := hR_pos (Lr j + 1) (by linarith)
      exact (mul_pos hLpos hR2).ne')
    (fun j => hrec j (Lr j) (hLr j)) (fun j => by simp)
  have := hδ d
  linarith


/-- **`∂_t G6c` at `t = 0` is the closed form `G_{f,2}`** (canonical sector, strict-triangle shape):
`∂_t G6c(·,t)|_{t=0} = P_f d' + Q_f d` (`nlo6G`), `f = m + d`, `d = wignerSmallDx f n m` at
`x = cosA α β γ`, with `ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`. -/
theorem hasDerivAt_G6c_closed (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ)
    (f : ℚ) (hf : f = m + (d : ℚ)) {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) (ρ w x : ℝ)
    (hρ : ρ = ((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (hw : w = 1 / (α * β)) (hxx : x = cosA α β γ) :
    HasDerivAt (fun t => G6c m n d α β γ t)
      (nlo6G ((f : ℝ) * ((f : ℝ) + 1)) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x
        (wignerSmallDx f n m x) (deriv (wignerSmallDx f n m) x)) 0 := by
  have hxI := nlo6_cosA_mem_Ioo hz
  rw [← hxx] at hxI
  have h := hasDerivAt_G6c_t m n p q hp hq d hz
  refine h.congr_deriv ?_
  rw [← hρ, ← hw, ← hxx]
  have he := nlo6_e_eq m n p q hp hq hxI α β ρ w hρ hw d
  have hb := dZero6c_eq_wignerD m n p q hp hq ⟨hxI.1.le, hxI.2.le⟩ d
  rw [he, hb, ← hf]
  have hfr : (f : ℝ) = (m : ℝ) + (d : ℝ) := by rw [hf]; push_cast; ring
  have hHs : nlo6Hs m n ρ w x d =
      nlo6G ((f : ℝ) * ((f : ℝ) + 1)) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x
        (wignerSmallDx f n m x) (deriv (wignerSmallDx f n m) x) -
      ρ * (2 * (f : ℝ) + 1) * ((f : ℝ) * ((f : ℝ) + 1)) / 6 * wignerSmallDx f n m x := by
    unfold nlo6Hs nlo6D nlo6D' nlo6Hr
    rw [← hf]
  rw [hHs]
  unfold nlo6D
  rw [← hf]
  have : (((m : ℝ) + d) * (((m : ℝ) + d) + 1) * (2 * ((m : ℝ) + d) + 1) / 6) =
      (f : ℝ) * ((f : ℝ) + 1) * (2 * (f : ℝ) + 1) / 6 := by rw [hfr]
  rw [this]
  ring


/-! ### All chambers -/

lemma nlo6G_transfer (σ J S τ ρ w x : ℝ) (g h : ℝ → ℝ) (hfun : ∀ y, σ * g y = h y)
    (hg : DifferentiableAt ℝ g x) :
    σ * nlo6G J S τ ρ w x (g x) (deriv g x) = nlo6G J S τ ρ w x (h x) (deriv h x) := by
  have hh : h = fun y => σ * g y := funext fun y => (hfun y).symm
  rw [hh, deriv_const_mul σ hg]
  unfold nlo6G
  ring

lemma a6_one_eq_deriv (f m n : ℚ) (α β γ : ℝ) :
    a6 f m n 1 (α, β, γ) = deriv (fun t => G6 f m n α β γ t) 0 := by
  simp [a6, taylorCoeff, iteratedDeriv_one]

/-- **`thm:6jclosedcorrection`, `eq:6jclosedg`** (proved, all four chambers): for `f ± m`, `f ± n`
natural and a strict-triangle shape `(α,β,γ)`, the `t`-coefficient `a_{f,1} = ∂_t G6(·,t)|_{t=0}` of
the germ is `P_f d' + Q_f d` with `d = d^f_{nm}(arccos x)` (`wignerSmallDx f n m`), `x = cosA α β γ`,
`ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`, i.e. `nlo6G`. -/
theorem a6_one_closed (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m)) (n3 : IsNat (f + n))
    (n4 : IsNat (f - n)) {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    a6 f m n 1 (α, β, γ) =
      nlo6G ((f : ℝ) * ((f : ℝ) + 1)) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n)
        (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ)
        (wignerSmallDx f n m (cosA α β γ)) (deriv (wignerSmallDx f n m) (cosA α β γ)) := by
  rw [a6_one_eq_deriv]
  have hxI := nlo6_cosA_mem_Ioo hz
  have hz' := swap6_mem_StrictTri hz
  have hdiff : ∀ (a b : ℚ), DifferentiableAt ℝ (wignerSmallDx f a b) (cosA α β γ) :=
    fun a b => nlo6_differentiableAt f a b hxI
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m - n = k := by
    obtain ⟨a, ha⟩ := n4
    obtain ⟨b, hb⟩ := n2
    exact ⟨(a : ℤ) - (b : ℤ), by push_cast; linarith⟩
  have hfl : ⌊m - n⌋ = k := by rw [hk]; exact Int.floor_intCast k
  unfold G6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels c1 n2 n3 n4
    exact (hasDerivAt_G6c_closed m n p q hp hq _ f hf hz _ _ _ rfl rfl rfl).deriv
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte, hfl]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    rw [sub_neg_eq_add] at hf
    have h := ((hasDerivAt_G6c_closed (-m) (-n) p q hp hq _ f hf hz _ _ _ rfl rfl rfl).const_mul
      ((-1 : ℝ) ^ k)).deriv
    have hS : (((-m : ℚ) : ℝ)) ^ 2 + (((-n : ℚ) : ℝ)) ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
      push_cast; ring
    have hT : (((-m : ℚ) : ℝ)) * (((-n : ℚ) : ℝ)) = (m : ℝ) * n := by push_cast; ring
    rw [hS, hT] at h
    rw [h]
    refine nlo6G_transfer _ _ _ _ _ _ _ _ _ (fun y => ?_) (hdiff _ _)
    unfold wignerSmallDx
    rw [wignerSmallD_neg f m n]
    exact wignerSmallD_swap_int f m n k hk _
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte, hfl]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    have h := ((hasDerivAt_G6c_closed n m p q hp hq _ f hf hz' (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8)
      (1 / (α * β)) (cosA α β γ) (by ring) (by rw [mul_comm]) (cosA_comm' α β γ).symm).const_mul
      ((-1 : ℝ) ^ k)).deriv
    have hS : (n : ℝ) ^ 2 + (m : ℝ) ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by ring
    have hT : (n : ℝ) * m = (m : ℝ) * n := by ring
    rw [hS, hT] at h
    rw [h]
    refine nlo6G_transfer _ _ _ _ _ _ _ _ _ (fun y => ?_) (hdiff _ _)
    unfold wignerSmallDx
    exact wignerSmallD_swap_int f m n k hk _
  have c4 : |m| ≤ -n := by
    rcases le_total 0 n with hn | hn
    · rw [abs_of_nonneg hn] at c1 c2
      exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
    · rw [abs_of_nonpos hn] at c1 c2
      rw [abs_le]; push Not at c1 c2; constructor <;> linarith
  simp only [c1, c2, c3, ↓reduceIte]
  obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
    (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
  rw [sub_neg_eq_add] at hf
  have h := (hasDerivAt_G6c_closed (-n) (-m) p q hp hq _ f hf hz' (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8)
    (1 / (α * β)) (cosA α β γ) (by ring) (by rw [mul_comm]) (cosA_comm' α β γ).symm).deriv
  have hS : (((-n : ℚ) : ℝ)) ^ 2 + (((-m : ℚ) : ℝ)) ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    push_cast; ring
  have hT : (((-n : ℚ) : ℝ)) * (((-m : ℚ) : ℝ)) = (m : ℝ) * n := by push_cast; ring
  rw [hS, hT] at h
  rw [h]
  have := nlo6G_transfer 1 ((f : ℝ) * ((f : ℝ) + 1)) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n)
    (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ) (wignerSmallDx f (-m) (-n))
    (wignerSmallDx f n m) (fun y => by
      unfold wignerSmallDx
      rw [one_mul]
      exact wignerSmallD_neg f n m _) (hdiff _ _)
  rw [one_mul] at this
  exact this


/-! ### The homogeneous coefficient `G_{f,2}(A,B,C)` and the expansion -/

/-- **The paper's closed form `G_{f,2}(A,B,C) = P_f(x) ∂_x d + Q_f(x) d`** (`eq:6jclosedg`), with
`x = cosA A B C`, `d = d^f_{nm}(arccos x)`, `ϱ_{AB} = (A⁻²+B⁻²)/8`, `1/(AB)`. -/
noncomputable def G6closed (f m n : ℚ) (A B C : ℝ) : ℝ :=
  nlo6G ((f : ℝ) * ((f : ℝ) + 1)) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n)
    (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) (1 / (A * B)) (cosA A B C)
    (wignerSmallDx f n m (cosA A B C)) (deriv (wignerSmallDx f n m) (cosA A B C))

lemma strictTri_shape {A B C S : ℝ} (hS : 0 < S) (h : (A / S, B / S, C / S) ∈ StrictTri) :
    (A, B, C) ∈ StrictTri := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  rw [← add_div, div_lt_div_iff_of_pos_right hS] at h4 h5 h6
  exact ⟨(div_pos_iff_of_pos_right hS).mp h1, (div_pos_iff_of_pos_right hS).mp h2,
    (div_pos_iff_of_pos_right hS).mp h3, h4, h5, h6⟩

lemma shape_strictTri {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    (A / (A + B + C), B / (A + B + C), C / (A + B + C)) ∈ StrictTri := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hS : 0 < A + B + C := by linarith
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩ <;>
    rw [← add_div, div_lt_div_iff_of_pos_right hS] <;> assumption

/-- **`thm:6jclosedcorrection` (`eq:6jclosedg`), homogeneous form** (proved, all chambers): on the
whole open strict-triangle cone, `G_{f,2}(A,B,C) = P_f(x) ∂_x d^f_{nm} + Q_f(x) d^f_{nm}`. -/
theorem G6even_one_eq_closed (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    G6even f m n 1 A B C = G6closed f m n A B C := by
  have hshape := shape_strictTri h
  obtain ⟨hA, hB, hC, -⟩ := h
  have hS : 0 < A + B + C := by linarith
  unfold G6even
  rw [a6_one_closed f m n n1 n2 n3 n4 hshape]
  unfold G6closed
  have e1 : (((A / (A + B + C)) ^ 2)⁻¹ + ((B / (A + B + C)) ^ 2)⁻¹) / 8 =
      (A + B + C) ^ 2 * (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) := by
    field_simp
  have e2 : 1 / (A / (A + B + C) * (B / (A + B + C))) = (A + B + C) ^ 2 * (1 / (A * B)) := by
    field_simp
  have e3 : cosA (A / (A + B + C)) (B / (A + B + C)) (C / (A + B + C)) = cosA A B C :=
    (cosA_shape A B C _ hS.ne').symm
  rw [e1, e2, e3, nlo6G_smul]
  have : ((A + B + C) ^ (2 * 1))⁻¹ * (A + B + C) ^ 2 = 1 := by
    rw [mul_one]; field_simp
  rw [← mul_assoc, this, one_mul]


/-- **`thm:6jclosedcorrection` with remainder** (proved, Lean form).  Fix admissible `f, m, n`, a
compact set `K` of strict-triangle shapes.  There are `C, S₀` such that for every physical admissible
point (the four triads of the `6j` family) with `S = A+B+C ≥ S₀` and normalised shape in `K`,
`|Φ_f - d^f_{nm}(arccos x) - G_{f,2}(A,B,C)| ≤ C S⁻⁴`, where `G_{f,2} = P_f ∂_x d + Q_f d`
(`G6closed`), `x = cosA A B C`, `A = wA a n`, `B = wB b m`, `C = wC c`. -/
theorem Phi6_nlo_expansion (f m n : ℚ) {K : Set Shape6} (hK : IsCompact K) (hKS : K ⊆ StrictTri) :
    ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → S₀ ≤ wA a n + wB b m + wC c →
      (wA a n / (wA a n + wB b m + wC c), wB b m / (wA a n + wB b m + wC c),
        wC c / (wA a n + wB b m + wC c)) ∈ K →
      |Phi6 a b c f m n - wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) -
          G6closed f m n (wA a n) (wB b m) (wC c)| ≤
        C / (wA a n + wB b m + wC c) ^ 4 := by
  obtain ⟨C, S₀, h⟩ := Phi6_even_expansion f m n hK hKS 2
  refine ⟨C, S₀, fun a b c h1 h2 h3 h4 hS0 hz => ?_⟩
  have key := h a b c h1 h2 h3 h4 hS0 hz
  obtain ⟨hA, hB, hC, hSpos⟩ := physical_scale_pos h1 h2 h3
  obtain ⟨n1, n2, n3, n4⟩ := four_nat h1 h2
  have hst := strictTri_shape hSpos (hKS hz)
  have hxI := nlo6_cosA_mem_Ioo hst
  have hx : cosA (wA a n) (wB b m) (wC c) ∈ Icc (-1 : ℝ) 1 := ⟨hxI.1.le, hxI.2.le⟩
  have h0 : G6even f m n 0 (wA a n) (wB b m) (wC c) =
      wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) := by
    rw [G6even_zero_eq_dZero6 f m n ⟨n1, n2, n3, n4⟩ hA hB hSpos,
      dZero6_eq_wignerD f m n n1 n2 n3 n4 hx]
  have h1' := G6even_one_eq_closed f m n n1 n2 n3 n4 hst
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at key
  rw [h0, h1'] at key
  have e : 2 * 2 = 4 := rfl
  rw [e] at key
  rw [sub_sub]
  exact key


/-- **`thm:6jclosedcorrection` on the paper's cone `T_δ`** (proved, Lean form): for every `δ > 0`
there are `C, H₀` with `|Φ_f - d^f_{nm}(arccos x) - G_{f,2}| ≤ C H⁻⁴` for every physical admissible
point with `H = max(A,B,C) ≥ H₀` and `min(A,B,C,A+B-C,A+C-B,B+C-A) ≥ δ H` (`eq:6jstrictcone`). -/
theorem Phi6_nlo_expansion_cone (f m n : ℚ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C H₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → H₀ ≤ Hscale (wA a n) (wB b m) (wC c) →
      δ * Hscale (wA a n) (wB b m) (wC c) ≤ Tmin (wA a n) (wB b m) (wC c) →
      |Phi6 a b c f m n - wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) -
          G6closed f m n (wA a n) (wB b m) (wC c)| ≤
        C / Hscale (wA a n) (wB b m) (wC c) ^ 4 := by
  obtain ⟨C, S₀, hC⟩ := Phi6_nlo_expansion f m n (TriDelta_isCompact hδ) (TriDelta_subset hδ)
  refine ⟨max C 0, max S₀ 1, ?_⟩
  intro a b c h1 h2 h3 h4 hH hT
  obtain ⟨hA, hB, hC', hSpos⟩ := physical_scale_pos h1 h2 h3
  have hHle : Hscale (wA a n) (wB b m) (wC c) ≤ wA a n + wB b m + wC c :=
    Hscale_le_sum hA.le hB.le hC'.le
  have hH1 : 1 ≤ Hscale (wA a n) (wB b m) (wC c) := le_trans (le_max_right _ _) hH
  have hHpos : 0 < Hscale (wA a n) (wB b m) (wC c) := by linarith
  have key := hC a b c h1 h2 h3 h4 (le_trans (le_trans (le_max_left _ _) hH) hHle) (by
    refine ⟨?_, ?_⟩
    · field_simp
    · rw [Hscale_div _ _ _ _ hSpos, Tmin_div _ _ _ _ hSpos, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hT hSpos.le)
  refine key.trans ?_
  calc C / (wA a n + wB b m + wC c) ^ 4
      ≤ max C 0 / (wA a n + wB b m + wC c) ^ 4 :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 / Hscale (wA a n) (wB b m) (wC c) ^ 4 :=
        div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
          (pow_le_pow_left₀ hHpos.le hHle _)

/-- info: 'FormalResearch.Racah.nlo6_e_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo6_e_eq

/-- info: 'FormalResearch.Racah.a6_one_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms a6_one_closed

/-- info: 'FormalResearch.Racah.G6even_one_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6even_one_eq_closed

/-- info: 'FormalResearch.Racah.Phi6_nlo_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_nlo_expansion

/-- info: 'FormalResearch.Racah.Phi6_nlo_expansion_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_nlo_expansion_cone

end FormalResearch.Racah
