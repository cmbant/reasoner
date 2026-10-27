import Mathlib

/-!
# Filtered-gate law: the real-algebra core

Pure real `3×3` algebra behind the bound `‖T₁(K)‖ ≤ δ` for `K = U†(a ⊗ b)U` (Paper P `cor:ftg`, via
QI-B `thm:ftg`).  Vectors are `V3 = Fin 3 → ℝ`, matrices are `Fin 3 → Fin 3 → ℝ`.

* `schur_bil`, `schur_vec`: the Schur-multiplier bound (QI-B `lem:ftg-schur`) for
  `[cos(θ_i + θ_j) ρ_ij]` with `ρ` orthogonal, via a hyperbolic boost factorisation
  (`boost_exists`), with `C_i = cos θ_i`, `S_i = sin θ_i`, `sin 2θ_i ≥ 0`, `|cos 2θ_i| ≤ d ≤ 1`.
* `cof_cross`: `cof(Q)(a × b) = Qa × Qb`.
* `tau_bound`: for `Q = CρC + Sρ'S` with `ρ' = ρ(2nnᵀ - 1)`, every `xᵀ cof(Q) y` with unit `x, y`
  is at most `d`.
-/

open Finset

namespace FormalResearch.FrameFree.FTG

abbrev V3 := Fin 3 → ℝ

/-- squared length -/
def sq3 (u : V3) : ℝ := ∑ i, u i ^ 2

def cr (u v : V3) : V3 := ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def mv (Q : Fin 3 → Fin 3 → ℝ) (v : V3) : V3 := fun i => ∑ j, Q i j * v j

def cofm (Q : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => Q (i+1) (j+1) * Q (i+2) (j+2) - Q (i+1) (j+2) * Q (i+2) (j+1)

theorem cof_cross (Q : Fin 3 → Fin 3 → ℝ) (a b : V3) :
    mv (cofm Q) (cr a b) = cr (mv Q a) (mv Q b) := by
  funext i
  fin_cases i <;> simp [mv, cofm, cr, Fin.sum_univ_three] <;> ring

theorem sq3_eq (u : V3) : sq3 u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp [sq3, Fin.sum_univ_three]

/-- `ρ` is an orthogonal matrix (columns orthonormal). -/
def Orth (ρ : Fin 3 → Fin 3 → ℝ) : Prop := ∀ j k, ∑ i, ρ i j * ρ i k = if j = k then 1 else 0

def dot3 (u v : V3) : ℝ := ∑ i, u i * v i

theorem dot_mv_orth {ρ : Fin 3 → Fin 3 → ℝ} (hρ : Orth ρ) (x y : V3) :
    dot3 (mv ρ x) (mv ρ y) = dot3 x y := by
  have h00 := hρ 0 0; have h01 := hρ 0 1; have h02 := hρ 0 2
  have h10 := hρ 1 0; have h11 := hρ 1 1; have h12 := hρ 1 2
  have h20 := hρ 2 0; have h21 := hρ 2 1; have h22 := hρ 2 2
  simp [Fin.sum_univ_three] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  simp only [dot3, mv, Fin.sum_univ_three]
  linear_combination (x 0 * y 0) * h00 + (x 0 * y 1) * h01 + (x 0 * y 2) * h02 + (x 1 * y 0) * h10 + (x 1 * y 1) * h11 + (x 1 * y 2) * h12 + (x 2 * y 0) * h20 + (x 2 * y 1) * h21 + (x 2 * y 2) * h22

theorem sq3_eq_dot (u : V3) : sq3 u = dot3 u u := by simp [sq3, dot3, sq]

theorem sq3_mv_orth {ρ : Fin 3 → Fin 3 → ℝ} (hρ : Orth ρ) (b : V3) : sq3 (mv ρ b) = sq3 b := by
  rw [sq3_eq_dot, sq3_eq_dot, dot_mv_orth hρ]

theorem sq3_cr_le (u v : V3) : sq3 (cr u v) ≤ sq3 u * sq3 v := by
  simp only [sq3_eq, cr]
  simp
  nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1 + u 2 * v 2)]

theorem cs3 (a w : V3) : (∑ i, a i * w i) ^ 2 ≤ sq3 a * sq3 w := by
  simp only [sq3_eq, Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 * w 1 - a 1 * w 0), sq_nonneg (a 0 * w 2 - a 2 * w 0),
    sq_nonneg (a 1 * w 2 - a 2 * w 1)]

theorem cs_contr {ρ : Fin 3 → Fin 3 → ℝ} (hρ : Orth ρ) (a b : V3) :
    (∑ i, ∑ j, a i * ρ i j * b j) ^ 2 ≤ sq3 a * sq3 b := by
  have h := cs3 a (mv ρ b)
  rw [sq3_mv_orth hρ] at h
  have e : ∑ i, ∑ j, a i * ρ i j * b j = ∑ i, a i * mv ρ b i := by
    apply Finset.sum_congr rfl; intro i _
    simp only [mv, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e]; exact h

/-- Two-term Cauchy–Schwarz for squared bilinear bounds. -/
theorem cs_two (B₁ B₂ A₁ A₂ E₁ E₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (h₁ : B₁ ^ 2 ≤ A₁ * E₁) (h₂ : B₂ ^ 2 ≤ A₂ * E₂) :
    (B₁ + B₂) ^ 2 ≤ (A₁ + A₂) * (E₁ + E₂) := by
  have hXY : (B₁ * B₂) ^ 2 ≤ (A₁ * E₂) * (A₂ * E₁) := by
    calc (B₁ * B₂) ^ 2 = B₁ ^ 2 * B₂ ^ 2 := by ring
      _ ≤ (A₁ * E₁) * (A₂ * E₂) := mul_le_mul h₁ h₂ (sq_nonneg _) (mul_nonneg hA₁ hE₁)
      _ = (A₁ * E₂) * (A₂ * E₁) := by ring
  have hX : 0 ≤ A₁ * E₂ + A₂ * E₁ := by positivity
  have h2 : 2 * (B₁ * B₂) ≤ A₁ * E₂ + A₂ * E₁ := by
    by_contra h
    rw [not_le] at h
    nlinarith [sq_nonneg (A₁ * E₂ - A₂ * E₁), mul_nonneg hA₁ hE₂, mul_nonneg hA₂ hE₁]
  nlinarith


theorem boost_exists (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ p q : ℝ, p ^ 2 - q ^ 2 = 1 ∧ d * (p ^ 2 + q ^ 2) = 1 ∧
      d * (2 * p * q) = -Real.sqrt (1 - d ^ 2) := by
  have h1 : 0 ≤ 1 - d := by linarith
  have h2 : 0 ≤ 1 + d := by linarith
  have ha : 0 ≤ (1 + d) / (2 * d) := by positivity
  have hb : 0 ≤ (1 - d) / (2 * d) := div_nonneg h1 (by positivity)
  set s := Real.sqrt (1 - d ^ 2) with hs
  have hs2 : s ^ 2 = 1 - d ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine ⟨Real.sqrt ((1 + d) / (2 * d)), -Real.sqrt ((1 - d) / (2 * d)), ?_, ?_, ?_⟩
  · rw [neg_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; field_simp; ring
  · rw [neg_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; field_simp; ring
  · have hab : (1 + d) / (2 * d) * ((1 - d) / (2 * d)) = (s / (2 * d)) ^ 2 := by
      rw [div_pow, hs2]; field_simp; ring
    have : Real.sqrt ((1 + d) / (2 * d)) * Real.sqrt ((1 - d) / (2 * d)) = s / (2 * d) := by
      rw [← Real.sqrt_mul ha, hab, Real.sqrt_sq (by positivity)]
    calc d * (2 * Real.sqrt ((1 + d) / (2 * d)) * -Real.sqrt ((1 - d) / (2 * d)))
        = -(d * 2 * (Real.sqrt ((1 + d) / (2 * d)) * Real.sqrt ((1 - d) / (2 * d)))) := by ring
      _ = -s := by rw [this]; field_simp


theorem schur_bil (C S : V3) (hCS : ∀ i, C i ^ 2 + S i ^ 2 = 1) (hpos : ∀ i, 0 ≤ C i * S i)
    (d : ℝ) (hd1 : d ≤ 1) (hd : ∀ i, |C i ^ 2 - S i ^ 2| ≤ d) {ρ : Fin 3 → Fin 3 → ℝ}
    (hρ : Orth ρ) (u v : V3) :
    (∑ i, ∑ j, u i * ((C i * C j - S i * S j) * ρ i j) * v j) ^ 2 ≤ d ^ 2 * (sq3 u * sq3 v) := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  rcases hd0.eq_or_lt with h0 | hpos'
  · -- d = 0
    have hCeq : ∀ i, C i = S i := by
      intro i
      have h := hd i
      rw [← h0] at h
      have h' : C i ^ 2 - S i ^ 2 = 0 := abs_nonpos_iff.mp h
      have hcs := hCS i
      have hp := hpos i
      have : (C i - S i) ^ 2 = 0 := by nlinarith [sq_nonneg (C i + S i), sq_nonneg (C i * S i - 1/2)]
      nlinarith [pow_eq_zero_iff (two_ne_zero) |>.mp this]
    have : ∀ i j, C i * C j - S i * S j = 0 := by
      intro i j; rw [hCeq i, hCeq j]; ring
    simp only [this, zero_mul, mul_zero, zero_mul, Finset.sum_const_zero]
    rw [← h0]; simp
  · obtain ⟨p, q, hpq, hpq2, hpq3⟩ := boost_exists d hpos' hd1
    set s := Real.sqrt (1 - d ^ 2) with hs
    have hs2 : s ^ 2 = 1 - d ^ 2 := Real.sq_sqrt (by nlinarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    set x1 : V3 := fun i => p * C i + q * S i with hx1
    set x2 : V3 := fun i => q * C i + p * S i with hx2
    have hm : ∀ i j, C i * C j - S i * S j = x1 i * x1 j - x2 i * x2 j := by
      intro i j; simp only [hx1, hx2]; linear_combination (-(C i * C j - S i * S j)) * hpq
    have hx : ∀ i, x1 i ^ 2 + x2 i ^ 2 ≤ d := by
      intro i
      have hcs := hCS i
      have hp := hpos i
      have h2cs : s ≤ 2 * (C i * S i) := by
        by_contra hcon
        rw [not_le] at hcon
        have hdi := hd i
        have hsq : (C i ^ 2 - S i ^ 2) ^ 2 ≤ d ^ 2 := by
          have := abs_le.mp hdi
          nlinarith
        nlinarith [mul_nonneg hp hp]
      have key : d * (x1 i ^ 2 + x2 i ^ 2) = 1 - s * (2 * (C i * S i)) := by
        simp only [hx1, hx2]
        linear_combination (C i ^ 2 + S i ^ 2) * hpq2 + hcs + (2 * (C i * S i)) * hpq3
      have : d * (x1 i ^ 2 + x2 i ^ 2) ≤ d * d := by
        rw [key]; nlinarith
      exact le_of_mul_le_mul_left this hpos'
    -- the factorisation
    set a1 : V3 := fun i => u i * x1 i
    set b1 : V3 := fun j => v j * x1 j
    set a2 : V3 := fun i => u i * x2 i
    set b2 : V3 := fun j => -(v j * x2 j)
    have hsum : ∑ i, ∑ j, u i * ((C i * C j - S i * S j) * ρ i j) * v j =
        (∑ i, ∑ j, a1 i * ρ i j * b1 j) + (∑ i, ∑ j, a2 i * ρ i j * b2 j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp only [a1, b1, a2, b2, hm i j]; ring
    have hA : sq3 a1 + sq3 a2 ≤ d * sq3 u := by
      have : sq3 a1 + sq3 a2 = ∑ i, u i ^ 2 * (x1 i ^ 2 + x2 i ^ 2) := by
        simp only [sq3, a1, a2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, sq3, Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      nlinarith [hx i, sq_nonneg (u i)]
    have hE : sq3 b1 + sq3 b2 ≤ d * sq3 v := by
      have : sq3 b1 + sq3 b2 = ∑ i, v i ^ 2 * (x1 i ^ 2 + x2 i ^ 2) := by
        simp only [sq3, b1, b2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, sq3, Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      nlinarith [hx i, sq_nonneg (v i)]
    have hnn : ∀ w : V3, 0 ≤ sq3 w := fun w => Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [hsum]
    calc _ ≤ (sq3 a1 + sq3 a2) * (sq3 b1 + sq3 b2) :=
          cs_two _ _ _ _ _ _ (hnn _) (hnn _) (hnn _) (hnn _) (cs_contr hρ a1 b1) (cs_contr hρ a2 b2)
      _ ≤ (d * sq3 u) * (d * sq3 v) :=
          mul_le_mul hA hE (add_nonneg (hnn _) (hnn _)) (mul_nonneg hd0 (hnn _))
      _ = d ^ 2 * (sq3 u * sq3 v) := by ring


theorem sq3_nonneg (w : V3) : 0 ≤ sq3 w := Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem schur_vec (C S : V3) (hCS : ∀ i, C i ^ 2 + S i ^ 2 = 1) (hpos : ∀ i, 0 ≤ C i * S i)
    (d : ℝ) (hd1 : d ≤ 1) (hd : ∀ i, |C i ^ 2 - S i ^ 2| ≤ d) {ρ : Fin 3 → Fin 3 → ℝ}
    (hρ : Orth ρ) (a : V3) :
    sq3 (mv (fun i j => (C i * C j - S i * S j) * ρ i j) a) ≤ d ^ 2 * sq3 a := by
  set w := mv (fun i j => (C i * C j - S i * S j) * ρ i j) a with hw
  have h := schur_bil C S hCS hpos d hd1 hd hρ w a
  have e : ∑ i, ∑ j, w i * ((C i * C j - S i * S j) * ρ i j) * a j = sq3 w := by
    rw [sq3]
    apply Finset.sum_congr rfl; intro i _
    rw [sq, hw]; simp only [mv, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e] at h
  rcases (sq3_nonneg w).eq_or_lt with h0 | hp
  · rw [← h0]; exact mul_nonneg (sq_nonneg _) (sq3_nonneg _)
  · have : sq3 w * sq3 w ≤ sq3 w * (d ^ 2 * sq3 a) := by nlinarith
    exact le_of_mul_le_mul_left this hp

theorem orth_reflect {ρ : Fin 3 → Fin 3 → ℝ} (hρ : Orth ρ) (n : V3) (hn : sq3 n = 1) :
    Orth (fun i j => 2 * mv ρ n i * n j - ρ i j) := by
  intro j k
  set xj : V3 := fun l => 2 * n j * n l - if l = j then 1 else 0 with hxj
  set xk : V3 := fun l => 2 * n k * n l - if l = k then 1 else 0 with hxk
  have e1 : ∀ i, (2 * mv ρ n i * n j - ρ i j) = mv ρ xj i := by
    intro i
    simp only [mv, hxj, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    simp [Fin.sum_univ_three, Fin.ext_iff]
    fin_cases j <;> simp [Fin.sum_univ_three] <;> ring
  have e2 : ∀ i, (2 * mv ρ n i * n k - ρ i k) = mv ρ xk i := by
    intro i
    simp only [mv, hxk, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    simp [Fin.sum_univ_three, Fin.ext_iff]
    fin_cases k <;> simp [Fin.sum_univ_three] <;> ring
  have := dot_mv_orth hρ xj xk
  simp only [dot3] at this
  simp only [e1, e2]
  rw [this]
  simp only [hxj, hxk]
  rw [sq3_eq] at hn
  fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_three]
  · nlinarith [hn]
  · linear_combination (4 * n 0 * n 1) * hn
  · linear_combination (4 * n 0 * n 2) * hn
  · linear_combination (4 * n 1 * n 0) * hn
  · nlinarith [hn]
  · linear_combination (4 * n 1 * n 2) * hn
  · linear_combination (4 * n 2 * n 0) * hn
  · linear_combination (4 * n 2 * n 1) * hn
  · nlinarith [hn]


/-- Normalisation of a nonzero vector. -/
noncomputable def nrm (v : V3) : V3 := fun i => v i / Real.sqrt (sq3 v)

theorem sq3_nrm (v : V3) (h : sq3 v ≠ 0) : sq3 (nrm v) = 1 := by
  have hp : 0 < sq3 v := lt_of_le_of_ne (sq3_nonneg v) (Ne.symm h)
  have : sq3 (nrm v) = sq3 v / (Real.sqrt (sq3 v)) ^ 2 := by
    simp only [sq3, nrm, div_pow, ← Finset.sum_div]
  rw [this, Real.sq_sqrt hp.le]; field_simp

theorem dot_nrm (v w : V3) : dot3 (nrm v) w = dot3 v w / Real.sqrt (sq3 v) := by
  simp only [dot3, nrm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _; ring

theorem sq3_zero_iff (v : V3) : sq3 v = 0 ↔ ∀ i, v i = 0 := by
  constructor
  · intro h i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp h i (Finset.mem_univ i)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · intro h; simp [sq3, h]

theorem dot_nrm_zero (v w : V3) (h : dot3 v w = 0) : dot3 (nrm v) w = 0 := by
  rw [dot_nrm, h, zero_div]

theorem exists_frame (y m : V3) (hy : sq3 y = 1) :
    ∃ a : V3, sq3 a = 1 ∧ dot3 a y = 0 ∧ dot3 a m = 0 := by
  by_cases hc : sq3 (cr y m) = 0
  · have h0 := (sq3_zero_iff _).mp hc
    have c0 := h0 0; have c1 := h0 1; have c2 := h0 2
    simp [cr] at c0 c1 c2
    have hy' := hy; rw [sq3_eq] at hy'
    obtain ⟨c, hcdef⟩ : ∃ c, c = dot3 y m := ⟨_, rfl⟩
    have hm : ∀ i, m i = c * y i := by
      intro i
      rw [hcdef]
      simp only [dot3, Fin.sum_univ_three]
      fin_cases i <;> simp
      · linear_combination (-m 0) * hy' + (-y 1) * c2 + (y 2) * c1
      · linear_combination (-m 1) * hy' + (y 0) * c2 + (-y 2) * c0
      · linear_combination (-m 2) * hy' + (-y 0) * c1 + (y 1) * c0
    have key : ∀ w : V3, dot3 w m = c * dot3 w y := by
      intro w
      simp only [dot3, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; rw [hm i]; ring
    by_cases hy0 : y 0 ^ 2 < 1
    · let v : V3 := ![0, y 2, -y 1]
      have hv : sq3 v = 1 - y 0 ^ 2 := by rw [sq3_eq]; simp [v]; nlinarith [hy']
      have hvne : sq3 v ≠ 0 := by rw [hv]; linarith
      have hvy : dot3 v y = 0 := by simp [dot3, Fin.sum_univ_three, v]; ring
      have h1 := dot_nrm_zero v y hvy
      exact ⟨nrm v, sq3_nrm v hvne, h1, by rw [key, h1, mul_zero]⟩
    · let v : V3 := ![-y 2, 0, y 0]
      have hv : sq3 v = 1 - y 1 ^ 2 := by rw [sq3_eq]; simp [v]; nlinarith [hy']
      have hy1 : y 1 ^ 2 = 0 := by
        have : y 1 ^ 2 + y 2 ^ 2 ≤ 0 := by nlinarith [hy', hy0, not_lt.mp hy0]
        nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
      have hvne : sq3 v ≠ 0 := by rw [hv, hy1]; norm_num
      have hvy : dot3 v y = 0 := by simp [dot3, Fin.sum_univ_three, v]; ring
      have h1 := dot_nrm_zero v y hvy
      exact ⟨nrm v, sq3_nrm v hvne, h1, by rw [key, h1, mul_zero]⟩
  · refine ⟨nrm (cr y m), sq3_nrm _ hc, dot_nrm_zero _ _ ?_, dot_nrm_zero _ _ ?_⟩
    · simp [dot3, Fin.sum_univ_three, cr]; ring
    · simp [dot3, Fin.sum_univ_three, cr]; ring


/-- `Q = C ρ C + S ρ' S`. -/
def Qm (C S : V3) (ρ ρ' : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun k l => C k * C l * ρ k l + S k * S l * ρ' k l

theorem sq3_mvQ_le (C S : V3) (hCS : ∀ i, C i ^ 2 + S i ^ 2 = 1) {ρ ρ' : Fin 3 → Fin 3 → ℝ}
    (hρ : Orth ρ) (hρ' : Orth ρ') (b : V3) : sq3 (mv (Qm C S ρ ρ') b) ≤ sq3 b := by
  set u := mv ρ (fun l => C l * b l) with hu
  set v := mv ρ' (fun l => S l * b l) with hv
  have h1 : ∀ k, mv (Qm C S ρ ρ') b k = C k * u k + S k * v k := by
    intro k
    simp only [mv, Qm, hu, hv, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have h2 : sq3 (mv (Qm C S ρ ρ') b) ≤ sq3 u + sq3 v := by
    simp only [sq3, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro k _
    rw [h1 k]
    nlinarith [sq_nonneg (C k * v k - S k * u k), hCS k, sq_nonneg (u k), sq_nonneg (v k)]
  have h3 : sq3 u + sq3 v = sq3 b := by
    rw [hu, hv, sq3_mv_orth hρ, sq3_mv_orth hρ']
    simp only [sq3, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _
    have := hCS l
    linear_combination (b l ^ 2) * this
  linarith

theorem mvQ_eq (C S n : V3) {ρ ρ' : Fin 3 → Fin 3 → ℝ}
    (hρ' : ∀ i j, ρ' i j = 2 * mv ρ n i * n j - ρ i j) (a : V3)
    (ha : dot3 a (fun l => S l * n l) = 0) :
    mv (Qm C S ρ ρ') a = mv (fun i j => (C i * C j - S i * S j) * ρ i j) a := by
  funext k
  have : ∑ l, a l * (S l * n l) = 0 := ha
  simp only [mv, Qm]
  simp only [hρ']
  have e : ∑ l, (C k * C l * ρ k l + S k * S l * (2 * mv ρ n k * n l - ρ k l)) * a l =
      ∑ l, (C k * C l - S k * S l) * ρ k l * a l + 2 * S k * mv ρ n k * ∑ l, a l * (S l * n l) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  rw [e, this]; simp

theorem tau_bound (C S : V3) (hCS : ∀ i, C i ^ 2 + S i ^ 2 = 1) (hpos : ∀ i, 0 ≤ C i * S i)
    (d : ℝ) (hd1 : d ≤ 1) (hd : ∀ i, |C i ^ 2 - S i ^ 2| ≤ d)
    {ρ ρ' : Fin 3 → Fin 3 → ℝ} (hρ : Orth ρ) (n : V3) (hn : sq3 n = 1)
    (hρ' : ∀ i j, ρ' i j = 2 * mv ρ n i * n j - ρ i j) (x y : V3) (hx : sq3 x = 1)
    (hy : sq3 y = 1) :
    ∑ i, ∑ j, x i * cofm (Qm C S ρ ρ') i j * y j ≤ d := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have hρ'o : Orth ρ' := by
    have := orth_reflect hρ n hn
    intro j k; have h := this j k
    simpa [hρ'] using h
  obtain ⟨a, ha1, hay, ham⟩ := exists_frame y (fun l => S l * n l) hy
  set b := cr y a with hb
  have hcra : ∀ i, cr a b i = y i * sq3 a - a i * dot3 a y := by
    intro i
    fin_cases i <;> simp [hb, cr, sq3_eq, dot3, Fin.sum_univ_three] <;> ring
  have hyab : cr a b = y := by
    funext i; rw [hcra, ha1, hay]; ring
  have hbq : sq3 b ≤ 1 := by
    have := sq3_cr_le y a
    rw [hy, ha1] at this; simpa [hb] using this
  have hw : mv (cofm (Qm C S ρ ρ')) y = cr (mv (Qm C S ρ ρ') a) (mv (Qm C S ρ ρ') b) := by
    have := cof_cross (Qm C S ρ ρ') a b
    rw [hyab] at this; exact this
  have hQa : sq3 (mv (Qm C S ρ ρ') a) ≤ d ^ 2 := by
    rw [mvQ_eq C S n hρ' a ham]
    have := schur_vec C S hCS hpos d hd1 hd hρ a
    rwa [ha1, mul_one] at this
  have hQb : sq3 (mv (Qm C S ρ ρ') b) ≤ 1 := (sq3_mvQ_le C S hCS hρ hρ'o b).trans hbq
  have hwy : sq3 (mv (cofm (Qm C S ρ ρ')) y) ≤ d ^ 2 := by
    rw [hw]
    calc _ ≤ sq3 (mv (Qm C S ρ ρ') a) * sq3 (mv (Qm C S ρ ρ') b) := sq3_cr_le _ _
      _ ≤ d ^ 2 * 1 := mul_le_mul hQa hQb (sq3_nonneg _) (sq_nonneg _)
      _ = d ^ 2 := mul_one _
  have hsum : ∑ i, ∑ j, x i * cofm (Qm C S ρ ρ') i j * y j =
      ∑ i, x i * mv (cofm (Qm C S ρ ρ')) y i := by
    apply Finset.sum_congr rfl; intro i _
    simp only [mv, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsum]
  have hcs := cs3 x (mv (cofm (Qm C S ρ ρ')) y)
  rw [hx, one_mul] at hcs
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [hcs, hwy, hcon, hd0]

end FormalResearch.FrameFree.FTG
