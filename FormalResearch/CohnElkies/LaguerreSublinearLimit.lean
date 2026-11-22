module

public import FormalResearch.CohnElkies.FiniteDimensionCrossings
public import FormalResearch.CohnElkies.LaguerreJacobiSpectral

/-!
# Sublinear-Degree Laguerre Limitation (`ce_finite_bounds.tex` Theorem E.3a)

Source: `CFT/sign_uncertainty/paper/ce_finite_bounds.tex` (PR 240, commit `c3d8c90fe`).

`[0, ∞)`-SOS factorization, exact finite lower bound `ce_laguerre_finite_lower_bound`,
`ce_laguerre_limit` (`limsup ≤ kappaGauss` for `K_d = o(d)`), and `ce_laguerre_equality_quad_cubic`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform Polynomial RealInnerProductSpace SchwartzMap Matrix

namespace FormalResearch.CohnElkies

private lemma list_sum_map_mul_sq (g : ℝ[X]) (L : List ℝ[X]) :
    (L.map (fun x => (g * x) ^ 2)).sum = g ^ 2 * (L.map (· ^ 2)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]; rw [ih, mul_pow]; ring

private lemma list_eval_zero_sq_sum (L : List ℝ[X]) :
    ((L.map (· ^ 2)).sum).eval 0 = (L.map (fun a => (a.eval 0) ^ 2)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma lagMeasure_add {c : ℝ} (hc : 0 < c) (P Q : ℝ[X]) :
    lagMeasure c (P + Q) = lagMeasure c P + lagMeasure c Q := by
  have h1 := lagInner_add_left c (hc := hc) P Q 1
  simpa only [lagInner, mul_one] using h1

private lemma list_lagMeasure_sq_sum (c : ℝ) (hc : 0 < c) (L : List ℝ[X]) :
    (L.map (fun a => lagMeasure c (a ^ 2))).sum = lagMeasure c (L.map (· ^ 2)).sum := by
  induction L with
  | nil => simp [lagMeasure]
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    exact (lagMeasure_add hc (a ^ 2) ((A.map (· ^ 2)).sum)).symm

private lemma list_sum_le_mul_sum {α : Type*} (k : ℝ) (f g : α → ℝ) (L : List α)
    (h : ∀ x ∈ L, f x ≤ k * g x) : (L.map f).sum ≤ k * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add (h x (List.mem_cons_self)) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

private lemma poly_nonneg_of_Ici_mul_lin_neg {r : ℝ} (hr : r < 0) {q q₁ : ℝ[X]}
    (hq : q = (Polynomial.X - Polynomial.C r) * q₁) (hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) :
    ∀ s : ℝ, 0 ≤ s → 0 ≤ q₁.eval s := fun s hs => by
  have hev := hq_nn s hs
  rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  exact (mul_nonneg_iff_of_pos_left (by linarith)).mp hev

private lemma poly_nonneg_of_Ici_mul_X {q q₁ : ℝ[X]} (hq : q = Polynomial.X * q₁)
    (hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) : ∀ s : ℝ, 0 ≤ s → 0 ≤ q₁.eval s := fun s hs => by
  rcases eq_or_lt_of_le hs with rfl | hs_pos
  · have htend : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact ge_of_tendsto (q₁.continuous.tendsto 0 |>.comp htend)
      (Eventually.of_forall fun n => by
        have htp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hev := hq_nn (1 / ((n : ℝ) + 1)) htp.le
        rw [hq, Polynomial.eval_mul, Polynomial.eval_X] at hev
        exact (mul_nonneg_iff_of_pos_left htp).mp hev)
  · have hev := hq_nn s hs_pos.le
    rw [hq, Polynomial.eval_mul, Polynomial.eval_X] at hev
    exact (mul_nonneg_iff_of_pos_left hs_pos).mp hev

private lemma poly_nonneg_isRoot_sq_of_pos {r : ℝ} (hr : 0 < r) {q q₁ : ℝ[X]}
    (hq : q = (Polynomial.X - Polynomial.C r) * q₁) (hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) :
    q₁.IsRoot r := by
  by_contra hne
  rcases lt_or_gt_of_ne (show q₁.eval r ≠ 0 from hne) with hneg | hpos
  · obtain ⟨δ, hδ, hmem⟩ := Metric.continuousAt_iff.mp q₁.continuous.continuousAt (-q₁.eval r) (by linarith)
    have hev := hq_nn (r + δ / 2) (by linarith)
    have hlt : q₁.eval (r + δ / 2) < 0 := by
      have hd := hmem (show dist (r + δ / 2) r < δ by simp [abs_of_pos hδ]; linarith)
      rw [Real.dist_eq, abs_lt] at hd; linarith
    rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
    nlinarith
  · obtain ⟨δ, hδ, hmem⟩ := Metric.continuousAt_iff.mp q₁.continuous.continuousAt (q₁.eval r) hpos
    let δ₁ := min (r / 2) (δ / 2)
    have hmin_pos : 0 < δ₁ := lt_min (by positivity) (by positivity)
    have hmin_le : δ₁ ≤ δ / 2 := min_le_right _ _
    have hev := hq_nn (r - δ₁) (by linarith [min_le_left (r / 2) (δ / 2)])
    have hpos' : 0 < q₁.eval (r - δ₁) := by
      have hd := hmem (show dist (r - δ₁) r < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at hd; linarith
    rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
    nlinarith

private lemma poly_nonneg_of_Ici_mul_sq {r : ℝ} {q q₂ : ℝ[X]}
    (hq : q = (Polynomial.X - Polynomial.C r) ^ 2 * q₂) (hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) :
    ∀ s : ℝ, 0 ≤ s → 0 ≤ q₂.eval s := fun s hs => by
  by_cases hsr : s = r
  · subst hsr
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have htend : Tendsto (fun n : ℕ => s + 1 / ((n : ℝ) + 1)) atTop (𝓝 s) := by
      simpa using tendsto_const_nhds.add h0
    exact ge_of_tendsto (q₂.continuous.tendsto s |>.comp htend)
      (Eventually.of_forall fun n => by
        have hstep : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        have hev := hq_nn (s + 1 / ((n : ℝ) + 1)) (by linarith)
        rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hev
        exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (by linarith : s + 1 / ((n : ℝ) + 1) - s ≠ 0))).mp hev)
  · have hev := hq_nn s hs
    rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hev
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (sub_ne_zero.mpr hsr))).mp hev

private lemma sos_step_neg {r : ℝ} (hr_neg : r < 0) {q q₁ : ℝ[X]}
    (hq_mul : q = (Polynomial.X - Polynomial.C r) * q₁) (hdeg_q₁ : q₁.natDegree + 1 = q.natDegree)
    (A₁ B₁ : List ℝ[X]) (hq₁_eq : q₁ = (A₁.map (· ^ 2)).sum + Polynomial.X * (B₁.map (· ^ 2)).sum)
    (hA₁ : ∀ a ∈ A₁, 2 * a.natDegree ≤ q₁.natDegree)
    (hB₁ : ∀ b ∈ B₁, 2 * b.natDegree + 1 ≤ q₁.natDegree) :
    ∃ A B : List ℝ[X],
      q = (A.map (· ^ 2)).sum + Polynomial.X * (B.map (· ^ 2)).sum ∧
      (∀ a ∈ A, 2 * a.natDegree ≤ q.natDegree) ∧
      (∀ b ∈ B, 2 * b.natDegree + 1 ≤ q.natDegree) := by
  let a : ℝ := Real.sqrt (-r)
  have ha2 : Polynomial.X - Polynomial.C r = Polynomial.C a ^ 2 + Polynomial.X * 1 ^ 2 := by
    rw [← map_pow, Real.sq_sqrt (by linarith : 0 ≤ -r), one_pow, mul_one,
      sub_eq_add_neg, ← map_neg]; ring
  refine ⟨A₁.map (Polynomial.C a * ·) ++ B₁.map (Polynomial.X * ·),
    A₁ ++ B₁.map (Polynomial.C a * ·), ?_, fun u hu => ?_, fun v hv => ?_⟩
  · simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append, list_sum_map_mul_sq]
    rw [hq_mul, ha2, hq₁_eq]; ring
  · simp only [List.mem_append, List.mem_map] at hu
    rcases hu with ⟨u₁, hu₁, rfl⟩ | ⟨v₁, hv₁, rfl⟩
    · exact ((Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le a u₁)).trans
        (hA₁ u₁ hu₁)).trans (by omega)
    · have h2 : (Polynomial.X * v₁).natDegree ≤ 1 + v₁.natDegree :=
        (Polynomial.natDegree_mul_le (p := Polynomial.X) (q := v₁)).trans
          (add_le_add Polynomial.natDegree_X_le le_rfl)
      have h3 := hB₁ v₁ hv₁
      omega
  · simp only [List.mem_append, List.mem_map] at hv
    rcases hv with hu₁ | ⟨v₁, hv₁, rfl⟩
    · have := hA₁ v hu₁; omega
    · exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2
        (Polynomial.natDegree_C_mul_le a v₁)) 1).trans ((hB₁ v₁ hv₁).trans (by omega))

private lemma sos_step_zero {q q₁ : ℝ[X]}
    (hq_X : q = Polynomial.X * q₁) (hdeg_q₁ : q₁.natDegree + 1 = q.natDegree)
    (A₁ B₁ : List ℝ[X]) (hq₁_eq : q₁ = (A₁.map (· ^ 2)).sum + Polynomial.X * (B₁.map (· ^ 2)).sum)
    (hA₁ : ∀ a ∈ A₁, 2 * a.natDegree ≤ q₁.natDegree)
    (hB₁ : ∀ b ∈ B₁, 2 * b.natDegree + 1 ≤ q₁.natDegree) :
    ∃ A B : List ℝ[X],
      q = (A.map (· ^ 2)).sum + Polynomial.X * (B.map (· ^ 2)).sum ∧
      (∀ a ∈ A, 2 * a.natDegree ≤ q.natDegree) ∧
      (∀ b ∈ B, 2 * b.natDegree + 1 ≤ q.natDegree) := by
  refine ⟨B₁.map (Polynomial.X * ·), A₁, ?_, fun u hu => ?_, fun v hv => ?_⟩
  · rw [List.map_map, Function.comp_def, list_sum_map_mul_sq, hq_X, hq₁_eq]; ring
  · obtain ⟨v₁, hv₁, rfl⟩ := List.mem_map.mp hu
    have h2 : (Polynomial.X * v₁).natDegree ≤ 1 + v₁.natDegree :=
      (Polynomial.natDegree_mul_le (p := Polynomial.X) (q := v₁)).trans
        (add_le_add Polynomial.natDegree_X_le le_rfl)
    have h3 := hB₁ v₁ hv₁
    omega
  · have := hA₁ v hv; omega

private lemma sos_step_pos {r : ℝ} {q q₂ : ℝ[X]}
    (hq_sq : q = (Polynomial.X - Polynomial.C r) ^ 2 * q₂) (hdeg_q₂ : q₂.natDegree + 2 = q.natDegree)
    (A₂ B₂ : List ℝ[X]) (hq₂_eq : q₂ = (A₂.map (· ^ 2)).sum + Polynomial.X * (B₂.map (· ^ 2)).sum)
    (hA₂ : ∀ a ∈ A₂, 2 * a.natDegree ≤ q₂.natDegree)
    (hB₂ : ∀ b ∈ B₂, 2 * b.natDegree + 1 ≤ q₂.natDegree) :
    ∃ A B : List ℝ[X],
      q = (A.map (· ^ 2)).sum + Polynomial.X * (B.map (· ^ 2)).sum ∧
      (∀ a ∈ A, 2 * a.natDegree ≤ q.natDegree) ∧
      (∀ b ∈ B, 2 * b.natDegree + 1 ≤ q.natDegree) := by
  refine ⟨A₂.map ((Polynomial.X - Polynomial.C r) * ·),
    B₂.map ((Polynomial.X - Polynomial.C r) * ·), ?_, fun u hu => ?_, fun v hv => ?_⟩
  · simp only [List.map_map, Function.comp_def, list_sum_map_mul_sq, hq_sq, hq₂_eq]; ring
  · obtain ⟨u₁, hu₁, rfl⟩ := List.mem_map.mp hu
    have h1 : ((Polynomial.X - Polynomial.C r) * u₁).natDegree ≤ 1 + u₁.natDegree :=
      (Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C r) (q := u₁)).trans
        (add_le_add (Polynomial.natDegree_X_sub_C r).le le_rfl)
    have h2 := hA₂ u₁ hu₁
    omega
  · obtain ⟨v₁, hv₁, rfl⟩ := List.mem_map.mp hv
    have h1 : ((Polynomial.X - Polynomial.C r) * v₁).natDegree ≤ 1 + v₁.natDegree :=
      (Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C r) (q := v₁)).trans
        (add_le_add (Polynomial.natDegree_X_sub_C r).le le_rfl)
    have h2 := hB₂ v₁ hv₁
    omega

private lemma sos_step_complex (z : ℂ) {q q₁ : ℝ[X]}
    (hq_mul : q = (Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X + Polynomial.C (‖z‖ ^ 2)) * q₁)
    (hdeg_q₁ : q₁.natDegree + 2 = q.natDegree)
    (A₁ B₁ : List ℝ[X]) (hq₁_eq : q₁ = (A₁.map (· ^ 2)).sum + Polynomial.X * (B₁.map (· ^ 2)).sum)
    (hA₁ : ∀ a ∈ A₁, 2 * a.natDegree ≤ q₁.natDegree)
    (hB₁ : ∀ b ∈ B₁, 2 * b.natDegree + 1 ≤ q₁.natDegree) :
    ∃ A B : List ℝ[X],
      q = (A.map (· ^ 2)).sum + Polynomial.X * (B.map (· ^ 2)).sum ∧
      (∀ a ∈ A, 2 * a.natDegree ≤ q.natDegree) ∧
      (∀ b ∈ B, 2 * b.natDegree + 1 ≤ q.natDegree) := by
  have hf_sos : Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X + Polynomial.C (‖z‖ ^ 2) =
      (Polynomial.X - Polynomial.C z.re) ^ 2 + Polynomial.C z.im ^ 2 := by
    have hns : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hns]; simp only [map_add, map_pow, map_mul, map_ofNat]; ring
  refine ⟨A₁.map ((Polynomial.X - Polynomial.C z.re) * ·) ++ A₁.map (Polynomial.C z.im * ·),
    B₁.map ((Polynomial.X - Polynomial.C z.re) * ·) ++ B₁.map (Polynomial.C z.im * ·), ?_,
    fun u hu => ?_, fun v hv => ?_⟩
  · simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append, list_sum_map_mul_sq]
    rw [hq_mul, hf_sos, hq₁_eq]; ring
  · simp only [List.mem_append, List.mem_map] at hu
    rcases hu with ⟨u₁, hu₁, rfl⟩ | ⟨u₁, hu₁, rfl⟩
    · have h1 : ((Polynomial.X - Polynomial.C z.re) * u₁).natDegree ≤ 1 + u₁.natDegree :=
        (Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C z.re) (q := u₁)).trans
          (add_le_add (Polynomial.natDegree_X_sub_C z.re).le le_rfl)
      have h2 := hA₁ u₁ hu₁; omega
    · exact ((Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le z.im u₁)).trans
        (hA₁ u₁ hu₁)).trans (by omega)
  · simp only [List.mem_append, List.mem_map] at hv
    rcases hv with ⟨v₁, hv₁, rfl⟩ | ⟨v₁, hv₁, rfl⟩
    · have h1 : ((Polynomial.X - Polynomial.C z.re) * v₁).natDegree ≤ 1 + v₁.natDegree :=
        (Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C z.re) (q := v₁)).trans
          (add_le_add (Polynomial.natDegree_X_sub_C z.re).le le_rfl)
      have h2 := hB₁ v₁ hv₁; omega
    · exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2
        (Polynomial.natDegree_C_mul_le z.im v₁)) 1).trans ((hB₁ v₁ hv₁).trans (by omega))

private lemma poly_nonneg_Ici_sos :
    ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n → (∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) →
      ∃ A B : List ℝ[X],
        q = (A.map (· ^ 2)).sum + Polynomial.X * (B.map (· ^ 2)).sum ∧
        (∀ a ∈ A, 2 * a.natDegree ≤ q.natDegree) ∧
        (∀ b ∈ B, 2 * b.natDegree + 1 ≤ q.natDegree) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q hq_deg hq_nn
    by_cases hq0 : q = 0
    · subst hq0; exact ⟨[], [], by simp, by simp, by simp⟩
    rcases Nat.eq_zero_or_pos q.natDegree with hdeg0 | hdeg_pos
    · have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg0.le
      have hc0 : 0 ≤ q.coeff 0 := by
        have := hq_nn 0 le_rfl; rwa [hqc, Polynomial.eval_C] at this
      refine ⟨[Polynomial.C (Real.sqrt (q.coeff 0))], [], ?_, fun a ha => ?_, by simp⟩
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_zero]
        rw [← map_pow, Real.sq_sqrt hc0, ← hqc]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; simp [hdeg0]
    by_cases hreal : ∃ r : ℝ, q.IsRoot r
    · obtain ⟨r, hr⟩ := hreal
      obtain ⟨q₁, hq_mul⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      have hq₁0 : q₁ ≠ 0 := fun h => hq0 (by rw [hq_mul, h, mul_zero])
      have hdeg_q₁ : q₁.natDegree + 1 = q.natDegree := by
        rw [hq_mul, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁0,
          Polynomial.natDegree_X_sub_C, add_comm]
      rcases lt_trichotomy r 0 with hr_neg | rfl | hr_pos
      · obtain ⟨A₁, B₁, hq₁_eq, hA₁, hB₁⟩ := ih q₁.natDegree (by omega) q₁ le_rfl
          (poly_nonneg_of_Ici_mul_lin_neg hr_neg hq_mul hq_nn)
        exact sos_step_neg hr_neg hq_mul hdeg_q₁ A₁ B₁ hq₁_eq hA₁ hB₁
      · have hq_X : q = Polynomial.X * q₁ := by rwa [map_zero, sub_zero] at hq_mul
        obtain ⟨A₁, B₁, hq₁_eq, hA₁, hB₁⟩ := ih q₁.natDegree (by omega) q₁ le_rfl
          (poly_nonneg_of_Ici_mul_X hq_X hq_nn)
        exact sos_step_zero hq_X hdeg_q₁ A₁ B₁ hq₁_eq hA₁ hB₁
      · obtain ⟨q₂, hq₁_mul⟩ := Polynomial.dvd_iff_isRoot.mpr
          (poly_nonneg_isRoot_sq_of_pos hr_pos hq_mul hq_nn)
        have hq_sq : q = (Polynomial.X - Polynomial.C r) ^ 2 * q₂ := by rw [hq_mul, hq₁_mul]; ring
        have hq₂0 : q₂ ≠ 0 := fun h => hq0 (by rw [hq_sq, h, mul_zero])
        have hdeg_q₂ : q₂.natDegree + 2 = q.natDegree := by
          rw [hq_sq, Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero r)) hq₂0,
            Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, add_comm]
        obtain ⟨A₂, B₂, hq₂_eq, hA₂, hB₂⟩ := ih q₂.natDegree (by omega) q₂ le_rfl
          (poly_nonneg_of_Ici_mul_sq hq_sq hq_nn)
        exact sos_step_pos hq_sq hdeg_q₂ A₂ B₂ hq₂_eq hA₂ hB₂
    · have hcdeg : 0 < (Polynomial.map (algebraMap ℝ ℂ) q).degree := by
        rw [Polynomial.degree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
        exact Polynomial.natDegree_pos_iff_degree_pos.mp hdeg_pos
      obtain ⟨z, hz⟩ := Complex.exists_root hcdeg
      have hzim : z.im ≠ 0 := fun him => hreal ⟨z.re, by
        have heq : z = (z.re : ℂ) := Complex.ext rfl him
        rw [heq] at hz
        have hzr : (z.re : ℂ) = algebraMap ℝ ℂ z.re := rfl
        rw [hzr, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hz
        change ((q.eval z.re : ℝ) : ℂ) = 0 at hz
        exact Complex.ofReal_eq_zero.mp hz⟩
      obtain ⟨q₁, hq_mul⟩ := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero q
        (by simpa [Polynomial.aeval_def] using hz) hzim
      let f : ℝ[X] := Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X + Polynomial.C (‖z‖ ^ 2)
      have hf_sos : f = (Polynomial.X - Polynomial.C z.re) ^ 2 + Polynomial.C z.im ^ 2 := by
        have hns : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        dsimp [f]; rw [hns]; simp only [map_add, map_pow, map_mul, map_ofNat]; ring
      have hf_pos : ∀ s : ℝ, 0 < f.eval s := fun s => by
        rw [hf_sos, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_pow]
        simp only [Polynomial.eval_C]
        exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hzim)
      have hq₁0 : q₁ ≠ 0 := fun h => hq0 (by rw [hq_mul]; change f * q₁ = 0; rw [h, mul_zero])
      have hdeg_f : f.natDegree = 2 := by dsimp [f]; compute_degree!
      have hf0 : f ≠ 0 := fun h => by rw [h] at hdeg_f; simp at hdeg_f
      have hdeg_q₁ : q₁.natDegree + 2 = q.natDegree := by
        rw [hq_mul]; change q₁.natDegree + 2 = (f * q₁).natDegree
        rw [Polynomial.natDegree_mul hf0 hq₁0, hdeg_f, add_comm]
      have hq₁_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q₁.eval s := fun s hs => by
        have hev := hq_nn s hs
        rw [hq_mul] at hev
        change 0 ≤ (f * q₁).eval s at hev
        rw [Polynomial.eval_mul] at hev
        exact (mul_nonneg_iff_of_pos_left (hf_pos s)).mp hev
      obtain ⟨A₁, B₁, hq₁_eq, hA₁, hB₁⟩ := ih q₁.natDegree (by omega) q₁ le_rfl hq₁_nn
      exact sos_step_complex z hq_mul hdeg_q₁ A₁ B₁ hq₁_eq hA₁ hB₁

private lemma list_sum_sq_eval_nonneg (L : List ℝ[X]) (s : ℝ) :
    0 ≤ ((L.map (· ^ 2)).sum).eval s := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, Polynomial.eval_pow]
    exact add_nonneg (sq_nonneg _) ih

private lemma lagMeasure_eval_zero_le_of_nonneg {c : ℝ} (hc : 0 < c) {K : ℕ} {q : ℝ[X]}
    (hq_deg : q.natDegree ≤ K) (hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s) :
    q.eval 0 ≤ laguerreBinom (K / 2) c * lagMeasure c q := by
  obtain ⟨A, B, hq_eq, hA, _⟩ := poly_nonneg_Ici_sos q.natDegree q le_rfl hq_nn
  let m₁ := K / 2
  have ha_bd : ∀ a ∈ A, (a.eval 0) ^ 2 ≤ laguerreBinom m₁ c * lagMeasure c (a ^ 2) := fun a ha => by
    have ha_deg : a.natDegree ≤ m₁ := by have := hA a ha; omega
    let α : ℕ → ℝ := fun n => lagInner c a (laguerreHat c n)
    have hexp : a = ∑ n ∈ Finset.range (m₁ + 1), α n • laguerreHat c n :=
      poly_expand_laguerreHat hc ha_deg
    have h0_eq : a.eval 0 = ∑ n ∈ Finset.range (m₁ + 1), α n * (laguerreHat c n).eval 0 := by
      conv_lhs => rw [hexp]
      simp [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
    have hL2 : lagMeasure c (a ^ 2) = ∑ n ∈ Finset.range (m₁ + 1), α n ^ 2 := by
      have ha2 : lagMeasure c (a ^ 2) = lagInner c a a := by simp [lagInner, sq]
      rw [ha2]; conv_lhs => arg 2; rw [hexp]
      rw [lagInner_sum_left _ c (hc := hc)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [lagInner_smul_left, lagInner_comm]; dsimp [α]; ring
    have hsum0 : ∑ n ∈ Finset.range (m₁ + 1), ((laguerreHat c n).eval 0) ^ 2 = laguerreBinom m₁ c := by
      calc ∑ n ∈ Finset.range (m₁ + 1), ((laguerreHat c n).eval 0) ^ 2
          = ∑ n ∈ Finset.range (m₁ + 1), poch c n / (n.factorial : ℝ) := by
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [laguerreHat_eval_zero hc n, mul_pow, ← pow_mul, show (-1 : ℝ) ^ (n * 2) = 1 by
                rw [mul_comm, pow_mul]; norm_num, one_mul,
                Real.sq_sqrt (div_nonneg (poch_pos hc n).le (Nat.cast_nonneg _))]
        _ = laguerreBinom m₁ c := poch_pascal_sum c m₁
    rw [h0_eq, hL2, ← hsum0, mul_comm]
    exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m₁ + 1)) α (fun n => (laguerreHat c n).eval 0)
  have hsum_A_0 : q.eval 0 = (A.map (fun a => (a.eval 0) ^ 2)).sum := by
    conv_lhs => rw [hq_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, zero_mul, add_zero]
    exact list_eval_zero_sq_sum A
  have hB_nn : 0 ≤ lagMeasure c (Polynomial.X * (B.map (· ^ 2)).sum) := by
    unfold lagMeasure
    refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    have hsp : 0 < s := hs
    have hsum_nn : 0 ≤ ((B.map (· ^ 2)).sum).eval s := list_sum_sq_eval_nonneg B s
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    exact div_nonneg (mul_nonneg (mul_nonneg hsp.le hsum_nn)
      (mul_nonneg (Real.rpow_nonneg hsp.le _) (Real.exp_pos _).le)) (Real.Gamma_pos_of_pos hc).le
  have hq_int : lagMeasure c q = lagMeasure c (A.map (· ^ 2)).sum +
      lagMeasure c (Polynomial.X * (B.map (· ^ 2)).sum) := by
    conv_lhs => rw [hq_eq]
    exact lagMeasure_add hc _ _
  have hA_le : (A.map (fun a => (a.eval 0) ^ 2)).sum ≤
      laguerreBinom m₁ c * (A.map (fun a => lagMeasure c (a ^ 2))).sum :=
    list_sum_le_mul_sum _ _ _ A ha_bd
  have hbinom_nn : 0 ≤ laguerreBinom m₁ c := (laguerreBinom_pos hc.le m₁).le
  calc q.eval 0
      = (A.map (fun a => (a.eval 0) ^ 2)).sum := hsum_A_0
    _ ≤ laguerreBinom m₁ c * (A.map (fun a => lagMeasure c (a ^ 2))).sum := hA_le
    _ = laguerreBinom m₁ c * lagMeasure c (A.map (· ^ 2)).sum := by rw [list_lagMeasure_sq_sum c hc A]
    _ ≤ laguerreBinom m₁ c * lagMeasure c q := by rw [hq_int]; nlinarith

lemma ce_laguerre_cond_sufficient {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (hcond : K = 1 ∨ 5 * K < d) :
    (d : ℝ) > 4 * ((K / 2 : ℕ) : ℝ) +
      4 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (2 * ((K / 2 : ℕ) : ℝ) - 1)) := by
  let m₁ : ℕ := K / 2
  rcases hcond with rfl | hd5K
  · change (d : ℝ) > 4 * ((1 / 2 : ℕ) : ℝ) + 4 * Real.sqrt (((1 / 2 : ℕ) : ℝ) * (2 * ((1 / 2 : ℕ) : ℝ) - 1))
    norm_num; exact_mod_cast (by omega : 0 < d)
  · rcases Nat.eq_zero_or_pos m₁ with hm0 | hm_pos
    · dsimp [m₁] at hm0; rw [hm0]; norm_num; exact Nat.cast_pos.mpr (by omega)
    · have hm1 : (1 : ℝ) ≤ m₁ := by exact_mod_cast hm_pos
      have hsq_lt : (m₁ : ℝ) * (2 * (m₁ : ℝ) - 1) < (3 / 2 * (m₁ : ℝ)) ^ 2 := by nlinarith
      have hrt : Real.sqrt ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)) < 3 / 2 * (m₁ : ℝ) := by
        rw [Real.sqrt_lt' (by positivity)]; exact hsq_lt
      have hd_gt : (10 : ℝ) * m₁ < d := by
        have h1 : 2 * m₁ ≤ K := Nat.mul_div_le K 2
        have h2 : 10 * m₁ < d := by omega
        exact_mod_cast h2
      dsimp [m₁] at *; linarith

/-- **Theorem E.3a (`thm:ce-laguerre-limit`, `(eq:finite:E.5c)`).** -/
theorem ce_laguerre_finite_lower_bound {d K : ℕ} (hd : 2 ≤ d) (_hK : 1 ≤ K) {t r : ℝ} (ht : 0 < t)
    {P : ℝ[X]} (hP_deg : P.natDegree ≤ K)
    (hf_nonneg : ∀ y : Euc d,
      (𝓕 (fun x : Euc d => ((P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ)) y).im = 0 ∧
      0 ≤ (𝓕 (fun x : Euc d => ((P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ)) y).re)
    (h0 : 0 < P.eval 0)
    (hf0 : 0 < (𝓕 (fun x : Euc d => ((P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ)) 0).re)
    (h_nonpos : ∀ x : Euc d, r ≤ ‖x‖ →
      P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) ≤ 0)
    (hm_cond : (d : ℝ) > 4 * ((K / 2 : ℕ) : ℝ) +
      4 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (2 * ((K / 2 : ℕ) : ℝ) - 1))) :
    (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ * (Real.Gamma ((d : ℝ) / 2 + 1))⁻¹ *
        (((d : ℝ) - 2 * Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2))) / 8) ^
          ((d : ℝ) / 2) ≤
      cohnElkiesBound d r (fun x : Euc d => P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)) := by
  let h : Euc d → ℝ := fun x => P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)
  have hr_pos : 0 < r := by
    by_contra hr0; push Not at hr0
    have := h_nonpos 0 (by simp; exact hr0)
    simp [h0.not_ge] at this
  have hc_pos : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  let c : ℝ := (d : ℝ) / 2
  let Ptilde : ℝ[X] := P.comp (Polynomial.C (1 / (2 * π * t)) * Polynomial.X)
  let Qtilde : ℝ[X] := fourierPolyTransform c Ptilde
  let p : ℝ[X] := Ptilde.comp (Polynomial.C 2 * Polynomial.X)
  let q : ℝ[X] := Qtilde.comp (Polynomial.C 2 * Polynomial.X)
  have hPtilde_deg : Ptilde.natDegree ≤ K :=
    (Polynomial.natDegree_comp_le).trans (by
      have : (Polynomial.C (1 / (2 * π * t)) * Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      exact (Nat.mul_le_mul hP_deg this).trans (by omega))
  have hQtilde_deg : Qtilde.natDegree ≤ K :=
    (fourierPolyTransform_natDegree_le c Ptilde).trans hPtilde_deg
  have hp_deg : p.natDegree ≤ K :=
    (Polynomial.natDegree_comp_le).trans (by
      have : (Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      exact (Nat.mul_le_mul hPtilde_deg this).trans (by omega))
  have hq_deg : q.natDegree ≤ K :=
    (Polynomial.natDegree_comp_le).trans (by
      have : (Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      exact (Nat.mul_le_mul hQtilde_deg this).trans (by omega))
  let g : Euc d → ℝ := fun x => Ptilde.eval (2 * π * ‖x‖ ^ 2) * Real.exp (-π * ‖x‖ ^ 2)
  have hg_scale : ∀ x : Euc d, g x = h ((1 / Real.sqrt t) • x) := fun x => by
    have hnorm : ‖(1 / Real.sqrt t) • x‖ ^ 2 = (1 / t) * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr ht)),
        mul_pow, div_pow, one_pow, Real.sq_sqrt ht.le]
    dsimp [g, h, Ptilde]
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hnorm]
    congr 2
    · field_simp [Real.pi_ne_zero, ht.ne']
    · field_simp [ht.ne']
  have hft_scale : ∀ y : Euc d,
      𝓕 (fun x : Euc d => (g x : ℂ)) y =
        (t ^ ((d : ℝ) / 2) : ℝ) • 𝓕 (fun x : Euc d => (h x : ℂ)) (Real.sqrt t • y) := by
    intro y
    let s : ℝ := (Real.sqrt t)⁻¹
    have hs_pos : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr ht)
    have hg_eq : (fun x : Euc d => (g x : ℂ)) = fun x => (h (s • x) : ℂ) := by
      ext x; rw [hg_scale x, one_div]
    rw [hg_eq, Real.fourier_eq]
    have hrew : (fun x : Euc d => 𝐞 (-⟪x, y⟫) • (h (s • x) : ℂ)) =
        fun x => (fun u => 𝐞 (-⟪u, Real.sqrt t • y⟫) • (h u : ℂ)) (s • x) := by
      ext x
      have hinn : ⟪x, y⟫ = ⟪s • x, Real.sqrt t • y⟫ := by
        rw [real_inner_smul_left, real_inner_smul_right]
        dsimp [s]; rw [inv_mul_cancel_left₀ (Real.sqrt_pos.mpr ht).ne']
      rw [hinn]
    rw [hrew, Measure.integral_comp_smul_of_nonneg (μ := volume)
        (fun u => 𝐞 (-⟪u, Real.sqrt t • y⟫) • (h u : ℂ)) s (hR := hs_pos.le),
      finrank_euclideanSpace_fin, Real.fourier_eq]
    congr 1
    dsimp [s]
    rw [inv_pow, inv_inv, ← Real.rpow_natCast (Real.sqrt t) d, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    congr 1; ring
  have hft_g : ∀ y : Euc d,
      𝓕 (fun x : Euc d => (g x : ℂ)) y =
        ((Qtilde.eval (2 * π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ) := fun y => by
    simpa [g, Qtilde, c] using fourier_poly_gaussian d Ptilde y
  let idx0 : Fin d := ⟨0, by omega⟩
  let e0 : Euc d := WithLp.toLp 2 (Pi.single idx0 (1 : ℝ))
  have he0_norm : ‖e0‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    simp [e0]
  have hq_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ q.eval s := fun s hs => by
    let y : Euc d := Real.sqrt (s / π) • e0
    have hnorm : ‖y‖ = Real.sqrt (s / π) := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), he0_norm, mul_one]
    have h2pi : 2 * π * ‖y‖ ^ 2 = 2 * s := by
      rw [hnorm, Real.sq_sqrt (div_nonneg hs Real.pi_pos.le)]
      field_simp [Real.pi_ne_zero]
    have hy_eq := congr_arg Complex.re (hft_g y)
    rw [hft_scale y, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re] at hy_eq
    have hre_nn : 0 ≤ t ^ ((d : ℝ) / 2) * (𝓕 (fun x : Euc d => (h x : ℂ)) (Real.sqrt t • y)).re :=
      mul_nonneg (Real.rpow_nonneg ht.le _) (hf_nonneg (Real.sqrt t • y)).2
    have hq_ev : q.eval s = Qtilde.eval (2 * π * ‖y‖ ^ 2) := by
      dsimp [q]; simp [Polynomial.eval_comp, h2pi]
    rw [hq_ev]
    have hmul_nn : 0 ≤ Qtilde.eval (2 * π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) := hy_eq ▸ hre_nn
    exact nonneg_of_mul_nonneg_left hmul_nn (Real.exp_pos _)
  have h_inv_g0 : g 0 = ∫ y : Euc d, q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) := by
    let Ptilde2 : ℝ[X] := Ptilde.comp (Polynomial.C (2 * π) * Polynomial.X)
    let Sg := polyGaussianSchwartz d one_pos Ptilde2
    have hSg_eq : (⇑Sg : Euc d → ℂ) = fun x => (g x : ℂ) := funext fun x => by
      simp [Sg, polyGaussianSchwartz_apply, g, Ptilde2, mul_assoc]
    have hcont_g : Continuous (fun x : Euc d => (g x : ℂ)) := by rw [← hSg_eq]; exact Sg.continuous
    have hint_g : Integrable (fun x : Euc d => (g x : ℂ)) := by rw [← hSg_eq]; exact Sg.integrable
    have hint_fg : Integrable (𝓕 (fun x : Euc d => (g x : ℂ))) := by
      rw [← hSg_eq]; exact (𝓕 Sg).integrable
    have hinv := congr_arg Complex.re (congr_fun (hcont_g.fourierInv_fourier_eq hint_g hint_fg) 0)
    rw [Real.fourierInv_eq'] at hinv
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, smul_eq_mul, one_mul, Complex.ofReal_re] at hinv
    rw [← hinv]
    simp_rw [hft_g]
    have hint : Integrable (fun y : Euc d => q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2)) := by
      have h_eq : (fun y : Euc d => q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2)) =
          fun y => Qtilde.eval (2 * π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) := funext fun y => by
        dsimp [q]; simp [Polynomial.eval_comp, mul_assoc]
      rw [h_eq]
      have hS := Complex.reCLM.integrable_comp ((𝓕 Sg).integrable (μ := volume))
      refine hS.congr (Eventually.of_forall fun y => ?_)
      change (Complex.reCLM ((𝓕 Sg) y)) = _
      rw [SchwartzMap.fourier_coe, hSg_eq, hft_g]
      simp only [Complex.reCLM_apply, Complex.ofReal_re]
    have hintC : Integrable (fun y : Euc d =>
        ((q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hint
    calc (∫ y : Euc d, ((Qtilde.eval (2 * π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ)).re
        = (∫ y : Euc d, ((q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ)).re := by
            congr 1; refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            dsimp [q]; simp [Polynomial.eval_comp, mul_assoc]
      _ = Complex.reCLM (∫ y : Euc d, ((q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ)) := rfl
      _ = ∫ y : Euc d, Complex.reCLM ((q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ) :=
            (Complex.reCLM.integral_comp_comm hintC).symm
      _ = ∫ y : Euc d, q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2) := rfl
  have hlag_q : lagMeasure c q = g 0 := by
    have h_eq : (∫ y : Euc d, q.eval (π * ‖y‖ ^ 2) * Real.exp (-π * ‖y‖ ^ 2)) =
        ∫ y : Euc d, q.eval (π * ‖y‖ ^ 2) * Real.exp (-(π * ‖y‖ ^ 2)) :=
      integral_congr_ae (Eventually.of_forall fun y => by
        dsimp only; rw [show -π * ‖y‖ ^ 2 = -(π * ‖y‖ ^ 2) by ring])
    rw [h_inv_g0, h_eq]
    have hp_pol := polar_integral_eq (d := d) (by omega) (fun s => q.eval s * Real.exp (-s))
    rw [hp_pol]
    unfold lagMeasure c
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  have hlag_p : lagMeasure c p = q.eval 0 := by
    have hp_pol := polar_integral_eq (d := d) (by omega) (fun s => p.eval s * Real.exp (-s))
    have h_lhs : (fun x : Euc d => p.eval (π * ‖x‖ ^ 2) * Real.exp (-(π * ‖x‖ ^ 2))) = g := by
      ext x; dsimp [g, p]
      simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [show 2 * (π * ‖x‖ ^ 2) = 2 * π * ‖x‖ ^ 2 by ring,
        show -(π * ‖x‖ ^ 2) = -π * ‖x‖ ^ 2 by ring]
    rw [h_lhs] at hp_pol
    have hg_int : (∫ x : Euc d, g x) = q.eval 0 := by
      have hft0 := congr_arg Complex.re (hft_g 0)
      rw [Real.fourier_eq'] at hft0
      simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        smul_eq_mul, one_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Real.exp_zero, mul_one, Complex.ofReal_re] at hft0
      let Ptilde2 : ℝ[X] := Ptilde.comp (Polynomial.C (2 * π) * Polynomial.X)
      let Sg := polyGaussianSchwartz d one_pos Ptilde2
      have hSg_eq : (⇑Sg : Euc d → ℂ) = fun x => (g x : ℂ) := funext fun x => by
        simp [Sg, polyGaussianSchwartz_apply, g, Ptilde2, mul_assoc]
      have hint_gℂ : Integrable (fun x : Euc d => (g x : ℂ)) := by rw [← hSg_eq]; exact Sg.integrable
      rw [show (∫ x : Euc d, (g x : ℂ)).re = ∫ x : Euc d, g x by
        calc (∫ x : Euc d, (g x : ℂ)).re
            = Complex.reCLM (∫ x : Euc d, (g x : ℂ)) := rfl
          _ = ∫ x : Euc d, Complex.reCLM (g x : ℂ) :=
                (Complex.reCLM.integral_comp_comm hint_gℂ).symm
          _ = ∫ x : Euc d, g x := rfl] at hft0
      dsimp [q]; simp [Polynomial.eval_comp]; exact hft0
    rw [hg_int] at hp_pol
    unfold lagMeasure c
    rw [hp_pol, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  have hq0_pos : 0 < q.eval 0 := by
    have heq := congr_arg Complex.re (hft_g 0)
    rw [hft_scale 0, smul_zero, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re] at heq
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero, mul_one] at heq
    have : q.eval 0 = Qtilde.eval 0 := by dsimp [q]; simp [Polynomial.eval_comp]
    rw [this, ← heq]
    exact mul_pos (Real.rpow_pos_of_pos ht _) hf0
  have hg0_eq : g 0 = h 0 := by rw [hg_scale 0, smul_zero]
  have h_origin_ratio : q.eval 0 ≤ laguerreBinom (K / 2) c * g 0 := by
    rw [← hlag_q]
    exact lagMeasure_eval_zero_le_of_nonneg hc_pos hq_deg hq_nn
  have hp_nonpos : ∀ s : ℝ, π * t * r ^ 2 ≤ s → p.eval s ≤ 0 := fun s hs => by
    have hs_nn : 0 ≤ s := le_trans (by positivity) hs
    let x : Euc d := Real.sqrt (s / π) • e0
    have hnorm_x : ‖x‖ = Real.sqrt (s / π) := by
      dsimp [x]; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), he0_norm, mul_one]
    have hnorm_sc : r ≤ ‖(1 / Real.sqrt t) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr ht)),
        hnorm_x, one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr ht.le),
        ← Real.sqrt_sq hr_pos.le]
      refine Real.sqrt_le_sqrt ?_
      rw [← div_eq_inv_mul, div_div, le_div_iff₀ (mul_pos Real.pi_pos ht)]
      linarith
    have hgx := hg_scale x
    have hp2 : π * ‖x‖ ^ 2 = s := by
      rw [hnorm_x, Real.sq_sqrt (div_nonneg hs_nn Real.pi_pos.le)]; field_simp [Real.pi_ne_zero]
    have h2pi : 2 * π * ‖x‖ ^ 2 = 2 * s := by linarith
    rw [show g x = p.eval s * Real.exp (-s) by
      dsimp [g, p]
      simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, h2pi]
      rw [show -π * ‖x‖ ^ 2 = -(π * ‖x‖ ^ 2) by ring, hp2]] at hgx
    have h_le0 : p.eval s * Real.exp (-s) ≤ 0 := hgx ▸ h_nonpos _ hnorm_sc
    exact le_of_not_gt fun hpos => absurd (mul_pos hpos (Real.exp_pos _)) (not_lt.mpr h_le0)
  have hm_lt : c - 2 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (((K / 2 : ℕ) : ℝ) + c - 1)) < π * t * r ^ 2 := by
    have hp_deg2 : p.natDegree ≤ 2 * (K / 2) + 1 := hp_deg.trans (by omega)
    exact lagMeasure_pos_radius_bound hc_pos (K / 2) hp_deg2 (hlag_p ▸ hq0_pos) hp_nonpos
  have hsqrt_eq : 2 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (((K / 2 : ℕ) : ℝ) + c - 1)) =
      Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2)) := by
    calc 2 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (((K / 2 : ℕ) : ℝ) + c - 1))
        = Real.sqrt 4 * Real.sqrt (((K / 2 : ℕ) : ℝ) * (((K / 2 : ℕ) : ℝ) + c - 1)) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ = Real.sqrt (4 * (((K / 2 : ℕ) : ℝ) * (((K / 2 : ℕ) : ℝ) + c - 1))) :=
            (Real.sqrt_mul (by norm_num) _).symm
      _ = Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2)) := by
            congr 1; dsimp [c]; ring
  have hrad_pos : 0 < (d : ℝ) - 2 * Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2)) := by
    let m₁ : ℕ := K / 2
    have h1 : 4 * (m₁ : ℝ) < d := by linarith [Real.sqrt_nonneg ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)), hm_cond]
    have h2 : 4 * Real.sqrt ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)) < (d : ℝ) - 4 * m₁ := by linarith
    have h3 : (16 : ℝ) * ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)) < ((d : ℝ) - 4 * m₁) ^ 2 := by
      rcases Nat.eq_zero_or_pos m₁ with hm0 | hm_pos
      · rw [hm0]; norm_num; positivity
      · have hnn : 0 ≤ (m₁ : ℝ) * (2 * (m₁ : ℝ) - 1) := by
          have : (1 : ℝ) ≤ m₁ := by exact_mod_cast hm_pos
          nlinarith
        have hsq_eq : (16 : ℝ) * ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)) =
            (4 * Real.sqrt ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hnn]; ring
        rw [hsq_eq]
        nlinarith [Real.sqrt_nonneg ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1))]
    have hid : ((d : ℝ) - 4 * m₁) ^ 2 - 16 * ((m₁ : ℝ) * (2 * (m₁ : ℝ) - 1)) =
        (d : ℝ) ^ 2 - 4 * (2 * (m₁ : ℝ) * ((d : ℝ) + 2 * m₁ - 2)) := by ring
    have h4 : 4 * (2 * (m₁ : ℝ) * ((d : ℝ) + 2 * m₁ - 2)) < (d : ℝ) ^ 2 := by linarith
    have hm2 : 0 ≤ 2 * (m₁ : ℝ) * ((d : ℝ) + 2 * m₁ - 2) := by
      rcases Nat.eq_zero_or_pos m₁ with hm0 | hm_pos
      · rw [hm0]; norm_num
      · have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [Nat.cast_nonneg (α := ℝ) m₁]
    have h5 : (2 * Real.sqrt (2 * (m₁ : ℝ) * ((d : ℝ) + 2 * m₁ - 2))) ^ 2 < (d : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hm2]; linarith
    have hd_pos : 0 < (d : ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg (2 * (m₁ : ℝ) * ((d : ℝ) + 2 * m₁ - 2))]
  have hpi_gt : ((d : ℝ) - 2 * Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2))) / 2 <
      π * t * r ^ 2 := by
    rw [← hsqrt_eq]; dsimp [c] at hm_lt; linarith
  have h_rpow : (((d : ℝ) - 2 * Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2))) / 8) ^
      ((d : ℝ) / 2) ≤ (π * (t * r ^ 2) / 4) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) hc_pos.le
  have hratio_lb : (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ * t ^ ((d : ℝ) / 2) ≤
      h 0 / (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re := by
    have hq0_eq : q.eval 0 = t ^ ((d : ℝ) / 2) * (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re := by
      have heq := congr_arg Complex.re (hft_g 0)
      rw [hft_scale 0, smul_zero, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re] at heq
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        Real.exp_zero, mul_one] at heq
      dsimp [q]; simp [Polynomial.eval_comp, ← heq]
    have hb_pos : 0 < laguerreBinom (K / 2) c := laguerreBinom_pos hc_pos.le (K / 2)
    rw [hq0_eq, hg0_eq] at h_origin_ratio
    rw [le_div_iff₀ hf0, inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hb_pos]
    dsimp [c]; linarith
  unfold cohnElkiesBound
  rw [volume_half_ball_eq (by omega) hr_pos.le]
  have hvol_scale : t ^ ((d : ℝ) / 2) * ((π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) =
      (π * (t * r ^ 2) / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
    rw [mul_div_assoc', ← Real.mul_rpow ht.le (by positivity : 0 ≤ π * r ^ 2 / 4)]
    congr 2; ring
  have hG_pos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  calc (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ * (Real.Gamma ((d : ℝ) / 2 + 1))⁻¹ *
        (((d : ℝ) - 2 * Real.sqrt (2 * (K / 2 : ℕ) * ((d : ℝ) + 2 * (K / 2 : ℕ) - 2))) / 8) ^
          ((d : ℝ) / 2)
      ≤ (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ * (Real.Gamma ((d : ℝ) / 2 + 1))⁻¹ *
          (π * (t * r ^ 2) / 4) ^ ((d : ℝ) / 2) := by
          gcongr
          exact mul_nonneg (inv_nonneg.mpr (laguerreBinom_pos hc_pos.le _).le) (inv_nonneg.mpr hG_pos.le)
    _ = (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ *
          ((π * (t * r ^ 2) / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) := by ring
    _ = (laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ *
          (t ^ ((d : ℝ) / 2) * ((π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))) := by
          rw [← hvol_scale]
    _ = ((laguerreBinom (K / 2) ((d : ℝ) / 2))⁻¹ * t ^ ((d : ℝ) / 2)) *
          ((π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) := by ring
    _ ≤ (h 0 / (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re) *
          ((π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) := by
          exact mul_le_mul_of_nonneg_right hratio_lb (div_nonneg (Real.rpow_nonneg (by positivity) _) hG_pos.le)

private lemma real_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsq : x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx.le).symm
  calc Real.log x
      = Real.log (Real.sqrt x ^ 2) := by rw [← hsq]
    _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; norm_num
    _ ≤ 2 * (Real.sqrt x - 1) := by linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)]
    _ ≤ 2 * Real.sqrt x := by linarith

private lemma one_le_laguerreBinom (m : ℕ) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ laguerreBinom m c := by
  unfold laguerreBinom poch
  have hfac : (m.factorial : ℝ) = ∏ i ∈ Finset.range m, ((i : ℝ) + 1) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.factorial_succ, Finset.prod_range_succ, ← ih]; push_cast; ring
  rw [hfac, one_le_div (Finset.prod_pos fun i _ => by positivity)]
  exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => by linarith

private lemma laguerreBinom_sublinear_rate_tendsto_zero {m : ℕ → ℕ}
    (hm : Tendsto (fun d : ℕ => (m d : ℝ) / (d : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun d : ℕ => (1 / (d : ℝ)) * Real.log (laguerreBinom (m d) ((d : ℝ) / 2))) atTop (𝓝 0) := by
  have hm_lt : ∀ᶠ d : ℕ in atTop, (m d : ℝ) / (d : ℝ) < 1 :=
    hm (gt_mem_nhds zero_lt_one)
  have h_upper : ∀ᶠ d : ℕ in atTop,
      (1 / (d : ℝ)) * Real.log (laguerreBinom (m d) ((d : ℝ) / 2)) ≤
        (m d : ℝ) / (d : ℝ) + 2 * Real.sqrt 2 * Real.sqrt ((m d : ℝ) / (d : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1, hm_lt] with d hd1 hmlt
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd1
    have hmd_le : m d ≤ d := by
      have : (m d : ℝ) < (d : ℝ) := (div_lt_one hd_pos).mp hmlt
      exact_mod_cast this.le
    rcases Nat.eq_zero_or_pos (m d) with hm0 | hmpos
    · rw [hm0]; simp [laguerreBinom, poch_zero]
    · have hm_pos : (0 : ℝ) < m d := Nat.cast_pos.mpr hmpos
      have hpoch_le : poch ((d : ℝ) / 2 + 1) (m d) ≤ ((m d : ℝ) + (d : ℝ) / 2) ^ (m d) := by
        unfold poch
        calc ∏ i ∈ Finset.range (m d), ((d : ℝ) / 2 + 1 + i)
            ≤ ∏ _i ∈ Finset.range (m d), ((m d : ℝ) + (d : ℝ) / 2) :=
                Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => by
                  have : (i : ℝ) + 1 ≤ m d := by exact_mod_cast Finset.mem_range.mp hi
                  linarith
          _ = ((m d : ℝ) + (d : ℝ) / 2) ^ (m d) := by simp
      have hfac_lb : ((m d : ℝ) / Real.exp 1) ^ (m d) ≤ ((m d).factorial : ℝ) := by
        have h1 := Real.pow_div_factorial_le_exp (m d : ℝ) hm_pos.le (m d)
        calc ((m d : ℝ) / Real.exp 1) ^ (m d)
            = (m d : ℝ) ^ m d / (Real.exp 1) ^ m d := by rw [div_pow]
          _ = (m d : ℝ) ^ m d / Real.exp (m d : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
          _ ≤ ((m d).factorial : ℝ) := by
                rw [div_le_iff₀ (Real.exp_pos _)]
                rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (m d)))] at h1
                linarith
      have hbin_le : laguerreBinom (m d) ((d : ℝ) / 2) ≤
          (Real.exp 1 * (2 * (d : ℝ)) / (m d : ℝ)) ^ (m d) := by
        unfold laguerreBinom
        have hfac_pos : (0 : ℝ) < (m d).factorial := Nat.cast_pos.mpr (Nat.factorial_pos (m d))
        calc poch ((d : ℝ) / 2 + 1) (m d) / ((m d).factorial : ℝ)
            ≤ ((m d : ℝ) + (d : ℝ) / 2) ^ (m d) / ((m d : ℝ) / Real.exp 1) ^ (m d) :=
                div_le_div₀ (by positivity) hpoch_le (by positivity) hfac_lb
          _ = (Real.exp 1 * ((m d : ℝ) + (d : ℝ) / 2) / (m d : ℝ)) ^ (m d) := by
                rw [← div_pow]; congr 1; field_simp [hm_pos.ne', (Real.exp_pos 1).ne']
          _ ≤ (Real.exp 1 * (2 * (d : ℝ)) / (m d : ℝ)) ^ (m d) := by
                gcongr; linarith [show (m d : ℝ) ≤ d by exact_mod_cast hmd_le]
      have hbin_pos : 0 < laguerreBinom (m d) ((d : ℝ) / 2) :=
        laguerreBinom_pos (by positivity) (m d)
      have hlog_le : Real.log (laguerreBinom (m d) ((d : ℝ) / 2)) ≤
          (m d : ℝ) * (1 + Real.log (2 * (d : ℝ) / (m d : ℝ))) := by
        have hl := Real.log_le_log hbin_pos hbin_le
        rw [Real.log_pow, Real.log_div (by positivity) hm_pos.ne',
          Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp] at hl
        rwa [add_sub_assoc, ← Real.log_div (by positivity) hm_pos.ne'] at hl
      have hlog_sqrt : Real.log (2 * (d : ℝ) / (m d : ℝ)) ≤
          2 * Real.sqrt (2 * (d : ℝ) / (m d : ℝ)) := real_log_le_two_sqrt (by positivity)
      calc (1 / (d : ℝ)) * Real.log (laguerreBinom (m d) ((d : ℝ) / 2))
          ≤ ((m d : ℝ) / (d : ℝ)) * (1 + 2 * Real.sqrt (2 * (d : ℝ) / (m d : ℝ))) := by
              rw [one_div_mul_eq_div, div_le_iff₀ hd_pos]
              have h1 : Real.log (laguerreBinom (m d) ((d : ℝ) / 2)) ≤
                  (m d : ℝ) * (1 + 2 * Real.sqrt (2 * (d : ℝ) / (m d : ℝ))) :=
                hlog_le.trans (mul_le_mul_of_nonneg_left (by linarith) hm_pos.le)
              calc Real.log (laguerreBinom (m d) ((d : ℝ) / 2))
                  ≤ (m d : ℝ) * (1 + 2 * Real.sqrt (2 * (d : ℝ) / (m d : ℝ))) := h1
                _ = (m d : ℝ) / (d : ℝ) * (1 + 2 * Real.sqrt (2 * (d : ℝ) / (m d : ℝ))) * (d : ℝ) := by
                      field_simp [hd_pos.ne']
        _ = (m d : ℝ) / (d : ℝ) +
              2 * Real.sqrt 2 * Real.sqrt ((m d : ℝ) / (d : ℝ)) := by
              have hdiv_pos : 0 < (m d : ℝ) / (d : ℝ) := div_pos hm_pos hd_pos
              have hterm : ((m d : ℝ) / (d : ℝ)) * Real.sqrt (2 * (d : ℝ) / (m d : ℝ)) =
                  Real.sqrt 2 * Real.sqrt ((m d : ℝ) / (d : ℝ)) := by
                calc ((m d : ℝ) / (d : ℝ)) * Real.sqrt (2 * (d : ℝ) / (m d : ℝ))
                    = Real.sqrt (((m d : ℝ) / (d : ℝ)) ^ 2) *
                        Real.sqrt (2 * (d : ℝ) / (m d : ℝ)) := by
                          rw [Real.sqrt_sq hdiv_pos.le]
                  _ = Real.sqrt (((m d : ℝ) / (d : ℝ)) ^ 2 * (2 * (d : ℝ) / (m d : ℝ))) := by
                        rw [← Real.sqrt_mul (by positivity)]
                  _ = Real.sqrt (2 * ((m d : ℝ) / (d : ℝ))) := by
                        congr 1; field_simp [hm_pos.ne', hd_pos.ne']
                  _ = Real.sqrt 2 * Real.sqrt ((m d : ℝ) / (d : ℝ)) :=
                        Real.sqrt_mul (by norm_num) _
              linarith
  have h_lower : ∀ᶠ d : ℕ in atTop,
      (0 : ℝ) ≤ (1 / (d : ℝ)) * Real.log (laguerreBinom (m d) ((d : ℝ) / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with d hd1
    exact mul_nonneg (by positivity) (Real.log_nonneg (one_le_laguerreBinom (m d) (by positivity)))
  have h_bound_lim : Tendsto (fun d : ℕ =>
      (m d : ℝ) / (d : ℝ) + 2 * Real.sqrt 2 * Real.sqrt ((m d : ℝ) / (d : ℝ))) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hm
    rw [Real.sqrt_zero] at hs
    simpa using hm.add (tendsto_const_nhds.mul hs)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_bound_lim h_lower h_upper

private lemma log_gamma_half_asymptotic :
    Tendsto (fun d : ℕ =>
      (1 / (d : ℝ)) * Real.log (Real.Gamma ((d : ℝ) / 2 + 1)) -
        (1 / 2) * (Real.log ((d : ℝ) / 2) - 1)) atTop (𝓝 0) := by
  let C : ℝ := |Real.log (2 * π)| + 10
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbd : ∀ᶠ d : ℕ in atTop,
      |(1 / (d : ℝ)) * Real.log (Real.Gamma ((d : ℝ) / 2 + 1)) -
        (1 / 2) * (Real.log ((d : ℝ) / 2) - 1)| ≤ C / Real.sqrt d := by
    filter_upwards [eventually_ge_atTop 4] with d hd4
    rcases Nat.even_or_odd' d with ⟨n, rfl | rfl⟩
    · have hn2 : 2 ≤ n := by omega
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
        push_cast; rw [show 2 * (n : ℝ) / 2 + 1 = (n : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial]
      obtain ⟨hst_lo, hst_hi⟩ := log_factorial_stirling_bounds hn1
      set R := Real.log (n.factorial : ℝ) -
        ((1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n))
      have hR : |R| ≤ 1 / (144 * (n : ℝ) ^ 3) := abs_le.mpr (by dsimp [R]; constructor <;> linarith)
      have hR1 : |R| ≤ 1 := hR.trans (by
        rw [div_le_one (by positivity)]
        have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.one_le_pow 3 n hn1
        linarith)
      have h1_eq : (1 / ((2 * n : ℕ) : ℝ)) * Real.log (Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1)) -
          (1 / 2) * (Real.log (((2 * n : ℕ) : ℝ) / 2) - 1) =
          (Real.log (2 * π) / 2 + (1 / 2) * Real.log n + 1 / (12 * n) + R) / (2 * n) := by
        rw [hG]; push_cast
        rw [show 2 * (n : ℝ) / 2 = n by ring,
          show Real.log (n.factorial : ℝ) =
            (1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n) + R by
              dsimp [R]; ring]
        field_simp [hn0.ne']; ring
      have hlog_n : |Real.log n| ≤ 2 * Real.sqrt n := by
        rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1))]
        exact real_log_le_two_sqrt hn0
      have h1n : 1 / (12 * (n : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1]
      have hnum : |Real.log (2 * π) / 2 + (1 / 2) * Real.log n + 1 / (12 * n) + R| ≤
          (|Real.log (2 * π)| / 2 + 3) * Real.sqrt n := by
        have hsn1 : 1 ≤ Real.sqrt n := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
        have ha := abs_add_le (Real.log (2 * π) / 2 + (1 / 2) * Real.log n + 1 / (12 * n)) R
        have hb := abs_add_le (Real.log (2 * π) / 2 + (1 / 2) * Real.log n) (1 / (12 * n))
        have hc := abs_add_le (Real.log (2 * π) / 2) ((1 / 2) * Real.log n)
        have ha1 : |Real.log (2 * π) / 2| = |Real.log (2 * π)| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have ha2 : |(1 / 2 : ℝ) * Real.log n| = (1 / 2) * |Real.log n| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have ha3 : |1 / (12 * (n : ℝ))| = 1 / (12 * n) := abs_of_pos (by positivity)
        rw [ha1, ha2] at hc
        rw [ha3] at hb
        nlinarith [abs_nonneg (Real.log (2 * π))]
      rw [h1_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
      calc |Real.log (2 * π) / 2 + (1 / 2) * Real.log n + 1 / (12 * n) + R| / (2 * n)
          ≤ ((|Real.log (2 * π)| / 2 + 3) * Real.sqrt n) / (2 * n) :=
              div_le_div_of_nonneg_right hnum (by positivity)
        _ = (|Real.log (2 * π)| / 2 + 3) / (2 * Real.sqrt n) := by
              calc ((|Real.log (2 * π)| / 2 + 3) * Real.sqrt n) / (2 * (n : ℝ))
                  = ((|Real.log (2 * π)| / 2 + 3) * Real.sqrt n) /
                      (2 * (Real.sqrt n * Real.sqrt n)) := by rw [Real.mul_self_sqrt hn0.le]
                _ = (|Real.log (2 * π)| / 2 + 3) / (2 * Real.sqrt n) := by
                      field_simp [(Real.sqrt_pos.mpr hn0).ne']
        _ ≤ C / Real.sqrt ((2 * n : ℕ) : ℝ) := by
              push_cast
              rw [show (2 : ℝ) * n = 2 * (n : ℝ) by ring, Real.sqrt_mul (by norm_num)]
              have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
              have hdiv_le : 1 / (2 * Real.sqrt n) ≤ 1 / (Real.sqrt 2 * Real.sqrt n) :=
                div_le_div_of_nonneg_left zero_le_one (by positivity)
                  (mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg _))
              have hcl : |Real.log (2 * π)| / 2 + 3 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log (2 * π))]
              calc (|Real.log (2 * π)| / 2 + 3) / (2 * Real.sqrt n)
                  = (|Real.log (2 * π)| / 2 + 3) * (1 / (2 * Real.sqrt n)) := by ring
                _ ≤ C * (1 / (Real.sqrt 2 * Real.sqrt n)) :=
                    mul_le_mul hcl hdiv_le (by positivity) hC
                _ = C / (Real.sqrt 2 * Real.sqrt n) := by ring
    · let m := n + 1
      have hm2 : 2 ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
      have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
        dsimp [m]; push_cast; ring
      have hG : Real.Gamma (((2 * n + 1 : ℕ) : ℝ) / 2 + 1) = Real.Gamma ((m : ℝ) + 1 / 2) := by
        rw [hcast]; congr 1; ring
      obtain ⟨hg_lo, hg_hi⟩ := log_gamma_half_odd_bounds hm1
      set R := Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) -
        ((1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m))
      have hR : |R| ≤ 1 / (144 * (m : ℝ) ^ 3) := abs_le.mpr (by dsimp [R]; constructor <;> linarith)
      have hR1 : |R| ≤ 1 := hR.trans (by
        rw [div_le_one (by positivity)]
        have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := by exact_mod_cast Nat.one_le_pow 3 m hm1
        linarith)
      have hm_half : (1 : ℝ) ≤ (m : ℝ) - 1 / 2 := by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        linarith
      have hm_diff_pos : 0 < (m : ℝ) - 1 / 2 := by linarith
      have hm_den_pos : 0 < 2 * (m : ℝ) - 1 := by linarith
      have h_log_diff : 0 ≤ Real.log m - Real.log ((m : ℝ) - 1 / 2) ∧
          Real.log m - Real.log ((m : ℝ) - 1 / 2) ≤ 1 / (2 * (m : ℝ) - 1) := by
        rw [← Real.log_div hm0.ne' hm_diff_pos.ne']
        refine ⟨Real.log_nonneg (by rw [one_le_div hm_diff_pos]; linarith), ?_⟩
        calc Real.log ((m : ℝ) / ((m : ℝ) - 1 / 2))
            ≤ (m : ℝ) / ((m : ℝ) - 1 / 2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = (1 / 2) / ((m : ℝ) - 1 / 2) := by
                rw [div_sub_one hm_diff_pos.ne']; congr 1; ring
          _ = 1 / (2 * ((m : ℝ) - 1 / 2)) := div_div 1 2 ((m : ℝ) - 1 / 2)
          _ = 1 / (2 * (m : ℝ) - 1) := by congr 1; ring
      have hm_den_ge : (m : ℝ) ≤ 2 * (m : ℝ) - 1 := by linarith [show (1 : ℝ) ≤ m by exact_mod_cast hm1]
      have h1_eq : (1 / ((2 * n + 1 : ℕ) : ℝ)) * Real.log (Real.Gamma (((2 * n + 1 : ℕ) : ℝ) / 2 + 1)) -
          (1 / 2) * (Real.log (((2 * n + 1 : ℕ) : ℝ) / 2) - 1) =
          (Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
            m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)) - 1 / (24 * m) - 1 / 2 + R) /
            (2 * (m : ℝ) - 1) := by
        rw [hG, hcast, show (2 * (m : ℝ) - 1) / 2 = (m : ℝ) - 1 / 2 by ring,
          show Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) =
            (1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m) + R by
              dsimp [R]; ring]
        field_simp [hm_den_pos.ne']; ring
      have hlog_mh : |Real.log ((m : ℝ) - 1 / 2)| ≤ 2 * Real.sqrt m := by
        rw [abs_of_nonneg (Real.log_nonneg hm_half)]
        exact (real_log_le_two_sqrt hm_diff_pos).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num))
      have hm_diff_bd : |(m : ℝ) * (Real.log m - Real.log ((m : ℝ) - 1 / 2))| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg hm0.le h_log_diff.1)]
        calc (m : ℝ) * (Real.log m - Real.log ((m : ℝ) - 1 / 2))
            ≤ (m : ℝ) * (1 / (2 * (m : ℝ) - 1)) := mul_le_mul_of_nonneg_left h_log_diff.2 hm0.le
          _ ≤ (m : ℝ) * (1 / (m : ℝ)) := by
                gcongr
          _ = 1 := by field_simp [hm0.ne']
      have h24 : |1 / (24 * (m : ℝ))| ≤ 1 := by
        rw [abs_of_pos (by positivity)]; rw [div_le_one (by positivity)]; linarith
      have hsn1 : 1 ≤ Real.sqrt m := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hm1)
      have hnum : |Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
          m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)) - 1 / (24 * m) - 1 / 2 + R| ≤
          (C / 2) * Real.sqrt m := by
        have h1 := abs_add_le (Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
          m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)) - 1 / (24 * m) - 1 / 2) R
        have h2 := abs_sub (Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
          m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)) - 1 / (24 * m)) (1 / 2 : ℝ)
        have h3 := abs_sub (Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
          m * (Real.log m - Real.log ((m : ℝ) - 1 / 2))) (1 / (24 * (m : ℝ)))
        have h4 := abs_add_le (Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2))
          (m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)))
        have h5 := abs_add_le (Real.log (2 * π) / 2) ((1 / 2) * Real.log ((m : ℝ) - 1 / 2))
        have ha1 : |Real.log (2 * π) / 2| = |Real.log (2 * π)| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have ha2 : |(1 / 2 : ℝ) * Real.log ((m : ℝ) - 1 / 2)| = (1 / 2) * |Real.log ((m : ℝ) - 1 / 2)| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [ha1, ha2] at h5
        have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [hhalf] at h2
        dsimp [C]; nlinarith [abs_nonneg (Real.log (2 * π))]
      rw [h1_eq, abs_div, abs_of_pos hm_den_pos]
      have hd_le_2m : ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by rw [hcast]; linarith
      calc |Real.log (2 * π) / 2 + (1 / 2) * Real.log ((m : ℝ) - 1 / 2) +
            m * (Real.log m - Real.log ((m : ℝ) - 1 / 2)) - 1 / (24 * m) - 1 / 2 + R| /
            (2 * (m : ℝ) - 1)
          ≤ ((C / 2) * Real.sqrt m) / m := by
              refine (div_le_div_of_nonneg_right hnum hm_den_pos.le).trans
                (div_le_div_of_nonneg_left (by positivity) hm0 hm_den_ge)
        _ = (C / 2) / Real.sqrt m := by
              calc ((C / 2) * Real.sqrt m) / (m : ℝ)
                  = ((C / 2) * Real.sqrt m) / (Real.sqrt m * Real.sqrt m) := by
                      rw [Real.mul_self_sqrt hm0.le]
                _ = (C / 2) / Real.sqrt m := by field_simp [(Real.sqrt_pos.mpr hm0).ne']
        _ ≤ C / Real.sqrt ((2 * n + 1 : ℕ) : ℝ) := by
              have hrt : Real.sqrt ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt m := by
                have : Real.sqrt ((2 * n + 1 : ℕ) : ℝ) ≤ Real.sqrt (2 * (m : ℝ)) :=
                  Real.sqrt_le_sqrt hd_le_2m
                rw [Real.sqrt_mul (by norm_num)] at this
                nlinarith [show Real.sqrt 2 ≤ 2 by rw [Real.sqrt_le_left (by norm_num)]; norm_num,
                  Real.sqrt_nonneg (m : ℝ)]
              rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hm0)
                (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (2 * n + 1 : ℕ)))]
              nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have h0_lim : Tendsto (fun d : ℕ => C / Real.sqrt d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop |>.congr fun d => by dsimp; rw [← Real.sqrt_eq_rpow])
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero, Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbd h0_lim

private lemma genD_rate_tendsto_kappaGauss {r : ℕ → ℝ} (hr_pos : ∀ᶠ d in atTop, 0 < r d)
    (hr_lim : Tendsto (fun d : ℕ => r d / (d : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun d : ℕ => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (genD d (r d)))
      atTop (𝓝 kappaGauss) := by
  have hlog_r : Tendsto (fun d : ℕ => Real.log (r d / (d : ℝ))) atTop (𝓝 0) := by
    have h0 := (Real.continuousAt_log one_ne_zero).tendsto.comp hr_lim
    rw [Real.log_one] at h0
    exact h0
  have hbase : Tendsto (fun d : ℕ => -(1 / (d : ℝ)) * Real.log (genD d (r d)))
      atTop (𝓝 (Real.log 2 - 1 / 2)) := by
    have hev : (fun d : ℕ => -(1 / (d : ℝ)) * Real.log (genD d (r d))) =ᶠ[atTop]
        fun d : ℕ =>
          ((1 / (d : ℝ)) * Real.log (Real.Gamma ((d : ℝ) / 2 + 1)) -
            (1 / 2) * (Real.log ((d : ℝ) / 2) - 1)) +
          (Real.log 2 - 1 / 2) - (1 / 2) * Real.log (r d / (d : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1, hr_pos] with d hd1 hrd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd1
      have hG_pos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
      have hr8 : 0 < r d / 8 := div_pos hrd (by norm_num)
      have hrd_pos : 0 < r d / (d : ℝ) := div_pos hrd hd0
      unfold genD
      rw [Real.log_div (Real.rpow_pos_of_pos hr8 _).ne' hG_pos.ne', Real.log_rpow hr8,
        show r d / 8 = (r d / (d : ℝ)) * ((d : ℝ) / 2) / 4 by field_simp [hd0.ne']; ring,
        Real.log_div (mul_pos hrd_pos (by positivity)).ne' (by norm_num),
        Real.log_mul hrd_pos.ne' (by positivity), Real.log_four_eq]
      field_simp [hd0.ne']; ring
    refine Tendsto.congr' hev.symm ?_
    simpa using (log_gamma_half_asymptotic.add tendsto_const_nhds).sub (tendsto_const_nhds.mul hlog_r)
  have hdiv : kappaGauss = (Real.log 2 - 1 / 2) / Real.log 2 := by
    unfold kappaGauss; field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hdiv]
  refine (hbase.div_const (Real.log 2)).congr fun d => by ring

/-- **Theorem E.3a (`thm:ce-laguerre-limit`, `(eq:finite:E.5d)`).** -/
theorem ce_laguerre_limit (K : ℕ → ℕ) (t r : ℕ → ℝ) (P : ℕ → ℝ[X])
    (hK_ge : ∀ᶠ d in atTop, 1 ≤ K d)
    (hK_sub : Tendsto (fun d : ℕ => (K d : ℝ) / (d : ℝ)) atTop (𝓝 0))
    (ht_pos : ∀ᶠ d in atTop, 0 < t d)
    (hP_deg : ∀ᶠ d in atTop, (P d).natDegree ≤ K d)
    (hf_nonneg : ∀ᶠ d in atTop, ∀ y : Euc d,
      (𝓕 (fun x : Euc d => (((P d).eval (‖x‖ ^ 2) * Real.exp (-π * t d * ‖x‖ ^ 2) : ℝ) : ℂ)) y).im = 0 ∧
      0 ≤ (𝓕 (fun x : Euc d => (((P d).eval (‖x‖ ^ 2) * Real.exp (-π * t d * ‖x‖ ^ 2) : ℝ) : ℂ)) y).re)
    (h0 : ∀ᶠ d in atTop, 0 < (P d).eval 0)
    (hf0 : ∀ᶠ d in atTop,
      0 < (𝓕 (fun x : Euc d => (((P d).eval (‖x‖ ^ 2) * Real.exp (-π * t d * ‖x‖ ^ 2) : ℝ) : ℂ)) 0).re)
    (h_nonpos : ∀ᶠ d in atTop, ∀ x : Euc d, r d ≤ ‖x‖ →
      (P d).eval (‖x‖ ^ 2) * Real.exp (-π * t d * ‖x‖ ^ 2) ≤ 0) :
    let rate : ℕ → ℝ := fun d =>
      -(1 / ((d : ℝ) * Real.log 2)) *
        Real.log (cohnElkiesBound d (r d) (fun x : Euc d =>
          (P d).eval (‖x‖ ^ 2) * Real.exp (-π * t d * ‖x‖ ^ 2)))
    Filter.limsup (fun d => ((rate d : ℝ) : EReal)) atTop ≤ (kappaGauss : EReal) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ d in atTop, rate d ≤ kappaGauss + ε) ∧
      (atTop.IsCoboundedUnder (· ≤ ·) rate → Filter.limsup rate atTop ≤ kappaGauss) := by
  intro rate
  let m₁ : ℕ → ℕ := fun d => K d / 2
  let r_eff : ℕ → ℝ := fun d =>
    (d : ℝ) - 2 * Real.sqrt (2 * (m₁ d : ℝ) * ((d : ℝ) + 2 * (m₁ d : ℝ) - 2))
  let lb : ℕ → ℝ := fun d => (laguerreBinom (m₁ d) ((d : ℝ) / 2))⁻¹ * genD d (r_eff d)
  let lb_rate : ℕ → ℝ := fun d => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (lb d)
  have hm_sub : Tendsto (fun d : ℕ => (m₁ d : ℝ) / (d : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hK_sub
    filter_upwards [eventually_ge_atTop 1] with d _
    have : (m₁ d : ℝ) ≤ K d := by exact_mod_cast Nat.div_le_self (K d) 2
    gcongr
  have hr_eff_lim : Tendsto (fun d : ℕ => r_eff d / (d : ℝ)) atTop (𝓝 1) := by
    have h_zero : Tendsto (fun d : ℕ => 2 * Real.sqrt (2 * ((m₁ d : ℝ) / d) *
        (1 + 2 * ((m₁ d : ℝ) / d) - 2 / d))) atTop (𝓝 0) := by
      have h2d : Tendsto (fun d : ℕ => (2 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hinner : Tendsto (fun d : ℕ => 2 * ((m₁ d : ℝ) / d) *
          (1 + 2 * ((m₁ d : ℝ) / d) - 2 / d)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hm_sub).mul
          (((tendsto_const_nhds.add (tendsto_const_nhds.mul hm_sub)).sub h2d))
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hinner
      rw [Real.sqrt_zero] at hsqrt
      simpa using tendsto_const_nhds.mul hsqrt
    have hev : (fun d : ℕ => r_eff d / (d : ℝ)) =ᶠ[atTop]
        fun d : ℕ => 1 - 2 * Real.sqrt (2 * ((m₁ d : ℝ) / d) * (1 + 2 * ((m₁ d : ℝ) / d) - 2 / d)) := by
      filter_upwards [eventually_ge_atTop 2] with d hd2
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      dsimp [r_eff]
      rw [sub_div, div_self hd_pos.ne']
      congr 2
      have hd2r : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      have hm0 : (0 : ℝ) ≤ m₁ d := Nat.cast_nonneg _
      have hrad_nn : 0 ≤ 2 * (m₁ d : ℝ) * ((d : ℝ) + 2 * (m₁ d : ℝ) - 2) := by nlinarith
      calc 2 * Real.sqrt (2 * (m₁ d : ℝ) * ((d : ℝ) + 2 * (m₁ d : ℝ) - 2)) / (d : ℝ)
          = 2 * (Real.sqrt (2 * (m₁ d : ℝ) * ((d : ℝ) + 2 * (m₁ d : ℝ) - 2)) /
              Real.sqrt ((d : ℝ) ^ 2)) := by rw [Real.sqrt_sq hd_pos.le]; ring
        _ = 2 * Real.sqrt (2 * (m₁ d : ℝ) * ((d : ℝ) + 2 * (m₁ d : ℝ) - 2) / (d : ℝ) ^ 2) := by
              rw [← Real.sqrt_div hrad_nn]
        _ = 2 * Real.sqrt (2 * ((m₁ d : ℝ) / d) * (1 + 2 * ((m₁ d : ℝ) / d) - 2 / d)) := by
              congr 2; field_simp [hd_pos.ne']
    refine Tendsto.congr' hev.symm ?_
    simpa using tendsto_const_nhds.sub h_zero
  have hr_eff_pos : ∀ᶠ d in atTop, 0 < r_eff d := by
    filter_upwards [eventually_ge_atTop 1, hr_eff_lim (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with d hd1 hhalf
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd1
    have hhalf' : (1 / 2 : ℝ) < r_eff d / (d : ℝ) := hhalf
    have : 0 < r_eff d / (d : ℝ) := by linarith
    exact (div_pos_iff_of_pos_right hd_pos).mp this
  have hK5 : ∀ᶠ d in atTop, 5 * K d < d := by
    filter_upwards [eventually_ge_atTop 1, hK_sub (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 5))] with d hd1 hlt
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd1
    have hlt1 : (K d : ℝ) / (d : ℝ) < 1 / 5 := hlt
    have hlt' : 5 * (K d : ℝ) < d := by rw [div_lt_iff₀ hd_pos] at hlt1; linarith
    exact_mod_cast hlt'
  have hle_ev : ∀ᶠ d in atTop, rate d ≤ lb_rate d := by
    filter_upwards [eventually_ge_atTop 2, hK_ge, ht_pos, hP_deg, hf_nonneg, h0, hf0, h_nonpos, hK5, hr_eff_pos] with
      d hd2 hKd htd hPd hfnn h0d hf0d hnpd hk5d hrp
    have hcond := ce_laguerre_cond_sufficient hd2 hKd (Or.inr hk5d)
    have hfin := ce_laguerre_finite_lower_bound hd2 hKd htd hPd hfnn h0d hf0d hnpd hcond
    have hlb_eq : lb d = (laguerreBinom (K d / 2) ((d : ℝ) / 2))⁻¹ * (Real.Gamma ((d : ℝ) / 2 + 1))⁻¹ *
        (((d : ℝ) - 2 * Real.sqrt (2 * (K d / 2 : ℕ) * ((d : ℝ) + 2 * (K d / 2 : ℕ) - 2))) / 8) ^
          ((d : ℝ) / 2) := by
      dsimp [lb, genD, m₁, r_eff]; ring
    have hlb_pos : 0 < lb d := by
      dsimp [lb, genD]
      have hbp := laguerreBinom_pos (c := (d : ℝ) / 2) (by positivity) (m₁ d)
      have hgp := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)
      exact mul_pos (inv_pos.mpr hbp) (div_pos (Real.rpow_pos_of_pos (div_pos hrp (by norm_num)) _) hgp)
    rw [← hlb_eq] at hfin
    have hlog_le := Real.log_le_log hlb_pos hfin
    dsimp [rate, lb_rate]
    have hcoeff : 0 ≤ 1 / ((d : ℝ) * Real.log 2) :=
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le)
    nlinarith [mul_le_mul_of_nonneg_left hlog_le hcoeff]
  have hlb_lim : Tendsto lb_rate atTop (𝓝 kappaGauss) := by
    have hgen := genD_rate_tendsto_kappaGauss hr_eff_pos hr_eff_lim
    have hbin := laguerreBinom_sublinear_rate_tendsto_zero hm_sub
    have hev : lb_rate =ᶠ[atTop] fun d : ℕ =>
        -(1 / ((d : ℝ) * Real.log 2)) * Real.log (genD d (r_eff d)) +
          (1 / Real.log 2) * ((1 / (d : ℝ)) * Real.log (laguerreBinom (m₁ d) ((d : ℝ) / 2))) := by
      filter_upwards [eventually_ge_atTop 1, hr_eff_pos] with d hd1 hrp
      have hbp : 0 < laguerreBinom (m₁ d) ((d : ℝ) / 2) := laguerreBinom_pos (by positivity) (m₁ d)
      have hgp : 0 < genD d (r_eff d) := by
        unfold genD; have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1); positivity
      dsimp [lb_rate, lb]
      rw [Real.log_mul (inv_ne_zero hbp.ne') hgp.ne', Real.log_inv]
      ring
    refine Tendsto.congr' hev.symm ?_
    simpa using hgen.add (tendsto_const_nhds.mul hbin)
  have h_eps : ∀ ε : ℝ, 0 < ε → ∀ᶠ d in atTop, rate d ≤ kappaGauss + ε := by
    intro ε hε
    filter_upwards [hle_ev, hlb_lim (gt_mem_nhds (by linarith : kappaGauss < kappaGauss + ε))] with d hle hlt
    exact hle.trans hlt.le
  have h_ereal : Filter.limsup (fun d => ((rate d : ℝ) : EReal)) atTop ≤ (kappaGauss : EReal) := by
    calc Filter.limsup (fun d => ((rate d : ℝ) : EReal)) atTop
        ≤ Filter.limsup (fun d => ((lb_rate d : ℝ) : EReal)) atTop := by
            refine Filter.limsup_le_limsup ?_
            filter_upwards [hle_ev] with d hd; exact EReal.coe_le_coe_iff.mpr hd
      _ = (kappaGauss : EReal) := (EReal.tendsto_coe.mpr hlb_lim).limsup_eq
  refine ⟨h_ereal, h_eps, fun hcb => ?_⟩
  exact (Filter.limsup_le_limsup hle_ev hcb hlb_lim.isBoundedUnder_le).trans_eq hlb_lim.limsup_eq

/-- Equality in `(eq:finite:E.5d)` is already attained at `K = 1` (`quadD`) and `K = 3` (`cubicD`). -/
theorem ce_laguerre_equality_quad_cubic :
    (∀ d ≥ 2, cohnElkiesBound d (quadR d) (quadH d) = quadD d) ∧
    (∀ d ≥ 1, cohnElkiesBound d (cubicR d) (cubicH d) = cubicD d) ∧
    Tendsto (fun d : ℕ => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (quadD d)) atTop (𝓝 kappaGauss) ∧
    Tendsto (fun d : ℕ => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (cubicD d)) atTop (𝓝 kappaGauss) := by
  refine ⟨fun d hd => quadH_bound_eq_quadD hd, fun d hd => ?_, ?_, ?_⟩
  · have hu : 0 < cubicU d := by
      unfold cubicU; have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
      exact div_pos (by linarith) (by positivity)
    exact cubicH_bound_eq hd hu
  · have hr_pos : ∀ᶠ d : ℕ in atTop, 0 < (d : ℝ) + 2 := by
      filter_upwards [eventually_ge_atTop 1] with d hd; positivity
    have hr_lim : Tendsto (fun d : ℕ => ((d : ℝ) + 2) / (d : ℝ)) atTop (𝓝 1) := by
      have hev : (fun d : ℕ => ((d : ℝ) + 2) / (d : ℝ)) =ᶠ[atTop] fun d : ℕ => 1 + 2 / (d : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with d hd
        field_simp [(Nat.cast_pos.mpr hd).ne']
      have h2d : Tendsto (fun d : ℕ => (2 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      exact Tendsto.congr' hev.symm (by simpa using tendsto_const_nhds.add h2d)
    have hgen := genD_rate_tendsto_kappaGauss hr_pos hr_lim
    have hlog_pref : Tendsto (fun d : ℕ =>
        -(1 / ((d : ℝ) * Real.log 2)) * Real.log (((d : ℝ) + 2) / 2)) atTop (𝓝 0) := by
      have hev : ∀ᶠ d : ℕ in atTop,
          |-(1 / ((d : ℝ) * Real.log 2)) * Real.log (((d : ℝ) + 2) / 2)| ≤
            (2 / Real.log 2) / Real.sqrt d := by
        filter_upwards [eventually_ge_atTop 2] with d hd2
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
        have hd2r : (2 : ℝ) ≤ d := by exact_mod_cast hd2
        have hd_half : (1 : ℝ) ≤ ((d : ℝ) + 2) / 2 := by linarith
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / ((d : ℝ) * Real.log 2)),
          abs_of_nonneg (Real.log_nonneg hd_half)]
        have hl : Real.log (((d : ℝ) + 2) / 2) ≤ 2 * Real.sqrt d := by
          refine (real_log_le_two_sqrt (by positivity)).trans ?_
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
        calc (1 / ((d : ℝ) * Real.log 2)) * Real.log (((d : ℝ) + 2) / 2)
            ≤ (1 / ((d : ℝ) * Real.log 2)) * (2 * Real.sqrt d) :=
                mul_le_mul_of_nonneg_left hl (by positivity)
          _ = (2 / Real.log 2) / Real.sqrt d := by
                calc (1 / ((d : ℝ) * Real.log 2)) * (2 * Real.sqrt d)
                    = (1 / ((Real.sqrt d * Real.sqrt d) * Real.log 2)) * (2 * Real.sqrt d) := by
                        rw [Real.mul_self_sqrt hd_pos.le]
                  _ = (2 / Real.log 2) / Real.sqrt d := by
                        field_simp [(Real.sqrt_pos.mpr hd_pos).ne', hl2.ne']
      have h0 : Tendsto (fun d : ℕ => (2 / Real.log 2) / Real.sqrt d) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          tendsto_natCast_atTop_atTop |>.congr fun d => by dsimp; rw [← Real.sqrt_eq_rpow])
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero, Real.norm_eq_abs]
      exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hev h0
    have hev : (fun d : ℕ => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (quadD d)) =ᶠ[atTop]
        fun d : ℕ => -(1 / ((d : ℝ) * Real.log 2)) * Real.log (genD d ((d : ℝ) + 2)) +
          -(1 / ((d : ℝ) * Real.log 2)) * Real.log (((d : ℝ) + 2) / 2) := by
      filter_upwards [eventually_ge_atTop 2] with d hd2
      have hq_eq : quadD d = (((d : ℝ) + 2) / 2) * genD d ((d : ℝ) + 2) := by
        unfold quadD genD; ring
      have hgp : 0 < genD d ((d : ℝ) + 2) := by
        unfold genD; have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1); positivity
      rw [hq_eq, Real.log_mul (by positivity) hgp.ne']; ring
    exact Tendsto.congr' hev.symm (by simpa using hgen.add hlog_pref)
  · have hr_pos : ∀ᶠ d : ℕ in atTop, 0 < cubicU d := by
      filter_upwards [eventually_ge_atTop 1] with d _; unfold cubicU
      have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
      exact div_pos (by linarith) (by positivity)
    have hr_lim : Tendsto (fun d : ℕ => cubicU d / (d : ℝ)) atTop (𝓝 1) := by
      have hev : (fun d : ℕ => cubicU d / (d : ℝ)) =ᶠ[atTop]
          fun d : ℕ => 1 + 6 / (d : ℝ) - 2 / ((d : ℝ) * ((d : ℝ) + 6)) := by
        filter_upwards [eventually_ge_atTop 1] with d hd1
        unfold cubicU; field_simp [(Nat.cast_pos.mpr hd1).ne', (by positivity : (d : ℝ) + 6 ≠ 0)]
      have h6 : Tendsto (fun d : ℕ => (6 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun d : ℕ => (2 : ℝ) / ((d : ℝ) * ((d : ℝ) + 6))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      exact Tendsto.congr' hev.symm (by simpa using (tendsto_const_nhds.add h6).sub h2)
    simpa [cubicD] using genD_rate_tendsto_kappaGauss hr_pos hr_lim


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.ce_laguerre_finite_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_laguerre_finite_lower_bound

/-- info: 'FormalResearch.CohnElkies.ce_laguerre_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_laguerre_limit

/-- info: 'FormalResearch.CohnElkies.ce_laguerre_equality_quad_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_laguerre_equality_quad_cubic

end FormalResearch.CohnElkies
