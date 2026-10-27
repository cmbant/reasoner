import FormalResearch.FrameFree.Unify
import FormalResearch.FrameFree.MaxChiral
import FormalResearch.FrameFree.PlanarSign
import FormalResearch.FourQubitEntropy.ClassifyMain

/-!
# The critical locus: equality in maximal chirality (Paper P, `app_c_critical.tex`)

Namespace `FormalResearch.FrameFree.CriticalLocus`.  Everything is **proved** (no hypothesis beyond those
displayed).  A *critical* four-qubit state is one with all one-qubit marginals maximally mixed; up to local
unitaries it is a magic-diagonal state `ψ_q = psiMag q` (the reduction is not formalised here), and
`blochSq_psiMag` shows that every magic-diagonal state is critical.

* `equality_moduli` (`thm:maxchiral`, equality case, magic-diagonal side).  For unit `q`, if the Weyl-vertex
  value meets the refined bound, `FKmag q ≤ 4/9 + |qᵀq|²/18`, then `qᵀq = 0` and every `|q_k|²` is `1/6` or
  `1/2`.  The proof follows the paper: for each of the three long bases the planar sign inequality must be an
  equality for `v_i = (u_i·q)²` (`balance`, from `design_identity`, `planar_sign4` and
  `sign_sum_le_FKmag`); the equality case of `PlanarSign.lean` leaves a regular hexagon (`hexagon`: one
  line orthogonal to `q`, three lines of weight `1/3`, `qᵀq = 0`), because the square is impossible
  (`real_pairs`: `|qᵀq| = ‖q‖²` forces `q` to be a phase times a real vector, for which all `v_i` are
  parallel); two bases then pin the moduli (`hex_moduli`).
* `maxchiral_equality` (`thm:maxchiral`, "only if", physical form).  If `F_K(ψ_q, ψ̄_q) ≤ 4/9`
  (`rotOverlap`, the quantity of `PhysicalBridge.lean`; here only the easy inequality
  `FKmag ≤ F_K` is needed, not the recalled input R7), then `ψ_q` is locally unitarily equivalent to `M₄` or
  `conj M₄` (`LUEquiv`), by Paper E's `FourQubitEntropy.classify`.
  `maxchiral_equality_refined`: the same with `F_K ≤ 4/9 + |qᵀq|²/18`.
  `maxchiral_equality_NQubit`: the `NQubit.FKΘ` form.

* `plane_formula` (`thm:planeformula`, bipartite part).  For `x, y ∈ ℂ^m ⊗ H` (written as families of `m`
  vectors of a finite-dimensional Hilbert space `H`, so `ρ_x = ∑_a |x_a⟩⟨x_a| = Tr_A |x⟩⟨x|` and
  `S_y = span y_c = supp Tr_A |y⟩⟨y|`) and a linear map `T` (the filter `h`),
  `sup_{g ∈ GL_m, (g⊗T)y ≠ 0} |⟨x,(g⊗T)y⟩|²/‖(g⊗T)y‖² = Tr(ρ_x P_{T S_y}) = ∑_a ‖P_{T S_y} x_a‖²`
  (`plane_upper`: Cauchy-Schwarz; `plane_approach`: the maximiser `g₀ y = P x` is approximated by the
  invertible `g₀ + t·1`, using finiteness of the spectrum).
* `helstrom_arith`, `branch_converse_arith`: only the real-arithmetic skeleton of `c-lem-branch`.

Not formalised from `app_c_critical.tex` (see the report): the analytic core of `c-lem-branch` (symmetric
subspace, twirl, integral over the Bloch sphere), the `n`-qubit consequence of the plane formula
(`F_C(ψ) = sup_h Tr(ρ' P_{h S̄})`, needs `SL` versus `GL` filters and `Θ` versus conjugation), the support
ceiling (`thm:ceiling` is in `Ceilings.lean`), the converse "LU-equivalent to `M₄` ⟹ `F_K = 4/9`" (needs R7)
and the reduction "critical ⟹ LU-equivalent to a magic-diagonal state".
-/

open scoped ComplexConjugate Matrix BigOperators
open FormalResearch.FourQubitEntropy
open Finset

namespace FormalResearch.FrameFree.CriticalLocus


theorem psiMag_apply (q : Fin 4 → ℂ) (a b c e : Fin 2) :
    psiMag q a b c e = ∑ x, magicB (a, b) x * q (pairEquiv x) * magicB (c, e) x := by
  unfold psiMag; exact psiMagP_apply _ a b c e

theorem pe00 : pairEquiv (0, 0) = 0 := by decide
theorem pe01 : pairEquiv (0, 1) = 1 := by decide
theorem pe10 : pairEquiv (1, 0) = 2 := by decide
theorem pe11 : pairEquiv (1, 1) = 3 := by decide

theorem rt_sq : rt * rt = 1 / 2 := rt_mul_rt

/-- The sixteen entries of a magic-diagonal state. -/
theorem psiMag_entry (q : Fin 4 → ℂ) (a b c e : Fin 2) :
    psiMag q a b c e =
      if a = b ∧ c = e then (if a = c then (q 0 - q 3) / 2 else (q 0 + q 3) / 2)
      else if a ≠ b ∧ c ≠ e then (if a = c then (q 2 - q 1) / 2 else -(q 1 + q 2) / 2)
      else 0 := by
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [psiMag_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, magicB, pe00, pe01, pe10, pe11] <;>
    (ring_nf; simp only [hI, hrt2]; ring)
  

theorem expectation_psiMag (q : Fin 4 → ℂ) (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ = pauliX ∨ σ = pauliY ∨ σ = pauliZ) : expectation i σ (psiMag q) = 0 := by
  rcases hσ with rfl | rfl | rfl <;> fin_cases i <;>
  · simp [expectation, actOn, Fin.sum_univ_two, psiMag_entry, pauliX, pauliY, pauliZ] <;> ring_nf

theorem blochSq_psiMag (q : Fin 4 → ℂ) : blochSq (psiMag q) = 0 := by
  unfold blochSq
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [expectation_psiMag q i _ (Or.inl rfl), expectation_psiMag q i _ (Or.inr (Or.inl rfl)),
    expectation_psiMag q i _ (Or.inr (Or.inr rfl))]
  simp



/-- Parallelogram identity. -/
theorem normSq_add_add_sub (x y : ℂ) :
    Complex.normSq (x + y) + Complex.normSq (x - y) = 2 * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Four-case lemma for one pairing: the vanishing line lies in one pair, whose two moduli are
`1/6`, and the other pair has total weight `2/3`. -/
theorem hex_moduli (x1 x2 x3 x4 : ℂ) (c : Fin 4 → ℂ) (hc0 : c 0 = x1 + x2) (hc1 : c 1 = x1 - x2)
    (hc2 : c 2 = x3 + x4) (hc3 : c 3 = x3 - x4) (l : Fin 4)
    (h0 : c l = 0) (h1 : ∀ i, i ≠ l → Complex.normSq (c i) = 2 / 3) :
    (Complex.normSq x1 = 1 / 6 ∧ Complex.normSq x2 = 1 / 6 ∧ Complex.normSq x3 + Complex.normSq x4 = 2 / 3) ∨
    (Complex.normSq x3 = 1 / 6 ∧ Complex.normSq x4 = 1 / 6 ∧ Complex.normSq x1 + Complex.normSq x2 = 2 / 3) := by
  have p12 := normSq_add_add_sub x1 x2
  have p34 := normSq_add_add_sub x3 x4
  have c0 := h1 0
  have c1 := h1 1
  have c2 := h1 2
  have c3 := h1 3
  rw [hc0] at c0
  rw [hc1] at c1
  rw [hc2] at c2
  rw [hc3] at c3
  have hl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hl with rfl | rfl | rfl | rfl
  · rw [hc0] at h0
    left
    have z : Complex.normSq (x1 + x2) = 0 := by rw [h0]; simp
    have e : Complex.normSq x2 = Complex.normSq x1 := by
      have : x2 = -x1 := by linear_combination h0
      rw [this]; simp
    have b1 := c1 (by decide)
    have b2 := c2 (by decide)
    have b3 := c3 (by decide)
    refine ⟨by linarith, by linarith, by linarith⟩
  · rw [hc1] at h0
    left
    have z : Complex.normSq (x1 - x2) = 0 := by rw [h0]; simp
    have e : Complex.normSq x2 = Complex.normSq x1 := by
      have : x2 = x1 := by linear_combination -h0
      rw [this]
    have b1 := c0 (by decide)
    have b2 := c2 (by decide)
    have b3 := c3 (by decide)
    refine ⟨by linarith, by linarith, by linarith⟩
  · rw [hc2] at h0
    right
    have z : Complex.normSq (x3 + x4) = 0 := by rw [h0]; simp
    have e : Complex.normSq x4 = Complex.normSq x3 := by
      have : x4 = -x3 := by linear_combination h0
      rw [this]; simp
    have b1 := c0 (by decide)
    have b2 := c1 (by decide)
    have b3 := c3 (by decide)
    refine ⟨by linarith, by linarith, by linarith⟩
  · rw [hc3] at h0
    right
    have z : Complex.normSq (x3 - x4) = 0 := by rw [h0]; simp
    have e : Complex.normSq x4 = Complex.normSq x3 := by
      have : x4 = x3 := by linear_combination -h0
      rw [this]
    have b1 := c0 (by decide)
    have b2 := c1 (by decide)
    have b3 := c2 (by decide)
    refine ⟨by linarith, by linarith, by linarith⟩

/-- Every signed sum of the long-basis products `v_i = (u_i·q)²` is at most `F_K`. -/
theorem sign_sum_le_FKmag (q : Fin 4 → ℂ) (P : Fin 3) (s : Fin 4 → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : ‖∑ i, (s i : ℂ) * vP P q q i‖ ^ 2 ≤ FKmag q := by
  have hb : ∀ i, s i = sgn (decide (s i = -1)) := by
    intro i
    rcases hs i with h | h
    · rw [h]; simp [sgn]
    · rw [h]; simp [sgn]
  have hmem := longW_mem P (decide (s 0 = -1)) (decide (s 1 = -1)) (decide (s 2 = -1))
    (decide (s 3 = -1))
  have := le_FKmag q hmem
  rw [weylVal_eq_bil, bil_longW, ← norm_sq_eq_normSq] at this
  have hsumv : ∑ i, (s i : ℂ) * vP P q q i =
      (sgn (decide (s 0 = -1)) : ℂ) * vP P q q 0 + (sgn (decide (s 1 = -1)) : ℂ) * vP P q q 1 +
      (sgn (decide (s 2 = -1)) : ℂ) * vP P q q 2 + (sgn (decide (s 3 = -1)) : ℂ) * vP P q q 3 := by
    rw [Fin.sum_univ_four, ← hb 0, ← hb 1, ← hb 2, ← hb 3]
  rw [hsumv]; exact this

theorem hdot_self (q : Fin 4 → ℂ) : hdot q q = (nrm2 q : ℂ) := by
  unfold hdot nrm2
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]


/-- Equality forces equality in the planar sign inequality for every long basis. -/
theorem balance (q : Fin 4 → ℂ) (hq : nrm2 q = 1)
    (hE : FKmag q ≤ 4 / 9 + Complex.normSq (bdot q q) / 18) (P : Fin 3) :
    (∑ i, ‖vP P q q i‖) ^ 2 = 1 ∧ ∑ i, ‖vP P q q i‖ ^ 2 = 1 / 3 + Complex.normSq (bdot q q) / 6 ∧
    ∀ s : Fin 4 → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      ‖∑ i, (s i : ℂ) * vP P q q i‖ ^ 2 ≤
        (1 / 3) * ((∑ i, ‖vP P q q i‖) ^ 2 + ∑ i, ‖vP P q q i‖ ^ 2) := by
  set b := Complex.normSq (bdot q q) with hb
  set L : Fin 3 → ℝ := fun P => ∑ i, ‖vP P q q i‖ with hLdef
  set S : Fin 3 → ℝ := fun P => ∑ i, ‖vP P q q i‖ ^ 2 with hSdef
  have hL1 : ∀ P, 1 ≤ L P := by
    intro P
    have h1 := norm_hdot_le P q q
    rw [hdot_self, hq] at h1
    simpa using h1
  have hSsum : ∑ P, S P = 1 + b / 2 := by
    have h1 := sum_vP_sq q q
    have h2 := design_identity q q
    have h3 : Complex.normSq (hdot q q) = 1 := by rw [hdot_self, hq]; simp
    rw [h3, hq] at h2
    have h4 : ∑ P, S P = ∑ P, ∑ i, Complex.normSq (vP P q q i) :=
      Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun i _ => norm_sq_eq_normSq _
    rw [h4, h1, h2]; ring
  have hPS : ∀ P, (1 / 3 : ℝ) * (L P ^ 2 + S P) ≤ 4 / 9 + b / 18 := by
    intro P
    obtain ⟨s, hs, hineq⟩ := planar_sign4 (vP P q q)
    have := sign_sum_le_FKmag q P (fun i => s i) hs
    have h5 : ‖∑ i, (s i : ℂ) * vP P q q i‖ ^ 2 ≤ 4 / 9 + b / 18 := this.trans hE
    simp only [hLdef, hSdef]
    linarith [hineq, h5]
  have h0 := hPS 0
  have h1 := hPS 1
  have h2 := hPS 2
  have l0 := hL1 0
  have l1 := hL1 1
  have l2 := hL1 2
  rw [Fin.sum_univ_three] at hSsum
  have hL0 : L 0 ^ 2 = 1 := by nlinarith
  have hL1' : L 1 ^ 2 = 1 := by nlinarith
  have hL2 : L 2 ^ 2 = 1 := by nlinarith
  have hS0 : S 0 = 1 / 3 + b / 6 := by nlinarith
  have hS1 : S 1 = 1 / 3 + b / 6 := by nlinarith
  have hS2 : S 2 = 1 / 3 + b / 6 := by nlinarith
  have key : ∀ P, L P ^ 2 = 1 ∧ S P = 1 / 3 + b / 6 := by
    intro P; fin_cases P
    · exact ⟨hL0, hS0⟩
    · exact ⟨hL1', hS1⟩
    · exact ⟨hL2, hS2⟩
  refine ⟨(key P).1, (key P).2, fun s hs => ?_⟩
  have h5 := sign_sum_le_FKmag q P s hs
  have h6 : (1 / 3 : ℝ) * ((∑ i, ‖vP P q q i‖) ^ 2 + ∑ i, ‖vP P q q i‖ ^ 2) = 4 / 9 + b / 18 := by
    have := key P
    simp only [hLdef, hSdef] at this
    rw [this.1, this.2]; ring
  rw [h6]; exact h5.trans hE


theorem normSq_sum_eq (z : Fin 4 → ℂ) :
    Complex.normSq (∑ x, z x) = ∑ x, ∑ y, (z x * conj (z y)).re := by
  have hn : Complex.normSq (∑ x, z x) = (conj (∑ x, z x) * ∑ x, z x).re := by
    have := Complex.normSq_eq_conj_mul_self (z := ∑ x, z x)
    have h2 := congrArg Complex.re this
    simpa using h2
  rw [hn]
  have : conj (∑ x, z x) * ∑ x, z x = ∑ y, ∑ x, z x * conj (z y) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [this]
  have h2 : (∑ y, ∑ x, z x * conj (z y)).re = ∑ y, ∑ x, (z x * conj (z y)).re := by
    simp [Complex.re_sum]
  rw [h2, Finset.sum_comm]

/-- If `|qᵀq| = ‖q‖² = 1` then all products `q_x conj q_y` are real (`q` is a phase times a real vector). -/
theorem real_pairs (q : Fin 4 → ℂ) (hq : nrm2 q = 1) (hb : Complex.normSq (bdot q q) = 1) :
    ∀ x y, (q x * conj (q y)).im = 0 := by
  set z : Fin 4 → ℂ := fun k => q k * q k with hz
  have hsum : Complex.normSq (∑ k, z k) = 1 := by simpa [hz, bdot] using hb
  have hnorm : ∑ k, ‖z k‖ = 1 := by
    rw [← hq]; unfold nrm2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hz, Complex.normSq_eq_norm_sq, sq]
  have h1 : (∑ k, ‖z k‖) ^ 2 = ∑ x, ∑ y, ‖z x‖ * ‖z y‖ := by
    rw [sq, Finset.sum_mul_sum]
  have h2 := normSq_sum_eq z
  have hle : ∀ x y, (z x * conj (z y)).re ≤ ‖z x‖ * ‖z y‖ := by
    intro x y
    calc (z x * conj (z y)).re ≤ ‖z x * conj (z y)‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj]
  have hsumeq : ∑ x, ∑ y, (‖z x‖ * ‖z y‖ - (z x * conj (z y)).re) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [← h1, ← h2, hnorm, hsum]; norm_num
  have hx : ∀ x ∈ (Finset.univ : Finset (Fin 4)), ∑ y, (‖z x‖ * ‖z y‖ - (z x * conj (z y)).re) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg fun y _ => ?_)).1 hsumeq
    linarith [hle x y]
  intro x y
  have hxy := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by linarith [hle x y])).1 (hx x (Finset.mem_univ x)) y
    (Finset.mem_univ y)
  have hre : (z x * conj (z y)).re = ‖z x * conj (z y)‖ := by
    rw [norm_mul, Complex.norm_conj]; linarith
  -- `w = z_x conj z_y` is a nonnegative real
  set w := z x * conj (z y) with hw
  have him : w.im = 0 := by
    have h := Complex.sq_norm w
    have : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by simp [Complex.normSq_apply]; ring
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← hre] at this
    nlinarith [sq_nonneg w.im]
  have hr : (q x * conj (q y)) ^ 2 = w := by
    simp only [hw, hz, map_mul]; ring
  set r := q x * conj (q y) with hrdef
  have e1 : (r ^ 2).re = r.re ^ 2 - r.im ^ 2 := by simp [sq]
  have e2 : (r ^ 2).im = 2 * r.re * r.im := by simp [sq]; ring
  rw [hr] at e1 e2
  have hge : 0 ≤ w.re := by rw [hre]; exact norm_nonneg _
  have : r.re * r.im = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · rw [h] at e1; nlinarith [sq_nonneg r.im]
  · exact h


theorem cx_conj_real (q : Fin 4 → ℂ) (h : ∀ x y, (q x * conj (q y)).im = 0) (P : Fin 3) (i j : Fin 4) :
    (cx P q i * conj (cx P q j)).im = 0 := by
  fin_cases P <;> fin_cases i <;> fin_cases j <;>
    simp [cx, pairing, mul_add, add_mul, mul_sub, sub_mul, Complex.add_im, Complex.sub_im, h]


theorem norm_vP (q : Fin 4 → ℂ) (P : Fin 3) (i : Fin 4) :
    ‖vP P q q i‖ = Complex.normSq (cx P q i) / 2 := by
  unfold vP
  rw [norm_div, norm_mul, Complex.normSq_eq_norm_sq]
  simp
  ring

theorem fin4_complement : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ ∀ m, m ≠ l → m = i ∨ m = j ∨ m = k := by decide

/-- Per-pairing consequence of equality: one of the four long lines is orthogonal to `q`, the other
three carry weight `1/3` each, and `qᵀq = 0`. -/
theorem hexagon (q : Fin 4 → ℂ) (hq : nrm2 q = 1) (P : Fin 3)
    (hL : (∑ i, ‖vP P q q i‖) ^ 2 = 1)
    (hS : ∑ i, ‖vP P q q i‖ ^ 2 = 1 / 3 + Complex.normSq (bdot q q) / 6)
    (hineq : ∀ s : Fin 4 → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      ‖∑ i, (s i : ℂ) * vP P q q i‖ ^ 2 ≤
        (1 / 3) * ((∑ i, ‖vP P q q i‖) ^ 2 + ∑ i, ‖vP P q q i‖ ^ 2)) :
    Complex.normSq (bdot q q) = 0 ∧
      ∃ l : Fin 4, cx P q l = 0 ∧ ∀ i, i ≠ l → Complex.normSq (cx P q i) = 2 / 3 := by
  have hL0 : 0 ≤ ∑ i, ‖vP P q q i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hL1 : ∑ i, ‖vP P q q i‖ = 1 := by nlinarith
  rcases (planar_sign4_equality_iff (vP P q q)).1 hineq with h | h | h
  · -- all vanish: impossible
    exfalso
    have : ∑ i, ‖vP P q q i‖ = 0 := Finset.sum_eq_zero fun i _ => by simp [h i]
    linarith
  · -- two perpendicular: forces `|qᵀq| = 1`, then `q` is a phase times a real vector
    exfalso
    obtain ⟨i, j, hij, h0, hi, hnorm, hre⟩ := h
    have hLs := sum_support2 (fun k => ‖vP P q q k‖) i j hij (fun k h1 h2 => by simp [h0 k h1 h2])
    have hSs := sum_support2 (fun k => ‖vP P q q k‖ ^ 2) i j hij
      (fun k h1 h2 => by simp [h0 k h1 h2])
    rw [hLs, ← hnorm] at hL1
    rw [hSs, ← hnorm] at hS
    have hb : Complex.normSq (bdot q q) = 1 := by nlinarith
    have hreal := real_pairs q hq hb
    have hw := cx_conj_real q hreal P i j
    set w := cx P q i * conj (cx P q j) with hw'
    have hvv : vP P q q i * conj (vP P q q j) = w ^ 2 / 4 := by
      simp only [vP, hw', map_div₀, map_mul]
      have : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
      rw [this]; ring
    rw [hvv] at hre
    have e1 : (w ^ 2 / 4).re = w.re ^ 2 / 4 := by
      simp [sq, hw]
    rw [e1] at hre
    have hwr : w.re = 0 := by nlinarith [sq_nonneg w.re]
    have hw0 : w = 0 := Complex.ext hwr hw
    have : cx P q i = 0 ∨ cx P q j = 0 := by
      rcases mul_eq_zero.1 hw0 with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using h)
    have hvi : vP P q q i ≠ 0 := hi
    have hvj : ‖vP P q q j‖ ≠ 0 := by rw [← hnorm]; exact norm_ne_zero_iff.2 hvi
    rcases this with h | h
    · exact hvi (by simp [vP, h])
    · exact hvj (by simp [vP, h])
  · obtain ⟨i, j, k, hij, hik, hjk, h0, hi, hnj, hnk, -, -, -⟩ := h
    have hLs := sum_support3 (fun m => ‖vP P q q m‖) i j k hij hik hjk
      (fun m h1 h2 h3 => by simp [h0 m h1 h2 h3])
    have hSs := sum_support3 (fun m => ‖vP P q q m‖ ^ 2) i j k hij hik hjk
      (fun m h1 h2 h3 => by simp [h0 m h1 h2 h3])
    rw [hLs, ← hnj, ← hnk] at hL1
    rw [hSs, ← hnj, ← hnk] at hS
    set a := ‖vP P q q i‖ with ha
    have ha3 : a = 1 / 3 := by linarith
    have hb0 : Complex.normSq (bdot q q) = 0 := by rw [ha3] at hS; nlinarith
    refine ⟨hb0, ?_⟩
    obtain ⟨l, hli, hlj, hlk, hcov⟩ := fin4_complement i j k hij hik hjk
    refine ⟨l, ?_, ?_⟩
    · have := h0 l hli hlj hlk
      simp only [vP] at this
      have h2 : cx P q l * cx P q l = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · norm_num at h
      exact mul_self_eq_zero.1 h2
    · intro m hm
      have hn : ‖vP P q q m‖ = 1 / 3 := by
        rcases hcov m hm with h | h | h
        · rw [h]; exact ha3
        · rw [h, ← hnj]; exact ha3
        · rw [h, ← hnk]; exact ha3
      rw [norm_vP] at hn
      linarith


/-- **Equality in `thm:maxchiral`, magic-diagonal form.** For a unit `q`, if `F_K` (Weyl-vertex value)
meets the refined bound `4/9 + |qᵀq|²/18`, then `qᵀq = 0` and every `|q_k|²` is `1/6` or `1/2`. -/
theorem equality_moduli (q : Fin 4 → ℂ) (hq : nrm2 q = 1)
    (hE : FKmag q ≤ 4 / 9 + Complex.normSq (bdot q q) / 18) :
    bdot q q = 0 ∧ ∀ k, Complex.normSq (q k) = 1 / 6 ∨ Complex.normSq (q k) = 1 / 2 := by
  have bal : ∀ P, _ := fun P => balance q hq hE P
  obtain ⟨hb0, l0, hl0, hn0⟩ := hexagon q hq 0 (bal 0).1 (bal 0).2.1 (bal 0).2.2
  obtain ⟨-, l1, hl1, hn1⟩ := hexagon q hq 1 (bal 1).1 (bal 1).2.1 (bal 1).2.2
  refine ⟨Complex.normSq_eq_zero.1 hb0, ?_⟩
  have A := hex_moduli (q 0) (q 1) (q 2) (q 3) (cx 0 q) rfl rfl rfl rfl l0 hl0 hn0
  have B := hex_moduli (q 0) (q 2) (q 1) (q 3) (cx 1 q) rfl rfl rfl rfl l1 hl1 hn1
  intro k
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
  rcases A with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;> rcases B with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;>
  first
    | (left; assumption)
    | (right; linarith)


/-! ### From the magic-diagonal statement to local-unitary equivalence -/

theorem zmat_psiMag (q : Fin 4 → ℂ) :
    zmat (psiMag q) = magicB * Matrix.diagonal (fun p : Pair => q (pairEquiv p)) * magicBᵀ := by
  unfold psiMag psiMagP; exact zmat_ofZmat _

theorem spinFlip_psiMag (q : Fin 4 → ℂ) : spinFlipForm (psiMag q) = bdot q q := by
  rw [spinFlip_coord, zmat_psiMag, coord_of_eq rfl]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  unfold bdot
  exact Equiv.sum_comp pairEquiv (fun k => q k * q k)

theorem red12_psiMag (q : Fin 4 → ℂ) :
    red12 (psiMag q) = magicB * Matrix.diagonal (fun p : Pair => conj (q (pairEquiv p)) * q (pairEquiv p)) *
      magicBᴴ := by
  rw [red12_zmat, zmat_psiMag, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    transpose_conjTranspose, Matrix.diagonal_conjTranspose]
  have h1 : magicBᵀ * magicB.map star = 1 := bT_conjB
  calc magicB * Matrix.diagonal (fun p : Pair => q (pairEquiv p)) * magicBᵀ *
        (magicB.map star * (Matrix.diagonal (star fun p : Pair => q (pairEquiv p)) * magicBᴴ))
      = magicB * Matrix.diagonal (fun p : Pair => q (pairEquiv p)) * (magicBᵀ * magicB.map star) *
        (Matrix.diagonal (star fun p : Pair => q (pairEquiv p)) * magicBᴴ) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [h1, Matrix.mul_one, ← Matrix.mul_assoc (magicB * _), Matrix.mul_assoc magicB,
            Matrix.diagonal_mul_diagonal]
          have hd : (fun p : Pair => q (pairEquiv p) * star (fun p : Pair => q (pairEquiv p)) p) =
              fun p => conj (q (pairEquiv p)) * q (pairEquiv p) := by
            funext p; simp [mul_comm]
          rw [hd]

theorem red12_psiMag_quadratic (q : Fin 4 → ℂ)
    (h : ∀ k, Complex.normSq (q k) = 1 / 6 ∨ Complex.normSq (q k) = 1 / 2) :
    (red12 (psiMag q) - (1 / 6 : ℂ) • 1) * (red12 (psiMag q) - (1 / 2 : ℂ) • 1) = 0 := by
  set E : Mat4 := Matrix.diagonal (fun p : Pair => conj (q (pairEquiv p)) * q (pairEquiv p)) with hE
  have hR := red12_psiMag q
  have hBB : magicB * magicBᴴ = 1 := magicB_unitary'
  have hc : ∀ c : ℂ, red12 (psiMag q) - c • 1 = magicB * (E - c • 1) * magicBᴴ := by
    intro c
    rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hBB]
  rw [hc, hc]
  calc magicB * (E - (1 / 6 : ℂ) • 1) * magicBᴴ * (magicB * (E - (1 / 2 : ℂ) • 1) * magicBᴴ)
      = magicB * ((E - (1 / 6 : ℂ) • 1) * (magicBᴴ * magicB) * (E - (1 / 2 : ℂ) • 1)) * magicBᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [magicB_unitary, Matrix.mul_one]
        have hsub : ∀ c : ℂ, E - c • 1 = Matrix.diagonal (fun p : Pair => conj (q (pairEquiv p)) * q (pairEquiv p) - c) := by
          intro c
          ext x y
          by_cases hxy : x = y
          · subst hxy; simp [hE, Matrix.diagonal_apply]
          · simp [hE, Matrix.diagonal_apply, Matrix.one_apply, hxy]
        have : (E - (1 / 6 : ℂ) • 1) * (E - (1 / 2 : ℂ) • 1) = 0 := by
          rw [hsub, hsub, Matrix.diagonal_mul_diagonal]
          ext x y
          by_cases hxy : x = y
          · subst hxy
            simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
            have hk := h (pairEquiv x)
            have hm : conj (q (pairEquiv x)) * q (pairEquiv x) = ((Complex.normSq (q (pairEquiv x)) : ℝ) : ℂ) :=
              (Complex.normSq_eq_conj_mul_self).symm
            rw [hm]
            rcases hk with hk | hk <;> rw [hk] <;> push_cast <;> ring
          · simp [Matrix.diagonal_apply, hxy]
        rw [this]; simp


/-- **`thm:maxchiral`, equality case ("only if"), refined form.**  If a unit magic-diagonal state has
`F_K(ψ_q, ψ̄_q) ≤ 4/9 + |qᵀq|²/18`, it is locally unitarily equivalent to `M₄` or `conj M₄`. -/
theorem maxchiral_equality_refined (q : Fin 4 → ℂ) (hq : nrm2 q = 1)
    (h : rotOverlap (psiMag q) (Psi.conj (psiMag q)) ≤ 4 / 9 + Complex.normSq (bdot q q) / 18) :
    LUEquiv (psiMag q) M4 ∨ LUEquiv (psiMag q) (Psi.conj M4) := by
  obtain ⟨hb, hm⟩ := equality_moduli q hq ((FKmag_le_rotOverlap q).trans h)
  have hn : normSqPsi (psiMag q) = 1 := by
    rw [← Unify.nsq_toN, Unify.nsq_toN_psiMag, hq]
  exact classify (psiMag q) hn (blochSq_psiMag q) (red12_psiMag_quadratic q hm)
    (by rw [spinFlip_psiMag]; exact hb)

/-- **`thm:maxchiral`, equality case ("only if").**  A unit critical magic-diagonal state with
`F_K(ψ_q, ψ̄_q) ≤ 4/9` is locally unitarily equivalent to `M₄` or `conj M₄`.  (Only the easy inequality
`FKmag ≤ F_K` is used; the recalled Weyl-vertex input R7 is not needed.) -/
theorem maxchiral_equality (q : Fin 4 → ℂ) (hq : nrm2 q = 1)
    (h : rotOverlap (psiMag q) (Psi.conj (psiMag q)) ≤ 4 / 9) :
    LUEquiv (psiMag q) M4 ∨ LUEquiv (psiMag q) (Psi.conj M4) :=
  maxchiral_equality_refined q hq (h.trans (by linarith [Complex.normSq_nonneg (bdot q q)]))

/-- The same in the `NQubit` set-up. -/
theorem maxchiral_equality_NQubit (q : Fin 4 → ℂ) (hq : nrm2 q = 1)
    (h : NQubit.FKΘ (Unify.toN (psiMag q)) ≤ 4 / 9) :
    LUEquiv (psiMag q) M4 ∨ LUEquiv (psiMag q) (Psi.conj M4) :=
  maxchiral_equality q hq (by rw [Unify.rotOverlap_conj_eq_FKΘ]; exact h)

section PlaneFormula

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {m : ℕ}

/-- `(g ⊗ T) y` for `y ∈ ℂ^m ⊗ H`, written as a family of `m` vectors of `H`. -/
def act (g : Matrix (Fin m) (Fin m) ℂ) (T : H →ₗ[ℂ] H) (y : Fin m → H) : Fin m → H :=
  fun a => ∑ c, g a c • T (y c)

/-- The pairing `⟨x, w⟩`. -/
noncomputable def ipA (x w : Fin m → H) : ℂ := ∑ a, inner ℂ (x a) (w a)

/-- The squared norm `‖w‖²`. -/
noncomputable def nsqA (w : Fin m → H) : ℝ := ∑ a, ‖w a‖ ^ 2

/-- `S_y = supp Tr_A |y⟩⟨y|` is the span of the components of `y`; `T S_y` is its image. -/
noncomputable def planeSpace (y : Fin m → H) (T : H →ₗ[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range y)).map T

/-- `Tr(ρ_x P_K)`, with `ρ_x = ∑_a |x_a⟩⟨x_a|`: `∑_a ‖P_K x_a‖²`. -/
noncomputable def planeWeight (x : Fin m → H) (K : Submodule ℂ H) : ℝ :=
  ∑ a, ‖K.starProjection (x a)‖ ^ 2

omit [FiniteDimensional ℂ H] in
theorem planeSpace_eq (y : Fin m → H) (T : H →ₗ[ℂ] H) :
    planeSpace y T = Submodule.span ℂ (Set.range fun c => T (y c)) := by
  unfold planeSpace
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem act_mem (g : Matrix (Fin m) (Fin m) ℂ) (T : H →ₗ[ℂ] H) (y : Fin m → H) (a : Fin m) :
    act g T y a ∈ planeSpace y T := by
  rw [planeSpace_eq]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)


theorem inner_proj_of_mem (K : Submodule ℂ H) (u w : H) (hw : w ∈ K) :
    inner ℂ u w = inner ℂ (K.starProjection u) w := by
  have h1 : K.starProjection w = w := (Submodule.starProjection_eq_self_iff).2 hw
  calc inner ℂ u w = inner ℂ u (K.starProjection w) := by rw [h1]
    _ = inner ℂ (K.starProjection u) w := (K.inner_starProjection_left_eq_right u w).symm

/-- **Plane formula, upper bound.**  Every `(g ⊗ T) y` has overlap with `x` at most `Tr(ρ_x P_{T S_y})`
times its squared norm (Cauchy-Schwarz in `A ⊗ T S_y`). -/
theorem plane_upper (x y : Fin m → H) (T : H →ₗ[ℂ] H) (g : Matrix (Fin m) (Fin m) ℂ) :
    Complex.normSq (ipA x (act g T y)) ≤ planeWeight x (planeSpace y T) * nsqA (act g T y) := by
  set K := planeSpace y T
  have h1 : ipA x (act g T y) = ∑ a, inner ℂ (K.starProjection (x a)) (act g T y a) :=
    Finset.sum_congr rfl fun a _ => inner_proj_of_mem K _ _ (act_mem g T y a)
  rw [h1, Complex.normSq_eq_norm_sq]
  have h2 : ‖∑ a, inner ℂ (K.starProjection (x a)) (act g T y a)‖ ≤
      ∑ a, ‖K.starProjection (x a)‖ * ‖act g T y a‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_inner_le_norm _ _)
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖K.starProjection (x a)‖)
    (fun a => ‖act g T y a‖)
  calc ‖∑ a, inner ℂ (K.starProjection (x a)) (act g T y a)‖ ^ 2
      ≤ (∑ a, ‖K.starProjection (x a)‖ * ‖act g T y a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ _ := h3


theorem nsqA_nonneg (w : Fin m → H) : 0 ≤ nsqA w := Finset.sum_nonneg fun a _ => sq_nonneg _

theorem planeWeight_nonneg (x : Fin m → H) (K : Submodule ℂ H) : 0 ≤ planeWeight x K :=
  Finset.sum_nonneg fun a _ => sq_nonneg _

theorem exists_act_eq (y : Fin m → H) (T : H →ₗ[ℂ] H) (W : Fin m → H)
    (hW : ∀ a, W a ∈ planeSpace y T) : ∃ g : Matrix (Fin m) (Fin m) ℂ, act g T y = W := by
  have : ∀ a, ∃ c : Fin m → ℂ, ∑ i, c i • T (y i) = W a := fun a => by
    have := hW a
    rw [planeSpace_eq] at this
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose g hg using this
  exact ⟨Matrix.of g, funext fun a => hg a⟩

theorem act_add_smul_one (g : Matrix (Fin m) (Fin m) ℂ) (T : H →ₗ[ℂ] H) (y : Fin m → H) (t : ℂ)
    (a : Fin m) : act (g + t • 1) T y a = act g T y a + t • T (y a) := by
  simp [act, add_smul, Finset.sum_add_distrib, Matrix.one_apply]

/-- **Plane formula, attainment.**  The bound of `plane_upper` is approached by invertible `g`. -/
theorem plane_approach (x y : Fin m → H) (T : H →ₗ[ℂ] H)
    (hwt : 0 < planeWeight x (planeSpace y T)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Matrix (Fin m) (Fin m) ℂ, IsUnit g.det ∧ nsqA (act g T y) ≠ 0 ∧
      planeWeight x (planeSpace y T) - ε <
        Complex.normSq (ipA x (act g T y)) / nsqA (act g T y) := by
  set K := planeSpace y T with hK
  set wt := planeWeight x K with hwtdef
  have hmem : ∀ a, K.starProjection (x a) ∈ K := fun a => Submodule.starProjection_apply_mem K _
  obtain ⟨g0, hg0⟩ := exists_act_eq y T (fun a => K.starProjection (x a)) hmem
  set v : Fin m → H := fun a => T (y a) with hv
  -- values at `t = 0`
  have hN0 : nsqA (act g0 T y) = wt := by
    rw [hg0]; rfl
  have hF0 : ipA x (act g0 T y) = (wt : ℂ) := by
    rw [hg0]
    simp only [ipA, hwtdef, planeWeight]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_proj_of_mem K (x a) _ (hmem a), inner_self_eq_norm_sq_to_K]
    rfl
  -- the perturbation
  set F : ℝ → ℂ := fun t => ∑ a, inner ℂ (x a) (act g0 T y a + (t : ℂ) • v a) with hF
  set N : ℝ → ℝ := fun t => ∑ a, ‖act g0 T y a + (t : ℂ) • v a‖ ^ 2 with hN
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hF00 : F 0 = (wt : ℂ) := by simpa [hF, ipA] using hF0
  have hN00 : N 0 = wt := by simpa [hN, nsqA] using hN0
  have hR : ContinuousAt (fun t => Complex.normSq (F t) / N t) 0 :=
    (Complex.continuous_normSq.comp hFc).continuousAt.div hNc.continuousAt (by rw [hN00]; exact hwt.ne')
  have hR0 : Complex.normSq (F 0) / N 0 = wt := by
    rw [hF00, hN00, Complex.normSq_ofReal]; field_simp
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), wt - ε < Complex.normSq (F t) / N t := by
    have := hR.eventually (lt_mem_nhds (a := wt - ε) (by show wt - ε < Complex.normSq (F 0) / N 0; rw [hR0]; linarith))
    exact this
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), N t ≠ 0 := by
    exact hNc.continuousAt.eventually (isOpen_compl_singleton.mem_nhds (by
      show N 0 ∈ ({0}ᶜ : Set ℝ)
      rw [hN00]; exact hwt.ne'))
  -- invertibility away from a finite set
  set S : Set ℂ := spectrum ℂ g0 with hS
  have hSfin : S.Finite := Matrix.finite_spectrum g0
  set Bad : Set ℝ := {t : ℝ | -(t : ℂ) ∈ S} with hBad
  have hBadfin : Bad.Finite := hSfin.preimage (by
    intro a _ b _ hab
    have : (a : ℂ) = b := by simpa using hab
    exact_mod_cast this)
  have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (Bad \ {0})ᶜ :=
    (hBadfin.sdiff).isClosed.isOpen_compl.mem_nhds (by simp)
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), wt - ε < Complex.normSq (F t) / N t ∧ N t ≠ 0 ∧ t ∈ (Bad \ {0})ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (h1.and (h2.and h3))
  have h5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨hlt, hN, hnb⟩, htpos⟩ := (h4.and h5).exists
  refine ⟨g0 + (t : ℂ) • 1, ?_, ?_, ?_⟩
  · have htb : t ∉ Bad := fun hb => hnb ⟨hb, htpos.ne'⟩
    rw [← Matrix.isUnit_iff_isUnit_det]
    by_contra hnu
    apply htb
    show -(t : ℂ) ∈ S
    rw [hS, spectrum.mem_iff]
    intro hu
    apply hnu
    have : algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ) (-(t : ℂ)) - g0 = -(g0 + (t : ℂ) • 1) := by
      rw [Algebra.algebraMap_eq_smul_one, neg_smul]
      abel
    rw [this] at hu
    exact (IsUnit.neg_iff _).1 hu
  · have : nsqA (act (g0 + (t : ℂ) • 1) T y) = N t := by
      simp only [nsqA, act_add_smul_one]; rfl
    rw [this]; exact hN
  · have e1 : ipA x (act (g0 + (t : ℂ) • 1) T y) = F t := by
      simp only [ipA, hF, act_add_smul_one]; rfl
    have e2 : nsqA (act (g0 + (t : ℂ) • 1) T y) = N t := by
      simp only [nsqA, act_add_smul_one]; rfl
    rw [e1, e2]; exact hlt


/-- **Plane formula (`thm:planeformula`, bipartite part).**  For `x, y ∈ ℂ^m ⊗ H` and a linear map `T`
(the filter `h` on `B = H`),
`sup_{g ∈ GL_m} |⟨x, (g ⊗ T) y⟩|² / ‖(g ⊗ T) y‖² = Tr(ρ_x P_{T S_y})`, with `ρ_x = ∑_a |x_a⟩⟨x_a|`
(`= Tr_A |x⟩⟨x|`) and `S_y = span {y_c} = supp Tr_A |y⟩⟨y|`. -/
theorem plane_formula (x y : Fin m → H) (T : H →ₗ[ℂ] H) :
    sSup {r : ℝ | ∃ g : Matrix (Fin m) (Fin m) ℂ, IsUnit g.det ∧ nsqA (act g T y) ≠ 0 ∧
        r = Complex.normSq (ipA x (act g T y)) / nsqA (act g T y)} =
      planeWeight x (planeSpace y T) := by
  set wt := planeWeight x (planeSpace y T) with hwt
  have hwt0 : 0 ≤ wt := planeWeight_nonneg _ _
  have hub : ∀ r ∈ {r : ℝ | ∃ g : Matrix (Fin m) (Fin m) ℂ, IsUnit g.det ∧ nsqA (act g T y) ≠ 0 ∧
        r = Complex.normSq (ipA x (act g T y)) / nsqA (act g T y)}, r ≤ wt := by
    rintro r ⟨g, -, hne, rfl⟩
    have hpos : 0 < nsqA (act g T y) := lt_of_le_of_ne (nsqA_nonneg _) (Ne.symm hne)
    rw [div_le_iff₀ hpos]
    exact plane_upper x y T g
  refine le_antisymm (Real.sSup_le hub hwt0) ?_
  by_cases h0 : wt = 0
  · rw [h0]
    exact Real.sSup_nonneg (by
      rintro r ⟨g, -, -, rfl⟩
      exact div_nonneg (Complex.normSq_nonneg _) (nsqA_nonneg _))
  · have hpos : 0 < wt := lt_of_le_of_ne hwt0 (Ne.symm h0)
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hu, hne, hg⟩ := plane_approach x y T hpos (wt - sSup _) (by linarith)
    have hmem : Complex.normSq (ipA x (act g T y)) / nsqA (act g T y) ∈
        {r : ℝ | ∃ g : Matrix (Fin m) (Fin m) ℂ, IsUnit g.det ∧ nsqA (act g T y) ≠ 0 ∧
          r = Complex.normSq (ipA x (act g T y)) / nsqA (act g T y)} := ⟨g, hu, hne, rfl⟩
    have := le_csSup ⟨wt, hub⟩ hmem
    linarith


/-! ### `c-lem-branch`: only the arithmetic skeleton

The analytic core of Lemma `c-lem-branch` (symmetric subspace of `k` copies of qubit 1, twirls, the integral
`∫|⟨w,e⟩|^{2k} dw = 1/(k+1)` over the Bloch sphere, the Helstrom form of `Pe(k)`) is not formalised; below are
the two real-arithmetic steps that turn its inputs into the stated bound. -/

/-- `s - √(s² - 4c) ≥ 2c/s`, hence `Pe ≥ ¼(s - √(s²-4c))` implies `Pe ≥ c/(2s)`. -/
theorem helstrom_arith {s c Pe : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (h4 : 4 * c ≤ s ^ 2)
    (hPe : (s - Real.sqrt (s ^ 2 - 4 * c)) / 4 ≤ Pe) : c / (2 * s) ≤ Pe := by
  have hsq : Real.sqrt (s ^ 2 - 4 * c) ≤ s - 2 * c / s := by
    apply Real.sqrt_le_iff.2
    have h2 : 0 ≤ s - 2 * c / s := by
      rw [sub_nonneg, div_le_iff₀ hs]; nlinarith
    refine ⟨h2, ?_⟩
    have : (s - 2 * c / s) ^ 2 = s ^ 2 - 4 * c + 4 * c ^ 2 / s ^ 2 := by field_simp; ring
    rw [this]
    have : 0 ≤ 4 * c ^ 2 / s ^ 2 := by positivity
    linarith
  have : c / (2 * s) = (2 * c / s) / 4 := by field_simp; ring
  rw [this]; linarith

/-- The chain of `c-lem-branch`: `|⟨a,b⟩|² ≥ ‖M‖^{2k}` and `‖a‖² + ‖b‖² ≤ (k+1)(p^k + p'^k)` give
`Pe ≥ ‖M‖^{2k} / (2 (k+1) (p^k + p'^k))`. -/
theorem branch_converse_arith {k : ℕ} {nM p p' a2 b2 c Pe : ℝ} (hnM : 0 ≤ nM) (hp : 0 ≤ p) (hp' : 0 ≤ p')
    (hden : 0 < p ^ k + p' ^ k) (ha : 0 ≤ a2) (hb : 0 ≤ b2) (hab : 0 < a2 + b2)
    (ha2 : a2 ≤ (k + 1) * p ^ k) (hb2 : b2 ≤ (k + 1) * p' ^ k) (hc : nM ^ (2 * k) ≤ c)
    (hc4 : 4 * c ≤ (a2 + b2) ^ 2)
    (hPe : ((a2 + b2) - Real.sqrt ((a2 + b2) ^ 2 - 4 * c)) / 4 ≤ Pe) :
    nM ^ (2 * k) / (2 * ((k + 1) * (p ^ k + p' ^ k))) ≤ Pe := by
  have hc0 : 0 ≤ c := (pow_nonneg hnM _).trans hc
  have h1 := helstrom_arith hab hc0 hc4 hPe
  have hk : (0 : ℝ) < ((k : ℝ) + 1) * (p ^ k + p' ^ k) := by positivity
  calc nM ^ (2 * k) / (2 * ((k + 1) * (p ^ k + p' ^ k)))
      ≤ c / (2 * (a2 + b2)) := by
        apply div_le_div₀ hc0 (by exact hc) (by positivity)
        have : a2 + b2 ≤ (k + 1) * (p ^ k + p' ^ k) := by nlinarith
        linarith
    _ ≤ Pe := h1

end PlaneFormula


end FormalResearch.FrameFree.CriticalLocus
