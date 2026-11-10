module

public import FormalResearch.PPTThreeQubit.Surface
public import FormalResearch.PPTThreeQubit.FamilyPPTFactor
public import FormalResearch.PPTThreeQubit.MomentCone

/-!
# The mixed `W` class (`thm:ppt3-w-class`): definitions and atoms

Source: `QI/hidden_entanglement/ppt_three_qubit/w_class_decompositions.tex`
(`thm:ppt3-w-class`, `eq:ppt3-w-atoms`).

Conventions as in `Basic.lean`: the amplitude `c_{abc}` of `|abc⟩` is `x (4a + 2b + c)`.
`hyperdet x` is Cayley's hyperdeterminant of a three-qubit vector (the three-tangle is `4 |Det|`).
`IsWClass ρ` says that `ρ` lies in the cone over the mixed `W` class of Acín et al.: a finite
nonnegative combination of rank-one projectors `|φ⟩⟨φ|` of vectors with vanishing hyperdeterminant
(the convex hull of such normalised pure states, scaled by the trace; `ρ ≠ 0` has its normalisation
in the class iff `ρ` does).  Biseparable operators lie in the class (`IsBiseparable.isWClass`, since a
cut-product vector has `Det = 0`).  The class is closed under addition and nonnegative scalars.

This file contains the definition, closure properties and the zero-hyperdeterminant atoms of
`eq:ppt3-w-atoms`: the pairs and triples of vectors with `Det = 0` whose averages give
`[u] + [e]`, `[u] + 4[v]`, `[u] + [w - v]` and `[v + b w] + b² [o]`.  The membership theorems for the
explicit states are in `WClassStates.lean`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- Cayley's hyperdeterminant of a three-qubit vector `x = ∑ c_{abc} |abc⟩`, `c_{abc} = x(4a+2b+c)`:
`c000² c111² + c001² c110² + c010² c101² + c100² c011²
 - 2(c000 c001 c110 c111 + c000 c010 c101 c111 + c000 c100 c011 c111 + c001 c010 c101 c110
 + c001 c100 c011 c110 + c010 c100 c011 c101) + 4(c000 c011 c101 c110 + c001 c010 c100 c111)`. -/
def hyperdet (x : Fin 8 → ℂ) : ℂ :=
  x 0 ^ 2 * x 7 ^ 2 + x 1 ^ 2 * x 6 ^ 2 + x 2 ^ 2 * x 5 ^ 2 + x 4 ^ 2 * x 3 ^ 2
    - 2 * (x 0 * x 1 * x 6 * x 7 + x 0 * x 2 * x 5 * x 7 + x 0 * x 4 * x 3 * x 7
      + x 1 * x 2 * x 5 * x 6 + x 1 * x 4 * x 3 * x 6 + x 2 * x 4 * x 3 * x 5)
    + 4 * (x 0 * x 3 * x 5 * x 6 + x 1 * x 2 * x 4 * x 7)

/-- The cone over the mixed `W` class: finite nonnegative combinations of `|φ⟩⟨φ|` with
`Det φ = 0` (`w_class_decompositions.tex`). -/
def IsWClass (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℝ) (φ : Fin n → Fin 8 → ℂ), (∀ i, 0 ≤ c i) ∧ (∀ i, hyperdet (φ i) = 0) ∧
    ρ = ∑ i, (c i : ℂ) • vecMulVec (φ i) (star (φ i))

/-! ### Closure properties -/

theorem IsWClass.zero : IsWClass (0 : Matrix (Fin 8) (Fin 8) ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem IsWClass.add {ρ σ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsWClass ρ) (hσ : IsWClass σ) :
    IsWClass (ρ + σ) := by
  obtain ⟨n, c, φ, hc, hφ, rfl⟩ := hρ
  obtain ⟨m, d, ψ, hd, hψ, rfl⟩ := hσ
  refine ⟨n + m, Fin.append c d, Fin.append φ ψ, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hc, hd]
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hφ, hψ]
  · rw [Fin.sum_univ_add]
    simp

theorem IsWClass.smul {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsWClass ρ) {r : ℝ} (hr : 0 ≤ r) :
    IsWClass ((r : ℂ) • ρ) := by
  obtain ⟨n, c, φ, hc, hφ, rfl⟩ := hρ
  refine ⟨n, fun i => r * c i, φ, fun i => mul_nonneg hr (hc i), hφ, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  push_cast
  rfl

theorem IsWClass.sum {ι : Type*} (s : Finset ι) {f : ι → Matrix (Fin 8) (Fin 8) ℂ}
    (h : ∀ i ∈ s, IsWClass (f i)) : IsWClass (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsWClass.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A rank-one projector onto a vector of vanishing hyperdeterminant. -/
theorem isWClass_rankOne {x : Fin 8 → ℂ} (h : hyperdet x = 0) :
    IsWClass (vecMulVec x (star x)) :=
  ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => h, by simp⟩

theorem isWClass_rankOne_smul {x : Fin 8 → ℂ} (h : hyperdet x = 0) {r : ℝ} (hr : 0 ≤ r) :
    IsWClass ((r : ℂ) • vecMulVec x (star x)) :=
  (isWClass_rankOne h).smul hr

/-! ### Biseparable operators are in the class -/

theorem hyperdet_prodA {x : Fin 8 → ℂ} (h : IsProdA x) : hyperdet x = 0 := by
  obtain ⟨α, μ, hx⟩ := h
  have h0 : x 0 = α 0 * μ 0 := hx 0
  have h1 : x 1 = α 0 * μ 1 := hx 1
  have h2 : x 2 = α 0 * μ 2 := hx 2
  have h3 : x 3 = α 0 * μ 3 := hx 3
  have h4 : x 4 = α 1 * μ 0 := hx 4
  have h5 : x 5 = α 1 * μ 1 := hx 5
  have h6 : x 6 = α 1 * μ 2 := hx 6
  have h7 : x 7 = α 1 * μ 3 := hx 7
  simp only [hyperdet, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

theorem hyperdet_prodB {x : Fin 8 → ℂ} (h : IsProdB x) : hyperdet x = 0 := by
  obtain ⟨α, μ, hx⟩ := h
  have h0 : x 0 = α 0 * μ 0 := hx 0
  have h1 : x 1 = α 0 * μ 1 := hx 1
  have h2 : x 2 = α 1 * μ 0 := hx 2
  have h3 : x 3 = α 1 * μ 1 := hx 3
  have h4 : x 4 = α 0 * μ 2 := hx 4
  have h5 : x 5 = α 0 * μ 3 := hx 5
  have h6 : x 6 = α 1 * μ 2 := hx 6
  have h7 : x 7 = α 1 * μ 3 := hx 7
  simp only [hyperdet, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

theorem hyperdet_prodC {x : Fin 8 → ℂ} (h : IsProdC x) : hyperdet x = 0 := by
  obtain ⟨α, μ, hx⟩ := h
  have h0 : x 0 = α 0 * μ 0 := hx 0
  have h1 : x 1 = α 1 * μ 0 := hx 1
  have h2 : x 2 = α 0 * μ 1 := hx 2
  have h3 : x 3 = α 1 * μ 1 := hx 3
  have h4 : x 4 = α 0 * μ 2 := hx 4
  have h5 : x 5 = α 1 * μ 2 := hx 5
  have h6 : x 6 = α 0 * μ 3 := hx 6
  have h7 : x 7 = α 1 * μ 3 := hx 7
  simp only [hyperdet, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- A cut-product vector has vanishing hyperdeterminant. -/
theorem hyperdet_cutProduct {x : Fin 8 → ℂ} (h : IsCutProduct x) : hyperdet x = 0 := by
  rcases h with h | h | h
  exacts [hyperdet_prodA h, hyperdet_prodB h, hyperdet_prodC h]

/-- Biseparable operators lie in the mixed `W` class. -/
theorem IsBiseparable.isWClass {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable ρ) :
    IsWClass ρ := by
  obtain ⟨n, φ, hφ, rfl⟩ := h
  exact IsWClass.sum _ fun i _ => isWClass_rankOne (hyperdet_cutProduct (hφ i))

/-- Mixtures of a `W`-class operator with biseparable (in particular fully separable) noise stay in
the class. -/
theorem IsWClass.mix {ρ σ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsWClass ρ) (hσ : IsBiseparable σ)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsWClass (((1 - p : ℝ) : ℂ) • ρ + (p : ℂ) • σ) :=
  (hρ.smul (by linarith)).add (hσ.isWClass.smul hp0)

/-! ### Local diagonal filters -/

theorem hyperdet_filter (lam : ℝ) (x : Fin 8 → ℂ) :
    hyperdet (fun i => filterDiag lam i * x i) = (lam : ℂ) ^ 6 * hyperdet x := by
  simp only [hyperdet, filterDiag]
  norm_num
  ring

/-- Diagonal local filters `F_λ = diag(1, λ)^{⊗3}` preserve the mixed `W` class. -/
theorem IsWClass.filterDiag {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsWClass ρ) (lam : ℝ) :
    IsWClass (diagonal (PPTThreeQubit.filterDiag lam) * ρ * (diagonal (PPTThreeQubit.filterDiag lam))ᴴ) := by
  obtain ⟨n, c, φ, hc, hφ, rfl⟩ := hρ
  refine ⟨n, c, fun i k => PPTThreeQubit.filterDiag lam k * φ i k, hc, fun i => ?_, ?_⟩
  · rw [hyperdet_filter, hφ, mul_zero]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext a b
    have hs : ∀ k : Fin 8, star (PPTThreeQubit.filterDiag lam k) = PPTThreeQubit.filterDiag lam k :=
      fun k => by simp [PPTThreeQubit.filterDiag]
    simp [Matrix.mul_apply, diagonal_apply, vecMulVec_apply, hs]
    ring

/-! ### Hyperdeterminant on parity sectors -/

/-- On the even sector (`c001 = c010 = c100 = c111 = 0`): `Det = 4 c000 c011 c101 c110`. -/
theorem hyperdet_even {x : Fin 8 → ℂ} (h1 : x 1 = 0) (h2 : x 2 = 0) (h4 : x 4 = 0) (h7 : x 7 = 0) :
    hyperdet x = 4 * (x 0 * x 3 * x 5 * x 6) := by
  simp only [hyperdet, h1, h2, h4, h7]
  ring

/-- On the odd sector (`c000 = c011 = c101 = c110 = 0`): `Det = 4 c001 c010 c100 c111`. -/
theorem hyperdet_odd {x : Fin 8 → ℂ} (h0 : x 0 = 0) (h3 : x 3 = 0) (h5 : x 5 = 0) (h6 : x 6 = 0) :
    hyperdet x = 4 * (x 1 * x 2 * x 4 * x 7) := by
  simp only [hyperdet, h0, h3, h5, h6]
  ring

theorem hyperdet_vVec : hyperdet vVec = 0 := by simp [hyperdet, vVec]
theorem hyperdet_wVec : hyperdet wVec = 0 := by simp [hyperdet, wVec]
theorem hyperdet_oVec : hyperdet oVec = 0 := by simp [hyperdet, oVec]
theorem hyperdet_eVec : hyperdet eVec = 0 := by simp [hyperdet, eVec]

/-- `Det(u + z e) = 4(z³ - 1)` (`w_class_decompositions.tex`). -/
theorem hyperdet_u_add_e (z : ℂ) : hyperdet (uVec 1 + z • eVec) = 4 * (z ^ 3 - 1) := by
  rw [hyperdet_even] <;> try simp [uVec, eVec]
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  ring_nf
  simp only [ω_cube, h2]
  ring_nf

/-- `Det(u + z v) = z² - 4` (`w_class_decompositions.tex`). -/
theorem hyperdet_u_add_v (z : ℂ) : hyperdet (uVec 1 + z • vVec) = z ^ 2 - 4 := by
  simp [hyperdet, uVec, vVec]
  ring

/-! ### The atoms of `eq:ppt3-w-atoms` -/

theorem vecMulVec_add_star (x y : Fin 8 → ℂ) :
    vecMulVec (x + y) (star (x + y)) = vecMulVec x (star x) + vecMulVec y (star y) +
      vecMulVec x (star y) + vecMulVec y (star x) := by
  ext i j
  simp only [vecMulVec_apply, Pi.add_apply, Pi.star_apply, star_add, Matrix.add_apply]
  ring

theorem vecMulVec_sub_star (x y : Fin 8 → ℂ) :
    vecMulVec (x - y) (star (x - y)) = vecMulVec x (star x) + vecMulVec y (star y) -
      vecMulVec x (star y) - vecMulVec y (star x) := by
  ext i j
  simp only [vecMulVec_apply, Pi.sub_apply, Pi.star_apply, star_sub, Matrix.add_apply,
    Matrix.sub_apply]
  ring

/-- Two vectors `x ± y` with vanishing hyperdeterminant give `[x] + [y]` (parity average). -/
theorem isWClass_pair {x y : Fin 8 → ℂ} (h1 : hyperdet (x + y) = 0) (h2 : hyperdet (x - y) = 0) :
    IsWClass (vecMulVec x (star x) + vecMulVec y (star y)) := by
  have e : vecMulVec x (star x) + vecMulVec y (star y) =
      ((1 / 2 : ℝ) : ℂ) • vecMulVec (x + y) (star (x + y)) +
        ((1 / 2 : ℝ) : ℂ) • vecMulVec (x - y) (star (x - y)) := by
    rw [vecMulVec_add_star, vecMulVec_sub_star]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e]
  exact (isWClass_rankOne_smul h1 (by norm_num)).add (isWClass_rankOne_smul h2 (by norm_num))

/-- The cyclic average identity behind `isWClass_triple`:
`[x + y] + [x + ω y] + [x + ω² y] = 3([x] + [y])`. -/
theorem triple_sum_id (x y : Fin 8 → ℂ) :
    vecMulVec (x + y) (star (x + y)) + vecMulVec (x + ω • y) (star (x + ω • y)) +
        vecMulVec (x + ω ^ 2 • y) (star (x + ω ^ 2 • y)) =
      (3 : ℂ) • (vecMulVec x (star x) + vecMulVec y (star y)) := by
  have hω2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have hstar : star (ω ^ 2) = ω := by
    rw [star_pow, star_ω]; linear_combination ω * ω_cube
  ext i j
  simp only [vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul,
    star_ω, hstar, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [ω_cube, hω2]
  ring_nf

/-- Three vectors `x + ω^m y` with vanishing hyperdeterminant give `[x] + [y]` (cyclic average). -/
theorem isWClass_triple {x y : Fin 8 → ℂ} (h0 : hyperdet (x + y) = 0)
    (h1 : hyperdet (x + ω • y) = 0) (h2 : hyperdet (x + ω ^ 2 • y) = 0) :
    IsWClass (vecMulVec x (star x) + vecMulVec y (star y)) := by
  have e : vecMulVec x (star x) + vecMulVec y (star y) =
      ((1 / 3 : ℝ) : ℂ) • vecMulVec (x + y) (star (x + y)) +
        ((1 / 3 : ℝ) : ℂ) • vecMulVec (x + ω • y) (star (x + ω • y)) +
        ((1 / 3 : ℝ) : ℂ) • vecMulVec (x + ω ^ 2 • y) (star (x + ω ^ 2 • y)) := by
    have h := triple_sum_id x y
    have h3 : ((1 / 3 : ℝ) : ℂ) * (3 : ℂ) = 1 := by push_cast; norm_num
    calc vecMulVec x (star x) + vecMulVec y (star y)
        = ((1 / 3 : ℝ) : ℂ) • ((3 : ℂ) • (vecMulVec x (star x) + vecMulVec y (star y))) := by
          rw [smul_smul, h3, one_smul]
      _ = _ := by rw [← h, smul_add, smul_add]
  rw [e]
  exact ((isWClass_rankOne_smul h0 (by norm_num)).add (isWClass_rankOne_smul h1 (by norm_num))).add
    (isWClass_rankOne_smul h2 (by norm_num))

/-- `eq:ppt3-w-atoms`, `C([u + e]) = [u] + [e]`. -/
theorem isWClass_u_e :
    IsWClass (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec eVec (star eVec)) := by
  apply isWClass_triple
  · have := hyperdet_u_add_e 1
    rwa [one_smul, one_pow, sub_self, mul_zero] at this
  · rw [hyperdet_u_add_e, ω_cube, sub_self, mul_zero]
  · rw [hyperdet_u_add_e, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, ω_cube, one_pow,
      sub_self, mul_zero]

/-- `eq:ppt3-w-atoms`, `P([u + 2v]) = [u] + 4[v]`. -/
theorem isWClass_u_v :
    IsWClass (vecMulVec (uVec 1) (star (uVec 1)) + (4 : ℂ) • vecMulVec vVec (star vVec)) := by
  have h := isWClass_pair (x := uVec 1) (y := (2 : ℂ) • vVec) (by
      rw [hyperdet_u_add_v]; norm_num) (by
      rw [sub_eq_add_neg, ← neg_smul, hyperdet_u_add_v]; norm_num)
  have h4 : ((Complex.normSq (2 : ℂ) : ℝ) : ℂ) = 4 := by
    simp [Complex.normSq_apply]; norm_num
  rwa [vecMulVec_smul_star, h4] at h

/-- `eq:ppt3-w-atoms`, `P([u + i(w - v)]) = [u] + [w - v]`: `u ± i(w - v)` are the product vectors
`(|0⟩ ± i|1⟩)^{⊗3}`. -/
theorem isWClass_u_wv :
    IsWClass (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec (wVec - vVec) (star (wVec - vVec))) := by
  have h := isWClass_pair (x := uVec 1) (y := Complex.I • (wVec - vVec)) (by
      simp [hyperdet, uVec, wVec, vVec]
      try ring_nf
      try simp [Complex.I_sq]) (by
      simp [hyperdet, uVec, wVec, vVec]
      try ring_nf
      try simp [Complex.I_sq])
  rwa [vecMulVec_smul_star, Complex.normSq_I, Complex.ofReal_one, one_smul] at h

/-- `eq:ppt3-w-atoms`, `C([v + b(w - o)]) = [v + b w] + b² [o]` for real `b`. -/
theorem isWClass_v_bw (b : ℝ) :
    IsWClass (vecMulVec (vVec + (b : ℂ) • wVec) (star (vVec + (b : ℂ) • wVec)) +
      ((b ^ 2 : ℝ) : ℂ) • vecMulVec oVec (star oVec)) := by
  have h := isWClass_triple (x := vVec + (b : ℂ) • wVec) (y := (-(b : ℂ)) • oVec) ?_ ?_ ?_
  · rwa [vecMulVec_smul_star, show Complex.normSq (-(b : ℂ)) = b ^ 2 by
      simp [Complex.normSq_apply]; ring] at h
  · rw [hyperdet_odd] <;> try simp [vVec, wVec, oVec]
  · rw [hyperdet_odd] <;> try simp [vVec, wVec, oVec]
    left; left
    linear_combination (-(b : ℂ)) * ω_cube
  · rw [hyperdet_odd] <;> try simp [vVec, wVec, oVec]
    left; right
    linear_combination (-(b : ℂ)) * ω_cube

end

/-- info: 'FormalResearch.PPTThreeQubit.IsBiseparable.isWClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsBiseparable.isWClass

/-- info: 'FormalResearch.PPTThreeQubit.IsWClass.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsWClass.add

/-- info: 'FormalResearch.PPTThreeQubit.IsWClass.filterDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsWClass.filterDiag

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_u_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_u_e

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_u_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_u_v

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_u_wv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_u_wv

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_v_bw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_v_bw

end FormalResearch.PPTThreeQubit
