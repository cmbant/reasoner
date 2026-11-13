module

public import FormalResearch.Racah.P2ThreeJOperator
public import FormalResearch.Wigner.ThreeJOrthComplete

/-!
# Exact finite Wigner spectral system: orthogonality and completeness (Weyl P2, `thm:3jspectral`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jspectral`, equations
`eq:3jdiscorth` and `eq:3jdisccomplete`.

The physical lattice `𝒳_N` is `xLat M σ N n`, `n < K`, `K = N - L₀`, `L₀ = max(|M|,|σ|)`
(`eq:physicalgrid`); `PhiX L M σ N` is `Φ_L^{M,σ}(·; 1/N)` and `h = 1/N`.  The hypothesis `SpecAdm`
is the integrality/admissibility of the data: `(L₀, j₋, j₊)` is a triangle with integral sum and
`L₀ ± M` are natural numbers (so `2L₀`, `L₀±M`, `L₀±σ`, `M±σ`, `N-L₀` are integers, which is all the
paper uses).

## Results

* `Phi_discorth` (`eq:3jdiscorth`): `2h ∑_{x∈𝒳_N} Φ_L(x) Φ_{L'}(x) = 2/(2L+1) δ_{LL'}` for admissible
  ranks `L, L'` (`(L j₋ j₊)` a triangle, `L ± M` natural).
* `Phi_disccomplete` (`eq:3jdisccomplete`): `h ∑_{L=L₀}^{N-1} (2L+1) Φ_L(x) Φ_L(y) = δ_{xy}` for
  lattice points `x = x_n`, `y = x_{n'}`.

Both are the library relations `threeJ_orthogonality` (DLMF 34.3.17) and `threeJ_completeness`
(DLMF 34.3.16) rewritten in the midpoint coordinate; the signs `(-1)^{2L+j₊+m₊}` of `Φ` multiply the
orthonormal rows/columns by a common sign.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- Admissibility of `(M, σ, N)` for the finite spectral system: `(L₀, j₋, j₊)` is a triangle with
integral sum and `L₀ ± M ∈ ℕ`, `L₀ = max(|M|,|σ|)`. -/
def SpecAdm (M σ N : ℚ) : Prop :=
  IsTri (max |M| |σ|) (jMinus N σ) (jPlus N σ) ∧ IsNat (max |M| |σ| + M) ∧
    IsNat (max |M| |σ| - M)

lemma min_four_eq (N M σ : ℚ) :
    min (min (N - 1 - σ) (N - 1 + σ)) (min (N - 1 + M) (N - 1 - M)) + 1 =
      N - max |M| |σ| := by
  rcases abs_cases σ with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases abs_cases M with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rw [h1, h2] <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

/-- The natural-number data of an admissible `(M, σ, N)`. -/
lemma specAdm_data {M σ N : ℚ} (h : SpecAdm M σ N) :
    ∃ a b P Q : ℕ, 2 * jMinus N σ = a ∧ 2 * jPlus N σ = b ∧
      jMinus N σ + jPlus N σ + M = P ∧ jMinus N σ + jPlus N σ - M = Q ∧
      ((nrk a b P Q : ℕ) : ℚ) = N - max |M| |σ| ∧
      mbot (jMinus N σ) a P = (-N + 1 + |M + σ| - M) / 2 := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := h
  unfold jMinus jPlus at hp1 hp2 hp3
  have hA : (p3 : ℚ) + p1 = N - 1 - σ := by linarith
  have hB : (p3 : ℚ) + p2 = N - 1 + σ := by linarith
  have hP : (p3 : ℚ) + q1 = N - 1 + M := by linarith
  have hQ : (p3 : ℚ) + q2 = N - 1 - M := by linarith
  refine ⟨p3 + p1, p3 + p2, p3 + q1, p3 + q2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold jMinus; push_cast; linarith
  · unfold jPlus; push_cast; linarith
  · unfold jMinus jPlus; push_cast; linarith
  · unfold jMinus jPlus; push_cast; linarith
  · unfold nrk
    push_cast [Nat.cast_min]
    rw [hA, hB, hP, hQ]
    exact min_four_eq N M σ
  · unfold mbot jMinus
    push_cast [Nat.cast_min]
    rw [hA, hP]
    rcases abs_cases (M + σ) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rw [h1] <;> simp only [min_def] <;>
      split_ifs <;> linarith

lemma mu_lat (M σ N : ℚ) (hN : N ≠ 0) (n : ℕ) :
    N * xLat M σ N n / 2 = (-N + 1 + |M + σ|) / 2 + n := by
  unfold xLat
  field_simp
  ring

lemma Phi3j_eq (L M σ N μ : ℚ) :
    Phi3j L M σ N μ = sgn (2 * L + jPlus N σ + mPlus M μ) * Real.sqrt (N : ℝ) *
      tt (jMinus N σ) (jPlus N σ) M L (mMinus M μ) := by
  unfold Phi3j tt
  have : mPlus M μ = -M - mMinus M μ := by unfold mMinus mPlus; ring
  rw [← this]

/-- At the lattice point `x_n`, the magnetic projection `m₋` is `m₀ + n`. -/
lemma mMinus_lat {M σ N : ℚ} {a P : ℕ} (hN : N ≠ 0)
    (hm : mbot (jMinus N σ) a P = (-N + 1 + |M + σ| - M) / 2) (n : ℕ) :
    mMinus M (N * xLat M σ N n / 2) = mbot (jMinus N σ) a P + n := by
  rw [mu_lat M σ N hN, hm]
  unfold mMinus
  ring

/-- The sign of `Φ_L` on the lattice: `sgn(2L + j₊ + m₊) = (-1)^{p+q} sgn(j₊+m₊)` for `L + M = p`,
`L - M = q`. -/
lemma sgn_rank {L M r s : ℚ} {p q : ℕ} (hp : L + M = p) (hq : L - M = q) :
    sgn (2 * L + r + s) = (-1 : ℝ) ^ (p + q) * sgn (r + s) := by
  have : 2 * L + r + s = (r + s) + (((p + q : ℕ) : ℤ) : ℚ) := by push_cast; linarith
  rw [this, sgn_add_int]
  rw [zpow_natCast]

/-- Product of two kernel values on lattice points. -/
lemma Phi_lat_prod {M σ N : ℚ} {a P : ℕ} (hN : 0 < N)
    (hm : mbot (jMinus N σ) a P = (-N + 1 + |M + σ| - M) / 2)
    {L L' : ℚ} {p q p' q' : ℕ} (hp : L + M = p) (hq : L - M = q) (hp' : L' + M = p')
    (hq' : L' - M = q') (n n' : ℕ) :
    PhiX L M σ N (xLat M σ N n) * PhiX L' M σ N (xLat M σ N n') =
      (-1 : ℝ) ^ (p + q + (p' + q')) * (sgn (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) *
        sgn (jPlus N σ + mPlus M (N * xLat M σ N n' / 2))) * (N : ℝ) *
      (tt (jMinus N σ) (jPlus N σ) M L (mbot (jMinus N σ) a P + n) *
        tt (jMinus N σ) (jPlus N σ) M L' (mbot (jMinus N σ) a P + n')) := by
  unfold PhiX
  rw [Phi3j_eq, Phi3j_eq, sgn_rank hp hq, sgn_rank hp' hq', mMinus_lat hN.ne' hm,
    mMinus_lat hN.ne' hm]
  have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N :=
    Real.mul_self_sqrt (by exact_mod_cast hN.le)
  rw [pow_add]
  linear_combination
    ((-1 : ℝ) ^ (p + q) * (-1 : ℝ) ^ (p' + q') * (sgn (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) *
        sgn (jPlus N σ + mPlus M (N * xLat M σ N n' / 2))) *
      (tt (jMinus N σ) (jPlus N σ) M L (mbot (jMinus N σ) a P + n) *
        tt (jMinus N σ) (jPlus N σ) M L' (mbot (jMinus N σ) a P + n'))) * hs

/-- The `j₊ + m₊` of an admissible lattice point is a natural number. -/
lemma sgn_lat_sq {M σ N : ℚ} {a b P Q : ℕ}
    (ha : 2 * jMinus N σ = a) (hb : 2 * jPlus N σ = b) (hP : jMinus N σ + jPlus N σ + M = P)
    (hQ : jMinus N σ + jPlus N σ - M = Q) (hN : N ≠ 0)
    (hm : mbot (jMinus N σ) a P = (-N + 1 + |M + σ| - M) / 2) {n : ℕ} (hn : n < nrk a b P Q) :
    sgn (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) *
      sgn (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) = 1 := by
  have hadm := mlat_adm ha hb hP hQ hn
  rw [← mMinus_lat hN hm] at hadm
  have h3 := hadm.2.2.1
  have : mPlus M (N * xLat M σ N n / 2) = -M - mMinus M (N * xLat M σ N n / 2) := by
    unfold mMinus mPlus; ring
  rw [this]
  apply sgn_mul_self_of_int
  obtain ⟨c, hc⟩ := h3
  exact ⟨c, by exact_mod_cast hc⟩

/-- **`eq:3jdiscorth`**: `2h ∑_{x∈𝒳_N} Φ_L(x)Φ_{L'}(x) = 2/(2L+1) δ_{LL'}` (`h = 1/N`),
for admissible ranks. -/
theorem Phi_discorth {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {L L' : ℚ}
    (hT : IsTri L (jMinus N σ) (jPlus N σ)) (h1 : IsNat (L + M)) (h2 : IsNat (L - M))
    (hT' : IsTri L' (jMinus N σ) (jPlus N σ)) (h1' : IsNat (L' + M)) (h2' : IsNat (L' - M)) :
    2 * (1 / (N : ℝ)) * ∑ n ∈ Finset.range K,
        PhiX L M σ N (xLat M σ N n) * PhiX L' M σ N (xLat M σ N n) =
      if L = L' then 2 / (2 * (L : ℝ) + 1) else 0 := by
  obtain ⟨a, b, P, Q, ha, hb, hP, hQ, hnrk, hm⟩ := specAdm_data hA
  have hKn : K = nrk a b P Q := by
    have : (K : ℚ) = ((nrk a b P Q : ℕ) : ℚ) := by rw [hK, hnrk]
    exact_mod_cast this
  subst hKn
  obtain ⟨p, hp⟩ := id h1
  obtain ⟨q, hq⟩ := id h2
  obtain ⟨p', hp'⟩ := id h1'
  obtain ⟨q', hq'⟩ := id h2'
  have hterm : ∀ n ∈ Finset.range (nrk a b P Q),
      PhiX L M σ N (xLat M σ N n) * PhiX L' M σ N (xLat M σ N n) =
      ((-1 : ℝ) ^ (p + q + (p' + q')) * (N : ℝ)) *
        (tt (jMinus N σ) (jPlus N σ) M L (mbot (jMinus N σ) a P + n) *
          tt (jMinus N σ) (jPlus N σ) M L' (mbot (jMinus N σ) a P + n)) := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [Phi_lat_prod hN hm hp hq hp' hq' n n,
      sgn_lat_sq ha hb hP hQ hN.ne' hm hn']
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hmain := threeJ_orthogonality (jMinus N σ) (jPlus N σ) M L L' hT h1 h2 hT' h1' h2'
  have hf : ∀ m, tt (jMinus N σ) (jPlus N σ) M L m * tt (jMinus N σ) (jPlus N σ) M L' m ≠ 0 →
      MAdm (jMinus N σ) (jPlus N σ) M m := by
    intro m hm
    by_contra hnot
    apply hm
    rw [tt_eq_zero_of_not_madm _ hnot]; ring
  have hsum : ∑ n ∈ Finset.range (nrk a b P Q),
      tt (jMinus N σ) (jPlus N σ) M L (mbot (jMinus N σ) a P + n) *
        tt (jMinus N σ) (jPlus N σ) M L' (mbot (jMinus N σ) a P + n) =
      if L = L' then 1 / (2 * (L : ℝ) + 1) else 0 := by
    rw [← msum_eq_range ha hb hP hQ hf]
    exact hmain
  rw [hsum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs with he
  · subst he
    have hpp : p = p' := by
      have : (p : ℚ) = p' := by rw [← hp, ← hp']
      exact_mod_cast this
    have hqq : q = q' := by
      have : (q : ℚ) = q' := by rw [← hq, ← hq']
      exact_mod_cast this
    subst hpp hqq
    have hsg : (-1 : ℝ) ^ (p + q + (p + q)) = 1 := by
      rw [← two_mul, pow_mul]; norm_num
    rw [hsg]
    have hpos : (0 : ℝ) < 2 * (L : ℝ) + 1 := by
      have : (0 : ℚ) ≤ L := by
        obtain ⟨⟨⟨n1, hn1⟩, ⟨n2, hn2⟩, -⟩⟩ : IsTri L (jMinus N σ) (jPlus N σ) ∧ True := ⟨hT, trivial⟩
        have : (0 : ℚ) ≤ n1 := by positivity
        have : (0 : ℚ) ≤ n2 := by positivity
        unfold jMinus jPlus at hn1 hn2
        linarith
      have : (0 : ℝ) ≤ L := by exact_mod_cast this
      linarith
    field_simp
  · simp

/-- **`eq:3jdisccomplete`**: `h ∑_{L=L₀}^{N-1} (2L+1) Φ_L(x_n) Φ_L(x_{n'}) = δ_{nn'}`,
`h = 1/N`, `L = L₀ + i`, `i < K = N - L₀`. -/
theorem Phi_disccomplete {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {n n' : ℕ} (hn : n < K) (hn' : n' < K) :
    (1 / (N : ℝ)) * ∑ i ∈ Finset.range K,
        (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
          (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
            PhiX (max |M| |σ| + i) M σ N (xLat M σ N n')) =
      if n = n' then 1 else 0 := by
  obtain ⟨a, b, P, Q, ha, hb, hP, hQ, hnrk, hm⟩ := specAdm_data hA
  have hKn : K = nrk a b P Q := by
    have : (K : ℚ) = ((nrk a b P Q : ℕ) : ℚ) := by rw [hK, hnrk]
    exact_mod_cast this
  subst hKn
  have hLb : Lbot (jMinus N σ) (jPlus N σ) (nrk a b P Q) = max |M| |σ| := by
    unfold Lbot
    rw [hnrk]
    unfold jMinus jPlus
    ring
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm : ∀ i ∈ Finset.range (nrk a b P Q),
      (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
          (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
            PhiX (max |M| |σ| + i) M σ N (xLat M σ N n')) =
      ((sgn (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) *
          sgn (jPlus N σ + mPlus M (N * xLat M σ N n' / 2))) * (N : ℝ)) *
        ((2 * ((Lbot (jMinus N σ) (jPlus N σ) (nrk a b P Q) + i : ℚ) : ℝ) + 1) *
          (tt (jMinus N σ) (jPlus N σ) M (Lbot (jMinus N σ) (jPlus N σ) (nrk a b P Q) + i)
              (mbot (jMinus N σ) a P + n) *
            tt (jMinus N σ) (jPlus N σ) M (Lbot (jMinus N σ) (jPlus N σ) (nrk a b P Q) + i)
              (mbot (jMinus N σ) a P + n'))) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hL := rlat_adm ha hb hP hQ hi'
    rw [hLb] at hL ⊢
    obtain ⟨p, hp⟩ := hL.2.1
    obtain ⟨q, hq⟩ := hL.2.2
    rw [Phi_lat_prod hN hm hp hq hp hq n n']
    have hsg : (-1 : ℝ) ^ (p + q + (p + q)) = 1 := by
      rw [← two_mul, pow_mul]; norm_num
    rw [hsg]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, threeJ_completeness ha hb hP hQ hn hn']
  by_cases hnn : n = n'
  · subst hnn
    simp only [ite_true]
    rw [sgn_lat_sq ha hb hP hQ hN.ne' hm hn]
    field_simp
  · simp [hnn]

/-- The ranks `L₀ + i`, `i < K`, are admissible. -/
lemma rank_adm {M σ N : ℚ} (hA : SpecAdm M σ N) {K : ℕ} (hK : (K : ℚ) = N - max |M| |σ|)
    {i : ℕ} (hi : i < K) :
    LAdm (jMinus N σ) (jPlus N σ) M (max |M| |σ| + i) := by
  obtain ⟨a, b, P, Q, ha, hb, hP, hQ, hnrk, hm⟩ := specAdm_data hA
  have hKn : K = nrk a b P Q := by
    have : (K : ℚ) = ((nrk a b P Q : ℕ) : ℚ) := by rw [hK, hnrk]
    exact_mod_cast this
  subst hKn
  have hLb : Lbot (jMinus N σ) (jPlus N σ) (nrk a b P Q) = max |M| |σ| := by
    unfold Lbot
    rw [hnrk]
    unfold jMinus jPlus
    ring
  have := rlat_adm ha hb hP hQ hi
  rwa [hLb] at this

/-- The lattice points `x_n`, `n < K`, are admissible: the four conditions of `Hh_Phi`. -/
lemma lat_adm {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {n : ℕ} (hn : n < K) :
    IsNat (jMinus N σ + mMinus M (N * xLat M σ N n / 2)) ∧
      IsNat (jPlus N σ - mPlus M (N * xLat M σ N n / 2)) ∧
      IsNat (jMinus N σ - mMinus M (N * xLat M σ N n / 2)) ∧
      IsNat (jPlus N σ + mPlus M (N * xLat M σ N n / 2)) := by
  obtain ⟨a, b, P, Q, ha, hb, hP, hQ, hnrk, hm⟩ := specAdm_data hA
  have hKn : K = nrk a b P Q := by
    have : (K : ℚ) = ((nrk a b P Q : ℕ) : ℚ) := by rw [hK, hnrk]
    exact_mod_cast this
  subst hKn
  have hadm := mlat_adm ha hb hP hQ hn
  rw [← mMinus_lat hN.ne' hm] at hadm
  obtain ⟨c1, c2, c3, c4⟩ := hadm
  have e : mPlus M (N * xLat M σ N n / 2) = -M - mMinus M (N * xLat M σ N n / 2) := by
    unfold mMinus mPlus; ring
  rw [e]
  exact ⟨c1, c4, c2, c3⟩

/-- info: 'FormalResearch.Racah.Phi_discorth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi_discorth

/-- info: 'FormalResearch.Racah.Phi_disccomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi_disccomplete

end FormalResearch.Racah
