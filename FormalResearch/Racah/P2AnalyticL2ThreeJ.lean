module

public import FormalResearch.Racah.P2ThreeJSystemSpec

/-!
# The exact finite-to-continuum map `S_N`, abstract orthonormal-family form (Weyl P2, `prop:SN`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:SN` (`eq:SNspectral`-`eq:SNintertwine`).

This is the `3j` mirror of `SRmap_*` in `P2RacahSystemWigner` (`prop:6jRacahTransmutation`).  The
continuum side of `prop:SN` is an orthonormal family `u_L`, `L = L₀,…,N-1`, of eigenvectors
`𝖧₀ u_L = L(L+1) u_L` in a real inner-product space `E`; the finite side is the exact orthonormal
eigenbasis `v_L(x_n) = √((2L+1)/2) Φ_L^{M,σ}(x_n; h)` of `𝖧_h` in `ℓ²(𝒳_N, 2h)`.  The statements
are made for an arbitrary `E` here and for `E = L²(-1,1)` in `P2AnalyticL2Transmutation`.

## Dictionary

| paper | Lean |
|---|---|
| `ℓ²(𝒳_N, 2h)`, `⟨f,g⟩ = 2h ∑ f g` | `Fin K → ℝ`, `ipN N` (`K = N - L₀`, `x_n = xLat M σ N n`) |
| `v_L`, `L = L₀ + i` | `vN M σ N i` |
| `S_N x = ∑_L ⟨u_L, x⟩ v_L` | `SNmap M σ N u x` |
| `𝖧_h` on lattice functions | `HhLat M σ N q` (`= Hh` of the zero extension; `HhLat_sample`) |

## Contents (all proved here, no hypotheses beyond `SpecAdm`)

* `vN_orthonormal`: `⟨v_L, v_{L'}⟩_{2h} = δ` (`eq:3jdiscorth`, `Phi_discorth`);
* `vN_expansion`: `q = ∑_L ⟨v_L, q⟩ v_L` (`eq:3jdisccomplete`, `Phi_disccomplete`), so `{v_L}` is an
  orthonormal basis of `ℓ²(𝒳_N, 2h)`;
* `SNmap_u`: `S_N u_L = v_L` (`eq:SNspectral`);
* `SNmap_isometry`, `SNmap_SNinv`, `SNinv_SNmap`: `S_N` is unitary from `span{u_L}` onto `ℓ²(𝒳_N, 2h)`;
* `SNmap_intertwine`: `𝖧_h S_N = S_N 𝖧₀` on `span{u_L}` when `𝖧₀ u_L = L(L+1) u_L`
  (`eq:SNintertwine`);
* `HhLat_vN`: `𝖧_h v_L = L(L+1) v_L` on the lattice (`thm:3jspectral`).

The kernel formula `eq:SNkernel` and the realisation in `L²(-1,1)` are in `P2AnalyticL2Transmutation`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- The rank `L₀ + i`, `L₀ = max(|M|,|σ|)`. -/
def rkN (M σ : ℚ) (i : ℕ) : ℚ := max |M| |σ| + i

/-- The inner product `⟨f,g⟩ = 2h ∑_n f(x_n) g(x_n)` of `ℓ²(𝒳_N, 2h)`, `h = 1/N`. -/
noncomputable def ipN (N : ℚ) {K : ℕ} (f g : Fin K → ℝ) : ℝ :=
  2 * (1 / (N : ℝ)) * ∑ n, f n * g n

/-- `v_L(x_n) = √((2L+1)/2) Φ_L^{M,σ}(x_n; h)`, `L = L₀ + i`. -/
noncomputable def vN (M σ N : ℚ) {K : ℕ} (i : Fin K) : Fin K → ℝ := fun n =>
  Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) * PhiX (rkN M σ i) M σ N (xLat M σ N n)

/-- The eigenvalue `L(L+1)` of rank `i` as a function of `i : Fin K`. -/
noncomputable def lamN (M σ : ℚ) {K : ℕ} (i : Fin K) : ℝ := rankEig M σ i

lemma rkN_nonneg (M σ : ℚ) (i : ℕ) : 0 ≤ rkN M σ i := by
  unfold rkN
  have := le_trans (abs_nonneg M) (le_max_left |M| |σ|)
  positivity

lemma rkN_injective (M σ : ℚ) : Function.Injective (rkN M σ) := by
  intro i j h
  unfold rkN at h
  exact_mod_cast (by linarith : (i : ℚ) = j)

lemma ipN_sum_left (N : ℚ) {K : ℕ} (c : Fin K → ℝ) (x : Fin K → Fin K → ℝ) (y : Fin K → ℝ) :
    ipN N (∑ k, c k • x k) y = ∑ k, c k * ipN N (x k) y := by
  simp only [ipN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

lemma ipN_sum_right (N : ℚ) {K : ℕ} (c : Fin K → ℝ) (x : Fin K → ℝ) (y : Fin K → Fin K → ℝ) :
    ipN N x (∑ k, c k • y k) = ∑ k, c k * ipN N x (y k) := by
  simp only [ipN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

section Spec

variable {M σ N : ℚ} {K : ℕ}

/-- `⟨v_L, v_{L'}⟩_{2h} = δ_{LL'}` (`eq:3jdiscorth`). -/
theorem vN_orthonormal (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (i j : Fin K) : ipN N (vN M σ N i) (vN M σ N j) = if i = j then 1 else 0 := by
  have hi := rank_adm hA hK i.2
  have hj := rank_adm hA hK j.2
  have h := Phi_discorth hA hN hK hi.1 hi.2.1 hi.2.2 hj.1 hj.2.1 hj.2.2
  have hpos : (0 : ℝ) < 2 * ((rkN M σ i : ℚ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((rkN M σ i : ℚ) : ℝ) := by exact_mod_cast rkN_nonneg M σ i
    linarith
  have hsum : ∑ n : Fin K, vN M σ N i n * vN M σ N j n =
      Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) *
        Real.sqrt ((2 * ((rkN M σ j : ℚ) : ℝ) + 1) / 2) *
        ∑ n ∈ Finset.range K, PhiX (rkN M σ i) M σ N (xLat M σ N n) *
          PhiX (rkN M σ j) M σ N (xLat M σ N n) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => PhiX (rkN M σ i) M σ N (xLat M σ N n) *
      PhiX (rkN M σ j) M σ N (xLat M σ N n)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold vN; ring
  unfold ipN
  rw [hsum]
  have h' : 2 * (1 / (N : ℝ)) * ∑ n ∈ Finset.range K, PhiX (rkN M σ i) M σ N (xLat M σ N n) *
      PhiX (rkN M σ j) M σ N (xLat M σ N n) =
      if rkN M σ i = rkN M σ j then 2 / (2 * ((rkN M σ i : ℚ) : ℝ) + 1) else 0 := h
  rw [mul_left_comm, h']
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [Real.mul_self_sqrt (div_nonneg hpos.le (by norm_num))]
    field_simp
  · have : rkN M σ i ≠ rkN M σ j := fun e => hij (Fin.ext (by exact_mod_cast rkN_injective M σ e))
    simp [hij, this]

/-- Completeness `eq:3jdisccomplete`, in the form `∑_L v_L(x_n) v_L(x_{n'}) = (N/2) δ_{nn'}`. -/
lemma vN_complete (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (n n' : Fin K) :
    ∑ i : Fin K, vN M σ N i n * vN M σ N i n' = (N : ℝ) / 2 * (if n = n' then 1 else 0) := by
  have h := Phi_disccomplete hA hN hK n.2 n'.2
  rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
    (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
      PhiX (max |M| |σ| + i) M σ N (xLat M σ N n'))) ] at h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnn : (n : ℕ) = n' ↔ n = n' := Fin.val_inj
  simp only [hnn] at h
  have e : ∀ i : Fin K, vN M σ N i n * vN M σ N i n' =
      (1 / 2) * ((2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
        (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
          PhiX (max |M| |σ| + i) M σ N (xLat M σ N n'))) := by
    intro i
    have hpos : (0 : ℝ) ≤ (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) / 2 := by
      have : (0 : ℝ) ≤ ((rkN M σ i : ℚ) : ℝ) := by exact_mod_cast rkN_nonneg M σ i
      unfold rkN at this
      linarith
    unfold vN rkN
    have hs := Real.mul_self_sqrt hpos
    linear_combination (PhiX (max |M| |σ| + (i : ℕ)) M σ N (xLat M σ N n) *
      PhiX (max |M| |σ| + (i : ℕ)) M σ N (xLat M σ N n')) * hs
  simp only [e, ← Finset.mul_sum]
  rw [← h]
  field_simp

/-- `q = ∑_L ⟨v_L, q⟩_{2h} v_L`: `{v_L}` is an orthonormal basis of `ℓ²(𝒳_N, 2h)`. -/
theorem vN_expansion (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (q : Fin K → ℝ) : q = ∑ i, ipN N (vN M σ N i) q • vN M σ N i := by
  funext n'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ipN]
  have e1 : ∀ i : Fin K, 2 * (1 / (N : ℝ)) * (∑ n, vN M σ N i n * q n) * vN M σ N i n' =
      2 * (1 / (N : ℝ)) * ∑ n, q n * (vN M σ N i n * vN M σ N i n') := by
    intro i
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro n _; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, vN_complete hA hN hK _ n']
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp

lemma ipN_sum_vN (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (c c' : Fin K → ℝ) :
    ipN N (∑ k, c k • vN M σ N k) (∑ k, c' k • vN M σ N k) = ∑ k, c k * c' k := by
  rw [ipN_sum_left]
  apply Finset.sum_congr rfl; intro k _
  rw [ipN_sum_right]
  simp only [vN_orthonormal hA hN hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

end Spec

/-! ### The abstract map `S_N` -/

section Map

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `S_N x = ∑_L ⟨u_L, x⟩ v_L` (`eq:SNspectral`, `eq:SNkernel`). -/
noncomputable def SNmap (M σ N : ℚ) {K : ℕ} (u : Fin K → E) (x : E) : Fin K → ℝ :=
  ∑ j, inner ℝ (u j) x • vN M σ N j

/-- `S_N⁻¹ q = ∑_L ⟨v_L, q⟩_{2h} u_L`. -/
noncomputable def SNinv (M σ N : ℚ) {K : ℕ} (u : Fin K → E) (q : Fin K → ℝ) : E :=
  ∑ j, ipN N (vN M σ N j) q • u j

variable {M σ N : ℚ} {K : ℕ} {u : Fin K → E}

lemma SNmap_sum (hu : Orthonormal ℝ u) (c : Fin K → ℝ) :
    SNmap M σ N u (∑ k, c k • u k) = ∑ k, c k • vN M σ N k := by
  unfold SNmap
  apply Finset.sum_congr rfl
  intro j _
  rw [hu.inner_right_fintype c j]

/-- **`eq:SNspectral`**: `S_N u_L = v_L`. -/
theorem SNmap_u (hu : Orthonormal ℝ u) (l : Fin K) : SNmap M σ N u (u l) = vN M σ N l := by
  have := SNmap_sum (M := M) (σ := σ) (N := N) hu (fun k => if k = l then 1 else 0)
  simpa using this

/-- **`prop:SN`, isometry**: `⟨S_N x, S_N y⟩_{2h} = ⟨x, y⟩` on `𝒱_N = span{u_L}`. -/
theorem SNmap_isometry (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (hu : Orthonormal ℝ u) {x y : E} (hx : x ∈ Submodule.span ℝ (Set.range u))
    (hy : y ∈ Submodule.span ℝ (Set.range u)) :
    ipN N (SNmap M σ N u x) (SNmap M σ N u y) = inner ℝ x y := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  obtain ⟨c', rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hy
  rw [SNmap_sum hu, SNmap_sum hu, ipN_sum_vN hA hN hK]
  have := hu.inner_sum c c' Finset.univ
  simpa using this.symm

/-- **`prop:SN`, onto**: `S_N (S_N⁻¹ q) = q` for every `q ∈ ℓ²(𝒳_N, 2h)`. -/
theorem SNmap_SNinv (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (hu : Orthonormal ℝ u) (q : Fin K → ℝ) :
    SNmap M σ N u (SNinv M σ N u q) = q := by
  unfold SNinv
  rw [SNmap_sum hu]
  exact (vN_expansion hA hN hK q).symm

/-- `S_N⁻¹` is a left inverse of `S_N` on `𝒱_N`; with `SNmap_isometry` and `SNmap_SNinv`,
`S_N : 𝒱_N → ℓ²(𝒳_N, 2h)` is unitary (`prop:SN`). -/
theorem SNinv_SNmap (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (hu : Orthonormal ℝ u) {x : E} (hx : x ∈ Submodule.span ℝ (Set.range u)) :
    SNinv M σ N u (SNmap M σ N u x) = x := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  rw [SNmap_sum hu]
  unfold SNinv
  apply Finset.sum_congr rfl
  intro k _
  have : ipN N (vN M σ N k) (∑ l, c l • vN M σ N l) = c k := by
    have := ipN_sum_vN hA hN hK (fun l => if l = k then 1 else 0) c
    have e : (∑ l : Fin K, (if l = k then (1 : ℝ) else 0) • vN M σ N l) = vN M σ N k := by
      simp
    rw [e] at this
    simpa using this
  rw [this]

end Map

/-! ### The operator `𝖧_h` on `ℓ²(𝒳_N)` -/

section Operator

variable {M σ N : ℚ} {K : ℕ}

lemma xLat_injective (hN : 0 < N) (M σ : ℚ) : Function.Injective (xLat M σ N) := by
  intro n m h
  unfold xLat at h
  have hN' : N ≠ 0 := hN.ne'
  have : (n : ℚ) = m := by
    field_simp at h
    linarith
  exact_mod_cast this

/-- A function on the physical lattice, extended by zero to `ℚ`. -/
noncomputable def extLat (M σ N : ℚ) {K : ℕ} (q : Fin K → ℝ) (x : ℚ) : ℝ :=
  ∑ m : Fin K, if xLat M σ N m = x then q m else 0

lemma extLat_lat (hN : 0 < N) (q : Fin K → ℝ) (n : Fin K) :
    extLat M σ N q (xLat M σ N n) = q n := by
  unfold extLat
  rw [Finset.sum_eq_single n]
  · simp
  · intro m _ hm
    have : xLat M σ N m ≠ xLat M σ N n := fun e => hm (Fin.ext (xLat_injective hN M σ e))
    simp [this]
  · intro h; exact absurd (Finset.mem_univ n) h

/-- `𝖧_h` on `ℓ²(𝒳_N)`: the operator `Hh` applied to the zero extension, sampled on the lattice. -/
noncomputable def HhLat (M σ N : ℚ) {K : ℕ} (q : Fin K → ℝ) : Fin K → ℝ := fun n =>
  Hh M σ N (extLat M σ N q) (xLat M σ N n)

/-- `𝖧_h ψ` at a lattice point only involves the values of `ψ` on the lattice. -/
theorem Hh_lat_congr (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|) (ψ φ : ℚ → ℝ)
    (h : ∀ n < K, ψ (xLat M σ N n) = φ (xLat M σ N n)) {n : ℕ} (hn : n < K) :
    Hh M σ N ψ (xLat M σ N n) = Hh M σ N φ (xLat M σ N n) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hU : aMid M σ N (((xLat M σ N n : ℚ) : ℝ) + 1 / (N : ℝ)) * ψ (xLat M σ N n + 2 / N) =
      aMid M σ N (((xLat M σ N n : ℚ) : ℝ) + 1 / (N : ℝ)) * φ (xLat M σ N n + 2 / N) := by
    by_cases h1 : n + 1 < K
    · rw [← xLat_succ, h (n + 1) h1]
    · have hn1 : n = K - 1 := by omega
      have := xLat_top M σ N hN.ne' K hK (by omega)
      rw [← hn1] at this
      rw [this]; simp
  have hD : aMid M σ N (((xLat M σ N n : ℚ) : ℝ) - 1 / (N : ℝ)) * ψ (xLat M σ N n - 2 / N) =
      aMid M σ N (((xLat M σ N n : ℚ) : ℝ) - 1 / (N : ℝ)) * φ (xLat M σ N n - 2 / N) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [xLat_bottom M σ N hN.ne']; simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have e : xLat M σ N (k + 1) - 2 / N = xLat M σ N k := by rw [xLat_succ]; ring
      rw [e, h k (by omega)]
  unfold Hh
  rw [h n hn]
  have := hU
  have := hD
  linear_combination (-1 / (4 * (1 / (N : ℝ)) ^ 2)) * (hU + hD)

/-- `𝖧_h` of a sampled function is the sampled `𝖧_h`. -/
theorem HhLat_sample (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|) (ψ : ℚ → ℝ) (n : Fin K) :
    HhLat M σ N (fun m => ψ (xLat M σ N m)) n = Hh M σ N ψ (xLat M σ N n) := by
  unfold HhLat
  refine Hh_lat_congr hN hK _ _ ?_ n.2
  intro m hm
  exact extLat_lat hN (fun m => ψ (xLat M σ N m)) ⟨m, hm⟩

lemma extLat_sum (c : Fin K → ℝ) (q : Fin K → Fin K → ℝ) (x : ℚ) :
    extLat M σ N (∑ k, c k • q k) x = ∑ k, c k * extLat M σ N (q k) x := by
  unfold extLat
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

lemma Hh_sum (c : Fin K → ℝ) (ψ : Fin K → ℚ → ℝ) (x : ℚ) :
    Hh M σ N (fun y => ∑ k, c k * ψ k y) x = ∑ k, c k * Hh M σ N (ψ k) x := by
  unfold Hh
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma HhLat_sum (c : Fin K → ℝ) (q : Fin K → Fin K → ℝ) :
    HhLat M σ N (∑ k, c k • q k) = ∑ k, c k • HhLat M σ N (q k) := by
  funext n
  unfold HhLat
  have : extLat M σ N (∑ k, c k • q k) = fun y => ∑ k, c k * extLat M σ N (q k) y := by
    funext y; exact extLat_sum c q y
  rw [this, Hh_sum]
  simp

/-- **`𝖧_h v_L = L(L+1) v_L`** on the lattice (`thm:3jspectral`, in the `ℓ²(𝒳_N, 2h)` form). -/
theorem HhLat_vN (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (i : Fin K) : HhLat M σ N (vN M σ N i) = lamN M σ i • vN M σ N i := by
  funext n
  have hsamp := HhLat_sample (M := M) (σ := σ) hN hK
    (fun x => Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) * PhiX (rkN M σ i) M σ N x) n
  have h := (Phi_latEigen hA hN hK i.2).2 n n.2
  have e : Hh M σ N (fun x => Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) *
      PhiX (rkN M σ i) M σ N x) (xLat M σ N n) =
      Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) *
        Hh M σ N (PhiX (rkN M σ i) M σ N) (xLat M σ N n) := by
    unfold Hh; ring
  have h' : Hh M σ N (PhiX (rkN M σ i) M σ N) (xLat M σ N n) =
      rankEig M σ i * PhiX (rkN M σ i) M σ N (xLat M σ N n) := h
  calc HhLat M σ N (vN M σ N i) n = Hh M σ N (fun x => Real.sqrt ((2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2) *
      PhiX (rkN M σ i) M σ N x) (xLat M σ N n) := hsamp
    _ = (lamN M σ i • vN M σ N i) n := by
      rw [e, h']
      simp only [Pi.smul_apply, smul_eq_mul, vN, lamN]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : Fin K → E}

/-- **`eq:SNintertwine`**: if `𝖧₀ u_L = L(L+1) u_L` then `𝖧_h S_N = S_N 𝖧₀` on
`𝒱_N = span{u_L}`. -/
theorem SNmap_intertwine (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|)
    (hu : Orthonormal ℝ u) (H0 : E →ₗ[ℝ] E) (hH0 : ∀ j, H0 (u j) = lamN M σ j • u j) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range u)) :
    HhLat M σ N (SNmap M σ N u x) = SNmap M σ N u (H0 x) := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  have e : H0 (∑ k, c k • u k) = ∑ k, (c k * lamN M σ k) • u k := by
    rw [map_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [map_smul, hH0, smul_smul]
  rw [e, SNmap_sum hu, SNmap_sum hu, HhLat_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [HhLat_vN hA hN hK, smul_smul]

end Operator

/-- info: 'FormalResearch.Racah.vN_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vN_orthonormal

/-- info: 'FormalResearch.Racah.vN_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vN_expansion

/-- info: 'FormalResearch.Racah.SNmap_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SNmap_u

/-- info: 'FormalResearch.Racah.SNmap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SNmap_isometry

/-- info: 'FormalResearch.Racah.SNmap_SNinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SNmap_SNinv

/-- info: 'FormalResearch.Racah.SNinv_SNmap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SNinv_SNmap

/-- info: 'FormalResearch.Racah.SNmap_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SNmap_intertwine

/-- info: 'FormalResearch.Racah.HhLat_vN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HhLat_vN

/-- info: 'FormalResearch.Racah.HhLat_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HhLat_sample

end FormalResearch.Racah
