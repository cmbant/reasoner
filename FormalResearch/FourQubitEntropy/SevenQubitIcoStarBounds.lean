import FormalResearch.FourQubitEntropy.SevenQubitMajorantDegreeSeven

/-!
# The bound `1/32 < x_* < 37/524` of `prop:entropy-seven-stationarity`

`prop:entropy-seven-stationarity` (`seven_qubit_entropy_local.tex`) states, for the maximiser `x_*` of the
mean three-qubit entropy `E₃` on the icosahedral family, `1/32 < x_* < 37/524`, hence
`x_*/u_* ∈ (1, 37/15)` with `u_* = (1-2x_*)/30`.

Here `x_*` is the unique maximiser of `E3` on `[0,1/2]` (`E3_unique_max`, which gives `0 < x_* < 37/524`).
`maximiser_gt_one_thirtysecond` (`SevenQubitMajorantDegreeSeven`) gives `1/32 < x_*`. Proved here: the ratio
statement. Not formalized: the closed equation `2³²(1-2x_*)¹⁵ = 3⁸(1+8x_*)⁸(1+28x_*)⁷` of the same
proposition and its full-space stationarity (the integer contraction identities ES-1).
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Set

theorem star_bounds : ∃ c, 1 / 32 < c ∧ c < 37 / 524 ∧
    (∀ y ∈ Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧ 1 < c / u c ∧ c / u c < 37 / 15 := by
  obtain ⟨c, hc0, hc1, hmax, -, -⟩ := E3_unique_max
  have h32 : 1 / 32 < c :=
    MajorantDegree.maximiser_gt_one_thirtysecond hc0 hc1 fun y hy => by
      by_cases h : y = c
      · rw [h]
      · exact (hmax y hy h).le
  have hu : 0 < u c := u_pos (by linarith)
  refine ⟨c, h32, hc1, hmax, ?_, ?_⟩
  · rw [lt_div_iff₀ hu]; unfold u; linarith
  · rw [div_lt_iff₀ hu]; unfold u; linarith

end FormalResearch.FourQubitEntropy.SevenQubitIco
