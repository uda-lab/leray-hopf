import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Blow-up lower bound (algebraic schema)

**Branch A scaffold.** A self-contained, PDE-free algebraic implication of the kind
used in blow-up lower bounds: a local-lifespan estimate forces a lower bound on the
blow-up quantity `N`. This is Branch A of the original roadmap (`docs/archive/milestone.md`,
archived, historical), independent of the main existence spine.

**Hypothesis:** the remaining lifespan from `t` is *at least* `C / N(t)²`, i.e.
`C / N(t)² ≤ T - t`. This says the solution cannot blow up sooner than `C/N²`.

**Conclusion:** rearranging gives `N(t) ≥ √(C/(T-t))`, equivalently
`1 / N(t) ≤ √((T-t)/C)` — a genuine **lower** bound on `N(t)`.
-/

namespace LerayHopf

/-- From a local-lifespan lower bound `C / N(t)² ≤ T - t` (with `C > 0` and `N` positive
on `(-∞, T)`), the blow-up quantity satisfies the lower bound `N(t) ≥ √(C/(T-t))`,
equivalently `1 / N(t) ≤ √((T-t)/C)`. -/
theorem lower_bound_from_inverse_square_lifespan
    (N : ℝ → ℝ) (T C : ℝ) (hC : 0 < C)
    (hNpos : ∀ t, t < T → 0 < N t)
    (h : ∀ t, t < T → C / (N t) ^ 2 ≤ T - t) :
    ∀ t, t < T → 1 / N t ≤ Real.sqrt ((T - t) / C) := by
  intro t ht
  have hNt : 0 < N t := hNpos t ht
  have hNt2 : 0 < (N t) ^ 2 := pow_pos hNt 2
  -- Rearrange the lifespan bound `C / N t ^ 2 ≤ T - t` into `(1 / N t) ^ 2 ≤ (T - t) / C`.
  have key : C ≤ (T - t) * (N t) ^ 2 := (div_le_iff₀ hNt2).mp (h t ht)
  have hsq : (1 / N t) ^ 2 ≤ (T - t) / C := by
    rw [div_pow, one_pow, div_le_div_iff₀ hNt2 hC, one_mul]
    exact key
  -- Take square roots.
  calc 1 / N t
      = Real.sqrt ((1 / N t) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((T - t) / C) := Real.sqrt_le_sqrt hsq

end LerayHopf
