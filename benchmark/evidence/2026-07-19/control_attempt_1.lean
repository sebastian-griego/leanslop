import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Control

/- REQUIRED:
theorem tested_shallow_control (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2
-/

theorem tested_shallow_control (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]


#print axioms tested_shallow_control

end Control
