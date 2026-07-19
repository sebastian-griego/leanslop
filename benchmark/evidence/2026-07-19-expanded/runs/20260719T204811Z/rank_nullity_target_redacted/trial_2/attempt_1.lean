import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Cardinal Submodule Module Function

namespace RankNullity

universe u v v'

variable {K : Type u} {V : Type v} {V₂ : Type v'} [DivisionRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup V₂] [Module K V₂]

/- REQUIRED:
theorem tested_rank_nullity [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V
-/

theorem tested_rank_nullity [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange f)]
  exact Submodule.finrank_quotient_add_finrank (LinearMap.ker f)


theorem benchmark_check_rank_nullity [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
  tested_rank_nullity f

#print axioms benchmark_check_rank_nullity

end RankNullity
