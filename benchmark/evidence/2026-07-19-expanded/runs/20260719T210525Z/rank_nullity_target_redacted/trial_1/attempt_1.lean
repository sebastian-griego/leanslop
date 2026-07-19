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
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f


theorem benchmark_check_rank_nullity [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
  tested_rank_nullity f

#print axioms benchmark_check_rank_nullity

end RankNullity
