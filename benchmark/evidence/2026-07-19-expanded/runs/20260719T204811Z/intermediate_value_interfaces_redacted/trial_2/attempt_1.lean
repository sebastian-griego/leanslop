import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Connected.TotallyDisconnected

open Filter OrderDual TopologicalSpace Function Set
open scoped Topology Filter Interval

namespace IntermediateValue

universe u v

variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α]
  [TopologicalSpace α] [OrderClosedTopology α]

/- REQUIRED:
theorem tested_intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s
-/

theorem tested_intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s := by
  exact (hs.image f hf).ordConnected.out
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩


theorem benchmark_check_intermediate_value {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α}
    (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  tested_intermediate_value hs ha hb hf

#print axioms benchmark_check_intermediate_value

end IntermediateValue
