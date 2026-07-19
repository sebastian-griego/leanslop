import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth4

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  let G₀ : Submodule ℝ (E × ℝ) :=
    { carrier := {z | ∃ x : f.domain, z = (x.1, f x)}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by simp⟩
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        exact ⟨c • x, by simp⟩ }
  let Good (G : Submodule ℝ (E × ℝ)) : Prop :=
    G₀ ≤ G ∧
      (∀ r : ℝ, (0, r) ∈ G → r = 0) ∧
      ∀ x r, (x, r) ∈ G → r ≤ N x
  have hG₀ : Good G₀ := by
    refine ⟨le_rfl, ?_, ?_⟩
    · intro r hr
      rcases hr with ⟨x, hx⟩
      have hx₀ : x = 0 := by
        apply Subtype.ext
        exact (congrArg Prod.fst hx).symm
      subst x
      simpa using congrArg Prod.snd hx
    · intro x r hr
      rcases hr with ⟨u, hu⟩
      have hx : x = u.1 := congrArg Prod.fst hu
      have hr : r = f u := congrArg Prod.snd hu
      simpa [hx, hr] using hf u
  have hchain :
      ∀ c : Set (Submodule ℝ (E × ℝ)),
        c ⊆ {G | Good G} →
        IsChain (· ≤ ·) c →
        ∃ U ∈ {G | Good G}, ∀ G ∈ c, G ≤ U := by
    intro c hc htot
    by_cases hne : c.Nonempty
    · let U : Submodule ℝ (E × ℝ) :=
        { carrier := {z | ∃ G ∈ c, z ∈ G}
          zero_mem' := by
            rcases hne with ⟨G, hGc⟩
            exact ⟨G, hGc, G.zero_mem⟩
          add_mem' := by
            rintro x y ⟨G, hGc, hx⟩ ⟨H, hHc, hy⟩
            rcases htot.total hGc hHc with hGH | hHG
            · exact ⟨H, hHc, H.add_mem (hGH hx) hy⟩
            · exact ⟨G, hGc, G.add_mem hx (hHG hy)⟩
          smul_mem' := by
            rintro a x ⟨G, hGc, hx⟩
            exact ⟨G, hGc, G.smul_mem a hx⟩ }
      have hU : Good U := by
        rcases hne with ⟨G, hGc⟩
        have hGoodG := hc hGc
        refine ⟨?_, ?_, ?_⟩
        · intro z hz
          exact ⟨G, hGc, hGoodG.1 hz⟩
        · intro r hr
          rcases hr with ⟨H, hHc, hr⟩
          exact (hc hHc).2.1 r hr
        · intro x r hr
          rcases hr with ⟨H, hHc, hr⟩
          exact (hc hHc).2.2 x r hr
      exact ⟨U, hU, by
        intro G hGc z hz
        exact ⟨G, hGc, hz⟩⟩
    · exact ⟨G₀, hG₀, by
        intro G hGc
        exact (hne ⟨G, hGc⟩).elim⟩
  obtain ⟨G, hG, hmax⟩ :=
    zorn_le (s := {G : Submodule ℝ (E × ℝ) | Good G}) hchain
  have hfull : ∀ y : E, ∃ r : ℝ, (y, r) ∈ G := by
    intro y
    by_contra hy
    push_neg at hy
    have hfun : ∀ r : ℝ, (0, r) ∈ G → r = 0 := hG.2.1
    have hdom : ∀ x r, (x, r) ∈ G → r ≤ N x := hG.2.2
    have hcross :
        ∀ {x r z s}, (x, r) ∈ G → (z, s) ∈ G →
          r - N (x - y) ≤ N (z + y) - s := by
      intro x r z s hxr hzs
      have hsum := hdom (x + z) (r + s) (G.add_mem hxr hzs)
      have hsub := N_add (x - y) (z + y)
      have heq : (x - y) + (z + y) = x + z := by abel
      rw [heq] at hsub
      linarith
    let L : Set ℝ :=
      {a | ∃ x r, (x, r) ∈ G ∧ a = r - N (x - y)}
    have hLne : L.Nonempty := by
      refine ⟨-N (-y), 0, 0, G.zero_mem, ?_⟩
      simp
    have hLb : BddAbove L := by
      refine ⟨N y, ?_⟩
      rintro a ⟨x, r, hxr, rfl⟩
      simpa using hcross hxr G.zero_mem
    let c : ℝ := sSup L
    have hlow : ∀ {x r}, (x, r) ∈ G →
        r - N (x - y) ≤ c := by
      intro x r hxr
      exact le_csSup hLb ⟨x, r, hxr, rfl⟩
    have hupp : ∀ {x r}, (x, r) ∈ G →
        c ≤ N (x + y) - r := by
      intro x r hxr
      apply csSup_le hLne
      rintro a ⟨z, s, hzs, rfl⟩
      exact hcross hzs hxr
    let H : Submodule ℝ (E × ℝ) :=
      { carrier :=
          {w | ∃ x r a, (x, r) ∈ G ∧
            w = (x + a • y, r + a * c)}
        zero_mem' := ⟨0, 0, 0, G.zero_mem, by simp⟩
        add_mem' := by
          rintro _ _ ⟨x, r, a, hxr, rfl⟩
            ⟨z, s, b, hzs, rfl⟩
          refine ⟨x + z, r + s, a + b, G.add_mem hxr hzs, ?_⟩
          apply Prod.ext
          · simp [add_smul]
            abel
          · dsimp
            ring
        smul_mem' := by
          rintro t _ ⟨x, r, a, hxr, rfl⟩
          refine ⟨t • x, t * r, t * a, ?_, ?_⟩
          · simpa using G.smul_mem t hxr
          · apply Prod.ext
            · simp [smul_add, mul_smul]
            · dsimp
              ring }
    have hGH : G ≤ H := by
      rintro ⟨x, r⟩ hxr
      exact ⟨x, r, 0, hxr, by simp⟩
    have hGoodH : Good H := by
      refine ⟨hG.1.trans hGH, ?_, ?_⟩
      · intro q hq
        rcases hq with ⟨x, r, a, hxr, hw⟩
        have hxy : 0 = x + a • y := congrArg Prod.fst hw
        have hqr : q = r + a * c := congrArg Prod.snd hw
        by_cases ha : a = 0
        · subst a
          have hx₀ : x = 0 := by simpa using hxy.symm
          have hr₀ : r = 0 := hfun r (by simpa [hx₀] using hxr)
          simpa [hr₀] using hqr
        · have hxeq : x = -(a • y) :=
            eq_neg_of_add_eq_zero_left hxy.symm
          have hxneg : -x = a • y := by simp [hxeq]
          have hm := G.smul_mem a⁻¹ (G.neg_mem hxr)
          have hm' : (y, a⁻¹ * (-r)) ∈ G := by
            simpa [hxneg, smul_smul, ha] using hm
          exact (hy _ hm').elim
      · intro w q hwq
        rcases hwq with ⟨x, r, a, hxr, hw⟩
        have hw₁ : w = x + a • y := congrArg Prod.fst hw
        have hw₂ : q = r + a * c := congrArg Prod.snd hw
        rw [hw₁, hw₂]
        rcases lt_trichotomy a 0 with ha | ha | ha
        · have hb : 0 < -a := neg_pos.mpr ha
          have hs := G.smul_mem (-a)⁻¹ hxr
          have hs' : (((-a)⁻¹) • x, ((-a)⁻¹) * r) ∈ G := by
            simpa using hs
          have hl := hlow hs'
          have heq :
              x + a • y =
                (-a) • (((-a)⁻¹) • x - y) := by
            rw [smul_sub, smul_smul]
            simp [ha.ne]
          have hn :
              N (x + a • y) =
                (-a) * N (((-a)⁻¹) • x - y) := by
            rw [heq]
            exact N_hom (-a) hb _
          have hr : (-a) * (((-a)⁻¹) * r) = r := by
            field_simp [ha.ne]
          linarith
        · subst a
          simpa using hdom x r hxr
        · have hs := G.smul_mem a⁻¹ hxr
          have hs' : (a⁻¹ • x, a⁻¹ * r) ∈ G := by
            simpa using hs
          have hu := hupp hs'
          have heq :
              x + a • y = a • (a⁻¹ • x + y) := by
            rw [smul_add, smul_smul]
            simp [ha.ne]
          have hn :
              N (x + a • y) =
                a * N (a⁻¹ • x + y) := by
            rw [heq]
            exact N_hom a ha _
          have hr : a * (a⁻¹ * r) = r := by
            field_simp [ha.ne]
          linarith
    have hHG : H ≤ G := hmax H hGoodH hGH
    have hyH : (y, c) ∈ H := ⟨0, 0, 1, G.zero_mem, by simp⟩
    exact hy c (hHG hyH)
  let v : E → ℝ := fun x => Classical.choose (hfull x)
  have hv : ∀ x, (x, v x) ∈ G :=
    fun x => Classical.choose_spec (hfull x)
  have huniq : ∀ {x r s}, (x, r) ∈ G → (x, s) ∈ G → r = s := by
    intro x r s hr hs
    have hd := G.sub_mem hr hs
    have hz : (0, r - s) ∈ G := by simpa using hd
    have := hG.2.1 (r - s) hz
    linarith
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := v
      map_add' := by
        intro x y
        exact huniq (G.add_mem (hv x) (hv y)) (hv (x + y))
      map_smul' := by
        intro a x
        exact huniq (by simpa using G.smul_mem a (hv x)) (hv (a • x)) }
  refine ⟨g, ?_, ?_⟩
  · intro x
    apply huniq (hv x)
    apply hG.1
    exact ⟨x, rfl⟩
  · intro x
    exact hG.2.2 x (g x) (hv x)


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth4
