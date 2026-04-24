import FormalConjectures.Problems.Erdos.E61.RootedP4

/-!
# Sauer-Shelah compression for crossing traces

This file packages the VC-dimension step in `cor:star-compress` from
`eh_forum_trimmed_v9.tex`.  The graph-specific input is kept as an explicit
hypothesis: every set shattered by the crossing-trace family is one of the
allowed rectangle/star-forest patterns.  The conclusion is the checked
Sauer-Shelah binomial bound.
-/

namespace Erdos61

open Finset

/--
Sauer-Shelah in the form used by `cor:star-compress`.

If a finite set family on a finite ground type shatters no set of size at least
`t`, then its size is bounded by the usual binomial sum up to `t - 1`.
-/
theorem sauer_shelah_no_large_shattered
    {ε : Type*} [DecidableEq ε] [Fintype ε]
    (𝒞 : Finset (Finset ε)) {t : ℕ}
    (hno : ∀ F : Finset ε, 𝒞.Shatters F → F.card < t) :
    𝒞.card ≤ ∑ k ∈ Iic (t - 1), (Fintype.card ε).choose k := by
  classical
  have hvc : 𝒞.vcDim ≤ t - 1 := by
    rw [Finset.vcDim]
    refine Finset.sup_le ?_
    intro F hF
    have hshatter : 𝒞.Shatters F := (Finset.mem_shatterer.mp hF)
    exact (Nat.lt_iff_le_pred (by
      by_contra ht
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
      have hlt := hno F hshatter
      omega)).mp (hno F hshatter)
  calc
    𝒞.card ≤ 𝒞.shatterer.card := Finset.card_le_card_shatterer 𝒞
    _ ≤ ∑ k ∈ Iic 𝒞.vcDim, (Fintype.card ε).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Iic (t - 1), (Fintype.card ε).choose k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.Iic_subset_Iic).mpr hvc)
        (by intro k _hk _hnot; exact Nat.zero_le _)

/--
Compression corollary for crossing traces, isolated from the graph-specific
star-forest characterization.

The hypothesis `hrect` is the checked interface to `thm:star-forest`: every set
shattered by the actual crossing-trace family is also shattered by the full
rectangle system, hence is an allowed pattern.  The hypothesis `hno` says that
no allowed pattern with `t` edges is shattered.
-/
theorem star_compress_abstract
    {ε : Type*} [DecidableEq ε] [Fintype ε]
    (𝒞 : Finset (Finset ε)) (Allowed : Finset ε → Prop) {t : ℕ}
    (hrect : ∀ F : Finset ε, 𝒞.Shatters F → Allowed F)
    (hno : ∀ F : Finset ε, Allowed F → F.card = t → ¬ 𝒞.Shatters F) :
    𝒞.card ≤ ∑ k ∈ Iic (t - 1), (Fintype.card ε).choose k := by
  classical
  refine sauer_shelah_no_large_shattered 𝒞 ?_
  intro F hF
  by_contra hnot
  have ht_le : t ≤ F.card := Nat.le_of_not_gt hnot
  rcases exists_subset_card_eq ht_le with ⟨F₀, hF₀sub, hF₀card⟩
  have hF₀shatter : 𝒞.Shatters F₀ := Finset.Shatters.mono_right hF₀sub hF
  exact hno F₀ (hrect F₀ hF₀shatter) hF₀card hF₀shatter

end Erdos61
