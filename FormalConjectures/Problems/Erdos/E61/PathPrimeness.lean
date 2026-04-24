import FormalConjectures.Problems.Erdos.E61.SafeProfiles

/-!
# Path primeness infrastructure

This file builds reusable checked lemmas toward the path-primeness ingredient
used in the safe-profile section.  The main result here is that a proper
homogeneous finite subset of a path has at most two vertices.
-/

namespace Erdos61

open Finset

/-- Any finite set contained in the neighborhood of one path vertex has size at most two. -/
theorem pathGraph_neighbor_finset_card_le_two {n : ℕ} (y : Fin n) (X : Finset (Fin n))
    (hX : ∀ x ∈ X, (SimpleGraph.pathGraph n).Adj y x) :
    X.card ≤ 2 := by
  classical
  let side : Fin n → Bool := fun x => decide (y.val + 1 = x.val)
  have hinj : Set.InjOn side X := by
    intro x hx z hz hside
    have hxadj := hX x hx
    have hzadj := hX z hz
    rw [SimpleGraph.pathGraph_adj] at hxadj hzadj
    dsimp [side] at hside
    by_cases hxright : y.val + 1 = x.val
    · have hzright : y.val + 1 = z.val := by
        have hbool : decide (y.val + 1 = z.val) = true := by
          simpa only [hxright, decide_true] using hside.symm
        exact of_decide_eq_true hbool
      exact Fin.ext (hxright.symm.trans hzright)
    · have hzxnot : ¬ y.val + 1 = z.val := by
        by_contra hzright
        have hbool : decide (y.val + 1 = x.val) = true := by
          simpa only [hzright, decide_true] using hside
        exact hxright (of_decide_eq_true hbool)
      rcases hxadj with hxright' | hxleft
      · exact False.elim (hxright hxright')
      rcases hzadj with hzright' | hzleft
      · exact False.elim (hzxnot hzright')
      · exact Fin.ext (by omega)
  calc
    X.card ≤ (univ : Finset Bool).card :=
      card_le_card_of_injOn side (by intro x _hx; exact mem_univ (side x)) hinj
    _ = 2 := by simp

/--
In a preconnected graph, any nonempty proper vertex set has an adjacent boundary
pair from the set to its complement.
-/
theorem exists_boundary_adj_of_preconnected {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (X : Set V) (hne : X.Nonempty) (hproper : ∃ v, v ∉ X) :
    ∃ x ∈ X, ∃ y ∉ X, G.Adj x y := by
  rcases hne with ⟨u, huX⟩
  rcases hproper with ⟨v, hvX⟩
  rcases hG u v with ⟨p⟩
  rcases p.exists_boundary_dart X huX hvX with ⟨d, _hd, hfst, hsnd⟩
  exact ⟨d.fst, hfst, d.snd, hsnd, d.adj⟩

/--
Toward path primeness: a proper homogeneous finite subset of a path has at most
two vertices.
-/
theorem pathGraph_homogeneous_proper_finset_card_le_two {n : ℕ}
    (X : Finset (Fin n))
    (hhom : HomogeneousSet (SimpleGraph.pathGraph n) (X : Set (Fin n)))
    (hne : X.Nonempty) (hproper : ∃ v : Fin n, v ∉ X) :
    X.card ≤ 2 := by
  rcases exists_boundary_adj_of_preconnected (SimpleGraph.pathGraph_preconnected n)
      (X : Set (Fin n)) (by simpa using hne) hproper with
    ⟨x, hxX, y, hyX, hxy⟩
  rcases hhom y hyX with hcomplete | hanti
  · exact pathGraph_neighbor_finset_card_le_two y X (by
      intro z hz
      exact hcomplete z hz)
  · exact False.elim (hanti x hxX hxy.symm)

/--
In a path on at least four vertices, every nonempty proper homogeneous finite
set is a singleton.
-/
theorem pathGraph_homogeneous_proper_finset_card_le_one {n : ℕ} (hn : 4 ≤ n)
    (X : Finset (Fin n))
    (hhom : HomogeneousSet (SimpleGraph.pathGraph n) (X : Set (Fin n)))
    (hne : X.Nonempty) (hproper : ∃ v : Fin n, v ∉ X) :
    X.card ≤ 1 := by
  classical
  have hle_two := pathGraph_homogeneous_proper_finset_card_le_two X hhom hne hproper
  by_contra hnot
  have hcard : X.card = 2 := by omega
  rcases exists_boundary_adj_of_preconnected (SimpleGraph.pathGraph_preconnected n)
      (X : Set (Fin n)) (by simpa using hne) hproper with
    ⟨x, hxX, y, hyX, hxy⟩
  rcases hhom y hyX with hcomplete | hanti
  · rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, hXeq⟩
    subst X
    have ha_adj : (SimpleGraph.pathGraph n).Adj y a := hcomplete a (by simp)
    have hb_adj : (SimpleGraph.pathGraph n).Adj y b := hcomplete b (by simp)
    rw [SimpleGraph.pathGraph_adj] at ha_adj hb_adj
    have hbad {l r : Fin n}
        (hlX : l ∈ ({a, b} : Finset (Fin n)))
        (hrX : r ∈ ({a, b} : Finset (Fin n)))
        (ha_lr : a = l ∨ a = r) (hb_lr : b = l ∨ b = r)
        (hl : l.val + 1 = y.val) (hr : y.val + 1 = r.val) : False := by
      by_cases hyright : y.val + 2 < n
      · let t : Fin n := ⟨y.val + 2, hyright⟩
        have ht_ne_l : t ≠ l := by
          intro htl
          have hv := congrArg Fin.val htl
          simp [t] at hv
          omega
        have ht_ne_r : t ≠ r := by
          intro htr
          have hv := congrArg Fin.val htr
          simp [t] at hv
          omega
        have htX : t ∉ (({a, b} : Finset (Fin n)) : Set (Fin n)) := by
          intro ht
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with hta | htb
          · rcases ha_lr with ha | ha
            · exact ht_ne_l (by rw [hta, ha])
            · exact ht_ne_r (by rw [hta, ha])
          · rcases hb_lr with hb | hb
            · exact ht_ne_l (by rw [htb, hb])
            · exact ht_ne_r (by rw [htb, hb])
        have htr : (SimpleGraph.pathGraph n).Adj t r := by
          rw [SimpleGraph.pathGraph_adj]
          right
          simp [t]
          omega
        have hnot_tl : ¬ (SimpleGraph.pathGraph n).Adj t l := by
          rw [SimpleGraph.pathGraph_adj]
          intro htl
          rcases htl with htl | htl <;> simp [t] at htl <;> omega
        rcases hhom t htX with ht_complete | ht_anti
        · exact hnot_tl (ht_complete l (by simpa using hlX))
        · exact ht_anti r (by simpa using hrX) htr
      · let t : Fin n := ⟨y.val - 2, by omega⟩
        have ht_ne_l : t ≠ l := by
          intro htl
          have hv := congrArg Fin.val htl
          simp [t] at hv
          omega
        have ht_ne_r : t ≠ r := by
          intro htr
          have hv := congrArg Fin.val htr
          simp [t] at hv
          omega
        have htX : t ∉ (({a, b} : Finset (Fin n)) : Set (Fin n)) := by
          intro ht
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with hta | htb
          · rcases ha_lr with ha | ha
            · exact ht_ne_l (by rw [hta, ha])
            · exact ht_ne_r (by rw [hta, ha])
          · rcases hb_lr with hb | hb
            · exact ht_ne_l (by rw [htb, hb])
            · exact ht_ne_r (by rw [htb, hb])
        have htl : (SimpleGraph.pathGraph n).Adj t l := by
          rw [SimpleGraph.pathGraph_adj]
          left
          simp [t]
          omega
        have hnot_tr : ¬ (SimpleGraph.pathGraph n).Adj t r := by
          rw [SimpleGraph.pathGraph_adj]
          intro htr
          rcases htr with htr | htr <;> simp [t] at htr <;> omega
        rcases hhom t htX with ht_complete | ht_anti
        · exact hnot_tr (ht_complete r (by simpa using hrX))
        · exact ht_anti l (by simpa using hlX) htl
    rcases ha_adj with ha_right | ha_left <;>
      rcases hb_adj with hb_right | hb_left
    · exact hab (Fin.ext (by omega))
    · exact hbad (l := b) (r := a) (by simp) (by simp)
        (Or.inr rfl) (Or.inl rfl) hb_left ha_right
    · exact hbad (l := a) (r := b) (by simp) (by simp)
        (Or.inl rfl) (Or.inr rfl) ha_left hb_right
    · exact hab (Fin.ext (by omega))
  · exact False.elim (hanti x hxX hxy.symm)

/-- Proper homogeneous subsets of a path on at least four vertices are subsingletons. -/
theorem pathGraph_homogeneous_proper_set_subsingleton {n : ℕ} (hn : 4 ≤ n)
    {X : Set (Fin n)}
    (hhom : HomogeneousSet (SimpleGraph.pathGraph n) X)
    (hne : X.Nonempty) (hproper : ∃ v : Fin n, v ∉ X) :
    X.Subsingleton := by
  classical
  let Xf : Finset (Fin n) := Finset.univ.filter fun v => v ∈ X
  have hXf : ∀ v : Fin n, v ∈ Xf ↔ v ∈ X := by
    intro v
    simp [Xf]
  have hhomf : HomogeneousSet (SimpleGraph.pathGraph n) (Xf : Set (Fin n)) := by
    intro v hv
    have hvX : v ∉ X := by
      intro hv'
      exact hv ((hXf v).mpr hv')
    rcases hhom v hvX with hcomplete | hanti
    · left
      intro x hx
      exact hcomplete x ((hXf x).mp hx)
    · right
      intro x hx
      exact hanti x ((hXf x).mp hx)
  have hnef : Xf.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨x, (hXf x).mpr hx⟩
  have hproperf : ∃ v : Fin n, v ∉ Xf := by
    rcases hproper with ⟨v, hv⟩
    exact ⟨v, by
      intro hvf
      exact hv ((hXf v).mp hvf)⟩
  have hle := pathGraph_homogeneous_proper_finset_card_le_one hn Xf hhomf hnef hproperf
  intro a ha b hb
  exact (Finset.card_le_one.mp hle) a ((hXf a).mpr ha) b ((hXf b).mpr hb)

/-- A path on at least four vertices is prime for finite homogeneous sets. -/
theorem pathGraph_prime {n : ℕ} (hn : 4 ≤ n) :
    PrimeGraph (SimpleGraph.pathGraph n) := by
  intro X hhom
  by_cases hne : X.Nonempty
  · by_cases hproper : ∃ v : Fin n, v ∉ X
    · right
      left
      rcases hne with ⟨a, ha⟩
      have hsub := pathGraph_homogeneous_proper_set_subsingleton hn hhom ⟨a, ha⟩ hproper
      refine ⟨a, ?_⟩
      ext v
      constructor
      · intro hv
        have hva : v = a := hsub hv ha
        rw [Set.mem_singleton_iff]
        exact hva
      · intro hv
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        exact ha
    · right
      right
      intro v
      by_contra hv
      exact hproper ⟨v, hv⟩
  · left
    intro v hv
    exact hne ⟨v, hv⟩

/-- Version of path primeness with the indexing used in the profile section. -/
theorem pathGraph_prime_add_two (n : ℕ) (hn : 2 ≤ n) :
    PrimeGraph (SimpleGraph.pathGraph (n + 2)) :=
  pathGraph_prime (n := n + 2) (by omega)

/--
Path-specialized singleton safe-profile substitution: the path-prime hypothesis
from `singleton_safe_profile_substitution` is discharged by the checked
primeness of paths on at least four vertices.
-/
theorem singleton_safe_profile_substitution_for_paths
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (n + 1)))
    (hS : S ≠ ({0} : Finset (Fin (n + 1))) ∧
      S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))))
    {VB : Type*} (B : SimpleGraph VB)
    (hB : InducedFree (SimpleGraph.pathGraph (n + 2)) B) :
    InducedFree (SimpleGraph.pathGraph (n + 2))
      (substituteVertex (oneVertexExtension S) B (none : Option (Fin (n + 1)))) := by
  exact singleton_safe_profile_substitution n hn S hS B
    (pathGraph_prime_add_two n hn) hB

/-- Version of path primeness with the indexing used in terminal path sections. -/
theorem pathGraph_prime_add_four (n : ℕ) :
    PrimeGraph (SimpleGraph.pathGraph (n + 4)) :=
  pathGraph_prime (n := n + 4) (by omega)

end Erdos61
