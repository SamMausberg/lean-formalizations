import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Recurrences.CapturePressure
import FormalConjectures.Problems.Erdos.E20.Kernels.LeafStripping

set_option linter.style.openClassical false

open Finset
open scoped BigOperators Classical
open FormalConjectures.Problems.Erdos.E20.Compendium

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace FormalConjectures
namespace Problems
namespace Erdos
namespace E20
namespace Kernels
namespace BridgeLock

variable {Route CutEdge Ground : Type*}
variable [DecidableEq Route] [DecidableEq CutEdge] [DecidableEq Ground]

/-- A finite family of routes together with an explicit cut certificate.

The data is intentionally concrete: rather than assuming a Menger-style theorem, we store a
`firstCut` label for each route and a finite cut set that contains every such label. A route also
carries a trace on a finite window, and every trace is assumed nonempty and contained in the
window.

This is enough to formalize the local BridgeLock argument in the pasted note. -/
structure RouteCutCertificate (Route CutEdge Ground : Type*) where
  routes : Finset Route
  cut : Finset CutEdge
  firstCut : Route → CutEdge
  firstCut_mem : ∀ r ∈ routes, firstCut r ∈ cut
  window : Finset Ground
  trace : Route → Finset Ground
  trace_subset_window : ∀ r ∈ routes, trace r ⊆ window
  trace_nonempty : ∀ r ∈ routes, (trace r).Nonempty

namespace RouteCutCertificate

/-- The routes whose first cut edge is `c`. -/
def routeClass (C : RouteCutCertificate Route CutEdge Ground) (c : CutEdge) : Finset Route :=
  C.routes.filter fun r => C.firstCut r = c

/-- The traces of a fixed route class on the finite window. -/
def routeClassTraces (C : RouteCutCertificate Route CutEdge Ground) (c : CutEdge) :
    Finset (Finset Ground) :=
  (routeClass C c).image C.trace

/-- The route-class mass of a weight function `μ` on the route family. -/
def routeClassMass (C : RouteCutCertificate Route CutEdge Ground) (μ : Route → ℝ)
    (c : CutEdge) : ℝ :=
  ∑ r ∈ routeClass C c, μ r

@[simp] theorem mem_routeClass_iff {C : RouteCutCertificate Route CutEdge Ground}
    {c : CutEdge} {r : Route} :
    r ∈ routeClass C c ↔ r ∈ C.routes ∧ C.firstCut r = c := by
  simp [routeClass]

@[simp] theorem mem_routeClassTraces_iff {C : RouteCutCertificate Route CutEdge Ground}
    {c : CutEdge}
    {T : Finset Ground} :
    T ∈ routeClassTraces C c ↔ ∃ r ∈ routeClass C c, T = C.trace r := by
  constructor
  · intro hT
    rcases Finset.mem_image.mp hT with ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

theorem routes_eq_biUnion_routeClass (C : RouteCutCertificate Route CutEdge Ground) :
    C.routes = C.cut.biUnion (routeClass C) := by
  ext r
  constructor
  · intro hr
    exact Finset.mem_biUnion.mpr
      ⟨C.firstCut r, C.firstCut_mem r hr, by simp [routeClass, hr]⟩
  · intro hr
    rcases Finset.mem_biUnion.mp hr with ⟨c, hc, hrc⟩
    exact (mem_routeClass_iff (C := C) (c := c) (r := r)).1 hrc |>.1

theorem routeClass_disjoint {C : RouteCutCertificate Route CutEdge Ground} {c d : CutEdge}
    (hc : c ∈ C.cut) (hd : d ∈ C.cut) (hcd : c ≠ d) :
    Disjoint (routeClass C c) (routeClass C d) := by
  rw [Finset.disjoint_left]
  intro r hr hd'
  have hrc : C.firstCut r = c := by
    exact (mem_routeClass_iff (C := C) (c := c) (r := r)).mp hr |>.2
  have hrd : C.firstCut r = d := by
    exact (mem_routeClass_iff (C := C) (c := d) (r := r)).mp hd' |>.2
  exact hcd (hrc.symm.trans hrd)

theorem routeClass_pairwiseDisjoint (C : RouteCutCertificate Route CutEdge Ground) :
    Set.PairwiseDisjoint (↑C.cut : Set CutEdge) fun c => routeClass C c := by
  intro c hc d hd hcd
  simpa using routeClass_disjoint (C := C) (c := c) (d := d) hc hd hcd

theorem routeClass_trace_subset_window
    {C : RouteCutCertificate Route CutEdge Ground} {c : CutEdge} {T : Finset Ground}
    (hT : T ∈ routeClassTraces C c) :
    T ⊆ C.window := by
  rcases (mem_routeClassTraces_iff (C := C) (c := c) (T := T)).mp hT with
    ⟨r, hr, rfl⟩
  have hroutes : r ∈ C.routes := (mem_routeClass_iff (C := C) (c := c) (r := r)).mp hr |>.1
  exact C.trace_subset_window r hroutes

theorem routeClass_trace_nonempty
    {C : RouteCutCertificate Route CutEdge Ground} {c : CutEdge} {T : Finset Ground}
    (hT : T ∈ routeClassTraces C c) :
    T.Nonempty := by
  rcases (mem_routeClassTraces_iff (C := C) (c := c) (T := T)).mp hT with
    ⟨r, hr, rfl⟩
  have hroutes : r ∈ C.routes := (mem_routeClass_iff (C := C) (c := c) (r := r)).mp hr |>.1
  exact C.trace_nonempty r hroutes

/-- Each route-class trace family is hit by the whole window.

This is the explicit transversal bound used in the pasted BridgeLock note: we do not invoke any
graph duality here, only the fact that every trace is a nonempty subset of the fixed window. -/
theorem routeClass_trace_has_transversal (C : RouteCutCertificate Route CutEdge Ground)
    (c : CutEdge) :
    ∃ T : Finset Ground, (∀ U ∈ routeClassTraces C c, ¬ Disjoint U T) ∧ T.card ≤ C.window.card := by
  refine ⟨C.window, ?_, le_rfl⟩
  intro U hU
  rcases routeClass_trace_nonempty (C := C) (c := c) hU with ⟨x, hxU⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨x, hxU, routeClass_trace_subset_window (C := C) (c := c) hU hxU⟩

/-- A class transversal family hits all class traces. -/
def ClassTransversalFamily (C : RouteCutCertificate Route CutEdge Ground)
    (T : CutEdge → Finset Ground) : Prop :=
  ∀ c ∈ C.cut, ∀ U ∈ routeClassTraces C c, ¬ Disjoint U (T c)

/-- Unioning class transversals preserves capture and multiplies the size bound by the cut size. -/
theorem biUnion_classTransversal_card_le (C : RouteCutCertificate Route CutEdge Ground)
    (T : CutEdge → Finset Ground)
    (hT : ClassTransversalFamily C T)
    (hcard : ∀ c ∈ C.cut, (T c).card ≤ C.window.card) :
    (∀ U ∈ C.cut.biUnion (routeClassTraces C), ¬ Disjoint U (C.cut.biUnion T)) ∧
      (C.cut.biUnion T).card ≤ C.window.card * C.cut.card := by
  constructor
  · intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨c, hc, hU⟩
    have hnd : ¬ Disjoint U (T c) := hT c hc U hU
    rw [Finset.not_disjoint_iff] at hnd
    rcases hnd with ⟨x, hxU, hxT⟩
    intro hdis
    rw [Finset.disjoint_left] at hdis
    exact hdis hxU (Finset.mem_biUnion.mpr ⟨c, hc, hxT⟩)
  · calc
      (C.cut.biUnion T).card ≤ C.cut.card * C.window.card := by
        exact Finset.card_biUnion_le_card_mul C.cut T C.window.card hcard
      _ = C.window.card * C.cut.card := by
        simp [Nat.mul_comm]

/-- The route-class masses sum to the total mass on the route family. -/
theorem sum_routeClassMass_eq_total (C : RouteCutCertificate Route CutEdge Ground) (μ : Route → ℝ) :
    ∑ c ∈ C.cut, routeClassMass C μ c = ∑ r ∈ C.routes, μ r := by
  have hpairwise : Set.PairwiseDisjoint (↑C.cut : Set CutEdge) fun c => routeClass C c :=
    routeClass_pairwiseDisjoint C
  calc
    ∑ c ∈ C.cut, routeClassMass C μ c = ∑ r ∈ C.cut.biUnion (routeClass C), μ r := by
      simpa [routeClassMass] using
        (Finset.sum_biUnion (s := C.cut) (t := fun c => routeClass C c) (f := μ) hpairwise).symm
    _ = ∑ r ∈ C.routes, μ r := by
      rw [routes_eq_biUnion_routeClass]

/-- The finite mass/capture corollary: some route class carries at least the average mass. -/
theorem exists_routeClass_mass_ge_average
    (C : RouteCutCertificate Route CutEdge Ground) (hcut : C.cut.Nonempty)
    (μ : Route → ℝ) (hμ : IsProbabilityOn C.routes μ) :
    ∃ c ∈ C.cut, (1 / (C.cut.card : ℝ)) ≤ routeClassMass C μ c := by
  by_contra h
  have hlt : ∀ c ∈ C.cut, routeClassMass C μ c < 1 / (C.cut.card : ℝ) := by
    intro c hc
    by_contra hge
    exact h ⟨c, hc, le_of_not_gt hge⟩
  have hsumlt :
      ∑ c ∈ C.cut, routeClassMass C μ c < ∑ c ∈ C.cut, (1 / (C.cut.card : ℝ)) := by
    exact Finset.sum_lt_sum_of_nonempty hcut hlt
  have hsum1 : ∑ c ∈ C.cut, routeClassMass C μ c < 1 := by
    calc
      ∑ c ∈ C.cut, routeClassMass C μ c < ∑ c ∈ C.cut, (1 / (C.cut.card : ℝ)) := hsumlt
      _ = (C.cut.card : ℝ) * (1 / (C.cut.card : ℝ)) := by
        simp [Finset.sum_const]
      _ = 1 := by
        have hcard_ne : (C.cut.card : ℝ) ≠ 0 := by
          exact_mod_cast Finset.card_ne_zero.2 hcut
        simp [div_eq_mul_inv, hcard_ne]
  rw [sum_routeClassMass_eq_total, hμ.2] at hsum1
  exact (lt_irrefl 1 hsum1).elim

/-- The solved-class capture statement that feeds directly into the existing pressure theorem. -/
theorem routeClass_capture (C : RouteCutCertificate Route CutEdge Ground) (hcut : C.cut.Nonempty) :
    UniformSolvedCapture C.routes (fun U : Finset Route => ∃ c ∈ C.cut, U = routeClass C c)
      (1 / (C.cut.card : ℝ)) := by
  intro μ hμ
  obtain ⟨c, hc, hmass⟩ := exists_routeClass_mass_ge_average (C := C) hcut μ hμ
  refine ⟨routeClass C c, ?_, ?_, ?_⟩
  · intro r hr
    exact (mem_routeClass_iff (C := C) (c := c) (r := r)).mp hr |>.1
  · exact ⟨c, hc, rfl⟩
  · simpa [routeClassMass] using hmass

end RouteCutCertificate

/-- An exact bridge class packages the extra route-level data that the pasted notes keep
separate from the cut-certificate data:

* a finite route alphabet and its cut set;
* a distinguished kernel shared by all realizations in the class;
* an exact local bridge witness on every route;
* a finite window trace whose nonemptiness and boundedness are the only facts used by the
  route-class capture argument.

The structure is intentionally conditional.  It does not claim that every class in the project
has such a presentation; it only records the interface needed to formalize the exact bridge
class note without overreaching. -/
structure ExactBridgeClass (Route CutEdge Ground : Type*) where
  certificate : RouteCutCertificate Route CutEdge Ground
  routeEdges : Route → Finset CutEdge
  routeEdges_firstCut_mem : ∀ r ∈ certificate.routes, certificate.firstCut r ∈ routeEdges r
  kernel : Finset Ground
  realization : Route → Finset Ground
  kernel_subset_realization : ∀ r ∈ certificate.routes, kernel ⊆ realization r
  exactFirstCarrier :
    ∀ {r s : Route}, r ∈ certificate.routes → s ∈ certificate.routes →
      ∀ {x : Ground}, x ∈ realization r → x ∈ realization s → x ∉ kernel →
        certificate.firstCut r = certificate.firstCut s

namespace ExactBridgeClass

variable {Route CutEdge Ground : Type*}
variable [DecidableEq Route] [DecidableEq CutEdge] [DecidableEq Ground]

/-- The underlying route-cut certificate obtained by forgetting the extra exact-bridge data. -/
def toRouteCutCertificate (C : ExactBridgeClass Route CutEdge Ground) :
    RouteCutCertificate Route CutEdge Ground :=
  C.certificate

theorem routeEdges_nonempty (C : ExactBridgeClass Route CutEdge Ground)
    {r : Route} (hr : r ∈ C.certificate.routes) :
    (C.routeEdges r).Nonempty := by
  exact ⟨C.certificate.firstCut r, C.routeEdges_firstCut_mem r hr⟩

/-- If two routes meet outside the shared kernel, the exact first-carrier label agrees. -/
theorem exactFirstCarrier_of_mem
    (C : ExactBridgeClass Route CutEdge Ground)
    {r s : Route} (hr : r ∈ C.certificate.routes) (hs : s ∈ C.certificate.routes)
    {x : Ground} (hxr : x ∈ C.realization r) (hxs : x ∈ C.realization s)
    (hxk : x ∉ C.kernel) :
    C.certificate.firstCut r = C.certificate.firstCut s :=
  C.exactFirstCarrier hr hs hxr hxs hxk

/-- Route-edge disjointness forces the realizations to be disjoint outside the shared kernel. -/
theorem realization_sdiff_disjoint_of_routeEdges_disjoint
    (C : ExactBridgeClass Route CutEdge Ground)
    (hdisj : ∀ r ∈ C.certificate.routes, ∀ s ∈ C.certificate.routes, r ≠ s →
      Disjoint (C.routeEdges r) (C.routeEdges s))
    {r s : Route} (hr : r ∈ C.certificate.routes) (hs : s ∈ C.certificate.routes)
    (hneq : r ≠ s) :
    Disjoint (C.realization r \ C.kernel) (C.realization s \ C.kernel) := by
  rw [Finset.disjoint_left]
  intro x hxr hxs
  rcases Finset.mem_sdiff.mp hxr with ⟨hxrR, hxrK⟩
  rcases Finset.mem_sdiff.mp hxs with ⟨hxsR, hxsK⟩
  have hfirst : C.certificate.firstCut r = C.certificate.firstCut s :=
    C.exactFirstCarrier hr hs hxrR hxsR hxrK
  have hmemr : C.certificate.firstCut r ∈ C.routeEdges r :=
    C.routeEdges_firstCut_mem r hr
  have hmems : C.certificate.firstCut s ∈ C.routeEdges s :=
    C.routeEdges_firstCut_mem s hs
  have hmems' : C.certificate.firstCut r ∈ C.routeEdges s := by
    simpa [hfirst] using hmems
  exact (Finset.disjoint_left.mp (hdisj r hr s hs hneq)) hmemr hmems'

/-- A finite set of routes in an exact bridge class forms a sunflower with kernel `kernel`
once the route edges are pairwise disjoint. -/
theorem image_realization_isSunflowerWithKernel
    (C : ExactBridgeClass Route CutEdge Ground)
    (hdisj : ∀ r ∈ C.certificate.routes, ∀ s ∈ C.certificate.routes, r ≠ s →
      Disjoint (C.routeEdges r) (C.routeEdges s))
    (U : Finset Route) (hU : U ⊆ C.certificate.routes) :
    IsSunflowerWithKernel (U.image C.realization) C.kernel := by
  constructor
  · intro e he
    rcases Finset.mem_image.mp he with ⟨r, hr, rfl⟩
    exact C.kernel_subset_realization r (hU hr)
  · intro e he f hf hne
    rcases Finset.mem_image.mp he with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hf with ⟨s, hs, rfl⟩
    by_cases hrs : r = s
    · subst hrs
      exact (hne rfl).elim
    · have hdisj' :=
        C.realization_sdiff_disjoint_of_routeEdges_disjoint hdisj (hU hr) (hU hs) hrs
      have hinter : C.realization r ∩ C.realization s = C.kernel := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_inter.mp hx with ⟨hxr, hxs⟩
          by_cases hxk : x ∈ C.kernel
          · exact hxk
          · have hxr : x ∈ C.realization r \ C.kernel := by
              simp [Finset.mem_sdiff, hxr, hxk]
            have hxs : x ∈ C.realization s \ C.kernel := by
              simp [Finset.mem_sdiff, hxs, hxk]
            exact False.elim <| Finset.disjoint_left.mp hdisj' hxr hxs
        · intro hx
          exact Finset.mem_inter.mpr
            ⟨C.kernel_subset_realization r (hU hr) hx,
              C.kernel_subset_realization s (hU hs) hx⟩
      simpa [hinter]

/-- The exact bridge class still feeds the existing route-cut capture lemma after forgetting
the extra route-level data. -/
theorem routeClass_capture_of_exactBridgeClass
    (C : ExactBridgeClass Route CutEdge Ground) (hcut : C.certificate.cut.Nonempty) :
    UniformSolvedCapture C.certificate.routes
      (fun U : Finset Route =>
        ∃ c ∈ C.certificate.cut, U = RouteCutCertificate.routeClass C.certificate c)
      (1 / (C.certificate.cut.card : ℝ)) := by
  simpa [ExactBridgeClass.toRouteCutCertificate] using
    (RouteCutCertificate.routeClass_capture (C := C.certificate) hcut)

end ExactBridgeClass

end BridgeLock
end Kernels
end E20
end Erdos
end Problems
end FormalConjectures
