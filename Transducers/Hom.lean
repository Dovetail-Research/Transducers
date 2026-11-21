import Transducers.KernelTheorems
import Transducers.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

open MeasureTheory ProbabilityTheory Kernel ENNReal

variable {D A O A' O' : Type} [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace A'] [MeasurableSpace O']

/-- The kernel of a transducer, with its output split into the observations and the next states
(in that order), so that the next states can be conditioned on the observations. -/
noncomputable def Transducer.Kswap (t : Transducer D A O) :
    MarkovKernel (D → A × t.S) ((D → O) × (D → t.S)) :=
  ⟨t.K.1.map (fun y ↦ (fun d ↦ (y d).2, fun d ↦ (y d).1)), by
    apply IsMarkovKernel.map; fun_prop⟩

variable [Countable D] (t : Transducer D A O) (t' : Transducer D A' O')
  [StandardBorelSpace t.S] [Nonempty t.S]
  [MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)]
  [StandardBorelSpace t'.S] [Nonempty t'.S]
  [MeasurableSpace.CountableOrCountablyGenerated (D → A' × t'.S) (D → O')]

/-- A homomorphism between two transducers. Maps φ, f, g are measurable, and
certain conditions ensure these function represent the transformations between
the maps. All maps are applied pointwise at each index `d : D`. -/
@[ext]
structure Transducer.Hom where
  φ : t.S → t'.S
  hφ : Measurable φ
  f : O → O'
  hf : Measurable f
  g : A → A'
  hg : Measurable g
  compat : t'.K.1.comap (fun x d ↦ Prod.map g φ (x d)) (by fun_prop) =
    t.K.1.map (fun y d ↦ Prod.map φ f (y d))
  markov : t'.Kswap.1.condKernel.comap
      (fun x ↦ (fun d ↦ Prod.map g φ (x.1 d), fun d ↦ f (x.2 d))) (by fun_prop) =
    t.Kswap.1.condKernel.map (fun s d ↦ φ (s d))
  init : t'.p = t.p.map φ

/-- Allow the tactic fun_prop to detect that φ is measurable -/
@[fun_prop]
lemma Transducer.Hom.measurable_φ {t t' : Transducer D A O}
    [StandardBorelSpace t.S] [Nonempty t.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)]
    [StandardBorelSpace t'.S] [Nonempty t'.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t'.S) (D → O)] (h : t.Hom t') :
    Measurable h.φ := h.hφ

/-- A reduction is between the same input and output spaces, with a reduced state space -/
def Transducer.Hom.reduction {t t' : Transducer D A O}
    [StandardBorelSpace t.S] [Nonempty t.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)]
    [StandardBorelSpace t'.S] [Nonempty t'.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t'.S) (D → O)] (h : t.Hom t') :=
  h.φ.Surjective ∧ h.f = id ∧ h.g = id

/-- Specfies whether a transducer is a reduction of another -/
def Transducer.IsReduction (t t' : Transducer D A O)
    [StandardBorelSpace t.S] [Nonempty t.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)]
    [StandardBorelSpace t'.S] [Nonempty t'.S]
    [MeasurableSpace.CountableOrCountablyGenerated (D → A × t'.S) (D → O)] :=
  ∃ (h : t.Hom t'), h.reduction

section Reduction

variable {t t' : Transducer D A O}
  [StandardBorelSpace t.S] [Nonempty t.S]
  [MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)]
  [StandardBorelSpace t'.S] [Nonempty t'.S]
  [MeasurableSpace.CountableOrCountablyGenerated (D → A × t'.S) (D → O)]

/-- Obtain a homomorphism of a reduction -/
noncomputable def Transducer.IsReduction.reduction (h : t.IsReduction t') : t.Hom t' := h.choose

/-- A chosen homomorphism is a reduction -/
lemma Transducer.IsReduction.reduction_spec (h : t.IsReduction t') : h.reduction.reduction :=
  Exists.choose_spec _

/-- Restate the compatability condition for reductions -/
lemma Transducer.IsReduction.compat (h : t.IsReduction t') :
    t'.K.1.comap (fun x d ↦ Prod.map id h.reduction.φ (x d)) (by fun_prop) =
      t.K.1.map (fun y d ↦ Prod.map h.reduction.φ id (y d)) := by
  simpa only [h.reduction_spec.2.1, h.reduction_spec.2.2] using h.reduction.compat

end Reduction

/-
TODO: `Transducer.traj_eq_of_reduction` (reductions preserve trajectories) was stated in terms of
`Transducer.trajKernel` from `Transducers.Traj`, which has not yet been ported to the new
definition of `Transducer`. Restore it (and the `import Transducers.Traj`) once `Traj` is updated.
-/
