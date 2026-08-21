import Transducers.KernelTheorems
import Transducers.Traj
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

variable {A S O : Type} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]
  {A' S' O' : Type} [MeasurableSpace A'] [MeasurableSpace S'] [MeasurableSpace O']
  [StandardBorelSpace S] [Nonempty S] [MeasurableSpace.CountableOrCountablyGenerated (A × S) O]
  [StandardBorelSpace S'] [Nonempty S'] [MeasurableSpace.CountableOrCountablyGenerated (A' × S') O']
  (t : Transducer A S O) (t' : Transducer A' S' O')

open MeasureTheory ProbabilityTheory Kernel ENNReal

/-- A homomorphism between two transducers. Maps φ, f, g are measurable, and
certain conditions ensure these function represent the transformations between
the maps -/
@[ext]
structure Transducer.Hom where
  φ : S → S'
  hφ : Measurable φ
  f : O → O'
  hf : Measurable f
  g : A → A'
  hg : Measurable g
  compat : ∀ n, (t'.K n).1.comap (Prod.map g φ) (by fun_prop) = (t.K n).1.map (Prod.map φ f)
  markov : ∀ n, ((t'.K n).1.swapRight.condKernel).comap (Prod.map (Prod.map g φ) f) (by fun_prop) =
                (t.K n).1.swapRight.condKernel.map φ
  init : t'.p = t.p.map φ

variable [MeasurableSpace.CountableOrCountablyGenerated (A × S') O]

/-- Allow the tactic fun_prop to detect that φ is measurable -/
@[fun_prop]
lemma Transducer.Hom.measurable_φ {t : Transducer A S O} {t' : Transducer A S' O} (h : t.Hom t') :
    Measurable h.φ := h.hφ

/-- A reduction is between the same input and output spaces, with a reduced state space -/
def Transducer.Hom.reduction {t : Transducer A S O} {t' : Transducer A S' O} (h : t.Hom t') :=
  h.φ.Surjective ∧ h.f = id ∧ h.g = id

/-- Specfies whether a transducer is a reduction of another -/
def Transducer.IsReduction (t : Transducer A S O) (t' : Transducer A S' O) :=
    ∃ (h : t.Hom t'), h.reduction

/-- Obtain a homomorphism of a reduction -/
noncomputable def Transducer.IsReduction.reduction {t : Transducer A S O} {t' : Transducer A S' O}
    (h : t.IsReduction t') := h.choose

/-- A chosen homomorphism is a reduction -/
lemma Transducer.IsReduction.reduction_spec {t : Transducer A S O} {t' : Transducer A S' O}
    (h : t.IsReduction t') : h.reduction.reduction := Exists.choose_spec _

/-- Restate the compatability condition for reductions -/
lemma Transducer.IsReduction.compat {t : Transducer A S O} {t' : Transducer A S' O}
    (h : t.IsReduction t') : ∀ n, ((t'.K n).1.comap (Prod.map id h.reduction.φ) (by fun_prop)) =
      (t.K n).1.map (Prod.map h.reduction.φ id) := by
  simpa only [h.reduction_spec.2.1, h.reduction_spec.2.2] using h.reduction.compat

set_option linter.style.multiGoal false in
/-- The trajectory of a reduction is preserved -/
theorem Transducer.traj_eq_of_reduction {t : Transducer A S O} {t' : Transducer A S' O}
    (h : t.IsReduction t') :
    ∀ n, (t.trajKernel n).1.map (Prod.map h.reduction.φ id) =
    (t'.trajKernel n).1.comap (Prod.map id h.reduction.φ) (by fun_prop) := by
  intro n
  induction n with
  | zero =>
    simp only [trajKernel]
    rw [deterministic_map, deterministic_comap]
    congr 1
    fun_prop
  | succ n hn =>
    ext f s hs
    rw [map_apply', comap_apply, trajProb_apply, trajProb_apply]
    conv =>
      enter [2, 1]
      tactic =>
        convert Eq.refl ((t'.trajKernel n).1.comap (Prod.map id h.reduction.φ)
          (by fun_prop) (Fin.init f.1, f.2))
        rfl
    rw [← hn, map_apply, MeasureTheory.lintegral_map']
    congr with x
    conv =>
      enter [2, 1]
      tactic =>
        convert Eq.refl ((t'.K n).1.comap (Prod.map id h.reduction.φ) (by fun_prop)
          (f.1 (Fin.last _), x.1))
        rfl
    rw [h.compat, map_apply']
    rfl
    any_goals apply measurableSet_preimage
    any_goals fun_prop
    any_goals exact hs
    apply Measurable.aemeasurable
    refine measurable_kernel_prodMk_left (κ := (t'.K n).1.comap (fun (s : S' × (Fin n → O)) ↦
      (f.1 (Fin.last _), s.1)) (by fun_prop)) (t := (fun y ↦ (y.2.1,
        (MeasurableEquiv.piFinSuccAbove (fun x ↦ O) (Fin.last n)).symm (y.2.2, y.1.2))) ⁻¹' s) ?_
    apply measurableSet_preimage
    fun_prop
    exact hs
