import Transducers.KernelTheorems
import Transducers.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Order.Antisymmetrization

/-!
# Homomorphisms and reductions of transducers

* `Transducer.Hom t t'`: a homomorphism of transducers, with identities `Transducer.Hom.id` and
  composition `Transducer.Hom.comp`.
* `Transducer.IsReduction t t'`: `t'` is obtained from `t` by a surjective map of state spaces.
* `RegularTransducer D A O`: transducers satisfying the regularity assumptions needed for
  conditional kernels, preordered by `s ≤ t ↔ t.IsReduction s`.
* `RegularTransducer.Equiv D A O`: the antisymmetrization of this preorder, i.e. transducers up to
  mutual reduction, which is a partial order.
-/

open MeasureTheory ProbabilityTheory Kernel ENNReal

variable {D A O A' O' A'' O'' : Type} [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace A'] [MeasurableSpace O'] [MeasurableSpace A''] [MeasurableSpace O'']

/-- The kernel of a transducer, with its output split into the observations and the next states
(in that order), so that the next states can be conditioned on the observations. -/
noncomputable def Transducer.Kswap (t : Transducer D A O) :
    MarkovKernel (D → A × t.S) ((D → O) × (D → t.S)) :=
  ⟨t.K.1.map (fun y ↦ (fun d ↦ (y d).2, fun d ↦ (y d).1)), by
    apply IsMarkovKernel.map; fun_prop⟩

/-- The regularity assumptions under which the next states of a transducer can be conditioned on
its observations. -/
class Transducer.Regular (t : Transducer D A O) : Prop where
  standardBorelSpace : StandardBorelSpace t.S
  nonempty : Nonempty t.S
  countableOrCountablyGenerated :
    MeasurableSpace.CountableOrCountablyGenerated (D → A × t.S) (D → O)

attribute [instance] Transducer.Regular.standardBorelSpace Transducer.Regular.nonempty
  Transducer.Regular.countableOrCountablyGenerated

variable [Countable D]
  (t : Transducer D A O) (t' : Transducer D A' O') (t'' : Transducer D A'' O'')
  [t.Regular] [t'.Regular] [t''.Regular]

/-- A homomorphism between two transducers. Maps φ, f, g are measurable, and
certain conditions ensure these function represent the transformations between
the maps. All maps are applied pointwise at each index `d : D`.

* `compat`: pushing the outputs of `t` forward along `φ` and `f` gives the outputs of `t'` on the
  translated inputs.
* `markov`: for every input, and almost every observation, the conditional law of the next states
  of `t'` given the translated observation is the pushforward along `φ` of that of `t`. Since
  conditional kernels are only unique almost everywhere, this does not depend on the choice made
  by `condKernel`. -/
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
  markov : ∀ x, ∀ᵐ o ∂(t.Kswap.1 x).map Prod.fst,
    t'.Kswap.1.condKernel (fun d ↦ Prod.map g φ (x d), fun d ↦ f (o d)) =
      (t.Kswap.1.condKernel (x, o)).map (fun s d ↦ φ (s d))
  init : t'.p = t.p.map φ

namespace Transducer.Hom

variable {t t' t''}

/-- Allow the tactic fun_prop to detect that φ is measurable -/
@[fun_prop]
lemma measurable_φ (h : t.Hom t') : Measurable h.φ := h.hφ

@[fun_prop]
lemma measurable_f (h : t.Hom t') : Measurable h.f := h.hf

@[fun_prop]
lemma measurable_g (h : t.Hom t') : Measurable h.g := h.hg

/-- A homomorphism maps the law of the observations of `t` to that of `t'`. -/
lemma map_obs (h : t.Hom t') (x : D → A × t.S) :
    ((t.Kswap.1 x).map Prod.fst).map (fun o d ↦ h.f (o d)) =
      (t'.Kswap.1 (fun d ↦ Prod.map h.g h.φ (x d))).map Prod.fst := by
  have hx : t'.K.1 (fun d ↦ Prod.map h.g h.φ (x d)) =
      (t.K.1 x).map (fun (y : D → t.S × O) d ↦ Prod.map h.φ h.f (y d)) := by
    have := congrArg (fun k ↦ k x) h.compat
    rwa [comap_apply, map_apply _ (by fun_prop)] at this
  simp only [Transducer.Kswap]
  rw [map_apply _ (by fun_prop), map_apply _ (by fun_prop), hx]
  repeat rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable (t) in
/-- The identity homomorphism. -/
protected def id : t.Hom t where
  φ := _root_.id
  hφ := measurable_id
  f := _root_.id
  hf := measurable_id
  g := _root_.id
  hg := measurable_id
  compat := by
    change t.K.1.comap _root_.id measurable_id = t.K.1.map _root_.id
    rw [comap_id, map_id]
  markov _ := Filter.Eventually.of_forall fun _ ↦ Measure.map_id.symm
  init := Measure.map_id.symm

/-- The composition of two homomorphisms. -/
def comp (h' : t'.Hom t'') (h : t.Hom t') : t.Hom t'' where
  φ := h'.φ ∘ h.φ
  hφ := h'.hφ.comp h.hφ
  f := h'.f ∘ h.f
  hf := h'.hf.comp h.hf
  g := h'.g ∘ h.g
  hg := h'.hg.comp h.hg
  compat := by
    calc t''.K.1.comap (fun x d ↦ Prod.map (h'.g ∘ h.g) (h'.φ ∘ h.φ) (x d)) _
        = (t''.K.1.comap (fun x d ↦ Prod.map h'.g h'.φ (x d)) (by fun_prop)).comap
            (fun x d ↦ Prod.map h.g h.φ (x d)) (by fun_prop) := rfl
      _ = (t'.K.1.comap (fun x d ↦ Prod.map h.g h.φ (x d)) (by fun_prop)).map
            (fun y d ↦ Prod.map h'.φ h'.f (y d)) := by
        rw [h'.compat, comap_map_comm _ _ (by fun_prop)]
      _ = t.K.1.map (fun y d ↦ Prod.map (h'.φ ∘ h.φ) (h'.f ∘ h.f) (y d)) := by
        rw [h.compat, ← map_comp_right _ (by fun_prop) (by fun_prop)]
        rfl
  markov x := by
    have h₂ : ∀ᵐ o ∂(t.Kswap.1 x).map Prod.fst,
        t''.Kswap.1.condKernel (fun d ↦ Prod.map h'.g h'.φ (Prod.map h.g h.φ (x d)),
          fun d ↦ h'.f (h.f (o d))) =
        (t'.Kswap.1.condKernel (fun d ↦ Prod.map h.g h.φ (x d), fun d ↦ h.f (o d))).map
          (fun s d ↦ h'.φ (s d)) := by
      refine ae_of_ae_map (f := fun (o : D → O) d ↦ h.f (o d))
        (p := fun o' ↦ t''.Kswap.1.condKernel
          (fun d ↦ Prod.map h'.g h'.φ (Prod.map h.g h.φ (x d)), fun d ↦ h'.f (o' d)) =
          (t'.Kswap.1.condKernel (fun d ↦ Prod.map h.g h.φ (x d), o')).map (fun s d ↦ h'.φ (s d)))
        (Measurable.of_eval fun d ↦ h.hf.comp (measurable_pi_apply d)).aemeasurable ?_
      rw [h.map_obs]
      exact h'.markov _
    filter_upwards [h.markov x, h₂] with o h₁ h₂
    change t''.Kswap.1.condKernel (fun d ↦ Prod.map h'.g h'.φ (Prod.map h.g h.φ (x d)),
      fun d ↦ h'.f (h.f (o d))) = _
    rw [h₂, h₁, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  init := by
    rw [h'.init, h.init, Measure.map_map h'.hφ h.hφ]

@[simp] lemma comp_φ (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).φ = h'.φ ∘ h.φ := rfl
@[simp] lemma comp_f (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).f = h'.f ∘ h.f := rfl
@[simp] lemma comp_g (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).g = h'.g ∘ h.g := rfl

end Transducer.Hom

/-! ### Reductions -/

section Reduction

variable {t t' t'' : Transducer D A O} [t.Regular] [t'.Regular] [t''.Regular]

/-- A reduction is between the same input and output spaces, with a reduced state space -/
def Transducer.Hom.reduction (h : t.Hom t') : Prop :=
  h.φ.Surjective ∧ h.f = id ∧ h.g = id

/-- Specfies whether a transducer is a reduction of another -/
def Transducer.IsReduction (t t' : Transducer D A O) [t.Regular] [t'.Regular] : Prop :=
  ∃ (h : t.Hom t'), h.reduction

lemma Transducer.Hom.reduction_id : (Transducer.Hom.id t).reduction :=
  ⟨Function.surjective_id, rfl, rfl⟩

lemma Transducer.Hom.reduction_comp {h' : t'.Hom t''} {h : t.Hom t'} (hh' : h'.reduction)
    (hh : h.reduction) : (h'.comp h).reduction := by
  refine ⟨hh'.1.comp hh.1, ?_, ?_⟩
  · rw [comp_f, hh'.2.1, hh.2.1]; rfl
  · rw [comp_g, hh'.2.2, hh.2.2]; rfl

lemma Transducer.IsReduction.refl (t : Transducer D A O) [t.Regular] : t.IsReduction t :=
  ⟨.id t, Transducer.Hom.reduction_id⟩

lemma Transducer.IsReduction.trans (h : t.IsReduction t') (h' : t'.IsReduction t'') :
    t.IsReduction t'' :=
  ⟨h'.choose.comp h.choose, Transducer.Hom.reduction_comp h'.choose_spec h.choose_spec⟩

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

/-! ### The reduction preorder -/

variable (D A O) in
/-- Transducers satisfying the regularity assumptions. -/
def RegularTransducer : Type 1 := {t : Transducer D A O // t.Regular}

instance (t : RegularTransducer D A O) : t.1.Regular := t.2

/-- Regular transducers are preordered by reduction: `s ≤ t` when `s` is a reduction of `t`.
This is not antisymmetric: transducers which are reductions of each other need not be equal. -/
instance : Preorder (RegularTransducer D A O) where
  le s t := t.1.IsReduction s.1
  le_refl t := Transducer.IsReduction.refl t.1
  le_trans _ _ _ hab hbc := hbc.trans hab

lemma RegularTransducer.le_iff {s t : RegularTransducer D A O} : s ≤ t ↔ t.1.IsReduction s.1 :=
  Iff.rfl

variable (D A O) in
/-- Regular transducers up to mutual reduction. By `Antisymmetrization`, this is a partial order. -/
abbrev RegularTransducer.Equiv : Type 1 :=
  Antisymmetrization (RegularTransducer D A O) (· ≤ ·)

/-- Two regular transducers are identified up to mutual reduction iff each is a reduction of the
other. -/
lemma RegularTransducer.toAntisymmetrization_eq_iff {s t : RegularTransducer D A O} :
    toAntisymmetrization (· ≤ ·) s = toAntisymmetrization (· ≤ ·) t ↔
      t.1.IsReduction s.1 ∧ s.1.IsReduction t.1 :=
  toAntisymmetrization_eq _ s t

/-! ### Minimal elements -/

/-- Two probability measures on a type with at most one element are equal. -/
lemma MeasureTheory.Measure.eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · rw [show s = Set.univ from Set.eq_univ_of_forall fun b ↦ Subsingleton.elim a b ▸ ha,
      measure_univ, measure_univ]

/-- A regular transducer whose state space has at most one element is minimal for reduction:
anything it reduces to is equivalent to it. -/
theorem RegularTransducer.isMin_of_subsingleton (t : RegularTransducer D A O)
    [Subsingleton t.1.S] : IsMin t := by
  intro s ⟨h, hsurj, hf, hg⟩
  obtain ⟨c⟩ := t.2.nonempty
  -- `s` is a reduction of `t`, so its state space has at most one element too.
  have : Subsingleton s.1.S := ⟨fun a b ↦ by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']⟩
  refine ⟨{
      φ := fun _ ↦ c
      hφ := measurable_const
      f := id
      hf := measurable_id
      g := id
      hg := measurable_id
      compat := ?_
      markov := fun x ↦ .of_forall fun o ↦ ?_
      init := Measure.eq_of_subsingleton _ _ },
    fun b ↦ s.2.nonempty.elim fun a ↦ ⟨a, Subsingleton.elim _ _⟩, rfl, rfl⟩
  · ext1 x
    -- Every input of `s` is the translate of an input of `t`.
    let x' : D → A × t.1.S := fun d ↦ ((x d).1, c)
    have hx : x = fun d ↦ Prod.map h.g h.φ (x' d) :=
      funext fun d ↦ Prod.ext (by rw [hg]; rfl) (Subsingleton.elim _ _)
    have hcomp := congrArg (fun k ↦ k x') h.compat
    simp only [comap_apply, map_apply _ (by fun_prop : Measurable
      fun (y : D → t.1.S × O) d ↦ Prod.map h.φ h.f (y d))] at hcomp
    have hid : (fun (y : D → t.1.S × O) d ↦
        Prod.map (fun _ : s.1.S ↦ c) id (Prod.map h.φ h.f (y d))) = id :=
      funext fun y ↦ funext fun d ↦ Prod.ext (Subsingleton.elim _ _) (by rw [hf]; rfl)
    rw [comap_apply, map_apply _ (by fun_prop)]
    conv_rhs => rw [hx, hcomp, Measure.map_map (by fun_prop) (by fun_prop)]
    rw [show (fun (y : D → s.1.S × O) d ↦ Prod.map (fun _ : s.1.S ↦ c) id (y d)) ∘
      (fun (y : D → t.1.S × O) d ↦ Prod.map h.φ h.f (y d)) = id from hid, Measure.map_id]
    rfl
  · exact Measure.eq_of_subsingleton _ _

/-
TODO: `Transducer.traj_eq_of_reduction` (reductions preserve trajectories) was stated in terms of
the old step-by-step `Transducer.trajKernel`, which no longer exists: `Transducers.Traj` now builds
transducers from interfaces via Mathlib's `Kernel.traj`. A trajectory statement for reductions
needs a notion of feeding states back along the order on `D` before it can be restated.
-/
