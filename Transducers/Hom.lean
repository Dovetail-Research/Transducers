import Transducers.Transducer
import Mathlib.Order.Antisymmetrization

/-!
# Homomorphisms and reductions of transducers

* `Transducer.Hom t t'`: a homomorphism of transducers (Definition 2 of the paper), with identities
  `Transducer.Hom.id` and composition `Transducer.Hom.comp`.
* `Transducer.IsReduction t t'`: `t'` is obtained from `t` by a surjective map of state spaces.
* The reduction preorder on `Transducer D A O`, with `s ≤ t ↔ t.IsReduction s`, and its
  antisymmetrization `Transducer.Equiv D A O`.
-/

open MeasureTheory ProbabilityTheory Kernel

variable {D A O A' O' A'' O'' : Type} [LinearOrder D] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace A'] [MeasurableSpace O'] [MeasurableSpace A''] [MeasurableSpace O'']
  (t : Transducer D A O) (t' : Transducer D A' O') (t'' : Transducer D A'' O'')

/-- A homomorphism between two transducers: measurable maps `φ` on states, `f` on observations
and `g` on actions, applied pointwise at each index, such that running `t'` from the translated
initial state on the translated actions gives the pushforward along `φ` and `f` of the outputs
of `t`. -/
@[ext]
structure Transducer.Hom where
  φ : t.S → t'.S
  hφ : Measurable φ
  f : O → O'
  hf : Measurable f
  g : A → A'
  hg : Measurable g
  compat : t'.K.1.comap (fun x ↦ (φ x.1, fun d ↦ g (x.2 d))) (by fun_prop) =
    t.K.1.map (fun y d ↦ Prod.map φ f (y d))

namespace Transducer.Hom

variable {t t' t''}

/-- Allow the tactic fun_prop to detect that φ is measurable -/
@[fun_prop]
lemma measurable_φ (h : t.Hom t') : Measurable h.φ := h.hφ

@[fun_prop]
lemma measurable_f (h : t.Hom t') : Measurable h.f := h.hf

@[fun_prop]
lemma measurable_g (h : t.Hom t') : Measurable h.g := h.hg

/-- The compatibility condition, applied to an initial state and an action path. -/
lemma compat_apply (h : t.Hom t') (s : t.S) (a : D → A) :
    t'.K.1 (h.φ s, fun d ↦ h.g (a d)) = (t.K.1 (s, a)).map (fun y d ↦ Prod.map h.φ h.f (y d)) := by
  have := congrArg (fun k ↦ k (s, a)) h.compat
  rwa [comap_apply, map_apply _ (by fun_prop)] at this

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

/-- The composition of two homomorphisms. -/
def comp (h' : t'.Hom t'') (h : t.Hom t') : t.Hom t'' where
  φ := h'.φ ∘ h.φ
  hφ := h'.hφ.comp h.hφ
  f := h'.f ∘ h.f
  hf := h'.hf.comp h.hf
  g := h'.g ∘ h.g
  hg := h'.hg.comp h.hg
  compat := by
    calc t''.K.1.comap (fun x ↦ ((h'.φ ∘ h.φ) x.1, fun d ↦ (h'.g ∘ h.g) (x.2 d))) _
        = (t''.K.1.comap (fun x ↦ (h'.φ x.1, fun d ↦ h'.g (x.2 d))) (by fun_prop)).comap
            (fun x ↦ (h.φ x.1, fun d ↦ h.g (x.2 d))) (by fun_prop) := rfl
      _ = (t'.K.1.comap (fun x ↦ (h.φ x.1, fun d ↦ h.g (x.2 d))) (by fun_prop)).map
            (fun y d ↦ Prod.map h'.φ h'.f (y d)) := by
        rw [h'.compat, comap_map_comm _ _ (by fun_prop)]
      _ = t.K.1.map (fun y d ↦ Prod.map (h'.φ ∘ h.φ) (h'.f ∘ h.f) (y d)) := by
        rw [h.compat, ← map_comp_right _ (by fun_prop) (by fun_prop)]
        rfl

@[simp] lemma comp_φ (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).φ = h'.φ ∘ h.φ := rfl
@[simp] lemma comp_f (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).f = h'.f ∘ h.f := rfl
@[simp] lemma comp_g (h' : t'.Hom t'') (h : t.Hom t') : (h'.comp h).g = h'.g ∘ h.g := rfl

end Transducer.Hom

/-! ### Reductions -/

section Reduction

variable {t t' t'' : Transducer D A O}

/-- A reduction is between the same input and output spaces, with a reduced state space -/
def Transducer.Hom.reduction (h : t.Hom t') : Prop :=
  h.φ.Surjective ∧ h.f = id ∧ h.g = id

/-- Specfies whether a transducer is a reduction of another -/
def Transducer.IsReduction (t t' : Transducer D A O) : Prop :=
  ∃ (h : t.Hom t'), h.reduction

lemma Transducer.Hom.reduction_id : (Transducer.Hom.id t).reduction :=
  ⟨Function.surjective_id, rfl, rfl⟩

lemma Transducer.Hom.reduction_comp {h' : t'.Hom t''} {h : t.Hom t'} (hh' : h'.reduction)
    (hh : h.reduction) : (h'.comp h).reduction := by
  refine ⟨hh'.1.comp hh.1, ?_, ?_⟩
  · rw [comp_f, hh'.2.1, hh.2.1]; rfl
  · rw [comp_g, hh'.2.2, hh.2.2]; rfl

lemma Transducer.IsReduction.refl (t : Transducer D A O) : t.IsReduction t :=
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
    t'.K.1.comap (fun x ↦ (h.reduction.φ x.1, x.2)) (by fun_prop) =
      t.K.1.map (fun y d ↦ Prod.map h.reduction.φ id (y d)) := by
  simpa only [h.reduction_spec.2.1, h.reduction_spec.2.2, id_eq] using h.reduction.compat

end Reduction

/-! ### The reduction preorder -/

/-- Transducers are preordered by reduction: `s ≤ t` when `s` is a reduction of `t`.
This is not antisymmetric: transducers which are reductions of each other need not be equal. -/
instance : Preorder (Transducer D A O) where
  le s t := t.IsReduction s
  le_refl t := Transducer.IsReduction.refl t
  le_trans _ _ _ hab hbc := hbc.trans hab

lemma Transducer.le_iff {s t : Transducer D A O} : s ≤ t ↔ t.IsReduction s :=
  Iff.rfl

variable (D A O) in
/-- Transducers up to mutual reduction. By `Antisymmetrization`, this is a partial order. -/
abbrev Transducer.Equiv : Type 1 :=
  Antisymmetrization (Transducer D A O) (· ≤ ·)

/-- Two transducers are identified up to mutual reduction iff each is a reduction of the other. -/
lemma Transducer.toAntisymmetrization_eq_iff {s t : Transducer D A O} :
    toAntisymmetrization (· ≤ ·) s = toAntisymmetrization (· ≤ ·) t ↔
      t.IsReduction s ∧ s.IsReduction t :=
  toAntisymmetrization_eq _ s t

/-! ### Minimal elements -/

/-- A transducer whose state space has exactly one element is minimal for reduction: anything
it reduces to is equivalent to it. -/
theorem Transducer.isMin_of_subsingleton (t : Transducer D A O) [Subsingleton t.S]
    [Nonempty t.S] : IsMin t := by
  intro s ⟨h, hsurj, hf, hg⟩
  obtain ⟨c⟩ := ‹Nonempty t.S›
  -- `s` is a reduction of `t`, so its state space has at most one element too.
  have : Subsingleton s.S := ⟨fun a b ↦ by
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
      compat := ?_ },
    fun b ↦ ⟨h.φ c, Subsingleton.elim _ _⟩, rfl, rfl⟩
  ext1 x
  -- Every input of `s` is the translate of an input of `t`.
  have hx : x = (h.φ c, fun d ↦ h.g (x.2 d)) :=
    Prod.ext (Subsingleton.elim _ _) (by rw [hg]; rfl)
  have hid : (fun (y : D → t.S × O) d ↦
      Prod.map (fun _ : s.S ↦ c) id (Prod.map h.φ h.f (y d))) = id :=
    funext fun y ↦ funext fun d ↦ Prod.ext (Subsingleton.elim _ _) (by rw [hf]; rfl)
  rw [comap_apply, map_apply _ (by fun_prop)]
  conv_rhs => rw [hx, h.compat_apply, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show (fun (y : D → s.S × O) d ↦ Prod.map (fun _ : s.S ↦ c) id (y d)) ∘
    (fun (y : D → t.S × O) d ↦ Prod.map h.φ h.f (y d)) = id from hid, Measure.map_id]
  rfl
