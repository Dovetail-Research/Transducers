import Transducers.Transducer

/-!
# Anticipation-free kernels and the observation kernel of a transducer

When the index type `D` carries a preorder (thought of as time), a kernel from action paths to
observation paths is *anticipation-free* if its observations up to index `d` only depend on the
actions up to index `d`: it cannot react to inputs from the future.

Every transducer, started in a state `s`, induces such a kernel `Transducer.obsKernel t s` (the
interface `I_{T,s}` of the paper): run the transducer from `s` and forget the states.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

variable {D A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-- A kernel from action paths to observation paths is anticipation-free if, for every index `d`,
the law of its observations at indices `≤ d` only depends on the actions at indices `≤ d`. -/
def ProbabilityTheory.Kernel.AnticipationFree [Preorder D] (κ : Kernel (D → A) (D → O)) : Prop :=
  ∀ (d : D) (x y : D → A), restrictIic d x = restrictIic d y →
    (κ x).map (restrictIic d) = (κ y).map (restrictIic d)

namespace Transducer

variable [LinearOrder D] (t : Transducer D A O)

/-- The outputs of a transducer at indices `≤ d` only depend on the initial state and on the
actions at indices `≤ d`. -/
lemma K_map_restrictIic (d : D) (s : t.S) (a b : D → A) (hab : restrictIic d a = restrictIic d b) :
    (t.K.1 (s, a)).map (restrictIic d) = (t.K.1 (s, b)).map (restrictIic d) := by
  obtain ⟨past, future, _, _, h⟩ := t.causalMarkov d
  have key : ∀ x, (t.K.1 (s, x)).map (restrictIic d) = past (s, restrictIic d x) := fun x ↦ by
    have hx := congrArg (Measure.map Prod.fst) (h s x)
    rwa [Measure.map_map measurable_fst (by fun_prop), ← Measure.fst, Measure.fst_compProd] at hx
  rw [key, key, hab]

/-- The observation kernel of a transducer started in the state `s` (the interface `I_{T,s}` of
the paper): run the transducer from `s` on the given actions, and forget the states. -/
def obsKernel (s : t.S) : Kernel (D → A) (D → O) :=
  (t.K.1.comap (Prod.mk s) measurable_prodMk_left).map (fun y d ↦ (y d).2)

instance (s : t.S) : IsMarkovKernel (t.obsKernel s) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma obsKernel_apply (s : t.S) (a : D → A) :
    t.obsKernel s a = (t.K.1 (s, a)).map (fun y d ↦ (y d).2) := by
  rw [obsKernel, Kernel.map_apply _ (by fun_prop), Kernel.comap_apply]

/-- The observation kernel of a transducer is anticipation-free. -/
theorem anticipationFree_obsKernel (s : t.S) : (t.obsKernel s).AnticipationFree := by
  intro d a b hab
  have hpast : ∀ x : D → A, (t.obsKernel s x).map (restrictIic d) =
      ((t.K.1 (s, x)).map (restrictIic d)).map (fun (v : Set.Iic d → t.S × O) e ↦ (v e).2) :=
    fun x ↦ by
      rw [obsKernel_apply, Measure.map_map (measurable_restrictIic d) (by fun_prop),
        Measure.map_map (by fun_prop) (measurable_restrictIic d)]
      rfl
  rw [hpast, hpast, t.K_map_restrictIic d s a b hab]

end Transducer
