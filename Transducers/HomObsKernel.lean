import Transducers.Hom
import Transducers.AnticipationFree

/-!
# Homomorphisms and observation kernels

* `Transducer.Hom.obsKernel_comap`: a homomorphism `t → t'` carries the observation kernel of `t`
  from `s` to that of `t'` from `φ s`, translating actions along `g` and observations along `f`.
* `Transducer.IsReduction.obsKernel_eq`: a reduction preserves the observation kernel from every
  initial state (Observation 1 of the paper).
-/

open MeasureTheory ProbabilityTheory Kernel

variable {D A O A' O' : Type} [LinearOrder D] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace A'] [MeasurableSpace O']

/-- Running `t'` from `φ s` on the translated actions gives the observations of `t` from `s`,
pushed forward along `f`. -/
theorem Transducer.Hom.obsKernel_comap {t : Transducer D A O} {t' : Transducer D A' O'}
    (h : t.Hom t') (s : t.S) :
    (t'.obsKernel (h.φ s)).comap (fun a d ↦ h.g (a d)) (by fun_prop) =
      (t.obsKernel s).map (fun o d ↦ h.f (o d)) := by
  ext1 a
  rw [comap_apply, map_apply _ (by fun_prop), Transducer.obsKernel_apply,
    Transducer.obsKernel_apply, h.compat_apply, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Observation 1.** If `t'` is a reduction of `t`, then from every initial state `s`, `t` and
`t'` started in the image of `s` have the same observation kernel (interface). -/
theorem Transducer.IsReduction.obsKernel_eq {t t' : Transducer D A O} (h : t.IsReduction t')
    (s : t.S) : t'.obsKernel (h.reduction.φ s) = t.obsKernel s := by
  have := h.reduction.obsKernel_comap s
  simp only [h.reduction_spec.2.1, h.reduction_spec.2.2, id_eq] at this
  exact (comap_id _).symm.trans (this.trans (map_id _))
