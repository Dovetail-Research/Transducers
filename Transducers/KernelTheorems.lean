-- These theorems are mostly unused, but are useful and not present in Mathlib

import Mathlib.Probability.Kernel.Disintegration.StandardBorel

open ProbabilityTheory Kernel

namespace ProbabilityTheory.Kernel

variable {α : Type} {β : Type} {γ : Type} {δ : Type} {ε : Type} [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace ε]
  (κ : Kernel α β) (η : Kernel β γ)


theorem deterministic_comap {f : β → γ} {hf : Measurable f} (g : α → β) (hg : Measurable g) :
    (deterministic f hf).comap g hg = deterministic (f ∘ g) (hf.comp hg) := rfl

theorem mapProd_fst (κ : Kernel α (β × γ)) (f : β → δ) (g : γ → ε) (hf : Measurable f)
      (hg : Measurable g) :
    (κ.map (Prod.map f g)).fst = κ.fst.map f := by
  rw [fst_eq, fst_eq, ← map_comp_right, ← map_comp_right]
  · congr 1
  all_goals fun_prop

theorem mapProd_snd (κ : Kernel α (β × γ)) (f : β → δ) (g : γ → ε) (hf : Measurable f)
      (hg : Measurable g) :
    (κ.map (Prod.map f g)).snd = κ.snd.map g := by
  rw [snd_eq, snd_eq, ← map_comp_right, ← map_comp_right]
  · congr 1
  all_goals fun_prop

theorem comp_comap {f : δ → α} (hf : Measurable f) : (η ∘ₖ κ).comap f hf = η ∘ₖ κ.comap f hf := rfl

end ProbabilityTheory.Kernel
