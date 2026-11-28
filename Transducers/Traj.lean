import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Equivariance of Ionescu-Tulcea trajectories

Results about Mathlib's `ProbabilityTheory.Kernel.partialTraj` and
`ProbabilityTheory.Kernel.traj` that are used to build transducers from interfaces
(see `Transducers.Interface`).

## Main results

* `ProbabilityTheory.Kernel.partialTraj_comap_coordMap`: if every step kernel is equivariant
  with respect to a coordinatewise map `F`, then so is `partialTraj κ 0 b`.
* `ProbabilityTheory.Kernel.traj_map_frestrictLe_coordMap`: the same for the finite-horizon
  marginals of `traj κ 0`.
-/

open MeasureTheory ProbabilityTheory Finset Preorder

noncomputable section

/-! ### Equivariance of `partialTraj` and `traj` under coordinatewise maps -/

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [(n : ℕ) → MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {F : (n : ℕ) → X n → X n}

/-- Apply the family of maps `F` coordinatewise to a partial trajectory. -/
def coordMap (F : (n : ℕ) → X n → X n) {I : Finset ℕ} (z : Π i : I, X i) : Π i : I, X i :=
  fun i ↦ F i (z i)

lemma measurable_coordMap (hF : ∀ n, Measurable (F n)) {I : Finset ℕ} :
    Measurable (coordMap F (I := I)) :=
  Measurable.of_eval fun i ↦ (hF i).comp (measurable_pi_apply i)

/-- One step of `partialTraj` commutes with `coordMap F`, provided the step kernel does. -/
lemma partialTraj_succ_self_comap_coordMap (hF : ∀ n, Measurable (F n)) (b : ℕ)
    (hb : (κ b).comap (coordMap F) (measurable_coordMap hF) = (κ b).map (F (b + 1))) :
    (partialTraj κ b (b + 1)).comap (coordMap F) (measurable_coordMap hF) =
      (partialTraj κ b (b + 1)).map (coordMap F) := by
  have h1 : MeasurableEquiv.piSingleton b ∘ F (b + 1) =
      coordMap F ∘ MeasurableEquiv.piSingleton (X := X) b := by
    funext x i
    cases Nat.mem_Ioc_succ' i
    rfl
  have h2 : IicProdIoc b (b + 1) ∘ Prod.map (coordMap F) (coordMap F) =
      coordMap F ∘ IicProdIoc (X := X) b (b + 1) := by
    funext x i
    simp only [Function.comp_apply, IicProdIoc, coordMap, Prod.map_fst, Prod.map_snd]
    split_ifs <;> rfl
  have hc {I : Finset ℕ} : Measurable (coordMap F (I := I)) := measurable_coordMap hF
  rw [partialTraj_succ_self, comap_map_comm _ _ measurable_IicProdIoc, comap_prod, id_comap,
    ← id_map hc, comap_map_comm _ _ (MeasurableEquiv.measurable _), hb,
    ← map_comp_right _ (hF _) (MeasurableEquiv.measurable _), h1,
    map_comp_right _ (MeasurableEquiv.measurable _) hc, map_prod_map _ _ hc hc,
    ← map_comp_right _ (hc.prodMap hc) measurable_IicProdIoc, h2,
    map_comp_right _ measurable_IicProdIoc hc]

/-- If every step kernel `κ n` with `n < b` commutes with the coordinatewise map `F`, then so
does the partial trajectory kernel `partialTraj κ 0 b`. -/
theorem partialTraj_comap_coordMap (hF : ∀ n, Measurable (F n)) (b : ℕ)
    (h : ∀ n < b, (κ n).comap (coordMap F) (measurable_coordMap hF) = (κ n).map (F (n + 1))) :
    (partialTraj κ 0 b).comap (coordMap F) (measurable_coordMap hF) =
      (partialTraj κ 0 b).map (coordMap F) := by
  induction b with
  | zero => rw [partialTraj_self, id_comap, id_map]
  | succ b ih =>
    have hc {I : Finset ℕ} : Measurable (coordMap F (I := I)) := measurable_coordMap hF
    rw [partialTraj_succ_eq_comp (Nat.zero_le b)]
    calc (partialTraj κ b (b + 1) ∘ₖ partialTraj κ 0 b).comap (coordMap F) hc
        = partialTraj κ b (b + 1) ∘ₖ (partialTraj κ 0 b).comap (coordMap F) hc := rfl
      _ = partialTraj κ b (b + 1) ∘ₖ (deterministic (coordMap F) hc ∘ₖ partialTraj κ 0 b) := by
        rw [ih fun n hn ↦ h n (by lia), deterministic_comp_eq_map]
      _ = (partialTraj κ b (b + 1)).comap (coordMap F) hc ∘ₖ partialTraj κ 0 b := by
        rw [← comp_assoc, comp_deterministic_eq_comap]
      _ = (partialTraj κ b (b + 1) ∘ₖ partialTraj κ 0 b).map (coordMap F) := by
        rw [partialTraj_succ_self_comap_coordMap hF b (h b (by lia)), map_comp]

/-- The finite-horizon marginals of `traj κ 0` commute with the coordinatewise map `F`, as long
as the step kernels up to that horizon do. -/
theorem traj_map_frestrictLe_coordMap (hF : ∀ n, Measurable (F n)) (b : ℕ)
    (h : ∀ n < b, (κ n).comap (coordMap F) (measurable_coordMap hF) = (κ n).map (F (n + 1)))
    (x : Π i : Iic 0, X i) :
    (traj κ 0 (coordMap F x)).map (frestrictLe b) =
      ((traj κ 0 x).map (frestrictLe b)).map (coordMap F) := by
  have := congrArg (fun k ↦ k x) (partialTraj_comap_coordMap hF b h)
  simp only [comap_apply, map_apply _ (measurable_coordMap hF)] at this
  rw [traj_map_frestrictLe_apply, traj_map_frestrictLe_apply, this]

end ProbabilityTheory.Kernel
