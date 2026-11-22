import Transducers.Traj
import Transducers.AnticipationFree
import Transducers.Hom

/-!
# Interfaces

An *interface* describes, at every time `n : ℕ`, the law of the observation at time `n` given
the actions and the observations at times `0, …, n - 1` (in particular, the observation at time
`0` is drawn before any action has been taken).

Using Mathlib's Ionescu-Tulcea construction `ProbabilityTheory.Kernel.traj`, an interface yields
a joint law of the whole observation sequence given the whole action sequence, and hence a
(stateless) `Transducer ℕ A O`. We show that this transducer is anticipation-free.

To run `Kernel.traj`, coordinate `n` of the trajectory holds the full action sequence together
with the observations at times `0, …, n - 1`.

## Main results

* `Interface.toTransducer`: the transducer built from an interface with `Kernel.traj`.
* `Interface.anticipationFree_toTransducer`: this transducer is anticipation-free.
* `Interface.isMin_toTransducer`: this transducer is minimal for reduction.
-/

open MeasureTheory ProbabilityTheory Finset Preorder ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-- An interface: at time `n`, the observation is drawn given the actions and the observations
at times `0, …, n - 1`. -/
structure Interface (A O : Type) [MeasurableSpace A] [MeasurableSpace O] where
  κ : (n : ℕ) → MarkovKernel ((Fin n → A) × (Fin n → O)) O

lemma measurable_fin_snoc {n : ℕ} :
    Measurable (fun q : (Fin n → O) × O ↦ (Fin.snoc q.1 q.2 : Fin (n + 1) → O)) :=
  Measurable.of_eval fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact measurable_snd
    | cast i => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply i).comp measurable_fst

namespace Interface

variable (I : Interface A O)

/-- One step of the trajectory: keep the action sequence, and append an observation drawn from
the interface given the first `n` actions and the `n` observations so far. -/
def step (n : ℕ) :
    Kernel (Π i : Iic n, (ℕ → A) × (Fin i → O)) ((ℕ → A) × (Fin (n + 1) → O)) :=
  ((Kernel.id ×ₖ (I.κ n).1.comap (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2))
      (by fun_prop)).map (fun q ↦ (q.1.1, Fin.snoc q.1.2 q.2))).comap
    (fun z ↦ z ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop)

instance (n : ℕ) : IsMarkovKernel (I.step n) := by
  unfold step
  have : IsMarkovKernel ((Kernel.id ×ₖ (I.κ n).1.comap
      (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2)) (by fun_prop)).map
      (fun q ↦ (q.1.1, Fin.snoc q.1.2 q.2) : _ → (ℕ → A) × (Fin (n + 1) → O))) :=
    IsMarkovKernel.map _ (measurable_fst.fst.prodMk
      (measurable_fin_snoc.comp (measurable_fst.snd.prodMk measurable_snd)))
  infer_instance

/-- The joint law of the observations given the actions, obtained from `Kernel.traj`: start from
the action sequence (with no observations yet), and read the observation at time `n` off the last
entry of coordinate `n + 1`. -/
def trajKernel : Kernel (ℕ → A × Unit) (ℕ → Unit × O) :=
  ((traj I.step 0).comap
    (fun x i ↦ (fun n ↦ (x n).1, fun j ↦ absurd (j.2.trans_le (mem_Iic.1 i.2)) j.val.not_lt_zero))
    (by fun_prop)).map
    (fun (ω : Π n, (ℕ → A) × (Fin n → O)) n ↦ ((), (ω (n + 1)).2 (Fin.last n)))

instance : IsMarkovKernel I.trajKernel :=
  IsMarkovKernel.map _ (by fun_prop)

/-- The stateless transducer induced by an interface. -/
def toTransducer : Transducer ℕ A O where
  S := Unit
  K := ⟨I.trajKernel, inferInstance⟩
  p := Measure.dirac ()

/-- The observations of `trajKernel` up to time `d` only depend on the actions up to time `d`. -/
lemma trajKernel_map_restrictIic (d : ℕ) (x y : ℕ → A × Unit) (hxy : ∀ e ≤ d, x e = y e) :
    (I.trajKernel x).map (restrictIic d) = (I.trajKernel y).map (restrictIic d) := by
  let start (z : ℕ → A × Unit) : Π i : Iic 0, (ℕ → A) × (Fin i → O) :=
    fun i ↦ (fun n ↦ (z n).1, fun j ↦ absurd (j.2.trans_le (mem_Iic.1 i.2)) j.val.not_lt_zero)
  -- Overwrite the actions after time `d` by those of `y`.
  let τ : (ℕ → A) → (ℕ → A) := fun b i ↦ if i ≤ d then b i else (y i).1
  have hτ : Measurable τ := Measurable.of_eval fun i ↦ by
    by_cases hi : i ≤ d
    · simpa [τ, hi] using measurable_pi_apply i
    · simp [τ, hi]
  let F : ∀ n : ℕ, (ℕ → A) × (Fin n → O) → (ℕ → A) × (Fin n → O) := fun _ ↦ Prod.map τ id
  have hF : ∀ n, Measurable (F n) := fun _ ↦ hτ.prodMap measurable_id
  -- The step kernels up to time `d` commute with `F`.
  have hstep : ∀ n < d + 1, (I.step n).comap (coordMap F) (measurable_coordMap hF) =
      (I.step n).map (F (n + 1)) := by
    intro n hn
    -- `step n` is a kernel `core` on the current coordinate, pulled back along `top`.
    have hP : Measurable (Prod.map τ (id : (Fin n → O) → (Fin n → O))) :=
      hτ.prodMap measurable_id
    have hP' : Measurable (Prod.map τ (id : (Fin (n + 1) → O) → (Fin (n + 1) → O))) :=
      hτ.prodMap measurable_id
    have hg : Measurable (fun q : ((ℕ → A) × (Fin n → O)) × O ↦
        ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O))) :=
      measurable_fst.fst.prodMk
        (measurable_fin_snoc.comp (measurable_fst.snd.prodMk measurable_snd))
    have hinp : ((I.κ n).1.comap (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2))
        (by fun_prop)).comap (Prod.map τ id) hP =
        (I.κ n).1.comap (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2)) (by fun_prop) := by
      ext1 p
      simp only [comap_apply, Prod.map_fst, Prod.map_snd, id_eq]
      congr 3
      funext i
      simp [τ, show (i : ℕ) ≤ d by lia]
    -- The step only reads the first `n ≤ d` actions, which `τ` does not change.
    have hcore : ((Kernel.id ×ₖ (I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2)) (by fun_prop)).map
          (fun q ↦ ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O)))).comap
          (Prod.map τ id) hP =
        ((Kernel.id ×ₖ (I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (fun i ↦ p.1 i, p.2)) (by fun_prop)).map
          (fun q ↦ ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O)))).map
          (Prod.map τ id) := by
      rw [comap_map_comm _ _ hg, comap_prod, hinp, id_comap, ← id_map hP, map_prod_eq _ _ hP,
        ← map_comp_right _ (hP.prodMap measurable_id) hg, ← map_comp_right _ hg hP']
      rfl
    have lift : ∀ K : Kernel ((ℕ → A) × (Fin n → O)) ((ℕ → A) × (Fin (n + 1) → O)),
        K.comap (Prod.map τ id) hP = K.map (Prod.map τ id) →
        (K.comap (fun z : Π i : Iic n, (ℕ → A) × (Fin i → O) ↦ z ⟨n, mem_Iic.2 le_rfl⟩)
          (by fun_prop)).comap (coordMap F) (measurable_coordMap hF) =
        (K.comap (fun z : Π i : Iic n, (ℕ → A) × (Fin i → O) ↦ z ⟨n, mem_Iic.2 le_rfl⟩)
          (by fun_prop)).map (Prod.map τ id) := by
      intro K hK
      rw [← comap_map_comm _ _ hP', ← hK]
      rfl
    exact lift _ hcore
  -- After applying `F`, the starting point of `x` becomes that of `y`.
  have hstart : coordMap F (start x) = start y := by
    funext i
    simp only [coordMap, F, start, Prod.map, id_eq, Prod.mk.injEq, and_true]
    funext n
    by_cases hn : n ≤ d
    · simp [τ, hn, hxy n hn]
    · simp [τ, hn]
  -- The observations up to time `d` are read off the trajectory up to time `d + 1`.
  let G : (Π i : Iic (d + 1), (ℕ → A) × (Fin i → O)) → Set.Iic d → Unit × O :=
    fun w e ↦ ((), (w ⟨e + 1, mem_Iic.2 (by have := e.2; simp only [Set.mem_Iic] at this; lia)⟩).2
      (Fin.last e))
  have hG : Measurable G := by unfold G; fun_prop
  have key : ∀ z : ℕ → A × Unit, (I.trajKernel z).map (restrictIic d) =
      ((traj I.step 0 (start z)).map
        (frestrictLe (π := fun i ↦ (ℕ → A) × (Fin i → O)) (d + 1))).map G := by
    intro z
    rw [trajKernel, map_apply _ (by fun_prop), comap_apply,
      Measure.map_map (measurable_restrictIic d) (by fun_prop),
      Measure.map_map hG (measurable_frestrictLe _)]
    rfl
  rw [key, key, ← hstart, traj_map_frestrictLe_coordMap hF (d + 1) hstep,
    Measure.map_map hG (measurable_coordMap hF)]
  rfl

/-- The transducer induced by an interface is anticipation-free. -/
theorem anticipationFree_toTransducer : I.toTransducer.AnticipationFree :=
  fun d x y hxy ↦ I.trajKernel_map_restrictIic d x y fun e he ↦ congrFun hxy ⟨e, he⟩

/-- The transducer induced by an interface is minimal for reduction: since its state space has a
single element, every reduction of it is equivalent to it. -/
theorem isMin_toTransducer [I.toTransducer.Regular] :
    IsMin (α := RegularTransducer ℕ A O) ⟨I.toTransducer, inferInstance⟩ :=
  have : Subsingleton I.toTransducer.S := inferInstanceAs (Subsingleton Unit)
  RegularTransducer.isMin_of_subsingleton _

end Interface
