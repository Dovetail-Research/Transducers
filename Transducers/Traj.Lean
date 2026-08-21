import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Lemmas
import Transducers.Basic

open MeasureTheory ProbabilityTheory Kernel Classical

open scoped Set ENNReal

variable {A S O : Type} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]

-- This an unhelpful linter setting if I want to discharge all secondary goals at the end
set_option linter.style.multiGoal false

/-- Given a starting state, feed a length-`n` input word through the transducer's
(possibly time-varying) kernels `t.K 0, …, t.K (n - 1)` and jointly return the state
reached after `n` steps together with the length-`n` output word.

Built by induction on `n`: `trajKernel (n + 1)` runs `trajKernel n` on the length-`n`
prefix of the input, then appends one more step via `t.K n` fed by the last input
symbol and the state reached so far. -/
noncomputable def Transducer.trajKernel (t : Transducer A S O) :
    Π n, MarkovKernel ((Fin n → A) × S) (S × (Fin n → O))
  | 0 =>
    ⟨Kernel.deterministic (fun sa => (sa.2, Fin.elim0)) (by fun_prop), inferInstance⟩
  | n + 1 =>
    -- split a length-`(n+1)` word into its last symbol and its length-`n` prefix
    let eA := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) (Fin.last n))
    let eO := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => O) (Fin.last n) |>.symm
    --
    -- Take the previous n steps, appending the current action, which does not participate
    let prev := ((t.trajKernel n).1.prodMkLeft A).comap
    -- Simplify term
      (MeasurableEquiv.prodAssoc) (MeasurableEquiv.measurable _)
    --
    -- The final state is given by applying the current step to the result of the previous step
    -- Note that all past information is present, but not all of it is used
    let final_state : Kernel (((A × (Fin n → A)) × S) × (S × (Fin n → O))) (S × O) :=
      (t.K n).1.comap (fun info ↦ (info.1.1.1, info.2.1)) (by fun_prop)
    -- Compose and bundle these two steps and bundle the final state and intermediate outputs,
    -- and simplify
    let total_outputs := ((prev ⊗ₖ final_state).comap (eA.prodCongr (.refl _)) (by fun_prop)
                         ).map (fun info ↦ (info.2.1, eO (info.2.2, info.1.2)))
    --
    ⟨total_outputs, by apply IsMarkovKernel.map; fun_prop⟩

/-- The 'interface' style definition -/
noncomputable def Transducer.stateless_traj (t : Transducer A S O) (n : ℕ) :
    MarkovKernel (Fin n → A) (Fin n → O) :=
  -- Push through the initial S distribution t.p, and discard the final state
  ((t.trajKernel (n)).1 ∘ₖ (.id ×ₖ .const _ t.p)).snd

/-- Helper lemma -/
lemma Prod.eq_mk_iff {α β : Type*} (a : α) (b : β) (p : Prod α β) :
    p = (a, b) ↔ p.1 = a ∧ p.2 = b := by grind

/-- Simplify trajProb when evaluated in terms of the previous time step -/
lemma Transducer.trajProb_apply (t : Transducer A S O) {n : ℕ} (a : Fin (n + 1) → A)
      (s₀ : S) (s : Set (S × (Fin (n + 1) → O))) (hs : MeasurableSet s) :
    t.trajKernel (n + 1) (a, s₀) s = ∫⁻ (b : S × (Fin n → O)), t.K n (a (Fin.last n), b.1)
      ((fun x ↦ (x.1, (MeasurableEquiv.piFinSuccAbove (fun _ ↦ O) (Fin.last _)).symm (x.2, b.2)))
        ⁻¹' s) ∂(t.trajKernel n (Fin.init a, s₀)) := by
  rw [trajKernel, map_apply, comap_apply, Measure.map_apply, compProd_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, MeasurableEquiv.prodCongr,
    MeasurableEquiv.refl_toEquiv, Equiv.prodCongr_apply, MeasurableEquiv.coe_toEquiv,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_last, Equiv.coe_refl, Prod.map_apply,
    Fin.snocEquiv_symm_apply, id_eq, coe_comap, Function.comp_apply, Equiv.prodAssoc_apply,
    prodMkLeft_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Set.preimage_preimage]
  apply measurableSet_preimage
  any_goals fun_prop
  all_goals exact hs

variable [Countable S] [MeasurableSingletonClass S] [MeasurableSingletonClass O]

/-- Rewrite trajProb in terms of its inductive definition -/
lemma Transducer.trajProb_inductive (t : Transducer A S O) {n : ℕ} (a : Fin (n + 1) → A)
      (o : Fin (n + 1) → O) (s₀ sf : S) : t.trajKernel (n + 1) (a, s₀) {(sf, o)} =
    ∑' s : S, t.trajKernel n (Fin.init a, s₀) {(s, Fin.init o)} *
      t.K n (a (Fin.last _), s) {(sf, o (Fin.last _))} := by
  rw [Transducer.trajProb_apply]
  · conv => {
      enter [1, 2, y]
      tactic =>
        convert Eq.refl <| Set.indicator (Set.univ ×ˢ {Fin.init o}) (fun s ↦
          (t.K n) (a (Fin.last _), s.1) {(sf, o (Fin.last _))}) y using 1
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last,
          Fin.snocEquiv, Equiv.coe_fn_mk, Set.mem_singleton_iff, Prod.mk.injEq, Set.indicator,
          Set.mem_prod, Set.mem_univ, true_and, Set.preimage]
        split_ifs with h <;> (rw [← Fin.snoc_init_self o]; simp only [Fin.snoc_inj])
        · simp [h, true_and, ← Prod.eq_mk_iff]
        · simp [h]
    }
    rw [lintegral_indicator, MeasureTheory.lintegral_countable]
    · conv_lhs => tactic => convert (tsum_setProd_singleton_right .univ (Fin.init o)
        (fun x ↦ ((t.K n) (a (Fin.last n), (x).1)) {(sf, o (Fin.last n))} *
        ((t.trajKernel n) (Fin.init a, s₀)) {x}))
      simp_rw [mul_comm]
      convert tsum_univ _; rfl
    · exact Set.Countable.prod Set.countable_univ (Set.countable_singleton _)
    · exact MeasurableSet.univ.prod (measurableSet_singleton _)
  · apply MeasurableSet.preimage (measurableSet_singleton _)
    fun_prop

/-- Prove the formula for calculating the probability of obtaining a given state and output
given a starting state and list of actions -/
lemma Transducer.trajProb_formula (t : Transducer A S O) {n : ℕ}
      (a : Fin n → A) (o : Fin n → O) (s₀ sf : S) : t.trajKernel n (a, s₀) {(sf, o)} =
    ∑' s : {s : Fin (n + 1) → S | s 0 = s₀ ∧ s (Fin.last _) = sf},
      ∏ i : Fin n, t.K i (a i, s.1 i.castSucc) {(s.1 i.succ, o i)} := by
  induction n generalizing sf with
  | zero =>
    simp only [trajKernel, deterministic_apply, Measure.dirac_apply, Set.indicator,
      Nat.reduceAdd, Fin.isValue, Finset.univ_eq_empty, Finset.prod_empty]
    split_ifs with h
    · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
      have : ENat.card (Subtype fun (s : Fin 1 → S) ↦ s 0 = sf) = 1 := by
        rw [ENat.card_eq_one_iff_unique]
        refine ⟨⟨⟨fun _ ↦ sf, rfl⟩, fun x ↦ ?_⟩⟩
        ext _
        simp [Fin.eq_zero _, x.2]
      simp [this, h]
    · simp only [Subsingleton.allEq Fin.elim0 o, Set.mem_singleton_iff, Prod.mk.injEq,
        and_true] at h
      convert tsum_empty.symm
      constructor
      intro x
      exact h (x.2.1 ▸ x.2.2)
  | succ n hn =>
    replace hn := hn (Fin.init a) (Fin.init o)
    simp_rw [trajProb_inductive, hn, Fin.prod_univ_castSucc]
    conv_rhs => rw [tsum_subtype (f := fun (s : Fin (n + 1 + 1) → S) ↦
      (∏ (i : Fin n), (t.K i.castSucc) (a i.castSucc, s i.castSucc.castSucc)
        {(s i.castSucc.succ, o i.castSucc)}) *
      (t.K (Fin.last n) (a (Fin.last n), s (Fin.last n).castSucc))
        {(s (Fin.last n).succ, o (Fin.last n))})]
    conv_lhs =>
      enter [1, s]
      rw [tsum_subtype (f := fun (s : Fin (n + 1) → S) ↦
        (∏ (i : Fin n), (t.K i) (Fin.init a i, s i.castSucc) {(s i.succ, Fin.init o i)}))]
      tactic => simp_rw [← ENNReal.tsum_mul_right, @eq_comm _ _ s]
    rw [← (Fin.snocEquiv _).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp only [Set.indicator, and_comm, Set.mem_setOf_eq, ite_and, ite_mul, zero_mul, tsum_ite_eq,
      Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_apply_zero, Fin.val_castSucc, Fin.snoc_castSucc,
      Fin.val_last, Fin.succ_last, Nat.succ_eq_add_one, ENNReal.tsum_comm]
    congr with s
    congr with i
    congr
    rw [← Fin.castSucc_succ, Fin.snoc_castSucc]

/-- Push the initial state distribution through the probability formula to
obtain the formula for the stateless trajectory -/
theorem Transducer.statesless_formula (t : Transducer A S O) {n : ℕ}
      (a : Fin n → A) (o : Fin n → O) : t.stateless_traj n a {o} =
    ∑' s : Fin (n + 1) → S,
      t.p {s 0} * ∏ i : Fin n, t.K i (a i, s i.castSucc) {(s i.succ, o i)} := by
    simp only [stateless_traj]
    rw [snd_apply', comp_apply', lintegral_prod, lintegral_id', Kernel.lintegral_const,
      lintegral_countable', ← (Fin.consEquiv _).tsum_eq, ENNReal.tsum_prod']
    apply tsum_congr
    intro s
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, mul_comm, ENNReal.tsum_mul_left]
    apply congrArg
    rw [Set.preimage_snd_singleton_eq_range, Set.range_eq_iUnion, MeasureTheory.measure_iUnion]
    · simp_rw [trajProb_formula]
      simp_rw [tsum_subtype _ (fun (q : Fin (n + 1) → S) ↦
        ∏ (i : Fin n), t.K i (a i, q i.castSucc) {(q i.succ, o i)})]
      rw [ENNReal.tsum_comm, ← (Fin.consEquiv _).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
      apply tsum_congr
      intro q
      simp [Set.indicator_apply, ite_and, ENNReal.tsum_comm]
    · intro i j hij t u v q hq
      simp only [Set.le_eq_subset, Set.subset_singleton_iff] at u v
      grind
    · exact fun _ ↦ measurableSet_singleton _
    apply Measurable.lintegral_prod_right
    any_goals apply Kernel.measurable_coe
    any_goals try exact measurableSet_preimage (measurable_snd) (measurableSet_singleton _)
    exact measurableSet_singleton _
