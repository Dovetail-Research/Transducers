import Transducers.Predictive.EpsilonTransducer
import Transducers.Hom

/-!
# Minimality of the ε-transducer

The second part of Proposition 1: every predictive transducer implementing an interface `I`
reduces to the ε-transducer `E(I)`.

Here *predictive* is the paper's Definition 6 read literally (`Transducer.IsInterfacePredictive`):
from every initial state `s`, at every time `n`, almost surely the interface of the state at time
`n` (run from time `0`) is the residual of the interface of `s` at the history so far. The residual
of a kernel at a history is defined by conditioning on the history, as in Eq. (4)
(`ProbabilityTheory.Kernel.condResid`). Since the states of `t` must be sent to states of `E(I)` by
a single map, the interface of each state must be a residual of `I`, which we assume.

Everything assumes countable actions and observations with measurable singletons.

## Main results

* `ProbabilityTheory.Kernel.condResid`: the residual of a kernel at a history, by conditioning.
* `Interface.condResid_resid`: at a history of positive probability, conditioning the residual
  gives the residual of the extended history.
* `Transducer.IsInterfacePredictive`: the paper's Definition 6.
* `Interface.isInterfacePredictive_epsTransducer`: the ε-transducer is predictive in this sense.
* `Transducer.IsInterfacePredictive.isReduction_epsTransducer`: Proposition 1, second part.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

open scoped ENNReal

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-! ### Measures on sequences and countable spaces -/

/-- A finite measure on sequences is determined by the laws of its first `n` entries. -/
lemma measure_eq_of_map_restrictFin {β : Type} [MeasurableSpace β] {μ ν : Measure (ℕ → β)}
    [IsFiniteMeasure μ] (h : ∀ n, μ.map (restrictFin n) = ν.map (restrictFin n)) : μ = ν := by
  refine IsProjectiveLimit.unique (P := fun I ↦ μ.map I.restrict) (fun _ ↦ rfl) (fun I ↦ ?_)
  have hI : ∀ i ∈ I, i < I.sup id + 1 := fun i hi ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  let g : (Fin (I.sup id + 1) → β) → (I → β) := fun x i ↦ x ⟨i, hI i i.2⟩
  have hg : Measurable g := Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hr : (I.restrict : (ℕ → β) → (I → β)) = g ∘ restrictFin (I.sup id + 1) := rfl
  simp only [hr]
  rw [← Measure.map_map hg (measurable_restrictFin _), ← Measure.map_map hg
    (measurable_restrictFin _), h]

/-- Almost every point of a countable space has positive mass. -/
lemma ae_measure_singleton_ne_zero {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ : Measure α) : ∀ᵐ x ∂μ, μ {x} ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {x | μ {x} = 0} = ⋃ x ∈ {x | μ {x} = 0}, {x} := (Set.biUnion_of_singleton _).symm
  rw [this, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun x hx ↦ hx

/-! ### Residuals by conditioning -/

/-- **The residual of a kernel at a history** (Eq. (4)): given the actions of `u` and then `c`,
condition on the observations of `u`, and drop the first `u.1` observations. -/
def ProbabilityTheory.Kernel.condResid (ν : Kernel (ℕ → A) (ℕ → O)) (u : FinHist A O)
    (c : ℕ → A) : Measure (ℕ → O) :=
  ((ν (glue u.2.1 c))[|restrictFin u.1 ⁻¹' {u.2.2}]).map (shiftBy u.1)

namespace Interface

variable (I : Interface A O) [MeasurableSingletonClass O]

/-- **Conditioning a residual.** After `h`, conditioning on steps `u` of positive probability gives
the residual at `h` extended by `u`. -/
theorem condResid_resid (h u : FinHist A O) (hu : I.extProb h u ≠ 0) :
    (I.resid h).condResid u = ⇑(I.resid (h.append u)) := by
  obtain ⟨j, b, w⟩ := u
  funext c
  ext B hB
  have hS : MeasurableSet (restrictFin j ⁻¹' {w} : Set (ℕ → O)) :=
    measurable_restrictFin j (measurableSet_singleton w)
  set μ := I.horizon h.1 j (Fin.append h.2.1 b) h.2.2
  have hmass : I.resid h (glue b c) (restrictFin j ⁻¹' {w}) = μ {w} := by
    rw [← Measure.map_apply (measurable_restrictFin j) (measurableSet_singleton w),
      resid_map_restrictFin]
  have hjoint : I.resid h (glue b c) (restrictFin j ⁻¹' {w} ∩ shiftBy j ⁻¹' B) =
      I.resid (h.append ⟨j, b, w⟩) c B * μ {w} := by
    have hsplit := congrArg (fun ν : Measure ((Fin j → O) × (ℕ → O)) ↦ ν ({w} ×ˢ B))
      (I.resid_map_split h j b c)
    rw [Measure.map_apply ((measurable_restrictFin j).prodMk (measurable_shiftBy j))
      ((measurableSet_singleton w).prod hB), Measure.compProd_apply_prod
      (measurableSet_singleton w) hB, lintegral_singleton, comap_apply] at hsplit
    have e : (restrictFin j ⁻¹' {w} ∩ shiftBy j ⁻¹' B : Set (ℕ → O)) =
        (fun a ↦ (restrictFin j a, shiftBy j a)) ⁻¹' ({w} ×ˢ B) := rfl
    rw [e, hsplit]
    rfl
  have hne : μ {w} ≠ 0 := hu
  have hfin : μ {w} ≠ ∞ := measure_ne_top _ _
  rw [condResid, Measure.map_apply (measurable_shiftBy j) hB, cond_apply hS, hmass, hjoint,
    mul_comm, mul_assoc, ENNReal.mul_inv_cancel hne hfin, mul_one]

/-- Almost surely, the history so far has positive probability. -/
lemma ae_extProb_pref_ne_zero [Countable O] (h : FinHist A O) (n : ℕ) (a : ℕ → A) :
    ∀ᵐ o ∂I.resid h a, I.extProb h (FinHist.pref n a o) ≠ 0 := by
  have h1 := ae_measure_singleton_ne_zero ((I.resid h a).map (restrictFin n))
  rw [I.resid_map_restrictFin'] at h1
  exact ae_of_ae_map
    (p := fun v ↦ I.horizon h.1 n (Fin.append h.2.1 (restrictFin n a)) h.2.2 {v} ≠ 0)
    (measurable_restrictFin n).aemeasurable (by rwa [I.resid_map_restrictFin'])

omit [MeasurableSingletonClass O] in
/-- A residual only depends on the actions so far. -/
lemma resid_map_restrictFin_congr (h : FinHist A O) (n : ℕ) {x y : ℕ → A}
    (hxy : ∀ i < n, x i = y i) :
    (I.resid h x).map (restrictFin n) = (I.resid h y).map (restrictFin n) := by
  rw [I.resid_map_restrictFin', I.resid_map_restrictFin',
    show restrictFin n x = restrictFin n y from funext fun i ↦ hxy i i.isLt]

omit [MeasurableSingletonClass O] in
/-- Classes of histories are determined by their residuals. -/
lemma residQ_injective {q q' : Quotient I.histSetoid} (hq : I.residQ q = I.residQ q') : q = q' := by
  induction q using Quotient.inductionOn
  induction q' using Quotient.inductionOn
  exact Quotient.sound hq

lemma EpsState.eq_of_residQ_eq {c c' : I.EpsState} (hc : I.residQ c.val = I.residQ c'.val) :
    c = c' :=
  EpsState.ext (I.residQ_injective hc)

end Interface

/-! ### Predictive transducers in the sense of the paper -/

/-- **Predictive transducers** (Definition 6, literally): from every initial state `s`, at every
time `n`, almost surely the interface of the state at time `n` is the residual of the interface of
`s` at the history up to time `n`. -/
def Transducer.IsInterfacePredictive (t : Transducer ℕ A O) : Prop :=
  ∀ (s : t.S) (n : ℕ) (a : ℕ → A), ∀ᵐ y ∂t.K.1 (s, a),
    ⇑(t.obsKernel (y n).1) = (t.obsKernel s).condResid (FinHist.pref (n + 1) a fun m ↦ (y m).2)

namespace Transducer

variable [Countable A] [MeasurableSingletonClass A] [Countable O] [MeasurableSingletonClass O]

omit [MeasurableSingletonClass A] in
/-- The set of states with a given anticipation-free interface is measurable. -/
lemma measurableSet_obsKernel_eq (t : Transducer ℕ A O) (J : Kernel (ℕ → A) (ℕ → O))
    [IsMarkovKernel J] (hJ : ∀ n x y, (∀ i < n, x i = y i) →
      (J x).map (restrictFin n) = (J y).map (restrictFin n)) :
    MeasurableSet {s | t.obsKernel s = J} := by
  have hobs : Measurable fun y : ℕ → t.S × O ↦ fun m ↦ (y m).2 := by fun_prop
  -- Equality of the interfaces reduces to countably many finite-dimensional probabilities.
  have hset : {s | t.obsKernel s = J} = ⋂ (n : ℕ) (b : Fin (n + 1) → A) (w : Fin (n + 1) → O),
      {s | t.K.1 (s, extendFin n b) ((fun y m ↦ (y m).2) ⁻¹' (restrictFin (n + 1) ⁻¹' {w})) =
        (J (extendFin n b)).map (restrictFin (n + 1)) {w}} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hs n b w
      rw [← Measure.map_apply hobs (measurable_restrictFin _ (measurableSet_singleton w)),
        ← obsKernel_apply, hs, Measure.map_apply (measurable_restrictFin _)
          (measurableSet_singleton w)]
    · intro hs
      ext1 x
      refine measure_eq_of_map_restrictFin fun m ↦ ?_
      rcases m with _ | n
      · exact Measure.ext_iff_singleton.2 fun w ↦ by
          rw [show ({w} : Set (Fin 0 → O)) = Set.univ from Set.eq_univ_of_forall fun v ↦
            Subsingleton.elim _ _, measure_univ, measure_univ]
      · have hext : ∀ i < n + 1, x i = extendFin n (restrictFin (n + 1) x) i := fun i hi ↦ by
          simp [extendFin, restrictFin, hi]
        rw [(t.anticipationFree_obsKernel s).map_restrictFin n x _ fun i hi ↦
          hext i (by omega), hJ (n + 1) x _ hext]
        refine Measure.ext_iff_singleton.2 fun w ↦ ?_
        rw [← hs n (restrictFin (n + 1) x) w, Measure.map_apply (measurable_restrictFin _)
          (measurableSet_singleton w), obsKernel_apply, Measure.map_apply hobs
          (measurable_restrictFin _ (measurableSet_singleton w))]
  rw [hset]
  refine MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun b ↦ MeasurableSet.iInter fun w ↦ ?_
  exact measurableSet_eq_fun ((Kernel.measurable_coe _ (hobs (measurable_restrictFin _
    (measurableSet_singleton w)))).comp measurable_prodMk_right) measurable_const

/-- **The ε-transducer is predictive in the sense of Definition 6.** -/
theorem _root_.Interface.isInterfacePredictive_epsTransducer (I : Interface A O) :
    I.epsTransducer.IsInterfacePredictive := by
  intro (s : I.EpsState) n a
  obtain ⟨h, hs⟩ : ∃ h, s.val = ⟦h⟧ := ⟨s.val.out, (Quotient.out_eq _).symm⟩
  have hsK : I.epsTransducer.obsKernel s = I.resid h := by
    rw [Interface.obsKernel_epsTransducer, hs]; rfl
  have hK : I.epsTransducer.K.1 (s, a) = (I.residQ s.val a).map (s.path a) := rfl
  -- The property only depends on the state at time `n` and the first `n + 1` observations.
  have hm : Measurable fun y : ℕ → I.EpsState × O ↦
      ((y n).1, restrictFin (n + 1) fun m ↦ (y m).2) :=
    (measurable_fst.comp (measurable_pi_apply n)).prodMk
      ((measurable_restrictFin _).comp (by fun_prop))
  have hset := hm ((Set.to_countable {p : I.EpsState × (Fin (n + 1) → O) |
    ⇑(I.epsTransducer.obsKernel p.1) =
      (I.epsTransducer.obsKernel s).condResid ⟨n + 1, restrictFin (n + 1) a, p.2⟩}).measurableSet)
  rw [hK]
  refine (ae_map_iff (s.measurable_path' a).aemeasurable hset).2 ?_
  rw [hs, Interface.residQ_mk]
  filter_upwards [I.ae_run_eq h a, I.ae_extProb_pref_ne_zero h (n + 1) a] with o ho hp
  have key : ⇑(I.epsTransducer.obsKernel (s.run a o (n + 1))) =
      (I.epsTransducer.obsKernel s).condResid (FinHist.pref (n + 1) a o) := by
    rw [Interface.obsKernel_epsTransducer, Interface.EpsState.run_val, hs, ho, hsK,
      I.condResid_resid h _ hp]
    rfl
  exact key

/-- **The ε-transducer is the minimal predictive transducer** (Proposition 1, second part). Let `t`
be predictive (in the sense of Definition 6), implement `I` from the state `s₀`, and let the
interface of each of its states be the residual of a state of `E(I)`. Then `t` reduces to
`E(I)`. -/
theorem IsInterfacePredictive.isReduction_epsTransducer {I : Interface A O} {t : Transducer ℕ A O}
    (ht : t.IsInterfacePredictive) (s₀ : t.S) (himpl : t.obsKernel s₀ = I.obsKernel)
    (hres : ∀ s, ∃ c : I.EpsState, t.obsKernel s = I.residQ c.val) :
    t.IsReduction I.epsTransducer := by
  classical
  -- Each state goes to the state of `E(I)` with the same interface.
  let φ : t.S → I.EpsState := fun s ↦ (hres s).choose
  have hφ : ∀ s, t.obsKernel s = I.residQ (φ s).val := fun s ↦ (hres s).choose_spec
  have hφ_iff : ∀ s c, φ s = c ↔ t.obsKernel s = I.residQ c.val := fun s c ↦
    ⟨fun h ↦ h ▸ hφ s, fun h ↦ Interface.EpsState.eq_of_residQ_eq I ((hφ s).symm.trans h)⟩
  have hφm : Measurable φ := by
    refine measurable_to_countable' fun c ↦ ?_
    have : φ ⁻¹' {c} = {s | t.obsKernel s = I.residQ c.val} := by
      ext s
      exact hφ_iff s c
    rw [this]
    obtain ⟨h, hh⟩ : ∃ h, c.val = ⟦h⟧ := ⟨c.val.out, (Quotient.out_eq _).symm⟩
    rw [hh, Interface.residQ_mk]
    exact t.measurableSet_obsKernel_eq _ fun n x y hxy ↦ I.resid_map_restrictFin_congr h n hxy
  have hobs : Measurable fun y : ℕ → t.S × O ↦ fun m ↦ (y m).2 := by fun_prop
  -- Almost surely, the run of `t` is sent to the run of `E(I)`.
  have hrun : ∀ s a, ∀ᵐ y ∂t.K.1 (s, a), ∀ n,
      φ (y n).1 = (φ s).run a (fun m ↦ (y m).2) (n + 1) := by
    intro s a
    obtain ⟨h, hh⟩ : ∃ h, (φ s).val = ⟦h⟧ := ⟨(φ s).val.out, (Quotient.out_eq _).symm⟩
    have hs : t.obsKernel s = I.resid h := by rw [hφ, hh]; rfl
    have hlaw : (t.K.1 (s, a)).map (fun y m ↦ (y m).2) = I.resid h a := by
      rw [← obsKernel_apply, hs]
    have hpos := ae_of_ae_map hobs.aemeasurable (hlaw ▸ ae_all_iff.2 fun n ↦
      I.ae_extProb_pref_ne_zero h (n + 1) a)
    have hrunE := ae_of_ae_map hobs.aemeasurable (hlaw ▸ I.ae_run_eq h a)
    filter_upwards [ae_all_iff.2 (ht s · a), hpos, hrunE] with y hy hp hr n
    rw [hφ_iff, ← DFunLike.coe_fn_eq, hy n, hs, I.condResid_resid h _ (hp n),
      Interface.EpsState.run_val, hh, hr (n + 1)]
    rfl
  -- The reduction.
  let hom : t.Hom I.epsTransducer :=
    { φ := φ
      hφ := hφm
      f := id
      hf := measurable_id
      g := id
      hg := measurable_id
      compat := by
        ext1 ⟨s, a⟩
        rw [comap_apply, map_apply _ (by fun_prop)]
        change I.epsKernel (φ s, a) = _
        rw [Interface.epsKernel_apply, ← hφ, obsKernel_apply,
          Measure.map_map ((φ s).measurable_path' a) hobs]
        refine Measure.map_congr ?_
        filter_upwards [hrun s a] with y hy
        funext n
        exact Prod.ext (hy n).symm rfl }
  refine ⟨hom, ?_, rfl, rfl⟩
  -- Every state of `E(I)` is reached.
  suffices hsurj : ∀ q, I.Reachable q → ∃ s, (φ s).val = q by
    intro c
    obtain ⟨s, hs⟩ := hsurj c.val c.reachable
    exact ⟨s, Interface.EpsState.ext hs⟩
  intro q hq
  induction hq with
  | empty =>
    refine ⟨s₀, I.residQ_injective ?_⟩
    rw [← hφ, himpl, Interface.residQ_mk, Interface.resid_empty]
  | @upd q u hq ih =>
    obtain ⟨s', hs'⟩ := ih
    obtain ⟨h, hh⟩ : ∃ h, q = ⟦h⟧ := ⟨q.out, (Quotient.out_eq _).symm⟩
    subst hh
    have hs : t.obsKernel s' = I.resid h := by rw [hφ, hs']; rfl
    rw [Interface.upd_mk]
    split_ifs with hu
    swap
    · exact ⟨s', hs'⟩
    obtain ⟨j, b, w⟩ := u
    rcases j with _ | m
    · refine ⟨s', hs'.trans (Quotient.sound ?_)⟩
      change I.resid h = I.resid _
      congr 1
      exact Sigma.ext rfl (heq_of_eq (Prod.ext (funext fun (i : Fin (h.1 + 0)) ↦
        (fin_append_apply_of_lt _ _ i i.isLt).symm) (funext fun (i : Fin (h.1 + 0)) ↦
          (fin_append_apply_of_lt _ _ i i.isLt).symm)))
    -- Run `t` on the actions of `u`, and pick a run whose history is `u`.
    set a := glue b fun _ ↦ b 0
    have hE : t.K.1 (s', a) ((fun y m ↦ (y m).2) ⁻¹' (restrictFin (m + 1) ⁻¹' {w})) ≠ 0 := by
      rw [← Measure.map_apply hobs (measurable_restrictFin _ (measurableSet_singleton w)),
        ← obsKernel_apply, hs, ← Measure.map_apply (measurable_restrictFin _)
          (measurableSet_singleton w), I.resid_map_restrictFin]
      exact hu
    obtain ⟨y, hyw, hy⟩ : ∃ y : ℕ → t.S × O, restrictFin (m + 1) (fun n ↦ (y n).2) = w ∧
        ⇑(t.obsKernel (y m).1) =
          (t.obsKernel s').condResid (FinHist.pref (m + 1) a fun n ↦ (y n).2) := by
      by_contra hcon
      refine hE (measure_mono_null (t := {y | ¬ ⇑(t.obsKernel (y m).1) =
        (t.obsKernel s').condResid (FinHist.pref (m + 1) a fun n ↦ (y n).2)})
        (fun y hy h' ↦ hcon ⟨y, hy, h'⟩) (ae_iff.1 (ht s' m a)))
    have hpref : FinHist.pref (m + 1) a (fun n ↦ (y n).2) = ⟨m + 1, b, w⟩ :=
      Sigma.ext rfl (heq_of_eq (Prod.ext (restrictFin_glue b fun _ ↦ b 0) hyw))
    refine ⟨(y m).1, I.residQ_injective ?_⟩
    rw [← hφ, Interface.residQ_mk]
    refine DFunLike.coe_fn_eq.1 ?_
    rw [hy, hpref, hs, I.condResid_resid h _ hu]

end Transducer
