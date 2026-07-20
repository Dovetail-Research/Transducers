import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Transducers.Basic

open MeasureTheory ProbabilityTheory Kernel ENNReal Classical

variable {A S O : Type} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]

/-- An "autoregressive-filter interface": for every length `n`, a Markov kernel turning an
input word of length `n` into a distribution over output words of length `n`. -/
abbrev AFInterface (A O : Type) [MeasurableSpace A] [MeasurableSpace O]
    := Π n, MarkovKernel (Fin n → A) (Fin n → O)

section trajKernel

/-- Given a starting state, feed a length-`n` input word through the transducer's
(possibly time-varying) kernels `t.K 0, …, t.K (n - 1)` and jointly return the state
reached after `n` steps together with the length-`n` output word.

Built by induction on `n`: `trajKernel (n + 1)` runs `trajKernel n` on the length-`n`
prefix of the input, then appends one more step via `t.K n` fed by the last input
symbol and the state reached so far. -/
noncomputable def Transducer.trajKernel (t : Transducer A S O) :
    Π n, MarkovKernel (S × (Fin n → A)) (S × (Fin n → O))
  | 0 =>
    ⟨Kernel.deterministic (fun sa => (sa.1, Fin.elim0)) (by fun_prop), inferInstance⟩
  | n + 1 =>
    -- split a length-`(n+1)` word into its last symbol and its length-`n` prefix
    let eA := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) (Fin.last n)
    let eO := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => O) (Fin.last n)
    -- reindex the incoming `(state, length-(n+1) word)` pair into
    -- `(state, length-n prefix)` next to the set-aside last symbol
    let split : S × (Fin (n + 1) → A) → (S × (Fin n → A)) × A :=
      fun sa => ((sa.1, (eA sa.2).2), (eA sa.2).1)
    have hsplit : Measurable split := by fun_prop
    -- run the first `n` steps, carrying the set-aside last symbol along unchanged
    let κ : Kernel ((S × (Fin n → A)) × A) (S × (Fin n → O)) :=
       (t.trajKernel n).1.prodMkRight A
    -- given the state reached after `n` steps and the last symbol, take one more step
    let reassoc : ((S × (Fin n → A)) × A) × (S × (Fin n → O)) → A × S :=
      fun p => (p.1.2, p.2.1)
    have hreassoc : Measurable reassoc := by fun_prop
    let η : Kernel (((S × (Fin n → A)) × A) × (S × (Fin n → O))) (S × O) :=
      (t.K n).1.comap reassoc hreassoc
    -- reassemble the final state and the length-(n+1) output word
    let combine : (S × (Fin n → O)) × (S × O) → S × (Fin (n + 1) → O) :=
      fun p => (p.2.1, eO.symm (p.2.2, p.1.2))
    have hcombine : Measurable combine := by fun_prop
    haveI : IsMarkovKernel (κ ⊗ₖ η) := inferInstance
    haveI : IsMarkovKernel ((κ ⊗ₖ η).map combine) := IsMarkovKernel.map _ hcombine
    ⟨((κ ⊗ₖ η).map combine).comap split hsplit, inferInstance⟩

/-- Turn a `Transducer` into an `AFInterface`: sample the initial state from `t.p`,
run it through `t.trajKernel n`, and marginalise the final state out, keeping only
the output word. -/
noncomputable def Transducer.toAFInterface (t : Transducer A S O) : AFInterface A O :=
  fun n =>
    haveI := t.hp
    let s0 : Kernel (Fin n → A) S := Kernel.const (Fin n → A) t.p
    let paired : Kernel (Fin n → A) (S × (Fin n → A)) := s0 ×ₖ Kernel.id
    let ran : Kernel (Fin n → A) (S × (Fin n → O)) := (t.trajKernel n).1 ∘ₖ paired
    haveI : IsMarkovKernel (ran.map Prod.snd) := IsMarkovKernel.map _ measurable_snd
    ⟨ran.snd, inferInstance⟩

end trajKernel

section CorrectnessGoal

variable [Countable S] [MeasurableSingletonClass S] [MeasurableSingletonClass O]

omit [MeasurableSingletonClass O] in
lemma temp (k : Kernel A O) (a : A) : k a = k.toFun a := rfl

/-- The explicit sum-product formula: the probability of the output word `o` given
the input word `a`, as a sum over latent state paths `s : Fin (n + 1) → S` of
`Pr(R₀ = s 0)` times the product of one-step kernel evaluations
`T_{s_i → s_{i+1}}^{(o_i∣a_i)}`. This is the formula depicted in the trajectory
diagram this project is built around. -/
noncomputable def Transducer.trajProbFormula (t : Transducer A S O) {n : ℕ}
    (a : Fin n → A) (o : Fin n → O) : ℝ≥0∞ :=
  ∑' s : Fin (n + 1) → S,
    t.p {s 0} * ∏ i : Fin n, t.K i (a i, s i.castSucc) {(s i.succ, o i)}

/-- Generic measure-theory fact used to unfold one step of the `trajKernel` recursion:
integrating a function of the first (countable) coordinate against a measure on `S × X`,
restricted to where the second coordinate hits a fixed point `x₀`, collapses to a `tsum` of
point masses of the measure. -/
private lemma lintegral_snd_indicator {X : Type} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure (S × X)) [SFinite μ] (x₀ : X) (g : S → ℝ≥0∞) :
    ∫⁻ p, (if p.2 = x₀ then g p.1 else 0) ∂μ = ∑' s : S, g s * μ {(s, x₀)} := by
  have hind : (fun p : S × X => if p.2 = x₀ then g p.1 else 0)
      = (Set.univ ×ˢ ({x₀} : Set X)).indicator (fun p => g p.1) := by
    funext p
    by_cases h : p.2 = x₀ <;> simp [h]
  rw [hind, lintegral_indicator (MeasurableSet.univ.prod (measurableSet_singleton _))]
  have hdecomp : (Set.univ : Set S) ×ˢ ({x₀} : Set X) = ⋃ s' : S, {(s', x₀)} := by
    ext ⟨s', x⟩
    simp [Prod.ext_iff, eq_comm]
  rw [hdecomp, lintegral_iUnion (fun _ => measurableSet_singleton _)
      (fun i j hij => by simp [Function.onFun, hij])]
  simp_rw [lintegral_singleton]

/-- **Point-mass form of the trajectory identity for `trajKernel`.** The joint mass of
ending in state `s_f` having emitted `o` after `n` steps starting from `s₀` decomposes
as a sum over full hidden-state paths `s : Fin (n + 1) → S` with matching endpoints
`s 0 = s₀` and `s (Fin.last n) = s_f`. This is the inductive engine behind
`Transducer.toAFInterface_apply`; the `n + 1` case is unfolded using the same
`compProd`/`map`/`comap` combinators `trajKernel` is built from, and the base case is a
direct computation of the deterministic kernel at `n = 0`. -/
theorem Transducer.trajKernel_apply (t : Transducer A S O) :
    ∀ (n : ℕ) (s₀ s_f : S) (a : Fin n → A) (o : Fin n → O),
      (t.trajKernel n).1 (s₀, a) {(s_f, o)} =
        ∑' s : Fin (n + 1) → S,
          (if s 0 = s₀ ∧ s (Fin.last n) = s_f then (1 : ℝ≥0∞) else 0) *
            ∏ i : Fin n, t.K i (a i, s i.castSucc) {(s i.succ, o i)}
  | 0, s₀, s_f, a, o => by
    have ho : o = Fin.elim0 := Subsingleton.elim _ _
    subst ho
    simp only [Transducer.trajKernel]
    rw [Kernel.deterministic_apply', Set.indicator_apply]
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, Fin.prod_univ_zero, mul_one]
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    simp only [hlast]
    by_cases hsf : s₀ = s_f
    · subst hsf
      rw [if_pos ⟨rfl, True.intro⟩, tsum_eq_single (fun _ : Fin 1 => s₀)]
      · simp
      · intro s' hs'
        rw [if_neg]
        rintro ⟨h1, -⟩
        exact hs' (funext fun i => (Subsingleton.elim i 0) ▸ h1)
    · rw [if_neg (fun h => hsf h.1)]
      symm
      convert tsum_zero
      funext
      simp
      exact fun h ↦ h ▸ hsf
    · rw [← Set.singleton_prod_singleton]
      apply MeasurableSet.prod (MeasurableSet.singleton _)
      apply Set.Subsingleton.measurableSet
      exact Set.subsingleton_of_subsingleton

  | n + 1, s₀, s_f, a, o => by
    simp only [Transducer.trajKernel]
    rw [Kernel.comap_apply,
      Kernel.map_apply' _ (by fun_prop) _ (measurableSet_singleton _),
      Kernel.compProd_apply (MeasurableSet.preimage (measurableSet_singleton _) (by fun_prop))]
    set eA := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) (Fin.last n)
    set eO := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => O) (Fin.last n)
    have key : ∀ b : S × (Fin n → O),
        ((t.K n).1.comap (fun p : ((S × (Fin n → A)) × A) × (S × (Fin n → O)) => (p.1.2, p.2.1))
            (by fun_prop))
          (((s₀, (eA a).2), (eA a).1), b)
          (Prod.mk b ⁻¹'
            ((fun p : (S × (Fin n → O)) × (S × O) => (p.2.1, eO.symm (p.2.2, p.1.2))) ⁻¹'
              ({(s_f, o)} : Set (S × (Fin (n + 1) → O))))) =
        if b.2 = (eO o).2 then t.K n ((eA a).1, b.1) {(s_f, (eO o).1)} else 0 := by
      intro b
      obtain ⟨s', o_init⟩ := b
      rw [Kernel.comap_apply]
      have hset : (Prod.mk (s', o_init) ⁻¹'
          ((fun p : (S × (Fin n → O)) × (S × O) => (p.2.1, eO.symm (p.2.2, p.1.2))) ⁻¹'
            ({(s_f, o)} : Set (S × (Fin (n + 1) → O))))) =
          if o_init = (eO o).2 then ({(s_f, (eO o).1)} : Set (S × O)) else ∅ := by
        ext ⟨s'', o_last⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
        by_cases h : o_init = (eO o).2
        · simp only [h, if_true, Set.mem_singleton_iff, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, heq⟩
            have heq2 : (o_last, o_init) = eO o := by
              rw [← eO.apply_symm_apply (o_last, o_init), h, heq]
            exact ⟨rfl, (Prod.ext_iff.mp heq2).1⟩
          · rintro ⟨rfl, rfl⟩
            refine ⟨rfl, ?_⟩
            exact eO.symm_apply_apply o
        · simp only [h, if_false, Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, heq⟩
          apply h
          have heq2 : (o_last, o_init) = eO o := by
            rw [← eO.apply_symm_apply (o_last, o_init), heq]
          exact (Prod.ext_iff.mp heq2).2
      rw [hset]
      split_ifs with h
      · rfl
      · exact measure_empty
    simp_rw [key]
    rw [Kernel.prodMkRight_apply]
    dsimp only
    haveI : IsSFiniteKernel (t.trajKernel n).1 := inferInstance
    haveI : SFinite ((t.trajKernel n).1 (s₀, (eA a).2)) := inferInstance
    conv_lhs => tactic =>
      convert lintegral_snd_indicator ((t.trajKernel n).1 (s₀, (eA a).2)) ((eO o).2)
        (fun s' => t.K n ((eA a).1, s') {(s_f, (eO o).1)})
    simp_rw [t.trajKernel_apply n s₀ _ (eA a).2 (eO o).2, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    have hcollapse : ∀ r : Fin (n + 1) → S,
        ∑' s' : S,
            t.K n ((eA a).1, s') {(s_f, (eO o).1)} *
              ((if r 0 = s₀ ∧ r (Fin.last n) = s' then (1 : ℝ≥0∞) else 0) *
                ∏ i : Fin n, t.K i ((eA a).2 i, r i.castSucc) {(r i.succ, (eO o).2 i)}) =
          (if r 0 = s₀ then (1 : ℝ≥0∞) else 0) *
            ((∏ i : Fin n, t.K i ((eA a).2 i, r i.castSucc) {(r i.succ, (eO o).2 i)}) *
              t.K n ((eA a).1, r (Fin.last n)) {(s_f, (eO o).1)}) := by
      intro r
      rw [tsum_eq_single (r (Fin.last n))]
      · by_cases h : r 0 = s₀ <;> simp [h] <;> ring
      · intro s' hs'
        simp [Ne.symm hs']
    simp_rw [hcollapse]
    let e := Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => S)
    simp [eA, eO]
    rw [← Equiv.tsum_eq e, ENNReal.tsum_prod', tsum_eq_single s_f]
    · refine tsum_congr fun r => ?_
      have h0 : e (s_f, r) 0 = r 0 := by simp [e]
      have hlastval : e (s_f, r) (Fin.last (n + 1)) = s_f := by simp [e]
      have hlast_succ : (Fin.last n).succ = Fin.last (n + 1) := by
        ext; simp
      simp [h0, hlastval]
      apply ite_congr rfl (fun h ↦ ?_) (fun _ ↦ rfl)
      rw [Fin.prod_univ_castSucc]
      congr
      · simp [e, Fin.init_def, ← Fin.castSucc_succ]
      · simp [e]
      · simp [e]
    · simp [e]
      intro b hb i hi hib
      exact (hb hib).elim

/-- Corollary of `trajKernel_apply`: marginalising out the final state (summing over `s_f`)
collapses the two endpoint conditions to a single one on `s 0`. -/
theorem Transducer.trajKernel_snd_apply (t : Transducer A S O) (n : ℕ) (s₀ : S)
    (a : Fin n → A) (o : Fin n → O) :
    (t.trajKernel n).1.snd (s₀, a) {o} =
      ∑' s : Fin (n + 1) → S,
        (if s 0 = s₀ then (1 : ℝ≥0∞) else 0) *
          ∏ i : Fin n, t.K i (a i, s i.castSucc) {(s i.succ, o i)} := by
  rw [Kernel.snd_apply' _ _ (measurableSet_singleton _)]
  have hdecomp : Prod.snd ⁻¹' ({o} : Set (Fin n → O)) = ⋃ s_f : S, {(s_f, o)} := by
    ext ⟨s', o'⟩
    simp [Prod.ext_iff, eq_comm]
  rw [hdecomp,
    measure_iUnion (fun i j hij => by simp [Function.onFun, hij])
      (fun _ => measurableSet_singleton _)]
  simp_rw [t.trajKernel_apply n s₀ _ a o]
  rw [ENNReal.tsum_comm]
  congr 1 with s
  rw [ENNReal.tsum_mul_right]
  congr 1
  by_cases h0 : s 0 = s₀
  · rw [if_pos h0, tsum_eq_single (s (Fin.last n))]
    · simp [h0]
    · intro s_f hs_f
      exact if_neg (fun h => hs_f h.2.symm)
  · rw [if_neg h0]
    simp [h0]

/-- **The trajectory-probability identity**: the `AFInterface` obtained from
`Transducer.toAFInterface` agrees with the explicit sum-product formula over hidden
state paths. -/
theorem Transducer.toAFInterface_apply (t : Transducer A S O) {n : ℕ}
    (a : Fin n → A) (o : Fin n → O) :
    t.toAFInterface n a {o} = t.trajProbFormula a o := by
  change ((t.trajKernel n).1 ∘ₖ (Kernel.const (Fin n → A) t.p ×ₖ Kernel.id)).snd a {o}
      = t.trajProbFormula a o
  have hmeas : Measurable fun b : S × (Fin n → A) => (t.trajKernel n).1.snd b {o} :=
    Kernel.measurable_coe _ (measurableSet_singleton _)
  rw [Kernel.snd_comp, Kernel.comp_apply' _ _ _ (measurableSet_singleton _),
    Kernel.prod_apply, Kernel.const_apply, Kernel.id_apply, Measure.prod_dirac,
    lintegral_map hmeas (by fun_prop), lintegral_countable']
  simp_rw [t.trajKernel_snd_apply n _ a o, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  unfold Transducer.trajProbFormula
  congr 1 with s
  rw [tsum_eq_single (s 0)]
  · simp [mul_comm]
  · intro x hx
    rw [if_neg hx.symm]
    ring

end CorrectnessGoal
