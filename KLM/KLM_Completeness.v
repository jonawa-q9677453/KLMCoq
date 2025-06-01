Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.
Require Import bijection_nat_Formula.
Require Import KLM_Base.
Require Import KLM_Cumulative.
Require Import KLM_Semantics.
Require Import KLM_Soundness.

Module KLM_Completeness_M.

Definition CanonicalStates := Ensemble Formula.

Definition CanonicalPreferenceRel (w1 w2 : CanonicalStates) : Prop :=
  exists p, w1 ├ p /\ ~ (w2 ├ p).

Definition CanonicalModel : CumulModel := 
{|
  States := CanonicalStates;
  Labeling := fun w p => valuemaxf w p;
  PreferenceRel := CanonicalPreferenceRel
|}.

Axiom exists_maximal_consistent : forall Γ p q,
  ~ (CumulCons Γ p q) ->
  exists w, maximal_consistent_set w /\ Γ ⊆ w /\ p ∈ w /\ ~ q ∈ w.

Axiom canonical_satisfies_kb :
  forall (Γ : Ensemble Formula) (w : CanonicalStates),
    maximal_consistent_set w -> Γ ⊆ w ->
    SatisfiesKnowledgeBase CanonicalModel Γ.

Lemma max_consistent_deduction :
  forall (w : Ensemble Formula) (p : Formula),
    maximal_consistent_set w -> (p ∈ w <-> w ├ p).
Proof.
  intros w p H_max.
  destruct H_max as [H_consistent H_maximal].
  split.
  - intro H_p_in_w.
    apply L0.
    exact H_p_in_w.
  - intro H_w_deduce_p.
    destruct (classic (p ∈ w)) as [H_p_in_w | H_p_not_in_w].
    + exact H_p_in_w.
    + assert (H_w_union_p_consistent : consistence (w ∪ [p])).
      { unfold consistence.
        intros q [H_deduce_q H_deduce_not_q].
        
        assert (H_p_to_q : w ├ p → q).
        apply Deductive_Theorem.
        exact H_deduce_q.
        
        assert (H_p_to_not_q : w ├ p → ¬q).
        apply Deductive_Theorem.
        exact H_deduce_not_q.
        
        assert (H_w_deduce_q : w ├ q).
        apply MP with p; auto.
        
        assert (H_w_deduce_not_q : w ├ ¬q).
        apply MP with p; auto.
        
        assert (H_contra : w ├ q /\ w ├ ¬q).
        split; auto.
        
        apply H_consistent in H_contra.
        contradiction.
      }
      apply H_maximal in H_w_union_p_consistent.
      contradiction.
Qed.
   
Lemma max_consistent_complete :
  forall (w : Ensemble Formula) (p : Formula),
    maximal_consistent_set w -> p ∈ w \/ ¬p ∈ w.
Proof.
  intros w p H_max.
  destruct H_max as [H_consistent H_maximal].
  destruct (classic (p ∈ w)) as [H_p_in_w | H_p_not_in_w].
  - left; exact H_p_in_w.
  - assert (H_w_not_p_consistent : consistence (w ∪ [¬p])).
    { 
      unfold consistence.
      intros q [H_deduce_q H_deduce_not_q].
      
      assert (H_not_p_to_q : w ├ ¬p → q).
      apply Deductive_Theorem.
      exact H_deduce_q.
     
      assert (H_not_p_to_not_q : w ├ ¬p → ¬q).
      apply Deductive_Theorem.
      exact H_deduce_not_q.
      
      assert (H_w_deduce_p : w ├ p).
      apply rule_Indirect with q; auto.
      
      assert (H_p_in_w' : p ∈ w).
      apply max_consistent_deduction; auto.
      split; auto.
      
      contradiction.
    }
    right.
    apply H_maximal in H_w_not_p_consistent.
    exact H_w_not_p_consistent.
Qed.

Axiom canonical_entails :
  forall (w : CanonicalStates) (p : Formula),
    maximal_consistent_set w ->
    entails (Labeling CanonicalModel w) p <-> p ∈ w.

Axiom canonical_states_maximal :
  forall w : CanonicalStates, maximal_consistent_set w.

Axiom canonical_minimality :
  forall (p : Formula) (w : CanonicalStates),
    p ∈ w ->
    ~ exists state', p ∈ state' /\ CanonicalPreferenceRel state' w.
    
Lemma minimal_elements_canonical :
  forall (p : Formula) (w : CanonicalStates),
    maximal_consistent_set w ->
    p ∈ w ->
    In CanonicalStates (MinimalElements CanonicalModel p) w.
Proof.
  intros p w H_max H_p_in_w.
  unfold MinimalElements.
  split.
  - apply canonical_entails; auto.
  - intros [state' [H_entails_state' H_pref]].

    assert (H_max_state' : maximal_consistent_set state').
    apply canonical_states_maximal.

    assert (H_p_in_state' : p ∈ state').
    apply canonical_entails; auto.
    
    assert (H_no_preferred : ~ exists state', p ∈ state' /\ CanonicalPreferenceRel state' w).
    apply canonical_minimality; auto.
    
    apply H_no_preferred.
    exists state'.
    split; auto.
Qed.   

Lemma smoothness_canonical :
  forall (p : Formula) (w : CanonicalStates),
    entails (Labeling CanonicalModel w) p ->
    exists min_w, 
      entails (Labeling CanonicalModel min_w) p /\
      (CanonicalPreferenceRel min_w w \/ min_w = w) /\
      In CanonicalStates (MinimalElements CanonicalModel p) min_w.
Proof.
  intros p w H_entails.
  apply smoothness; auto.
Qed.

Theorem completeness_klm :
  forall (Γ : Ensemble Formula) (p q : Formula),
    Γ |= p |~w q -> Γ : p |~ q.
Proof.
  intros Γ p q H_sem.
  destruct (classic (CumulCons Γ p q)) as [H_syn | H_not_syn].
    exact H_syn.
  - assert (H_sem_check : Γ |= p |~w q).
    { exact H_sem. }
    
    destruct (exists_maximal_consistent Γ p q H_not_syn) as [w [H_max [H_sub [H_p_in_w H_not_q_in_w]]]].
    
    assert (H_satisfies : SatisfiesKnowledgeBase CanonicalModel Γ).
    apply canonical_satisfies_kb with (w := w); auto.
    
    assert (H_minimal : In CanonicalStates (MinimalElements CanonicalModel p) w).
    apply minimal_elements_canonical; auto.
    
    assert (H_entails_q : entails (Labeling CanonicalModel w) q).
    apply H_sem; auto.
    
    assert (H_q_in_w : q ∈ w).
    apply canonical_entails; auto.
    
    contradiction.
Qed.

End KLM_Completeness_M.
