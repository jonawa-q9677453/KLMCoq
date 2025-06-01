Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import KLM_Base.
Require Import KLM_Cumulative.

Record CumulModel : Type := {
  States : Type;
  Labeling : States -> State;
  PreferenceRel : States -> States -> Prop;
}.

Definition MinimalElements (model : CumulModel) (formula : Formula) : Ensemble (States model) :=
  fun state => 
    entails (Labeling model state) formula /\
    ~ exists state', entails (Labeling model state') formula /\ PreferenceRel model state' state.
    
Definition SemanticEntails (model : CumulModel) (premise conclusion : Formula) : Prop :=
  forall state, In (States model) (MinimalElements model premise) state -> 
                entails (Labeling model state) conclusion.

Notation "model : premise |~w conclusion" := 
  (SemanticEntails model premise conclusion) (at level 80).

Definition SatisfiesKnowledgeBase (model : CumulModel) (Γ : Ensemble Formula) : Prop :=
  forall formula, In Formula Γ formula -> 
                 forall state, entails (Labeling model state) formula.

Definition CumulativeModelEntails (Γ : Ensemble Formula) (premise conclusion : Formula) : Prop :=
  forall model, SatisfiesKnowledgeBase model Γ -> model : premise |~w conclusion.

Notation "Γ |= premise |~w conclusion" := 
  (CumulativeModelEntails Γ premise conclusion) (at level 80).
                    
Axiom smoothness : forall model formula state, 
  entails (Labeling model state) formula ->
  exists minimal_state, 
    entails (Labeling model minimal_state) formula /\ 
    (PreferenceRel model minimal_state state \/ minimal_state = state) /\
    In (States model) (MinimalElements model formula) minimal_state.

Axiom preference_transitivity : 
  forall (model : CumulModel) (state1 state2 state3 : States model),
    PreferenceRel model state1 state2 -> 
    PreferenceRel model state2 state3 -> 
    PreferenceRel model state1 state3.
