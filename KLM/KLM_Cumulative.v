Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import KLM_Base.

Inductive CumulCons : Ensemble Formula -> Formula -> Formula -> Prop :=
  | Ref : forall Γ p, 
      CumulCons Γ p p
  | LLE : forall Γ p q r, 
      In Formula Γ (p ↔ q) -> 
      CumulCons Γ p r -> 
      CumulCons Γ q r
  | RW : forall Γ p q r, 
      In Formula Γ (p → q) -> 
      CumulCons Γ r p -> 
      CumulCons Γ r q
  | Cut : forall Γ p q r, 
      CumulCons Γ (p ∧ q) r -> 
      CumulCons Γ p q -> 
      CumulCons Γ p r
  | CM : forall Γ p q r, 
      CumulCons Γ p q -> 
      CumulCons Γ p r -> 
      CumulCons Γ (p ∧ q) r.
      
Notation "Γ ':' p '|~' q" := (CumulCons Γ p q) (at level 80).

Ltac solve_cumul :=
  match goal with
  | |- CumulCons _ _ _ => constructor; solve_cumul
  | _ => try assumption
  end.

