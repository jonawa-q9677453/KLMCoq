Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.

Require Import KLM_Base.
Require Import KLM_Cumulative.
Require Import KLM_Semantics.
Require Import KLM_Soundness.
Export KLM_Soundness_M.
Require Import KLM_Completeness.
Export KLM_Completeness_M.


Example simple_model : CumulModel.
  apply (Build_CumulModel nat 
                         (fun n => fun f => match f with Var 0 => true | _ => false end)
                         (fun n m => n < m)).
Defined.


Example simple_reflexivity : 
  forall Γ,  Γ : (Var 0) |~ (Var 0).
Proof.
  intros.
  (*wählt automatisch apply Ref. aus*)
  solve_cumul.
Qed.

Example simple_CM : 
  forall Γ p q r, 
    Γ : p |~ q -> 
    Γ : p |~ r -> 
    Γ: (p ∧ q) |~ r.
Proof.
  intros.
  solve_cumul.
Qed.

Example CM_RW_example : 
  forall Γ p q r s, 
    In Formula Γ (r → s) ->
    Γ : p |~ q ->
    Γ : p |~ r ->
    Γ : (p ∧ q) |~ s.
Proof.
  intros Γ p q r s H_impl H_p_q H_p_r.
  apply CM.
  - exact H_p_q.
  - apply RW with r.
    + exact H_impl.
    + exact H_p_r.
Qed.

Example soundness_example :
  forall Γ, Γ |= (Var 0) |~w (Var 0).
Proof.
  intros.
  apply soundness_klm.
  apply simple_reflexivity.
Qed.

Example complete_proof_cycle :
  forall Γ p q r,
    In Formula Γ (p → q) ->
    Γ : r |~ p ->
    Γ : r |~ q.
Proof.
  intros Γ p q r H_impl H_r_p.
  
  assert (H_syntactic : Γ : r |~ q).
  apply RW with p; auto.
  
  assert (H_semantic : Γ |= r |~w q).
  apply KLM_Soundness_M.soundness_klm; auto.
  
  apply completeness_klm; auto.
Qed.

Example tweety_penguin :
  forall Γ,
    													(* Vögel fliegen normalerweise *)
    Γ : (Var 0) |~ (Var 1) ->       					(* Vogel |~ fliegt *)
    													(* Pinguine sind Vögel, aber fliegen nicht *)
    In Formula Γ ((Var 2) → (Var 0)) ->  				(* Pinguin → Vogel *)
    In Formula Γ ((Var 2) → ¬(Var 1)) -> 				(* Pinguin → ¬fliegt *)
    													(* Pinguine fliegen üblicherweise nicht *)
    Γ : (Var 2) |~ ¬(Var 1).        					(* Pinguin |~ ¬fliegt *)
Proof.
  intros Γ H_bird_fly H_penguin_bird H_penguin_not_fly.
  apply RW with (Var 2).
  - exact H_penguin_not_fly.
  - apply Ref. (* Pinguin |~ Pinguin *)
Qed.


Definition Quaker := Var 0.
Definition Republican := Var 1.  
Definition Pacifist := Var 2.

Definition NixonKB : Ensemble Formula := 
  fun f => f = (Quaker → Pacifist) \/ 
           f = (Republican → ¬Pacifist) \/
           f = Quaker \/
           f = Republican.

Lemma quaker_pacifist_in_kb : In Formula NixonKB (Quaker → Pacifist).
Proof.
  unfold NixonKB. left. reflexivity.
Qed.

Lemma republican_not_pacifist_in_kb : In Formula NixonKB (Republican → ¬Pacifist).
Proof.
  unfold NixonKB. right. left. reflexivity.
Qed.

Lemma quaker_in_kb : In Formula NixonKB Quaker.
Proof.
  unfold NixonKB. right. right. left. reflexivity.
Qed.

Lemma republican_in_kb : In Formula NixonKB Republican.
Proof.
  unfold NixonKB. right. right. right. reflexivity.
Qed.

Example quakers_are_pacifists :
  NixonKB : Quaker |~ Pacifist.
Proof.
  apply RW with Quaker.
  - apply quaker_pacifist_in_kb.
  - apply Ref.
Qed.

Example republicans_not_pacifists :
  NixonKB : Republican |~ ¬Pacifist.
Proof.
  apply RW with Republican.
  - apply republican_not_pacifist_in_kb.
  - apply Ref.
Qed.

Example nixon_conflict :
  (* Nixon ist sowohl Quäker als auch Republikaner *)
  In Formula NixonKB Quaker /\
  In Formula NixonKB Republican /\
  (* Aber die Default-Schlussfolgerungen widersprechen sich *)
  (NixonKB : Quaker |~ Pacifist) /\
  (NixonKB : Republican |~ ¬Pacifist).
Proof.
  repeat split.
  - apply quaker_in_kb.
  - apply republican_in_kb.
  - apply quakers_are_pacifists.
  - apply republicans_not_pacifists.
Qed.

(* KLM-Theorem *)
Theorem klm_theorem :
  forall (Γ : Ensemble Formula) (p q : Formula),
    Γ : p |~ q <-> Γ |= p |~w q.
Proof.
  intros Γ p q.
  split.
  - apply KLM_Soundness_M.soundness_klm.
  - apply KLM_Completeness_M.completeness_klm.
Qed.
