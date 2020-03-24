Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Subtyping_inversion
        Deterministic
        rules_inf2
        dunfield.

Lemma subtyping_completeness : forall A B,
    isub A B -> sub A B.
Proof.
  intros A B H.
  induction* H.
Qed.


(* completeness of typing with respect to the bidirectional type system in ICFP 2016 *)
Theorem typing_completeness : forall G ee dir A e,
    IBTyping G ee dir A e -> Etyping G e A.
Proof with auto.
  intros G ee dir A e Typ.
  induction Typ...
  -
    eapply Etyp_abs.
    intros. forwards*: H1 H2.
    auto_sub. auto_sub.
  -
    lets HT1: IHTyp1. lets HT2: IHTyp2.
    eauto.
  - (* anno *)
    apply subtyping_completeness in H.
    eauto.
  - (* fixpoint *)
    eapply Etyp_fix.
    intros. forwards*: H1 H2.
Qed.
