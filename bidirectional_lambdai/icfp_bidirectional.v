Require Import Metalib.Metatheory.
(* verified in Coq 8.10.2 *)
(* requires The Penn Locally Nameless Metatheory Library, available via https://github.com/plclub/metalib *)

(** syntax *)
Definition i : Set := nat.

Inductive typ : Set :=  (* types *)
 | t_int : typ (* int *)
 | t_top : typ (* top *)
 | t_arrow (A:typ) (B:typ) (* function types *)
 | t_and (A:typ) (B:typ) (* intersection *).

Definition ctx : Set := list ( atom * typ ).

(* defns TopLikeType *)
Inductive topLike : typ -> Prop :=    (* defn topLike *)
 | TL_top :
     topLike t_top
 | TL_and : forall (A B:typ),
     topLike A ->
     topLike B ->
     topLike (t_and A B)
 | TL_arr : forall (A B:typ),
     topLike B ->
     topLike (t_arrow A B).

Inductive exp : Set :=  (* our expressions *)
 | e_var_b (_:nat) (* bound variables *)
 | e_var_f (x:var) (* free variables *)
 | e_top : exp (* top *)
 | e_lit (i5:i) (* lit *)
 | e_abs (A:typ) (e:exp) (B:typ) (* abstractions *)
 | e_fixpoint (e:exp) (A:typ) (* fixpoint *)
 | e_app (e1:exp) (e2:exp) (* applications *)
 | e_merge (e1:exp) (e2:exp) (* merge *)
 | e_anno (e:exp) (A:typ) (* annotation *).

(* opening up abstractions under locally nameless encoding *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
  | (e_fixpoint e A) => e_fixpoint (open_exp_wrt_exp_rec (S k) e_5 e) A
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(* our system *)
(* defns Subtyping *)
Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
 | S_z :
     sub t_int t_int
 | S_top : forall (A:typ),
     sub A t_top
 | S_toparr : forall (A B1 B2:typ),
     sub t_top B2 ->
     sub A (t_arrow B1 B2)
 | S_arr : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | S_andl1 : forall (A1 A2 A3:typ),
     sub A1 A3 ->
     sub (t_and A1 A2) A3
 | S_andl2 : forall (A1 A2 A3:typ),
     sub A2 A3 ->
     sub (t_and A1 A2) A3
 | S_andr : forall (A1 A2 A3:typ),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (t_and A2 A3).

(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
 | O_top :
     ord t_top
 | O_int :
     ord t_int
 | O_arrow : forall (A B:typ),
     ord (t_arrow A B).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_top :
     (lc_exp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e B))
 | lc_e_fixpoint : forall (e:exp) (A:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_fixpoint e A))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merge e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A)).

Inductive value : exp -> Prop :=
 | value_unit :
     value e_top
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_anno : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     value (e_abs A e B)
 | value_merge : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (e_merge v1 v2).

(* defns Semantics *)
Inductive TypedReduce : exp -> typ -> exp -> Prop :=    (* defn TypedReduce *)
 | TReduce_lit : forall (i5:i),
     TypedReduce (e_lit i5) t_int (e_lit i5)
 | TReduce_top : forall (v:exp),
     lc_exp v ->
     TypedReduce v t_top e_top
 | TReduce_toparr : forall (v:exp) (A B:typ),
     lc_exp v ->
     topLike B ->
     TypedReduce v (t_arrow A B) (e_abs t_top e_top B)
 | TReduce_arrow : forall (A:typ) (e:exp) (B C D:typ),
     lc_exp (e_abs A e B) ->
      not ( topLike D )  ->
     sub C A ->
     sub B D ->
     TypedReduce (e_abs A e B)  (t_arrow C D)  (e_abs A e D)
 | TReduce_mergevl : forall (v1 v2:exp) (A:typ) (v1':exp),
     lc_exp v2 ->
     TypedReduce v1 A v1' ->
     ord A ->
     TypedReduce (e_merge v1 v2) A v1'
 | TReduce_mergevr : forall (v1 v2:exp) (A:typ) (v2':exp),
     lc_exp v1 ->
     TypedReduce v2 A v2' ->
     ord A ->
     TypedReduce (e_merge v1 v2) A v2'
 | TReduce_and : forall (v:exp) (A B:typ) (v1 v2:exp),
     TypedReduce v A v1 ->
     TypedReduce v B v2 ->
     TypedReduce v (t_and A B) (e_merge v1 v2).

Definition disjointSpec A B :=
  forall C, sub A C -> sub B C -> topLike C.

Definition consistencySpec v1 v2 :=
  forall A v1' v2', TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.

(* typing in our system *)
Inductive Etyping : ctx -> exp -> typ -> Prop :=    (* defn Etyping *)
 | Etyp_top : forall (G:ctx),
      uniq  G  ->
     Etyping G e_top t_top
 | Etyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Etyping G (e_lit i5) t_int
 | Etyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Etyping G (e_var_f x) A
 | Etyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (D C B:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  B )  ->
     sub C A ->
     sub B D ->
     Etyping G  ( (e_abs A e D) )  (t_arrow C D)
 | Etyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Etyping G e2 A ->
     Etyping G e1 (t_arrow A B) ->
     Etyping G (e_app e1 e2) B
 | Etyp_merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     Etyping G e1 A ->
     Etyping G e2 B ->
      disjointSpec A B  ->
     Etyping G (e_merge e1 e2) (t_and A B)
 | Etyp_anno : forall (G:ctx) (e:exp) (A B:typ),
     Etyping G e B ->
     sub B A ->
     Etyping G  ( (e_anno e A) )  A
 | Etyp_fix : forall (L:vars) (G:ctx) (e:exp) (A:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A )  ->
     Etyping G  ( (e_fixpoint e A) )  A
 | Etyp_mergev : forall (G:ctx) (v1 v2:exp) (A B:typ),
     uniq  G  ->
     value (e_merge v1 v2) ->
     Etyping  nil  v1 A ->
     Etyping  nil  v2 B ->
     consistencySpec v1 v2  ->
     Etyping G (e_merge v1 v2) (t_and A B).


(* lambda_i *)
Inductive dexp : Set :=  (* lambda_i expressions *)
 | de_var_b (_:nat) (* bound variables *)
 | de_var_f (x:var) (* free variables *)
 | de_top : dexp (* top *)
 | de_lit (i5:i) (* lit *)
 | de_abs (ee:dexp) (* abstractions *)
 | de_app (ee1:dexp) (ee2:dexp) (* applications *)
 | de_merge (ee1:dexp) (ee2:dexp) (* merge *)
 | de_ann (ee:dexp) (A:typ) (* annotation *)
 | de_fixpoint (ee:dexp) (* fixpoint *).

Inductive dirflag : Set :=  (* type checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

(* lambdai type wellformedness *)
Inductive WF : ctx -> typ -> Prop :=
 | Wf_int : forall (G:ctx),
     WF G t_int
 | Wf_top : forall (G:ctx),
     WF G t_top
 | Wf_arr : forall (G:ctx) (A B:typ),
     WF G A ->
     WF G B ->
     WF G (t_arrow A B)
 | Wf_and : forall (G:ctx) (A B:typ),
     WF G A ->
     WF G B ->
     disjointSpec A B  ->
     WF G (t_and A B).

(* opening up abstractions under locally nameless encoding *)
Fixpoint open_dexp_wrt_dexp_rec (k:nat) (ee_5:dexp) (ee__6:dexp) {struct ee__6}: dexp :=
  match ee__6 with
  | (de_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => de_var_b nat
        | inleft (right _) => ee_5
        | inright _ => de_var_b (nat - 1)
      end
  | (de_var_f x) => de_var_f x
  | de_top => de_top
  | (de_lit i5) => de_lit i5
  | (de_abs ee) => de_abs (open_dexp_wrt_dexp_rec (S k) ee_5 ee)
  | (de_app ee1 ee2) => de_app (open_dexp_wrt_dexp_rec k ee_5 ee1) (open_dexp_wrt_dexp_rec k ee_5 ee2)
  | (de_merge ee1 ee2) => de_merge (open_dexp_wrt_dexp_rec k ee_5 ee1) (open_dexp_wrt_dexp_rec k ee_5 ee2)
  | (de_ann ee A) => de_ann (open_dexp_wrt_dexp_rec k ee_5 ee) A
  | (de_fixpoint ee) => de_fixpoint (open_dexp_wrt_dexp_rec (S k) ee_5 ee)
  end.

Definition open_dexp_wrt_dexp ee_5 ee__6 := open_dexp_wrt_dexp_rec 0 ee__6 ee_5.

(* lambdai bidirectional typing *)
Inductive IBTyping : ctx -> dexp -> dirflag -> typ -> exp -> Prop :=
 | IBTyp_top : forall (G:ctx),
      uniq  G  ->
     IBTyping G de_top Inf t_top e_top
 | IBTyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     IBTyping G (de_lit i5) Inf t_int (e_lit i5)
 | IBTyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     IBTyping G (de_var_f x) Inf A (e_var_f x)
 | IBTyp_lam : forall (L:vars) (G:ctx) (ee:dexp) (A B:typ) (e:exp),
     WF G A ->
      ( forall x , x \notin  L  -> IBTyping  (cons ( x , A )  G )   ( open_dexp_wrt_dexp ee (de_var_f x) )  Chk B  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     IBTyping G (de_abs ee) Chk (t_arrow A B)  ( (e_abs A e B) )
 | IBTyp_app : forall (G:ctx) (ee1 ee2:dexp) (B:typ) (e1 e2:exp) (A:typ),
     IBTyping G ee1 Inf (t_arrow A B) e1 ->
     IBTyping G ee2 Chk A e2 ->
     IBTyping G (de_app ee1 ee2) Inf B (e_app e1 e2)
 | IBTyp_merge : forall (G:ctx) (ee1 ee2:dexp) (A B:typ) (e1 e2:exp),
     IBTyping G ee1 Inf A e1 ->
     IBTyping G ee2 Inf B e2 ->
      disjointSpec A B  ->
     IBTyping G (de_merge ee1 ee2) Inf (t_and A B) (e_merge e1 e2)
 | IBTyp_anno : forall (G:ctx) (ee:dexp) (A:typ) (e:exp),
     IBTyping G ee Chk A e ->
     IBTyping G (de_ann ee A) Inf A e
 | IBTyp_sub : forall (G:ctx) (ee:dexp) (B:typ) (e:exp) (A:typ),
     IBTyping G ee Inf A e ->
     sub A B ->
     IBTyping G ee Chk B (e_anno e B)
 | IBTyp_fix : forall (L:vars) (G:ctx) (ee:dexp) (A:typ) (e:exp),
     WF G A ->
      ( forall x , x \notin  L  -> IBTyping  (cons ( x , A )  G )   ( open_dexp_wrt_dexp ee (de_var_f x) )  Chk A  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     IBTyping G (de_fixpoint ee) Chk A (e_fixpoint e A).

(** infrastructure *)
Hint Constructors value topLike ord sub TypedReduce Etyping WF IBTyping lc_exp : core.

Lemma sub_reflexivity : forall A,
    sub A A.
Proof.
  intros A.
  induction A; eauto.
Qed.

(* completeness of typing with respect to the bidirectional type system in ICFP 2016 *)
Theorem typing_completeness : forall G ee dir A e,
    IBTyping G ee dir A e -> Etyping G e A.
Proof with eauto.
  intros G ee dir A e Typ.
  induction Typ...
  - (* abs *)
    eapply Etyp_abs.
    intros. apply H1 in H2...
    apply sub_reflexivity. apply sub_reflexivity.
Qed.
