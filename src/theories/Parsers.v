
Require Import Ascii.
Require Import Coq.Lists.List.

Set Universe Polymorphism.

Definition string := list ascii.

Definition env_ty := list Type.

Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.
Import EqdepTheory.

Section Parsers.

  Set Universe Polymorphism.
  Variable (Vars: Set).
  Variable (Tys: Vars -> Set).

  Inductive parser: Set -> Type := 
    | pFail : forall {A: Set}, parser A
    | pEps : parser unit
    | pChar : ascii -> parser ascii
    | pAny : parser ascii
    | pCat : forall {A B: Set}, parser A -> parser B -> parser (A * B)
    | pMap : forall {A B: Set}, parser A -> (A -> B) -> parser B
    | pStar: forall {A: Set}, parser A -> parser (list A)
    | pAlt : forall {A: Set}, parser A -> parser A -> parser A
    | pVar : forall (v: Vars), parser (Tys v)
    | pBind : forall {A: Set} {F: A -> Set} (p: parser A) (f: forall a, parser (F a)),
      parser {a & F a}.

  Arguments pFail {_}.
  Arguments pCat {_ _} _ _.
  Arguments pMap {_ _} _ _.
  Arguments pStar {_} _.
  Arguments pAlt {_} _ _.
  Arguments pBind {_ _} _ _.

  Variable (Ps: forall (v: Vars), parser (Tys v)).

  Inductive Parses : string -> forall {A: Set}, parser A -> A -> Prop := 
    | Eps : Parses nil pEps tt
    | Chr : forall c, Parses (c :: nil) (pChar c) c
    | Any : forall c, Parses (c :: nil) pAny c
    | Concat : 
      forall s {A B: Set} (p: parser A) v s' (p': parser B) v',
      Parses s p v -> 
      Parses s' p' v' -> 
      Parses (s ++ s') (pCat p p') (v, v')
    | Map:
      forall s {A B: Set} (f: A -> B) p v,
      Parses s p v -> 
      Parses s (pMap p f) (f v)
    | AltL:
      forall s {A: Set} (p: parser A) p' v,
      Parses s p v -> 
      Parses s (pAlt p p') v
    | AltR:
      forall s {A: Set} (p: parser A) p' v,
      Parses s p' v -> 
      Parses s (pAlt p p') v
    | StarEmp:
      forall {A: Set} (p: parser A),
      Parses nil (pStar p) nil
    | StarIter:
      forall s s' {A: Set} (p: parser A) v vs,
      Parses s p v ->
      Parses s' (pStar p) vs ->
      Parses (s ++ s') (pStar p) (v :: vs)
    | Var: 
      forall s var (v: Tys var),
      Parses s (Ps var) v ->
      Parses s (pVar var) v
    | Bind:
      forall s s' {A: Set} (F: A -> Set) (p: parser A) (f: forall a, parser (F a)) a b,
      Parses s p a -> 
      Parses s' (f a) b -> 
      Parses (s ++ s') (pBind p f) (existT _ a b).

  Ltac my_simpl := 
    repeat (unfold eq_rect in *; simpl in *; try subst;
    try match goal with 
    | H: context[ match ?Eq with | eq_refl => _ end] |- _ => 
      pose (e := UIP_refl _ _ Eq);
      erewrite e in *;
      clear e
    end).

  Ltac simpl_exist H := 
    pose (e' := projT2_eq H);
    my_simpl;
    try clear e'.
    

  Lemma inv_map : 
    forall {A B : Set} {s p} {f: A -> B} {v: B}, 
      Parses s (pMap p f) v -> 
      exists v': A, Parses s p v' /\ f v' = v.
  Proof.
    intros.
    inversion H.
    subst.
    simpl_exist H6.
    clear H6.
    simpl_exist H4.
    clear H4.
    pose (e'' := projT2_eq H5).
    my_simpl.
    simpl_exist e''.
    clear e''.
    clear H5.
    exists v0.
    split; auto.
  Qed.

  Lemma inv_cat : 
    forall {A B : Set} {s p p'} {v: A * B}, 
      Parses s (pCat p p') v -> 
      exists s' s'' v' v'', 
        Parses s' p v' /\
        Parses s'' p' v'' /\
        s = s' ++ s'' /\
        v = (v', v'').
  Proof.
    intros.
    inversion H.
    subst.
    exists s0.
    exists s'.
    exists v0.
    exists v'.
    simpl_exist H8.
    simpl_exist H6.
    simpl_exist H7.
    repeat split; auto.
  Qed.

  Lemma inv_bind : 
    forall {A B: Set} {s p} {f: A -> parser B} {v},
      Parses s (pBind p f) v -> 
      exists s' s'' v' v'', 
        s = s' ++ s'' /\ 
        Parses s' p v' /\
        Parses s'' (f v') v'' /\
        v = existT _ v' v''.
    Proof.
    Admitted.

  Definition hoare_pc_parses {A: Set} (p: parser A) (Pre: string -> Prop) (Post: A -> string -> Prop) := 
    forall s v,
    Pre s ->
    Parses s p v -> 
    Post v s.

  Notation "{{ Pre }} p {{ Post }}" := (hoare_pc_parses p Pre Post) (at level 80).

  Lemma hoare_chr P:
    forall c, 
    {{ P c }} pChar c {{ P }}.
  Proof.
    unfold hoare_pc_parses.
    intros.
    inversion H0.
    simpl_exist H3.
    auto.
  Qed.

  Lemma hoare_eps P:
    {{ P tt }} pEps {{ P }}.
  Proof.
    unfold hoare_pc_parses.
    intros.
    inversion H0.
    simpl_exist H2.
    auto.
  Qed.

  Lemma hoare_concat {V V': Set} P P' P'' (p: parser V) (p': parser V'):
    forall v v',
    {{ P v }} p {{ P }} -> 
    {{ P' v' }} p' {{ P' }} -> 
    {{ P'' (v, v') }} pCat p p' {{ P'' }}.
  Admitted.

  Lemma hoare_map {A B: Set} P (p: parser A) (f: A -> B):
    forall v,
    {{ P (f v) }} pMap p f {{ P }}.
  Admitted.

  

  Fixpoint any {A} (ps: list (parser A)) : parser A := 
    match ps with 
    | nil => pFail
    | p :: ps' => pAlt p (any ps')
    end.

  Definition pure {A: Set} (a: A) : parser A := pMap pEps (fun _ => a).

  Lemma pure_spec {A: Set}:
    forall (a: A) s v, 
      Parses s (pure a) v -> 
      s = nil /\ v = a.
  Proof.
    unfold pure.
    intros.
    pose proof (inv_map H).
    destruct H0 as [x [? ?]].
    subst.
    inversion H0.
    split; exact eq_refl.
  Qed.

  Fixpoint fold {A B: Set} (f: A -> B -> B) (acc: B) (ps: list (parser A)) := 
    match ps with 
    | nil => pure acc
    | p :: ps' => 
      pMap (pCat p (fold f acc ps')) (fun '(a, b) => f a b)
    end.

  Definition filter {A: Set} (p: parser A) (check: A -> bool) : parser A := 
    pMap (pBind p (fun a => if check a then pure a else pFail))
      (fun x => projT2 x).

  
  Ltac destruct_all H := 
    try match H with 
    | _ /\ _ => 
      let Hl := fresh "H" in 
      let Hr := fresh "H" in 
      destruct H as [Hl Hr];
      destruct_all Hl;
      destruct_all Hr
    | exists _, _ => 
      let x := fresh "x" in 
      let H := fresh "H" in 
      destruct H as [x H];
      destruct_all H
    end.

  Lemma filter_spec {A: Set} f:
    forall s (p: parser A) (v : A), 
      Parses s (filter p f) v -> 
      f v = true.
  Proof.
    intros.
    unfold filter in H.
    pose proof (inv_map H).

    destruct H0 as [? [? ?]].
    subst.
    clear H.
    pose proof (inv_bind H0).
    do 4 destruct H.
    destruct H as [? [? [? ?]]].
    subst.
    simpl.
    destruct (f x2) eqn:?.
    - pose proof inv_map H2.
      destruct H as [? [? ?]].
      subst.
      auto.
    - inversion H2.
  Qed.


  Fixpoint repeat {A} (n: nat) (p: parser A) : parser (list A) := 
    match n with 
    | 0 => pure nil
    | S n' => pMap (pCat p (repeat n' p)) (fun '(x, xs) => x :: xs)
    end.

  Lemma repeat_spec {A: Set} n p:
    forall s (vs: list A), 
      Parses s (repeat n p) vs ->
      length vs = n.
  Proof.
    induction n; intros; simpl.
    - unfold repeat in H.
      pose proof (pure_spec _ _ _ H).
      destruct H0.
      subst.
      exact eq_refl.
    - unfold repeat in H.
      fold (@repeat A) in H.

      pose proof inv_map H.
      destruct H0 as [? [? ?]].
      subst.

      pose proof inv_cat H0.
      destruct H1 as [? [? [? [? [? [? [?]]]]]]].

      subst.
      simpl.
      erewrite IHn; [exact eq_refl|].
      eauto.
  Qed.

  Lemma repeat_len_spec {A: Set} n: 
    forall s p (v: list A) n', 
      (forall s' v', Parses s' p v' -> length s' = n') ->
      Parses s (repeat n p) v -> 
      length s = n * n'.
  Proof.
    intros.
    generalize H. 
    induction n; intros; simpl.
    - unfold repeat in H.
      pose proof (@pure_spec (list A)).
      specialize (H2 nil s v H0).
      destruct H2.
      subst.
      exact eq_refl.
    -
      unfold repeat in H.
      fold (@repeat A) in H.
      admit.
  Admitted.

End Parsers.

Arguments parser {_ _} _.
Arguments Parses {_ _ _} _ _ _.
Arguments pFail {_ _ _}.
Arguments pEps {_ _}.
Arguments pAny {_ _}.
Arguments pChar {_ _} _.
Arguments pCat {_ _ _ _} _ _.
Arguments pMap {_ _ _ _} _ _.
Arguments pStar {_ _ _} _.
Arguments pAlt {_ _ _} _ _.
Arguments pVar {_ _} _.
Arguments pBind {_ _ _ _} _ _.

Arguments any {_ _ _} _.
Arguments pure {_ _ _} _.
Arguments filter {_ _ _} _ _.
Arguments repeat {_ _ _} _ _.
Arguments fold {_ _ _ _} _ _ _.

Infix "$" := (pCat) (at level 80).
Infix "@" := (pMap) (at level 80).
Infix "||" := (pAlt) (at level 50, left associativity).
Infix ">>=" := (pBind) (at level 80).

Notation "p1 $> p2" := (pCat p1 p2 @ fun '(_,x) => x) (at level 50).
Notation "p1 <$ p2" := (pCat p1 p2 @ fun '(x,_) => x) (at level 50).


Local Open Scope char_scope.

Definition check_prefix (ss : string * string) := 
  match fst ss with 
  | nil => true 
  | _ => false
  end.

Ltac obl_tac := Tactics.program_simpl.

Program Fixpoint add_prefix {s} (c: ascii) (ss: list {ss' | s = fst ss' ++ snd ss'}) : list {ss' | c :: s = fst ss' ++ snd ss'} := 
  match ss with 
  | nil => nil
  | pr :: ss' => 
    let '(x, y) := pr in 
      match x with 
      | nil => (nil, c :: y) :: (c :: nil, y) :: add_prefix c ss' 
      | _ => (c :: x, y) :: add_prefix c ss'
      end
  end.

Program Fixpoint splits (s: list ascii) : list {ss' | s = fst ss' ++ snd ss'} := 
  match s with 
  | nil => (nil, nil) :: nil
  | c :: s' => 
    let ss := splits s' in 
      add_prefix c ss
  end.

Ltac cat_all ss := 
  match ss with 
  | ?x :: ?xs =>
    idtac "catting with:";
    idtac x;
    (cat_all xs) + 
    (eapply Concat with (s := fst x) (s' := snd x))
  end.

Ltac pose_all ss := 
  match ss with 
  | ?s :: ?ss' =>
    pose s; pose_all ss'
  | nil => idtac
  end.

Definition mp_ty (A: Set) := A -> list ascii -> bool.
Definition find {A: Set} (a: A) (s: list ascii) (mp: mp_ty A) := mp a s.

Scheme Equality for list.

Definition mp_empty {A: Set} : mp_ty A := fun _ _ => false.

Search (ascii -> ascii -> bool).

Definition mp_assoc {A: Set} {v_eqb: A -> A -> bool} (v: A) (s: list ascii) (mp: mp_ty A) : mp_ty A := 
  fun v' s' => if v_eqb v v' then list_beq ascii eqb s s' else find v s mp. 





Ltac parse Vs Tys Ps Mp V_eqb := 
  compute;
  match goal with 
  | |- Parses ?s _ ?p _ => 
    idtac "current s:";
    idtac s;
    idtac "current parser:";
    idtac p;
    idtac "current map:";
    idtac Mp
  end;
  match goal with 
  | |- Parses ?s _ (_ @ _) _ => eapply (Map Vs Tys Ps _); parse Vs Tys Ps Mp V_eqb
  | |- Parses ?s _ (pChar _) _ => eapply Chr
  | |- Parses ?s _ pAny _ => eapply Any
  | |- Parses ?s _ (pVar ?v) _ => 
    assert (find v s Mp = false) by exact eq_refl;
    let Mp' := fresh "Mp" in
    pose (Mp' := mp_assoc (v_eqb := V_eqb) v s Mp);
    subst Mp;
    eapply (Var Vs Tys Ps _ v); parse Vs Tys Ps Mp' V_eqb
  | |- Parses ?s _ (?pl || ?pr) _ => 
    (eapply AltL + eapply AltR); parse Vs Tys Ps Mp V_eqb
  | |- Parses nil _ pEps _ => eapply Eps
  | |- Parses nil _ (pStar _) _ => eapply StarEmp
  | |- Parses ?s _ (_ $ _ ) _ => 
    set (tmp := (splits s));
    vm_compute in tmp;
    match goal with 
    | _ := ?v |- _ => 
      pose_all v
    end;
    clear tmp;
    multimatch goal with 
    | sn := ?v |- Parses ?gs _ _ _ => 
      let H := fresh "H" in
      assert (H: fst (proj1_sig sn) ++ snd (proj1_sig sn) = gs) by exact eq_refl;
      subst sn;
      simpl in H;
      erewrite <- H;
      clear H;
      eapply Concat;
      parse Vs Tys Ps Mp V_eqb
    end
  | |- Parses ?s _ (pStar _ ) _ => 
    set (tmp := (splits s));
    vm_compute in tmp;
    match goal with 
    | _ := ?v |- _ => 
      pose_all v
    end;
    clear tmp;
    multimatch goal with 
    | sn := ?v |- Parses ?gs _ _ _ => 
      let H := fresh "H" in
      assert (H: fst (proj1_sig sn) ++ snd (proj1_sig sn) = gs) by exact eq_refl;
      subst sn;
      simpl in H;
      erewrite <- H;
      clear H;
      eapply StarIter;
      parse Vs Tys Ps Mp V_eqb
    end
  | |- Parses ?s _ (_ >>= _ ) _ => 
    set (tmp := (splits s));
    vm_compute in tmp;
    match goal with 
    | _ := ?v |- _ => 
      pose_all v
    end;
    clear tmp;
    multimatch goal with 
    | sn := ?v |- Parses ?gs _ _ _ => 
      let H := fresh "H" in
      assert (H: fst (proj1_sig sn) ++ snd (proj1_sig sn) = gs) by exact eq_refl;
      subst sn;
      simpl in H;
      erewrite <- H;
      clear H;
      eapply Bind;
      parse Vs Tys Ps Mp V_eqb
    end
  end. 
(* 
Ltac parse_one := 
  match goal with 
  | |- Parses ?s _ (_ @ _) _ => eapply Map
  | |- Parses ?s _ (pChar _) _ => eapply Chr
  | |- Parses nil _ _ pEps => eapply Eps
  end.

Ltac parse' := repeat parse_one. *)

(* a numeric parser *)
Definition dig {v env} : @parser v env nat := 
  any (
    (pChar "0" @ fun _ => 0) ::
    (pChar "1" @ fun _ => 1) ::
    (pChar "2" @ fun _ => 2) ::
    (pChar "3" @ fun _ => 3) ::
    (pChar "4" @ fun _ => 4) ::
    (pChar "5" @ fun _ => 5) ::
    (pChar "6" @ fun _ => 6) ::
    (pChar "7" @ fun _ => 7) ::
    (pChar "8" @ fun _ => 8) ::
    (pChar "9" @ fun _ => 9) ::
    nil
  ).

Definition pref_fun (x: nat * list nat) := fst x :: snd x.

Definition num {v env} := (@dig v env $ pStar dig) @ pref_fun.

Lemma length_cons: 
  forall A (x: A) xs, 
    length (x :: xs) = 1 + length xs.
Proof.
  intros.
  unfold length.
  fold (length xs).
  exact eq_refl.
Qed.

Require Import Coq.micromega.Lia.

Lemma pref_incr: forall x, 0 < length (pref_fun x).
Proof.
  intros.
  destruct x;
  unfold pref_fun.
  erewrite length_cons.
  Lia.lia.
Qed.

Lemma num_nonempty : 
  forall V env_t env_p s v,
  @Parses V env_t env_p s _ num v -> length v > 0.
Proof.
Admitted.

Definition emp_ty (v: Empty_set) : Set := match v with end.
Definition emp_p (v: Empty_set) : @parser Empty_set emp_ty (emp_ty v) := match v with end.

Example parsing_alt : {v & @Parses Empty_set emp_ty emp_p ("1" :: nil) _ (pChar "0" || pChar "1") v}.
Proof.
  econstructor.
  parse Empty_set emp_ty emp_p tt tt.
Defined.


Definition ab_parser : @parser Empty_set emp_ty (nat * nat) := 
  ((pChar "a" @ fun _ => 1) || ((pChar "a" $ pChar "a") @ fun _ => 2))
  $ 
  (((pChar "b") @ fun _ => 1) || ((pChar "b" $ pChar "b") @ fun _ => 2)).

Example parsing_cat : {v & @Parses Empty_set emp_ty emp_p ("a" :: "a" :: "b" :: nil) _ ab_parser v}.
Proof.
  econstructor. 
  set (v := ab_parser).
  vm_compute in v.
  subst v.

  Opaque "++".
  parse Empty_set emp_ty emp_p tt tt.
Defined.

Section NetString.
  Inductive V : Set := | ns.
  Definition Tys (v: V) : Set := list ascii.

  Fixpoint digs_2_num (digs: list nat) : nat := 
    match digs with 
    | nil => 0
    | d :: ds => d + digs_2_num ds * 10
    end.

  Definition num' : @parser V Tys (nat * nat) := num @ fun ds => (digs_2_num ds, length ds).

  Definition net_string : @parser V Tys (list ascii * nat) := 
    (num' >>= fun '(n, len) => 
      (pChar ":" $ (repeat n pAny) $ pChar ",") @ (fun '(x, y, z) => (x :: y ++ z :: nil, len + n + 2)))
    @
      fun (x : {a & (list ascii * nat)%type}) => projT2 x.

  Inductive fmt := 
    | base
    | nest: list fmt -> fmt.
  
  Fixpoint fmt2parser (f: fmt) : @parser V Tys (list ascii * nat) := 
    match f with 
    | base => net_string
    | nest fms => 
      (num' >>= fun '(n, len) => 
        let f := fun '(cs, len) '(cs', len') => (cs ++ cs', len + len') in
        let inner := fold f (nil, 0) (List.map fmt2parser fms) in 
          (pChar ":" $ filter inner (fun '(_, n') => Nat.eqb n n') $ pChar ",") 
          @
            fun '(x, y) => (fst x :: fst (snd x) ++ y :: nil, snd (snd x) + 1 + len))
      @ 
        fun (x : {a & (list ascii * nat)%type}) => projT2 x
    end.

  Definition fmt_2 := nest (base :: base :: nil).

  Definition Ps (v: V) : @parser V Tys (Tys v) := pFail.

  Definition hello :=  "5" :: ":" :: "h" :: "e" :: "l" :: "l" :: "o" :: "," :: nil.
  Definition world := "6" :: "w" :: "o" :: "r" :: "l" :: "d" :: "!" :: "," :: nil. 

  Definition hello_world := 
    "1" :: "7" :: ":" :: hello ++ world ++ "," :: nil.

  Example parse_net_num: {v & @Parses V Tys Ps ("5" :: nil) _ num' v}.
  Proof.
    econstructor.
    parse V Tys Ps tt tt.
  Defined.

  Eval vm_compute in parse_net_num.
  
  Example parse_net_hello : {v & @Parses V Tys Ps hello _ net_string v}.
  Proof.
    econstructor.

    (* parse Vs Tys Ps tt tt. *)

    eapply Map.

    match goal with 
    | |- Parses ?s _ (_ >>= _ ) _ => 
      set (tmp := (splits s));
      vm_compute in tmp;
      match goal with 
      | _ := ?v |- _ => 
        pose_all v
      end;
      clear tmp
     
    end.
    
    clear s.
    clear s1.
    clear s2.
    clear s3.
    clear s4.
    clear s5.
    clear s6.
    clear s7.
    multimatch goal with 
    | sn := ?v |- Parses ?gs _ _ _ => 
      let H := fresh "H" in
      assert (H: fst (proj1_sig sn) ++ snd (proj1_sig sn) = gs) by exact eq_refl;
      subst sn;
      simpl in H;
      erewrite <- H;
      eapply Bind; 
      parse V Tys Ps tt tt
    end.
  Defined.

  Example parse_fmt_2 : {v & @Parses V Tys Ps hello_world _ (fmt2parser fmt_2) v}.
  Proof.
    econstructor.
    set (foo := fmt2parser fmt_2).
    compute in foo.
    subst.
    Fail parse V Tys Ps tt tt.
  Admitted.
End NetString.

Section Expr.
  Inductive ExprV : Set := | e.
  Scheme Equality for ExprV.
  Definition ExprTys (x: ExprV) : Set := 
    match x with 
    | e => nat
    end.

  (* e ::= num | (e) | e + e | e * e *)

  Definition e_base : @parser ExprV ExprTys nat := 
    num @ digs_2_num.

  Definition e_parens : @parser ExprV ExprTys nat := 
    pChar "(" $> pVar e <$ pChar ")".

  Definition e_plus : @parser ExprV ExprTys nat := 
    pVar e $ (pChar "+" $> pVar e) @ fun '(x, y) => x + y.

  Definition e_times : @parser ExprV ExprTys nat := 
    pVar e $ (pChar "*" $> pVar e) @ fun '(x, y) => x * y.

  Definition expr_p : parser nat := 
    e_base || e_parens || e_plus || e_times.

  Definition ExprPs (v: ExprV) : @parser ExprV ExprTys (ExprTys v) := 
    match v with | e => expr_p end.
  

  Example expr_simpl : {v & @Parses ExprV ExprTys ExprPs ("4" :: "2" :: nil) _ expr_p v}.
  Proof.
    econstructor.
    pose (me := @mp_empty ExprV).
    parse ExprV ExprTys ExprPs me ExprV_beq.
  Defined.

  Example expr_var : {v & @Parses ExprV ExprTys ExprPs ("4" :: "2" :: nil) _ (pVar e) v}.
  Proof.
    econstructor.
    pose (me := @mp_empty ExprV).
    idtac "starting".
    parse ExprV ExprTys ExprPs me ExprV_beq.
  Defined.

  Example expr_parens : {v & @Parses ExprV ExprTys ExprPs ( "(" :: "3" :: ")" :: nil) _ expr_p v}.
  Proof.
    econstructor.
    pose (me := @mp_empty ExprV).

    idtac "starting".

    parse ExprV ExprTys ExprPs me ExprV_beq.
  Defined.

  Example expr_plus_times : {v & @Parses ExprV ExprTys ExprPs ( "3" :: "+" :: "4" :: "*" :: "5" :: nil) _ expr_p v}.
  Proof.
    econstructor.
    pose (me := @mp_empty ExprV).

    idtac "starting".

    parse ExprV ExprTys ExprPs me ExprV_beq.
  Defined.

End Expr.
