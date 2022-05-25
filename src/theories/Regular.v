
Require Import Ascii.
Require Import Coq.Lists.List.

Set Universe Polymorphism.

Definition string := list ascii.

Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.

From Equations Require Equations.
Import EqdepTheory.

Set Equations Transparent.

Section Parsers.

  Set Universe Polymorphism.

  (* fail, any, alt, bind, pure, star *)

  Inductive parser: Set -> Type := 
    | pFail : forall {A: Set}, parser A
    | pAny : parser ascii
    | pAlt : forall {A: Set} (l: parser A) (r: parser A), parser A
    | pPure : forall {A: Set} (a: A), parser A
    | pBind : forall {A B: Set} (p: parser A) (f: forall a: A, parser B), parser B
    | pStar : forall {A: Set} (p: parser A), parser (list A).

  Inductive Parses : string -> forall {A: Set}, parser A -> A -> Prop := 
    | Any: forall c, Parses (c :: nil) pAny c
    | AltL:
      forall {A: Set} (s: list ascii) (p p': parser A) (v: A),
      Parses s p v -> 
      Parses s (pAlt p p') v
    | AltR:
      forall {A: Set} (s: list ascii) (p p': parser A) (v: A),
      Parses s p' v -> 
      Parses s (pAlt p p') v
    | Pure : forall {A: Set} (a: A), Parses nil (pPure a) a
    | Bind: 
      forall {A B: Set} s s' p (f: A -> parser B) v v',
      Parses s p v -> 
      Parses s' (f v) v' -> 
      Parses (s ++ s') (pBind p f) v'
    | StarNone: 
      forall {A: Set} (p: parser A),
      Parses nil (pStar p) nil
    (* | StarOnce: 
      forall {A: Set} (s: list ascii) (p: parser A) (v: A),
      Parses s p v -> 
      Parses s (pStar p) (v :: nil) *)
    | StarIter: 
      forall {A: Set} (s s' : list ascii) (p: parser A) (v: A) (vs: list A),
      Parses s p v -> 
      Parses s' (pStar p) vs -> 
      s <> nil -> 
      Parses (s ++ s') (pStar p) (v :: vs).
  
  Definition hoare_parse {A} (p: parser A) (Pre: list ascii -> Prop) (Post: list ascii -> A -> Prop) := 
    forall s, 
      Pre s -> 
      (forall v, 
        Parses s p v ->
        Post s v
      ).

  Ltac parse_fail := 
    match goal with 
    | H: Parses _ pFail _ |- _ => inversion H
    end.

  Ltac inv_ctor H := 
    refine (
      match H with 
      | Bind _ _ _ _ _ _ _ _ => _
      | _ => _
      end
    ); try exact idProp.

  Lemma inv_pure: 
    forall {A: Set} {s} {v v' : A},
      Parses s (pPure v) v' -> 
        s = nil /\ v = v'.
  Proof.
    intros.
    inv_ctor H.
    intuition eauto.
  Qed.


  Lemma inv_any:
    forall {s v},
      Parses s pAny v ->
      s = v :: nil.
  Proof.
    intros.
    inv_ctor H.
    intuition eauto.
  Qed.

  (* Lemma inv_comb:
    forall {A: Set} {s} {p p': parser A} {v},
      Parses s (pComb p p') v ->
      Parses s p v /\ Parses s p v.
  Proof.
    intros.
    inv_ctor H.
    intuition eauto.
  Qed. *)

  Lemma inv_bind: 
    forall {A B: Set} {s p} {f: A -> parser B} {v},
      Parses s (pBind p f) v -> 
      exists v' s' s'', 
        s = s' ++ s'' /\ 
        Parses s' p v' /\
        Parses s'' (f v') v.
  Proof.
    intros.
    inv_ctor H.
    exists y.
    exists s0. exists s1.
    intuition eauto.
  Qed.

  Lemma inv_alt: 
    forall {A: Set} {s pl pr} {v: A}, 
    Parses s (pAlt pl pr) v -> 
    Parses s pl v \/ Parses s pr v.
  Proof.
    intros.
    inv_ctor H.
    - left; auto.
    - right; auto. 
  Qed.

  Lemma inv_star: 
    forall {A: Set} {s} {p: parser A} {vs},
      Parses s (pStar p) vs -> 
      (* ((exists v, vs = v :: nil /\ Parses s p v) \/  *)
      ((s = nil /\ vs = nil) \/
       (exists s' s'' v vs', 
         s' <> nil /\
         s = s' ++ s'' /\ 
         vs = v :: vs' /\  
         Parses s'' (pStar p) vs' /\ 
         Parses s' p v
       )
      ).
  Proof.
    intros.
    (* inv_ctor H. *)
    refine (
      match H in Parses s (pStar p) vs with 
      (* | StarOnce _ _ _ _ => _ *)
      | StarNone _ => _
      | StarIter _ _ _ _ _ _ _ _ => _
      | _ => _
      end
    ); try exact idProp.
    - left; intuition eauto.
    - right.
      do 4 eexists.
      intuition eauto.
  Qed.

  Ltac red_parses_all := 
    repeat (auto; match goal with 
    | H: @ex _ _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | H: Parses _ pFail _ |- _ => inversion H
    | H: Parses _ (pPure _) _ |- _ => 
      let H' := fresh "H" in 
      pose proof inv_pure H as H';
      clear H
    | H: Parses _ (pAlt _ _) _ |- _ =>
      let H' := fresh "H" in 
      pose proof inv_alt H as H';
      clear H
    | H: Parses _ (pBind _ _) _ |- _ =>
      let H' := fresh "H" in 
      pose proof inv_bind H as H';
      clear H
    | H: Parses _ pAny _ |- _ => 
      let H' := fresh "H" in 
      pose proof inv_any H as H';
      clear H
    | H: Parses _ (pStar _) _ |- _ => 
      let H' := fresh "H" in 
      pose proof inv_star H as H';
      clear H
    end; subst).

  Lemma hp_alt: 
    forall {A: Set} {pl pr: parser A} {Pre Post}, 
      hoare_parse pl Pre Post -> 
      hoare_parse pr Pre Post -> 
      hoare_parse (pAlt pl pr) Pre Post.
  Proof.
    unfold hoare_parse; intros.
    red_parses_all.
    destruct H3; intuition eauto.
  Qed.

  Lemma hp_fail: 
    forall {A: Set} {Pre Post}, 
      @hoare_parse A pFail Pre Post.
  Proof.
    unfold hoare_parse; intros.
    red_parses_all.
  Qed.
  
  Lemma hp_any: 
    forall {A: Set} c {Post}, 
      hoare_parse pAny (fun s => s = c :: nil /\ Post (c :: nil) c) Post.
  Proof.
    unfold hoare_parse; intros.
    red_parses_all.
    inversion H; 
    subst.
    auto.
  Qed.

  Lemma hp_impl: 
    forall {A: Set} {p} {Pre Pre' : list ascii -> Prop} {Post: list ascii -> A -> Prop},
    (forall s, Pre' s -> Pre s) -> 
    @hoare_parse A p Pre Post ->
    @hoare_parse A p Pre' Post.
  Proof.
    intros.
    unfold hoare_parse in *.
    intros.
    eapply H0; intuition eauto.
  Qed.
  
  Lemma hp_pure: 
    forall {A: Set} (v: A) {Post}, 
      hoare_parse (pPure v) (fun s => s = nil /\ Post nil v) Post.
  Proof.
    unfold hoare_parse; intros.
    red_parses_all.
  Qed.

  Lemma hp_bind: 
    forall {A B: Set} {p: parser A} {f: A -> parser B} {Pre Inter Post},
      (hoare_parse p (fun s => Pre s) Inter) -> (* forall s', Pre s' -> (forall v, Parses s' p v -> Inter s' v) *)
      (forall v, hoare_parse (f v) (fun s => Inter s v) Post) ->  (* forall s' v, Inter s' v -> (forall v', Parses s' (f v') v -> Post s' v) *) 
      hoare_parse (pBind p f) Pre Post.
  Proof.
    intros.
    unfold hoare_parse.
    intros.
    red_parses_all.
    unfold hoare_parse in H0.
    unfold hoare_parse in H.
    specialize (H x0).
    specialize (H0 x x1).
    assert (forall s s' a, Pre (s ++ s') -> Parses s p a -> Inter s' a) by shelve.
    specialize (H4 _ _ _ H1 H2).
    assert (forall s s' a b, Pre s -> Inter s' a -> Parses s' (f a) b -> Post s' b -> Post (s ++ s') b) by shelve.
    intuition eauto.
    eapply H5; intuition eauto.
    assert (forall s s', Pre (s ++ s') -> Pre s) by shelve.
    intuition eauto.

    Unshelve.
  Admitted.

  (* some identities and smart constructors *)

  Definition alt' {A} (p p' : parser A) := 
    match p' with 
    | pFail => p
    | _ => pAlt p p'
    end.
  Lemma alt'_spec : 
    forall {A s} {p p': parser A} {v}, 
    Parses s (alt' p p') v <-> Parses s (pAlt p p') v. 
  Proof.
    intros.
    destruct p'; simpl alt';

    split; intros; try auto;
    try now (eapply AltL; auto).
    red_parses_all.
    destruct H0; 
    red_parses_all.
  Qed.
  
  Definition alt {A} (p p' : parser A) := 
    match p with 
    | pFail => p'
    | _ => alt' p p'
    end.

  Lemma alt_spec : 
    forall {A s} {p p': parser A} {v}, 
      Parses s (alt p p') v <-> Parses s (pAlt p p') v. 
  Proof.
    intros.
    destruct p; try eapply alt'_spec.
    simpl.
    split; intros; try now (eapply AltR; auto).
    red_parses_all.
    destruct H0; red_parses_all.
  Qed.

  Equations bind {A B} (p : parser A) (f: A -> parser B) : parser B :=
    bind pFail _ := pFail;
    bind (pPure v) f := f v;
    (* bind (pBind p' g) f := bind p' (fun r => _); *)
    bind p f := pBind p f.
 (* Next Obligation. *)

  Lemma bind_spec : 
    forall {A B s} {p: parser A} {f: A -> parser B} {v}, 
      Parses s (bind p f) v <-> Parses s (pBind p f) v. 
  Proof.
    intros.
    destruct p; simpl; try eapply iff_refl;
    split; intros; try (red_parses_all).

    assert (s = nil ++ s) by exact eq_refl.
    erewrite H0.
    econstructor; [econstructor | auto].
  Qed.

  Equations star {A} (p: parser A) : parser (list A) :=
    (* star pFail := pFail; *)
    star p := pStar p.

  Lemma star_spec: 
    forall {A s} {p: parser A} {v},
      Parses s (star p) v <-> Parses s (pStar p) v.
  Proof.
    intros.
    destruct p; simpl; try eapply iff_refl; split; intros; red_parses_all.
    (* destruct H0; red_parses_all. *)
  Qed.

  Definition filter {A: Set} (p: parser A) (check: A -> bool) : parser A := 
    bind p (fun a => if check a then pPure a else pFail).

  Lemma parse_filter {A: Set} f:
    forall {s} {p: parser A} {v: A},
      f v = true -> 
      Parses s p v -> 
      Parses s (filter p f) v.
  Proof.
    intros.
    unfold filter.
    assert (s = s ++ nil) by (erewrite app_nil_r; exact eq_refl).
    erewrite H1; clear H1.
    erewrite bind_spec.
    econstructor; intuition eauto.
    erewrite H.
    econstructor.
  Qed.
  Lemma filter_spec {A: Set} f:
    forall s (p: parser A) (v : A), 
      Parses s (filter p f) v -> 
      f v = true.
  Proof.
    intros.
    unfold filter in H.
    erewrite bind_spec in H.
    red_parses_all.
    destruct (f _) eqn:?; red_parses_all.
  Qed.

  Lemma inv_filter: 
    forall {A s} {p: parser A} {v: A} {f: A -> bool},
    Parses s (filter p f) v -> 
    Parses s p v /\ f v = true.
  Proof. 
    intros.
    unfold filter in H.
    erewrite bind_spec in H.
    red_parses_all.
    destruct (f _) eqn:?; red_parses_all; try erewrite app_nil_r; intuition eauto.
  Qed.

  Definition char c := filter pAny (fun c' => eqb c c').

  Lemma parse_char: 
    forall {s c v}, 
      s = c :: nil -> 
      v = c ->
      Parses s (char c) v .
  Proof.
    intros.
    subst.
    unfold char.
    eapply parse_filter; intuition eauto; try econstructor.

    pose proof eqb_spec c c.
    destruct H; intuition eauto.
  Qed.
  
  Lemma inv_char:
    forall {s c v},
      Parses s (char c) v ->
      s = c :: nil /\ v = c.
  Proof.
    intros.
    unfold char in H.
    pose proof inv_filter H.
    clear H.
    red_parses_all.
    pose proof eqb_spec c v.
    destruct H; subst; intuition eauto;
    inversion H0.
  Qed.

  Definition eps : parser unit := pPure tt.

  Lemma inv_eps: 
    forall {s v}, 
    Parses s eps v -> 
    s = nil /\ v = tt.
  Proof.
    intros;
    unfold eps in *;
    red_parses_all;
    intuition eauto.
  Qed.

  Definition map {A B: Set} (p: parser A) (f: A -> B) : parser B :=
    bind p (fun x => pPure (f x)).

  Lemma inv_map : 
    forall {A B : Set} {s p} {f: A -> B} {v: B}, 
      Parses s (map p f) v -> 
      exists v': A, Parses s p v' /\ f v' = v.
  Proof.
    intros.
    unfold map in H.
    erewrite bind_spec in H.
    red_parses_all; subst.
    eexists; intuition eauto.
    erewrite app_nil_r.
    auto.
  Qed. 

  Lemma parse_map: 
    forall {A B: Set} {s p} {f: A -> B} v v',
      Parses s p v -> 
      v' = f v ->
      Parses s (map p f) v'.
  Proof.
    intros.
    assert (s = s ++ nil) by (erewrite app_nil_r; exact eq_refl).
    subst.
    erewrite H1.
    unfold map.
    erewrite bind_spec.

    econstructor; intuition eauto; econstructor.
  Qed.

  Definition cat {A B: Set} (p: parser A) (p': parser B) : parser (A * B) := 
    bind p (fun l => map p' (fun r => (l, r))).

  Lemma inv_cat : 
    forall {A B : Set} {s p p'} {v: A * B}, 
      Parses s (cat p p') v -> 
      exists s' s'' v' v'', 
        Parses s' p v' /\
        Parses s'' p' v'' /\
        s = s' ++ s'' /\
        v = (v', v'').
  Proof.
    intros.
    unfold cat in H.
    erewrite bind_spec in H.
    red_parses_all; subst.
    pose proof inv_map H0; red_parses_all.
    repeat eexists; intuition eauto.
  Qed.

  Lemma parse_cat : 
    forall {A B: Set} {s s' s'' p p'} {v v' v''},
      Parses s p v -> 
      Parses s' p' v' -> 
      s'' = s ++ s' -> 
      v'' = (v, v') -> 
      Parses s'' (@cat A B p p') v''. 
  Proof.
    intros; subst.
    unfold cat.
    erewrite bind_spec.
    econstructor; intuition eauto.
    eapply parse_map; intuition eauto.
  Qed.

  Lemma star_ident : 
    forall {A: Set} s {p: parser A} {v: list A}, 
      (forall s v, Parses s p v -> s <> nil) ->
      Parses s (pStar p) v <-> Parses s (
        pAlt 
        (pPure nil) 
        (map (cat p (pStar p)) (fun '(x, xs) => x :: xs))
      ) v.
  Proof.
    intros.
    split; intros; red_parses_all.
    - destruct H1.
      * destruct H0; subst.
        eapply AltL.
        econstructor.
      * 
        repeat match goal with 
        | H: _ /\ _ |- _ => destruct H
        | H: @ex _ _ |- _ => destruct H
        end; subst.
        eapply AltR.
        eapply parse_map; [|shelve].
        eapply parse_cat; intuition eauto.
        Unshelve.
        intuition eauto.
    - destruct H1; red_parses_all; try now econstructor.
      pose proof inv_map H0; clear H0; 
      repeat match goal with 
      | H: _ /\ _ |- _ => destruct H
      | H: @ex _ _ |- _ => destruct H
      end; subst.
      pose proof inv_cat H0; clear H0; 
      repeat match goal with 
      | H: _ /\ _ |- _ => destruct H
      | H: @ex _ _ |- _ => destruct H
      end; subst.
      econstructor; intuition eauto.
  Qed.

  Definition map_join {A B: Type} (xs: list A) (f: A -> list B) : list B := 
    concat (List.map f xs).

  Lemma In_mj:
    forall {A B: Type} (xs: list A) (f: A -> list B) v,
    In v (map_join xs f) -> 
    exists v', In v' xs /\
    In v (f v').
  Proof.
    intros ? ? ?.
    induction xs; intros; simpl in *; [inversion H|].
    pose proof in_app_or _ _ _ H.
    destruct H0.
    - eexists.
      split;
      eauto.
    - pose proof IHxs _ _ H0.
      destruct H1.
      intuition eauto.
  Qed.

  Lemma In_mj_inv:
    forall {A B: Type} (xs: list A) (f: A -> list B) v v',
    In v xs /\
    In v' (f v) ->
    In v' (map_join xs f).
  Proof.
    intros ? ? ?.
    induction xs; intros; simpl in *.
    - destruct H. inversion H.
    - 
      destruct H as [? ?].
      eapply in_or_app.
      destruct H; [ 
        left | 
        right; eapply IHxs; intuition eauto
      ].

      subst.
      simpl in *.
      auto.
  Qed.

  Equations interp_eps {A} (p: parser A) : list A := 
    interp_eps pFail := nil;
    interp_eps pAny := nil;
    interp_eps (pAlt l r) := interp_eps l ++ interp_eps r;
    (* interp_eps (pStar p) := List.map (fun x => x :: nil) (interp_eps p); *)
    interp_eps (pStar p) := nil :: nil;
    interp_eps (pPure x) := x :: nil;
    interp_eps (pBind p f) :=
      map_join (interp_eps p) (fun x => interp_eps (f x)).

  Lemma interp_eps_spec : 
    forall {A} (p: parser A) v, List.In v (interp_eps p) <-> Parses nil p v.
  Proof.
    intros ? ?.
    induction p; intros; simpl; try (now split; intros; contradiction || red_parses_all ).
    - split; intros.
      + pose proof in_app_or _ _ _ H.
        destruct H0; [eapply AltL; eapply IHp1 | eapply AltR; eapply IHp2]; intuition auto.
      + eapply in_or_app.
        red_parses_all.
        destruct H0; [left; eapply IHp1 | right; eapply IHp2]; intuition eauto.
    - split; intros; red_parses_all.
      destruct H; subst; auto; try constructor.
      inversion H.
    - split; intros.
      + pose proof In_mj _ _ _ H0.
        destruct H1.
        assert (forall A, @nil A = nil ++ nil) by (intros; exact eq_refl).
        erewrite H2.
        clear H2.
        destruct H1.
        econstructor.
        * eapply IHp.
          simpl in *.
          eauto.
        * simpl in *.
          eapply H.
          eapply H2.
      + 
        red_parses_all.
        pose proof app_eq_nil _ _ (eq_sym H0).
        destruct H3; subst.
        eapply In_mj_inv.
        split; 
        simpl in *;
        intuition eauto.
        * eapply IHp.
          eauto.
        * eapply H.
          auto.
  - split; intros.
    + destruct H; try now inversion H; subst; econstructor.
    + pose proof inv_star H.
      destruct H0; red_parses_all;
      exfalso;
      eapply H0;
      pose proof app_eq_nil _ _ (eq_sym H1).
      destruct H; intuition eauto.

  (* - split; intros.
    + destruct H; try now (subst; econstructor).
      pose proof @in_map_iff _ _ (fun x => x :: nil) (interp_eps p) v.
      destruct H0 as [? _].
      specialize (H0 H).
      clear H.
      red_parses_all.
      (* heck *)
      econstructor.
      eapply IHp.
      auto.
    + eapply in_map_iff.
      red_parses_all.
      destruct H0; red_parses_all.
      * eexists; intuition eauto.
        eapply IHp.
        auto.
      * 
        exfalso.
        eapply H.
        pose proof app_eq_nil _ _ (eq_sym H0).
        intuition eauto. *)
  Qed.
  
  Equations deriv {A} (c: ascii) (p: parser A) : parser A := 
    deriv _ pFail := pFail;
    deriv c pAny := pPure c;
    deriv c (pAlt l r) := alt (deriv c l) (deriv c r);
    deriv _ (pPure _) := pFail;
    (* pStar p = (p <$> pStar p)  *)
    deriv c (pStar p) := map (cat (deriv c p) (star p)) (fun '(x, xs) => x :: xs);
    deriv c (@pBind A B p f) :=  
      alt (bind (deriv c p) f)
      ((fix worker (xs: list A) : parser B := 
      match xs with 
      | x :: xs' => alt (deriv c (f x)) (worker xs')
      | nil => pFail
      end
      ) (interp_eps p)).

  Lemma deriv_sound:
    forall {A} (p: parser A) s c v,
    Parses s (deriv c p) v ->
    Parses (c :: s) p v.
  Proof.
    intros ? p.
    induction p; intros; simpl in *; try red_parses_all; try now econstructor.
    - erewrite alt_spec in H.
      red_parses_all.
      destruct H0; [eapply AltL | eapply AltR]; intuition eauto.
    - erewrite alt_spec in H0.
      red_parses_all.
      destruct H1.
      + erewrite bind_spec in H0.
        red_parses_all.
        assert (c :: x0 ++ x1 = (c :: x0) ++ x1) by exact eq_refl.
        erewrite H2.
        clear H2.
        econstructor; intuition eauto.
      + assert (forall v: A, In v (interp_eps p) -> Parses nil p v) by
          (intros; eapply interp_eps_spec; auto).
        revert H1.
        revert H0.
        induction (interp_eps p); intros; simpl in *; red_parses_all.
        erewrite alt_spec in H0.
        red_parses_all; subst.
        destruct H2.
        * assert (c :: s = nil ++ (c :: s)) by exact eq_refl.
          erewrite H2.
          econstructor; intuition eauto.
        * eapply IHl; intuition eauto.
    - pose proof inv_map H.
      clear H; red_parses_all.
      pose proof inv_cat H; clear H; red_parses_all.
      assert (c :: x0 ++ x1 = (c :: x0) ++ x1) by exact eq_refl.
      erewrite H1.
      clear H1.
      erewrite star_spec in H0.
      econstructor; intuition eauto.
      inversion H1.
  Qed.

  Lemma deriv_complete:
    forall {A} (p: parser A) s c v,
    Parses (c :: s) p v -> 
    Parses s (deriv c p) v.
  Proof.
    intros ? p.
    induction p; intros; simpl in *; try red_parses_all; try now econstructor.
    - inversion H0; subst; econstructor.
    - erewrite alt_spec.
      destruct H0; [eapply AltL | eapply AltR]; intuition eauto.
    - inversion H.
    - erewrite alt_spec.
      destruct x0.
      + eapply AltR.
        assert (Parses nil p x -> In x (interp_eps p)) by eapply interp_eps_spec.
        induction (interp_eps p); intros; simpl in *; try now (exfalso; intuition eauto).
        specialize (H3 H1).
        erewrite alt_spec.
        destruct H3; [eapply AltL; subst | eapply AltR];
        intuition eauto.
      + eapply AltL.
        erewrite bind_spec.
        inversion H0; subst.
        econstructor; intuition eauto.
    -
      destruct H0; [destruct H; inversion H|].
      setoid_rewrite <- star_spec in H.
      red_parses_all.
      destruct x; [exfalso; eapply H; intuition eauto|].
      eapply parse_map;
      try eapply parse_cat; 
      intuition eauto.
      2: {
        assert (s = x ++ x0) by shelve;
        eauto.
      }

      eapply IHp.
      inversion H0;
      subst; 
      intuition eauto.
      Unshelve.
      inversion H0;
      exact eq_refl.
  Qed.

  Fixpoint eval_derivs {A} (s: list ascii) (p: parser A) : parser A :=
    match s with 
    | nil => p
    | c :: cs => eval_derivs cs (deriv c p)
    end.
  
  Lemma derivs_sound {A}:
    forall s v (p: parser A),
    Parses nil (eval_derivs s p) v ->
    Parses s p v.
  Proof.
    intros s.
    induction s; intros; intuition eauto.
    simpl eval_derivs.
    eapply deriv_sound.
    intuition eauto.
  Qed.

  Lemma derivs_complete {A}:
    forall s v (p: parser A),
    Parses s p v -> 
    Parses nil (eval_derivs s p) v.
  Proof.
    intros s.
    induction s; intros; intuition eauto.
    simpl eval_derivs;
    eapply IHs.
    eapply deriv_complete.
    intuition eauto.
  Qed.

  Definition parses_derivs {A} (s: list ascii) (p: parser A) : list A := 
    interp_eps (eval_derivs s p).

  Theorem parses_spec {A}: 
    forall s v (p: parser A), 
      List.In v (parses_derivs s p) <-> 
      Parses s p v.
  Proof.
    intros.
    split; 
    intros; [ eapply derivs_sound; eapply interp_eps_spec | eapply interp_eps_spec; eapply derivs_complete ];
    intuition eauto.
  Qed.

  (* Print Assumptions parses_spec. *)


  Fixpoint any {A} (ps: list (parser A)) : parser A := 
    match ps with 
    | nil => pFail
    | p :: ps' => pAlt p (any ps')
    end.

  Fixpoint join {A} (ps: list (parser A)) (base: parser A) : parser (list A) := 
    match ps with 
    | nil => map base (fun x => x :: nil)
    | p :: ps' => 
      map (cat p (join ps' base)) (fun '(x, xs) => x :: xs)
    end.

  Fixpoint fold {A B: Set} (f: A -> B -> B) (acc: B) (ps: list (parser A)) := 
    match ps with 
    | nil => pPure acc
    | p :: ps' => 
       map (cat p (fold f acc ps')) (fun '(a, b) => f a b)
    end.

  Fixpoint repeat {A} (n: nat) (p: parser A) : parser (list A) := 
    match n with 
    | 0 => pPure nil
    | S n' => map (cat p (repeat n' p)) (fun '(x, xs) => x :: xs)
    end.

  Lemma repeat_spec {A: Set} n p:
    forall s (vs: list A), 
      Parses s (repeat n p) vs ->
      length vs = n.
  Proof.
    induction n; intros; simpl.
    - unfold repeat in H.
      red_parses_all.
    - unfold repeat in H.
      fold (@repeat A) in H.
      pose proof inv_map H.
      red_parses_all.
      destruct x.
      simpl length.
      pose proof inv_cat H0.
      red_parses_all.
      inversion H4.
      subst.
      erewrite IHn; intuition eauto.
  Qed.

  Lemma repeat_len_spec {A: Set} n: 
    forall s p (v: list A) n', 
      (forall s' v', Parses s' p v' -> length s' = n') ->
      Parses s (repeat n p) v -> 
      length s = n * n'.
  Proof.
    induction n; intros; simpl in *.
    - unfold repeat in H.
      inversion H0.
      exact eq_refl.
    - pose proof inv_map H0.
      clear H0.
      destruct H1 as [? [? ?]].
      pose proof inv_cat H0.
      clear H0.
      red_parses_all.
      erewrite app_length.
      erewrite (H _ _ H0).
      erewrite IHn; [exact eq_refl | exact H|].
      intuition eauto.
  Qed.

  Definition dep_bind {A: Set} {F: A -> Set} (p: parser A) (f: forall a, parser (F a)) : parser {a & F a} := 
    pBind p (fun x => pBind (f x) (fun b => pPure (existT _ x b))).

End Parsers.

Infix "$" := (cat) (at level 80).
Infix "@" := (map) (at level 80).
Infix "||" := (alt) (at level 50, left associativity).
Infix ">>=" := (pBind) (at level 80).
Infix ">=" := (dep_bind) (at level 70).

Notation "p1 $> p2" := (cat p1 p2 @ fun '(_,x) => x) (at level 50).
Notation "p1 <$ p2" := (cat p1 p2 @ fun '(x,_) => x) (at level 50).
