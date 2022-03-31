
Require Import Ascii.
Require Import Coq.Lists.List.

Require Import Parsers.Regular.

Local Open Scope char_scope.

Require Import Coq.micromega.Lia.

Ltac simpl_env := 
  repeat match goal with 
  | H: _ /\ _ |- _ => destruct H
  | H: @ex _ _ |- _ => destruct H
  end.
Ltac red_parses_all := 
  unfold "$>" in *;
  unfold "<$" in *;
  repeat (match goal with 
  | H: Parses _ (_ >>= _) _ |- _ =>
    let H' := fresh "H" in
    erewrite bind_spec in H;
    pose proof inv_bind H as H';
    clear H
  | H: Parses _ (pAlt _ _) _ |- _ =>
    let H' := fresh "H" in
    pose proof inv_alt H as H';
    clear H
  | H: Parses _ (pStar _) _ |- _ =>
    let H' := fresh "H" in
    pose proof inv_star H as H';
    clear H
  | H: Parses _ (char _) _ |- _ => 
    let H' := fresh "H" in
    pose proof inv_char H as H';
    clear H
  | H: Parses _ (pBind _ _) _ |- _ =>
    let H' := fresh "H" in
    pose proof inv_bind H as H';
    clear H
  | H: Parses _ (_ $ _) _ |- _ => 
    let H' := fresh "H" in 
    pose proof inv_cat H as H';
    clear H
  | H: Parses _ (pPure _) _ |- _ => 
    let H' := fresh "H" in 
    pose proof inv_pure H as H';
    clear H
  | H: Parses _ pAny _ |- _ => 
    let H' := fresh "H" in 
    pose proof inv_any H as H';
    clear H
  end; simpl_env; subst).

Section Single.
  Definition dig : parser nat := 
    (char "0" @ fun _ => 0) ||
    (char "1" @ fun _ => 1) || 
    (char "2" @ fun _ => 2) ||
    (char "3" @ fun _ => 3) ||
    (char "4" @ fun _ => 4) ||
    (char "5" @ fun _ => 5) ||
    (char "6" @ fun _ => 6) ||
    (char "7" @ fun _ => 7) ||
    (char "8" @ fun _ => 8) ||
    (char "9" @ fun _ => 9).

  Fixpoint digs_2_num (digs: list nat) : nat := 
    match digs with 
    | nil => 0
    | d :: ds => d + digs_2_num ds * 10
    end.

  Definition digs : parser (list nat) := pStar dig.

  Definition num : parser nat := digs @ fun x => digs_2_num (rev x).

  (* Eval vm_compute in parses_derivs ("1" :: "2" :: nil) num. *)
  Definition num_len : parser (nat * nat) := 
    digs @ fun x => (digs_2_num x, length x).

  Definition net_str_suff (n: nat) : parser (list ascii) := 
    (char ":" $> ((repeat n pAny) <$ char ",")).

  Lemma list_eq_char: 
    forall {A} {x:A} {xs xs'},
      x :: xs = x :: xs' <-> xs = xs'. 
  Proof.
    intros; split; intros.
    - inversion H; auto.
    - subst; auto.
  Qed.


  Lemma repeat_n_any_spec: 
    forall n s v,
      Parses s (repeat n pAny) v -> 
      s = v.
  Proof.
    intros n.
    induction n; intros; simpl repeat in *; red_parses_all; intuition eauto.
    erewrite app_nil_r; erewrite <- app_comm_cons; simpl;
    eauto.
    eapply list_eq_char.
    intuition eauto.
  Qed.

  Lemma net_str_suff_spec : 
    forall s n v, 
      Parses s (net_str_suff n) v -> 
      length s = n + 2 /\ s = ":" :: v ++ "," :: nil.
  Proof.
    intros.
    unfold net_str_suff in H.
    red_parses_all.
    simpl.
    repeat erewrite app_nil_r.
    erewrite app_length.
    simpl.
    split. 
    -
      erewrite repeat_len_spec with (n' := 1); [| | eauto].
      + Lia.lia.
      + intros.
        red_parses_all.
        auto.
    - pose proof repeat_n_any_spec _ _ _ H.
      subst.
      auto.
  Qed.

  Definition net_str := 
    num >>= net_str_suff.

  Lemma repeat_any: 
    forall {s s' n}, 
      Parses s (repeat n pAny) s' <->
      s = s' /\
      n = length s.
  Proof.
  intros ?.
    induction s.
    - simpl.
      intros.
      split; intros.
      + destruct n; simpl in *; red_parses_all; [intuition eauto|].
        exfalso.
        inversion H.
      + destruct H; subst.
        econstructor.
    - intros.
      split; intros.
      + 
        destruct n.
        * exfalso.
          simpl in H.
          inversion H.
        * simpl in H.
          red_parses_all.
          inversion H.
          simpl in *;
          subst.
          clear H.
          specialize (IHs x5 n).
          destruct IHs.
          erewrite app_nil_r in *.
          specialize (H H2).
          intuition (subst; eauto).
      + destruct H; subst.
        simpl repeat.
        eapply parse_map; [|shelve].
        eapply parse_cat; try econstructor.
        eapply IHs; intuition eauto.
        Unshelve.
        exact eq_refl.
  Qed.

  Theorem net_str_spec:
    forall s v, 
    Parses s net_str v <->
    exists s', 
      s = s' ++ (":" :: v ++ ("," :: nil)) /\  
      Parses s' num (length v).
  Proof.
    intros.
    split; intros.
    - unfold net_str in *.
      red_parses_all.
      pose proof net_str_suff_spec _ _ _ H1.
      simpl_env.
      unfold net_str_suff in *.
      red_parses_all.
      simpl in *; subst.
      repeat erewrite app_length in H.
      simpl in *.
      pose proof @repeat_any.
      specialize (H3 x5 v x).
      simpl_env.
      destruct H3.
      specialize (H3 H2).
      simpl_env; subst.
      repeat erewrite app_nil_r.
      eexists; intuition eauto.
    - intros.
      simpl_env; subst.
      unfold net_str.
      econstructor; eauto.
      unfold net_str_suff.
      assert (":" :: v ++ "," :: nil = (":" :: v ++ "," :: nil) ++ nil) by (erewrite app_nil_r; exact eq_refl).
      erewrite H; clear H.
      econstructor; [|shelve].
      assert (":" :: v ++ "," :: nil = (":" :: nil) ++ v ++ "," :: nil) by exact eq_refl.
      
      erewrite H; clear H.
      eapply parse_cat; try eapply parse_char; intuition eauto || intuition eauto.

      assert (v ++ "," :: nil = (v ++ "," :: nil) ++ nil) by (erewrite app_nil_r; exact eq_refl).
      erewrite H.
      clear H.
      econstructor; [|shelve].
      eapply parse_cat; intuition eauto; try eapply parse_char; intuition eauto.
      
      pose proof @repeat_any.
      evar (v': list ascii).
      specialize (H v v' (length v)).
      subst v'.
      eapply H.
      intuition eauto.
      Unshelve.
      3: econstructor.
      econstructor.
  Qed.

  Definition parse_netstr s := parses_derivs s net_str.

  (* Time Eval vm_compute in eval_derivs _ digs' eps_digs' test_digs num'. *)

  (* Eval vm_compute in parse' test_digs num. *)

  Definition test_hw_netstr := ("1" ::
  "3" ::
  ":" ::
  "h" ::
  "e" ::
  "l" ::
  "l" ::
  "o" ::
  "," ::
  " " ::
  "w" ::
  "o" ::
  "r" ::
  "l" ::
  "d" ::
  "!" ::
  "," :: nil).

  (* Time Eval vm_compute in parse_netstr test_hw_netstr. *)

End Single.

Module Nested.
  Inductive fmt : Set := 
  | base : fmt
  | nested: forall (inner: list fmt), fmt.

  Inductive sized_fmt : Set := 
  | base_sz: forall (s: list ascii) (sz: nat), sized_fmt
  | nested_sz: forall (inner: list sized_fmt) (sz: nat), sized_fmt.

  Fixpoint ind_fmt (P: fmt -> Prop) (P_base: P base) (rec: forall nst, Forall P nst -> P (nested nst)) (f: fmt) : P f :=
    match f with 
    | base => P_base
    | nested fs => 
      rec _ ((fix lrec l := 
        match l as l' return Forall P l' with 
        | nil => Forall_nil _
        | f :: fs => Forall_cons _ (ind_fmt _ P_base rec _) (lrec fs)
        end
      ) fs)
    end.

  Fixpoint ind_sz_fmt (P: sized_fmt -> Prop) (P_base: forall s n, P (base_sz s n)) (rec: forall nst n, Forall P nst -> P (nested_sz nst n)) (f: sized_fmt) : P f :=
    match f with 
    | base_sz s n => P_base s n
    | nested_sz fs n =>
      rec _ _ ((fix lrec l := 
        match l as l' return Forall P l' with 
        | nil => Forall_nil _
        | f :: fs => Forall_cons _ (ind_sz_fmt _ P_base rec _) (lrec fs)
        end
      ) fs)
    end.

  Definition get_sz (f: sized_fmt) := 
    match f with 
    | base_sz _ x => x
    | nested_sz _ x => x
    end.

  Fixpoint sum_sizes_deep (sfmt: sized_fmt) : nat := 
    match sfmt with 
    | base_sz _ x => x
    | nested_sz inner _ => List.fold_left (fun x y => x + y) (List.map sum_sizes_deep inner) 0
    end.

  Inductive proper_sz : sized_fmt -> Prop :=
    | proper_base: forall data len, length data = len -> proper_sz (base_sz data len)
    | proper_nested: forall inner len, 
      Forall proper_sz inner -> 
      sum_sizes_deep (nested_sz inner len) = len -> 
      proper_sz (nested_sz inner len).
  Require Import Coq.Arith.PeanoNat.
  Lemma proper_shallow: 
    forall f, 
    proper_sz f -> 
    get_sz f = sum_sizes_deep f.
  Proof.
    intros f.
    induction f using ind_sz_fmt; 
    intros; simpl; intuition eauto.
    revert H.
    revert H0.
    revert n.
    induction nst; intros; simpl; intuition eauto.
    - inversion H0; subst.
      simpl in H4; 
      subst; auto.
    - inversion H0;
      simpl in *;
      subst.
      auto.
  Qed.

  Lemma fold_sum: 
    forall n l,
      n + List.fold_left (fun x y => x + y) l 0 = List.fold_left (fun x y => x + y) l n.
  Proof.
    intros.
    revert n;
    induction l; intros; simpl; try Lia.lia.
    erewrite <- IHl with (n := a).
    erewrite Plus.plus_assoc.
    eapply IHl.
  Qed.


  Lemma proper_sz_cons : 
    forall f inner len n, 
      proper_sz (nested_sz inner len) -> 
      proper_sz f -> 
      get_sz f = n -> 
      proper_sz (nested_sz (f :: inner) (n + len)).
  Proof.
    intros.
    econstructor.
    - inversion H;
      econstructor; intuition eauto.
    - pose proof @proper_shallow.
      inversion H;
      subst.
      erewrite <- H6.
      erewrite proper_shallow; intuition eauto.
      simpl sum_sizes_deep.
      erewrite fold_sum.
      auto.
  Qed.


  Fixpoint add_len {A: Set} (p: parser A) : parser (A * nat) :=
    match p with 
    | pPure v => pPure v @ fun x => (x, 0)
    | pAny => pAny @ fun x => (x, 1)
    | pFail => pFail
    | pBind p f => 
      add_len p >>= 
      fun '(x, n) => (add_len (f x) @ fun '(y, m) => (y, n + m))
    | pStar p => pStar (add_len p) @
      fun xs => let '(r, lens) := List.split xs in 
        (r, List.fold_left (fun x y => x + y) lens 0)

    | pAlt l r => pAlt (add_len l) (add_len r)
    end. 

  Definition num_with_len := add_len num. 

  (* Time Eval vm_compute in parses_derivs ("0" :: "0" :: "1" :: "2" :: nil) num_with_len. *)

  Lemma inv_add_len: 
    forall {A} {s} {p: parser A} {v},
      Parses s (add_len p) v -> 
      exists v' n,
      Parses s p v' /\ n = length s /\ v = (v', n).
  Proof.
    intros ? ? ?.
    revert s.
    induction p; intros; simpl add_len in *;
    try match goal with 
    | H: Parses _ pFail _ |- _ => inversion H
    end.
    - red_parses_all; simpl;
      repeat match goal with
      | |- exists _, _ => eexists
      end;
      intuition (econstructor || eauto).
    - pose proof inv_alt H.
      clear H.
      destruct H0.
      + 
        specialize (IHp1 s v H).
        simpl_env.
        repeat match goal with
        | |- exists _, _ => eexists
        end;
        intuition eauto; try eapply AltL; intuition eauto;
        subst;
        exact eq_refl.

      + 
        specialize (IHp2 s v H).
        simpl_env.
        repeat match goal with
        | |- exists _, _ => eexists
        end;
        intuition eauto; try eapply AltR; intuition eauto;
        subst;
        exact eq_refl.
    - red_parses_all.
      repeat match goal with
      | |- exists _, _ => eexists
      end; simpl; try econstructor; intuition eauto.
      econstructor.
    - red_parses_all.
      specialize (IHp x0 x H1).
      simpl_env; subst.
      red_parses_all.
      specialize (H x2 x3 x H3).
      simpl_env; subst.
      repeat erewrite app_nil_r.
      exists x1.
      exists (length x0 + length x3);
      erewrite app_length;
      intuition eauto.
      econstructor; intuition eauto.
    - red_parses_all.
      destruct H; simpl_env; subst; simpl in *.
      + do 2 eexists; intuition (econstructor || eauto).
      + erewrite app_nil_r.
        specialize (IHp x1 x3 H3).
        simpl_env; subst.
        do 2 eexists; intuition eauto.
        2: shelve.
        (* TODO: need an induction principle for pstar parsing *)
        admit.

  Admitted. 


  Lemma add_len_spec : 
    forall {A} {s} {p: parser A} {v n}, 
      Parses s p v -> 
      length s = n -> 
      Parses s (add_len p) (v, n).
  Proof.
    intros ? ? ?.
    revert s.
    induction p; intros; red_parses_all; simpl add_len;
    try now (econstructor; intuition eauto);
    intuition eauto.
    - inversion H.
    - eapply parse_map; try econstructor; intuition eauto.
    - destruct H1; [eapply AltL | eapply AltR]; intuition eauto.
    - eapply parse_map; try econstructor; intuition eauto.
    - admit.
      (* erewrite bind_spec. econstructor; intuition eauto.
      eapply parse_map; intuition eauto.
      erewrite app_length; intuition eauto. *)
    - destruct H1; simpl_env; subst.
      + eapply parse_map; try econstructor; intuition eauto.
      + eapply parse_map; admit.
        (* uh oh... can't prove this... *)
  Admitted.

  Definition net_with_len : parser (sized_fmt * nat) := 
    num_with_len >>= fun '(n, len) => (net_str_suff n) >>= fun b => pPure (base_sz b n, len + n + 2).

  Definition test_fmt : sized_fmt := 
    nested_sz ((nested_sz (base_sz ("a" :: "b" :: "c" :: nil) 3 :: nil) 3) :: nil) 3.

  Goal proper_sz test_fmt.
  Proof.
    unfold test_fmt.
    repeat econstructor.
  Qed.

  (* Eval vm_compute in proper_sz test_fmt. *)

  Fixpoint sum_sizes_shallow (sfs: list (sized_fmt)) : nat := 
    match sfs with 
    | nil => 0
    | sf :: sfs' => 
      match sf with 
      | base_sz _ n => n
      | nested_sz _ n => n 
      end + sum_sizes_shallow sfs'
    end.

  Equations interp_fmt (f: fmt) : parser (sized_fmt * nat) by struct f :=
    interp_fmt base := net_with_len;
    interp_fmt (nested fs) := 
      (num_with_len <$ char ":") >>= fun '(n, len) => 
      (filter (interp_fmt_lst fs <$ char ",") (fun '(fs, n') => Nat.eqb n n') @ 
      fun '(fs, n') => (nested_sz fs (sum_sizes_shallow fs), n' + len + 2))
  where interp_fmt_lst (fs: list fmt) : parser (list sized_fmt * nat) by struct fs := 
    interp_fmt_lst nil := pPure (nil, 0);
    interp_fmt_lst (f :: fs') := 
      interp_fmt f $ interp_fmt_lst fs' @ fun '((sf, sz), (sfs, sz')) => (sf :: sfs, sz + sz').
  
  Lemma net_with_len_corr : 
    forall s v n, 
      Parses s net_with_len (v, n) -> 
      proper_sz v.
  Proof.
    intros.
    unfold net_with_len in H.
    red_parses_all.
    destruct x.
    red_parses_all.
    pose proof net_str_suff_spec _ _ _ H1.
    
    inversion H2.
    simpl_env; subst.
    econstructor.
    
    simpl length in H.
    erewrite app_length in H.
    simpl length in H.
    Lia.lia.
  Qed.

  Lemma interp_fmt_lst_corr: 
    forall nst c s l n,
      (Forall
        (fun f : fmt =>
        forall (s : string) (v : sized_fmt) (n : nat),
        Parses s (interp_fmt f) (v, n) -> proper_sz v) 
        (c :: nst)) -> 
      (Parses s (interp_fmt_clause_2_interp_fmt_lst interp_fmt (c :: nst) nst) (l, n)) -> 
      proper_sz (nested_sz l (sum_sizes_shallow l)).
  Proof.
    intros nst c s l n.
    revert n.
    revert nst.
    revert s.
    revert c.
    induction l; intros; simpl in *.
    - red_parses_all.
      destruct nst; simpl in *; intuition eauto; red_parses_all.
      * 
        inversion H1.
        econstructor; intuition eauto.
      * destruct x4;
        destruct x5;
        inversion H3.
    - destruct nst; [simpl in *; red_parses_all; inversion H1|].
      eapply proper_sz_cons.
      * simpl in H0.
        
        eapply IHl; intuition eauto.
        red_parses_all.
        admit.
      * inversion H.
        admit.
        (* inversion H5.
        subst.
        intuition eauto. *)
      * destruct a; auto.
        (* assert proper_sz (nested_sz l0 (sum_sizes_shallow l0)) by shelve.
        eapply proper_sz_cons; intuition eauto. *)
    Admitted.

  Theorem interp_fmt_corr: 
    forall f s v n, 
      Parses s (interp_fmt f) (v, n) -> 
      proper_sz v.
  Proof.
    intros f.
    induction f using ind_fmt.
    - intros; eapply net_with_len_corr; intuition eauto.
    - induction nst.
      + intros.
        autorewrite with interp_fmt in H0.
        red_parses_all.
        destruct x.
        red_parses_all.
        pose proof inv_filter H2.
        clear H2.
        red_parses_all.
        simpl_env.
        destruct x.
        red_parses_all.
        inversion H4.
        simpl.
        subst.
        inversion H3.
        subst.
        simpl.
        repeat econstructor.
      + intros.
        autorewrite with interp_fmt in H0.
        red_parses_all.
        destruct x.
        red_parses_all.
        pose proof inv_filter H2.
        clear H2.
        simpl_env.
        red_parses_all.
        destruct x8.
        destruct x9.
        inversion H3;
        subst.
        clear H3.
        simpl.
        eapply proper_sz_cons; intuition eauto.
        * eapply interp_fmt_lst_corr; intuition eauto.
        * inversion H.
          eapply H6; intuition eauto.
  Qed.
 
    Definition test_hw_nested := (
      "1" ::
      "6" ::
      ":" ::
      "5" :: 
      ":" ::
      "h" ::
      "e" ::
      "l" ::
      "l" ::
      "o" ::
      "," ::
      "5" ::
      ":" ::
      "w" ::
      "o" ::
      "r" ::
      "l" ::
      "d" ::
      "," ::
      "," :: nil).

  (* Eval vm_compute in parses_derivs test_hw_nested (interp_fmt (nested (base :: base :: nil))). *)

End Nested.

