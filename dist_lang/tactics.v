From distris Require Export lang notation.
Set Default Proof Using "Type".
Import ground_lang.
Import Network.

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implementation substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr0 :=
  (* Value together with the original expression *)
  | Val (v : val) (e : ground_lang.expr) (H : to_val e = Some v)
  | ClosedExpr (e : ground_lang.expr) `{!Closed [] e}
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr0)
  | App (e1 e2 : expr0)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr0)
  | BinOp (op : bin_op) (e1 e2 : expr0)
  | If (e0 e1 e2 : expr0)
  | FindFrom (e0 e1 e2 : expr0)
  | Substring (e0 e1 e2 : expr0)
  (* Products *)
  | Pair (e1 e2 : expr0)
  | Fst (e : expr0)
  | Snd (e : expr0)
  (* Sums *)
  | InjL (e : expr0)
  | InjR (e : expr0)
  | Case (e0 : expr0) (e1 : expr0) (e2 : expr0)
  (* Concurrency *)
  | Fork (e : expr0)
  (* Heap *)
  | Alloc (e : expr0)
  | Load (e : expr0)
  | Store (e1 : expr0) (e2 : expr0)
  | CAS (e0 : expr0) (e1 : expr0) (e2 : expr0)
  (* Sockets *)
  | MakeAddress (e1 : expr0) (e2 : expr0)
  | NewSocket (e0 : expr0) (e1 : expr0) (e2 : expr0)
  | SocketBind (e1 : expr0) (e2 : expr0)
  | SendTo (e0 : expr0) (e1 : expr0) (e2 : expr0)
  | ReceiveFrom (e : expr0)
  | Start (n : base_lit) (i : base_lit) (e : expr0)
.

Definition expr : Type := node * expr0.

Fixpoint to_ground_expr (e : expr0) : ground_lang.expr :=
  match e with
  | Val v e' _ => e'
  | ClosedExpr e => e
  | Var x => ground_lang.Var x
  | Rec f x e => ground_lang.Rec f x (to_ground_expr e)
  | App e1 e2 => ground_lang.App (to_ground_expr e1) (to_ground_expr e2)
  | Lit l => ground_lang.Lit l
  | UnOp op e => ground_lang.UnOp op (to_ground_expr e)
  | BinOp op e1 e2 => ground_lang.BinOp op (to_ground_expr e1) (to_ground_expr e2)
  | If e0 e1 e2 => ground_lang.If (to_ground_expr e0)
                                  (to_ground_expr e1) (to_ground_expr e2)
  | FindFrom e0 e1 e2 => ground_lang.FindFrom (to_ground_expr e0)
                                              (to_ground_expr e1) (to_ground_expr e2)
  | Substring e0 e1 e2 => ground_lang.Substring (to_ground_expr e0)
                                                (to_ground_expr e1) (to_ground_expr e2)
  | Pair e1 e2 => ground_lang.Pair (to_ground_expr e1) (to_ground_expr e2)
  | Fst e => ground_lang.Fst (to_ground_expr e)
  | Snd e => ground_lang.Snd (to_ground_expr e)
  | InjL e => ground_lang.InjL (to_ground_expr e)
  | InjR e => ground_lang.InjR (to_ground_expr e)
  | Case e0 e1 e2 => ground_lang.Case (to_ground_expr e0)
                                      (to_ground_expr e1) (to_ground_expr e2)
  | Fork e => ground_lang.Fork (to_ground_expr e)
  | Alloc e => ground_lang.Alloc (to_ground_expr e)
  | Load e => ground_lang.Load (to_ground_expr e)
  | Store e1 e2 => ground_lang.Store (to_ground_expr e1) (to_ground_expr e2)
  | CAS e0 e1 e2 => ground_lang.CAS (to_ground_expr e0) (to_ground_expr e1)
                                    (to_ground_expr e2)
  | MakeAddress e1 e2 => ground_lang.MakeAddress (to_ground_expr e1) (to_ground_expr e2)
  | NewSocket e0 e1 e2 =>
    ground_lang.NewSocket (to_ground_expr e0) (to_ground_expr e1) (to_ground_expr e2)
  | SocketBind e1 e2 => ground_lang.SocketBind (to_ground_expr e1) (to_ground_expr e2)
  | SendTo e0 e1 e2 => ground_lang.SendTo (to_ground_expr e0)
                                          (to_ground_expr e1) (to_ground_expr e2)
  | ReceiveFrom e => ground_lang.ReceiveFrom (to_ground_expr e)
  | Start n i e => ground_lang.Start n i (to_ground_expr e)
  end.

Definition to_expr (e : node * expr0) : dist_lang.expr :=
  {| expr_n := e.1; expr_e := to_ground_expr (e.2) |}.

Ltac of_expr e :=
  lazymatch e with
  | ground_lang.Var ?x => constr:(Var x)
  | ground_lang.Rec ?f ?x ?e => let e := of_expr e in constr:(Rec f x e)
  | ground_lang.App ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(App e1 e2)
  | ground_lang.Lit ?l => constr:(Lit l)
  | ground_lang.UnOp ?op ?e => let e := of_expr e in constr:(UnOp op e)
  | ground_lang.BinOp ?op ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | ground_lang.If ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(If e0 e1 e2)
  | ground_lang.FindFrom ?e0 ?e1 ?e2 =>
    let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(FindFrom e0 e1 e2)
  | ground_lang.Substring ?e0 ?e1 ?e2 =>
    let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(Substring e0 e1 e2)
  | ground_lang.Pair ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Pair e1 e2)
  | ground_lang.Fst ?e => let e := of_expr e in constr:(Fst e)
  | ground_lang.Snd ?e => let e := of_expr e in constr:(Snd e)
  | ground_lang.InjL ?e => let e := of_expr e in constr:(InjL e)
  | ground_lang.InjR ?e => let e := of_expr e in constr:(InjR e)
  | ground_lang.Case ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(Case e0 e1 e2)
  | ground_lang.Fork ?e => let e := of_expr e in constr:(Fork e)
  | ground_lang.Alloc ?e => let e := of_expr e in constr:(Alloc e)
  | ground_lang.Load ?e => let e := of_expr e in constr:(Load e)
  | ground_lang.Store ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store e1 e2)
  | ground_lang.CAS ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(CAS e0 e1 e2)
  | ground_lang.MakeAddress ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(MakeAddress e1 e2)
  | ground_lang.NewSocket ?e0 ?e1 ?e2 =>
    let e0 := of_expr e0 in
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(NewSocket e0 e1 e2)
  | ground_lang.SocketBind ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(SocketBind e1 e2)
  | ground_lang.SendTo ?e0 ?e1 ?e2 =>
    let e0 := of_expr e0 in
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(SendTo e0 e1 e2)
  | ground_lang.Start ?n ?i ?e =>
    let e := of_expr e in
    constr:(Start n i e)
  | ground_lang.ReceiveFrom ?e => let e := of_expr e in constr:(ReceiveFrom e)
  | to_expr ?e => e
  | of_val ?v => constr:(Val v (of_val v) (to_of_val v))
  | _ => match goal with
         | H : to_val e = Some ?v |- _ => constr:(Val v e H)
         | H : Closed [] e |- _ => constr:(@ClosedExpr e H)
         end
  end.

Fixpoint is_closed0 (X : list string) (e : expr0) : bool :=
  match e with
  | Val _ _ _ | ClosedExpr _ => true
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed0 (f :b: x :b: X) e
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e
  | ReceiveFrom e | Start _ _ e =>
     is_closed0 X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | SocketBind e1 e2
  | MakeAddress e1 e2 =>
     is_closed0 X e1 && is_closed0 X e2
  | If e0 e1 e2 | Case e0 e1 e2 | NewSocket e0 e1 e2 | SendTo e0 e1 e2
  | FindFrom e0 e1 e2 | Substring e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed0 X e0 && is_closed0 X e1 && is_closed0 X e2
  end.
Definition is_closed X (e : expr) : bool := is_closed0 X (e.2).

Lemma is_closed_correct0 X e : is_closed0 X e → ground_lang.is_closed X (to_ground_expr e).
Proof.
  revert X.
  induction e; naive_solver eauto using is_closed_to_val, is_closed_weaken_nil.
Qed.
Lemma is_closed_correct X e : is_closed X e → dist_lang.is_closed X (to_expr e).
Proof. destruct e. by move/is_closed_correct0. Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Fixpoint to_val0 (e : expr0) : option ground_lang.val :=
  match e with
  | Val v _ _ => Some v
  | Rec f x e =>
     if decide (is_closed0 (f :b: x :b: []) e) is left H
     then Some (@RecV f x (to_ground_expr e) (is_closed_correct0 _ _ H)) else None
  | Lit l => Some (LitV l)
  | Pair e1 e2 => v1 ← to_val0 e1; v2 ← to_val0 e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val0 e
  | InjR e => InjRV <$> to_val0 e
  | _ => None
  end.
Definition to_val (e : expr) : option dist_lang.val :=
  (λ v0, 〈e.1; v0〉) <$> to_val0 (e.2).

Lemma to_val0_Some e v :
  to_val0 e = Some v → ground_lang.to_val (to_ground_expr e) = Some v.
Proof.
  revert v. induction e; intros; simplify_option_eq; rewrite ?to_of_val; auto.
  - do 2 f_equal. apply proof_irrel.
  - exfalso. unfold Closed in *; eauto using is_closed_correct0.
Qed.
Lemma to_val_Some e v :
  to_val e = Some v → dist_lang.to_val (to_expr e) = Some v.
Proof.
  destruct e, v. cbv -[to_val0 ground_lang.to_val to_ground_expr].
  case H: (to_val0 e) => //.
  erewrite to_val0_Some; by eauto.
Qed.
Lemma to_val0_is_Some e :
  is_Some (to_val0 e) → is_Some (ground_lang.to_val (to_ground_expr e)).
Proof. intros [v ?]; exists v; eauto using to_val0_Some. Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → is_Some (dist_lang.to_val (to_expr e)).
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.

Fixpoint subst0 (x : string) (es : expr0) (e : expr0) : expr0 :=
  match e with
  | Val v e H => Val v e H
  | ClosedExpr e => ClosedExpr e
  | Var y => if decide (x = y) then es else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst0 x es e else e
  | App e1 e2 => App (subst0 x es e1) (subst0 x es e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (subst0 x es e)
  | BinOp op e1 e2 => BinOp op (subst0 x es e1) (subst0 x es e2)
  | If e0 e1 e2 => If (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | FindFrom e0 e1 e2 => FindFrom (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | Substring e0 e1 e2 => Substring (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | Pair e1 e2 => Pair (subst0 x es e1) (subst0 x es e2)
  | Fst e => Fst (subst0 x es e)
  | Snd e => Snd (subst0 x es e)
  | InjL e => InjL (subst0 x es e)
  | InjR e => InjR (subst0 x es e)
  | Case e0 e1 e2 => Case (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | Fork e => Fork (subst0 x es e)
  | Alloc e => Alloc (subst0 x es e)
  | Load e => Load (subst0 x es e)
  | Store e1 e2 => Store (subst0 x es e1) (subst0 x es e2)
  | CAS e0 e1 e2 => CAS (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | MakeAddress e1 e2 => MakeAddress (subst0 x es e1) (subst0 x es e2)
  | NewSocket e0 e1 e2 => NewSocket (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | SocketBind e1 e2 => SocketBind (subst0 x es e1) (subst0 x es e2)
  | SendTo e0 e1 e2 => SendTo (subst0 x es e0) (subst0 x es e1) (subst0 x es e2)
  | ReceiveFrom e => ReceiveFrom (subst0 x es e)
  | Start n i e => Start n i (subst0 x es e)
  end.
Definition subst x es (e : expr) := (e.1, subst0 x es (e.2)).

Lemma to_ground_expr_subst0 x er e :
  to_ground_expr (subst0 x er e) = ground_lang.subst x (to_ground_expr er)
                                                    (to_ground_expr e).
Proof.
  induction e; simpl; repeat case_decide;
    f_equal; eauto using subst_is_closed_nil, is_closed_to_val, eq_sym.
Qed.

Lemma to_expr_subst x er e :
  to_expr (subst x er e) = dist_lang.subst x (to_ground_expr er) (to_expr e).
Proof.
  destruct e. cbv -[to_ground_expr subst0 ground_lang.subst].
  by rewrite to_ground_expr_subst0.
Qed.

Definition is_atomic0 (e : expr0) :=
  match e with
  | Alloc e => bool_decide (is_Some (to_val0 e))
  | Load e => bool_decide (is_Some (to_val0 e))
  | Store e1 e2 => bool_decide (is_Some (to_val0 e1) ∧ is_Some (to_val0 e2))
  | CAS e0 e1 e2 => bool_decide (is_Some (to_val0 e0) ∧ is_Some (to_val0 e1) ∧
                                 is_Some (to_val0 e2))
  | NewSocket e0 e1 e2 =>
     bool_decide (is_Some (to_val0 e0) ∧ is_Some (to_val0 e1) ∧ is_Some (to_val0 e2))
  | SocketBind e1 e2 => bool_decide (is_Some (to_val0 e1) ∧ is_Some (to_val0 e2))
  | SendTo e0 e1 e2 =>
    bool_decide (is_Some (to_val0 e0) ∧ is_Some (to_val0 e1) ∧ is_Some (to_val0 e2))
  | ReceiveFrom e => bool_decide (is_Some (to_val0 e))
  | Fork _ => true
  (* Make "skip" atomic *)
  | App (Rec _ _ (Lit _)) (Lit _) => true
  | _ => false
  end.
Definition is_atomic (e : expr) := is_atomic0 (e.2).

Lemma is_atomic_correct s e : is_atomic e → Atomic s (to_expr e).
  destruct e as [n e].
  intros HE; apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ1 [n' e'] σ2 ef Hstep; simpl in *.
    destruct e=> //=; repeat (simplify_eq/=; case_match=>//);
    inversion Hstep; (inversion BaseStep || inversion SocketStep);
      rewrite ?/dist_lang.to_val /= ?ground_lang.to_of_val /=; eauto;
      rewrite ?ground_lang.to_of_val; eauto; simplify_eq.
    match goal with
      H : Is_true (is_atomic (_, App ?e1 ?e2)) |- _ =>
      destruct e1 as [| | | ? ? [] | | | | | | | | | | | | | | | | | | | | | | | |];
        destruct e2; simpl in *; try done
    end.
    match goal with
      H : (rec: _ _ := _)%E = _ |- _ => inversion H; simplify_eq
    end.
    unfold subst'; repeat (simplify_eq/=; case_match=>//); eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki [n' e'] Hfill.
    apply/fmap_is_Some. inversion Hfill as [[Hn Hfill']]; subst; clear Hfill.
    simpl.
    destruct e=> //; destruct Ki; repeat (simplify_eq/=; case_match=>//);
      rewrite /is_atomic /is_atomic0 in HE; cbn in HE;
        repeat case_match; simpl in *; simplify_eq; try done;
          try eapply to_val0_is_Some; try naive_solver.
    assert (∀ l f x, Closed (f :b: x :b: []) #l) by done.
    erewrite to_val_rec; eauto.
Qed.

End W.

Ltac solve_ground_lang_closed :=
  match goal with
  | |- ground_lang.Closed ?X ?e =>
     let e' := W.of_expr e in change (ground_lang.Closed X (W.to_ground_expr e'));
     apply W.is_closed_correct0; vm_compute; exact I
  end.
Hint Extern 0 (ground_lang.Closed _ _) => solve_ground_lang_closed : typeclass_instances.

Ltac solve_closed :=
  match goal with
  | |- dist_lang.Closed ?X ⟨?n;?e⟩ =>
    apply dist_lang.closed_ground_lang; unfold expr_e;
    let e' := W.of_expr e in change (ground_lang.Closed X (W.to_ground_expr e'));
    apply W.is_closed_correct0; vm_compute; exact I
  end.
Hint Extern 0 (dist_lang.Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_into_val :=
  repeat match goal with
  | H : dist_lang.Closed ?X ?e |- _ => apply is_closed_ground_lang in H; simpl in H
  end;
  match goal with
  | |- IntoVal ⟨?n;?e⟩ ?v =>
    let e' := W.of_expr e in
    change (dist_lang.to_val (W.to_expr (n,e')) = Some v);
      apply W.to_val_Some; unfold W.to_expr,W.to_ground_expr; unfold W.to_val; simpl;
        reflexivity
  end.
Hint Extern 10 (IntoVal _ _) => solve_into_val : typeclass_instances.

Ltac solve_as_val :=
  repeat match goal with
  | H : dist_lang.Closed ?X ?e |- _ => apply is_closed_ground_lang in H; simpl in H
  end;
  match goal with
  | |- AsVal ⟨?n;?e⟩ =>
    let e' := W.of_expr e in
    change (is_Some (dist_lang.to_val (W.to_expr (n,e'))));
    apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Hint Extern 10 (AsVal _) => solve_as_val : typeclass_instances.

Ltac solve_atomic :=
  match goal with
  | |- Atomic ?s ⟨?n;?e⟩ =>
     let e' := W.of_expr e in change (Atomic s (W.to_expr (n,e')));
     apply W.is_atomic_correct; vm_compute; exact I
  end.
Hint Extern 10 (Atomic _ _) => solve_atomic : typeclass_instances.
Hint Extern 10 (language.atomic _) => solve_atomic : typeclass_instances.

(** Substitution *)
Ltac simpl_subst :=
  simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  | |- context [ground_lang.subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (ground_lang.subst x er e) with
              (ground_lang.subst x (W.to_ground_expr er') (W.to_ground_expr e'));
      rewrite <-(W.to_ground_expr_subst0 x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr, W.to_ground_expr.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  lazymatch e with
  | ground_lang.of_val ?v => v
  | Rec ?f ?x ?e => constr:(RecV f x e)
  | Lit ?l => constr:(LitV l)
  | Pair ?e1 ?e2 =>
    let v1 := go e1 in let v2 := go e2 in constr:(PairV v1 v2)
  | InjL ?e => let v := go e in constr:(InjLV v)
  | InjR ?e => let v := go e in constr:(InjRV v)
  end in let v := go e in tac v
.

Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
  | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | FindFrom ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (FindFromRCtx v0 v1 :: K) e2)
     | go (FindFromMCtx v0 e2 :: K) e1 ])
  | FindFrom ?e0 ?e1 ?e2 => go (FindFromLCtx e1 e2 :: K) e0
  | Substring ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (SubstringRCtx v0 v1 :: K) e2)
     | go (SubstringMCtx v0 e2 :: K) e1 ])
  | Substring ?e0 ?e1 ?e2 => go (SubstringLCtx e1 e2 :: K) e0
  | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
  | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (StoreRCtx v1 :: K) e2)
  | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1
  | CAS ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasRCtx v0 v1 :: K) e2)
     | go (CasMCtx v0 e2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0
  | MakeAddress ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (MakeAddressRCtx v1 :: K) e2)
  | MakeAddress ?e1 ?e2 => go (MakeAddressLCtx e2 :: K) e1
  | NewSocket ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (NewSocketRCtx v0 v1 :: K) e2)
     | go (NewSocketMCtx v0 e2 :: K) e1 ])
  | NewSocket ?e0 ?e1 ?e2 => go (NewSocketLCtx e1 e2 :: K) e0
  | SocketBind ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (SocketBindRCtx v1 :: K) e2)
  | SocketBind ?e1 ?e2 => go (SocketBindLCtx e2 :: K) e1
  | SendTo ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (SendToRCtx v0 v1 :: K) e2)
     | go (SendToMCtx v0 e2 :: K) e1 ])
  | SendTo ?e0 ?e1 ?e2 => go (SendToLCtx e1 e2 :: K) e0
  | ReceiveFrom ?e => go (ReceiveFromCtx :: K) e
  end in go (@nil ectx_item) e.
