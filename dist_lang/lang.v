From distris Require Export network.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe.
Require Import Coq.Strings.Ascii.
From stdpp Require Export strings.
From stdpp Require Import gmap fin_collections pretty.
Set Default Proof Using "Type".

Module ground_lang.
  Local Open Scope Z_scope.
  Import Network.

  (** Expressions and vals. *)
  Definition loc := positive. (* Really, any countable type. *)

  Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc)
  | LitString (s : string)
  | LitAddressFamily (a : address_family)
  | LitSocketType (t : socket_type) | LitProtocol (p : protocol)
  | LitSocket (s : socket_handle) | LitSocketAddress (s : socket_address)
  .
  Inductive un_op : Set :=
  | NegOp | MinusUnOp | StringOfInt | IntOfString | StringLength.
  Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | StringApp.

  Inductive binder := BAnon | BNamed : string → binder.
  Delimit Scope binder_scope with bind.
  Bind Scope binder_scope with binder.
  Definition cons_binder (mx : binder) (X : list string) : list string :=
    match mx with BAnon => X | BNamed x => x :: X end.
  Infix ":b:" := cons_binder (at level 60, right associativity).
  Global Instance binder_eq_dec_eq : EqDecision binder.
  Proof. solve_decision. Defined.

  Global Instance set_unfold_cons_binder x mx X P :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
  Proof.
    constructor. rewrite -(set_unfold (x ∈ X) P).
    destruct mx; rewrite /= ?elem_of_cons; naive_solver.
  Qed.

  Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | FindFrom (e0 e1 e2 : expr)
  | Substring (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
  (* Sockets/Network *)
  | MakeAddress (e1 : expr) (e2 : expr)
  | NewSocket (e1 : expr) (e2 : expr) (e3 : expr)
  | SocketBind (e1 : expr) (e2 : expr)
  | SendTo (e1 : expr) (e2 : expr) (e3 : expr)
  | ReceiveFrom (e1 : expr)
  | Start (node : base_lit) (ip : base_lit) (e : expr).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with E.

  Fixpoint is_closed (X : list string) (e : expr) : bool :=
    match e with
    | Var x => bool_decide (x ∈ X)
    | Rec f x e => is_closed (f :b: x :b: X) e
    | Lit _ => true
    | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e
    | Alloc e | Load e | ReceiveFrom e | Start _ _ e =>
      is_closed X e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2
    | MakeAddress e1 e2 | SocketBind e1 e2 =>
      is_closed X e1 && is_closed X e2
    | If e0 e1 e2 | Case e0 e1 e2 | NewSocket e0 e1 e2
    | SendTo e0 e1 e2 | FindFrom e0 e1 e2 | Substring e0 e1 e2 | CAS e0 e1 e2
      => is_closed X e0 && is_closed X e1 && is_closed X e2
    end.

  Class Closed (X : list string) (e : expr) := closed : is_closed X e.
  Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.
  Global Instance closed_decision env e : Decision (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.

  Inductive val :=
  | RecV (f x : binder) (e : expr) `{!Closed (f :b: x :b: []) e}
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

  Bind Scope val_scope with val.
  Delimit Scope val_scope with V.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | RecV f x e  => Rec f x e
    | LitV l => Lit l
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Rec f x e =>
      if decide (Closed (f :b: x :b: []) e) then Some (RecV f x e) else None
    | Lit l => Some (LitV l)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | _ => None
    end.

  (** The state: heaps of vals. *)
  Definition state := gmap loc val.

  (** Equality and other typeclass stuff *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof.
      by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
  Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Global Instance base_lit_eq_dec : EqDecision base_lit.
  Proof.
    intros x y; unfold Decision;
      destruct x; destruct y; auto;
        match goal with
          |- {?f ?x = ?f ?y} + {_} =>
          destruct (decide (x = y)) as [|Hneq];
            [subst; by left| try by (right; inversion 1)];
            exfalso; apply Hneq;
              match goal with
              | |- ?A = ?B => by destruct A; destruct B
              end
        end.
  Qed.
  Global Instance un_op_eq_dec : EqDecision un_op.
  Proof. solve_decision. Defined.
  Global Instance bin_op_eq_dec : EqDecision bin_op.
  Proof. solve_decision. Defined.
  Global Instance expr_eq_dec : EqDecision expr.
  Proof. solve_decision. Defined.
  Global Instance val_eq_dec : EqDecision val.
  Proof.
    refine (λ v v', cast_if (decide (of_val v = of_val v'))); abstract naive_solver.
  Defined.

  Global Instance base_lit_countable : Countable base_lit.
  Proof.
    refine (inj_countable'
              (λ l,
               match l with
               | LitInt n => inl (inl (inl (inl n)))
               | LitBool b => inl (inl (inl (inr b)))
               | LitUnit => inl (inl (inr (inl ())))
               | LitLoc l => inl (inl (inr (inr l)))
               | LitString s => inl (inr (inl (inl s)))
               | LitAddressFamily a => inl (inr (inl (inr a)))
               | LitSocketType t => inl (inr (inr (inl t)))
               | LitProtocol p => inl (inr (inr (inr p)))
               | LitSocket s => inr (inl (inl (inl s)))
               | LitSocketAddress a => inr (inl (inl (inr a)))
               end)
              (λ l,
               match l with
               | inl (inl (inl (inl n))) => LitInt n
               | inl (inl (inl (inr b))) => LitBool b
               | inl (inl (inr (inl ()))) => LitUnit
               | inl (inl (inr (inr l))) => LitLoc l
               | inl (inr (inl (inl s))) => LitString s
               | inl (inr (inl (inr a))) => LitAddressFamily a
               | inl (inr (inr (inl t))) => LitSocketType t
               | inl (inr (inr (inr p))) => LitProtocol p
               | inr (inl (inl (inl s))) => LitSocket s
               | inr (inl (inl (inr a))) => LitSocketAddress a
               | inr (inl (inr (inl ()))) => LitUnit
               | inr (inl (inr (inr ()))) => LitUnit
               | inr (inr (inl (inl ()))) => LitUnit
               | inr (inr (inl (inr ()))) => LitUnit
               | inr (inr (inr (inl ()))) => LitUnit
               | inr (inr (inr (inr ()))) => LitUnit
               end)  _).
    by intros [].
  Qed.
  Global Instance un_op_countable : Countable un_op.
  Proof.
    refine (inj_countable'
              (λ op, match op with
                     | NegOp => 0
                     | MinusUnOp => 1
                     | StringOfInt => 2
                     | IntOfString => 3
                     | StringLength => 4
                     end)
              (λ n, match n with
                    | 0 => NegOp
                    | 1 => MinusUnOp
                    | 2 => StringOfInt
                    | 3 => IntOfString
                    | _ => StringLength
                    end) _).
      by intros [].
  Qed.

  Global Instance bin_op_countable : Countable bin_op.
  Proof.
    refine (inj_countable'
              (λ op, match op with
                     | PlusOp => 0
                     | MinusOp => 1
                     | MultOp => 2
                     | QuotOp => 3
                     | RemOp => 4
                     | AndOp => 5
                     | OrOp => 6
                     | XorOp => 7
                     | ShiftLOp => 8
                     | ShiftROp => 9
                     | LeOp => 10
                     | LtOp => 11
                     | EqOp => 12
                     | StringApp => 13
                     end)
              (λ n, match n with
                    | 0 => PlusOp
                    | 1 => MinusOp
                    | 2 => MultOp
                    | 3 => QuotOp
                    | 4 => RemOp
                    | 5 => AndOp
                    | 6 => OrOp
                    | 7 => XorOp
                    | 8 => ShiftLOp
                    | 9 => ShiftROp
                    | 10 => LeOp
                    | 11 => LtOp
                    | 12 => EqOp
                    | _ => StringApp
                    end) _); by intros [].
  Qed.

  Global Instance binder_countable : Countable binder.
  Proof.
    refine (inj_countable'
              (λ b, match b with BNamed s => Some s | BAnon => None end)
              (λ b, match b with Some s => BNamed s | None => BAnon end) _);
      by intros [].
  Qed.

  Global Instance expr_countable : Countable expr.
  Proof.
      set (enc := fix go e :=
             match e with
             | Var x => GenLeaf (inl (inl x))
             | Rec f x e => GenNode 0 [GenLeaf (inl (inr f));
                                       GenLeaf (inl (inr x)); go e]
             | App e1 e2 => GenNode 1 [go e1; go e2]
             | Lit l => GenLeaf (inr (inl l))
             | UnOp op e => GenNode 2 [GenLeaf (inr (inr (inl op))); go e]
             | BinOp op e1 e2 => GenNode 3 [GenLeaf (inr (inr (inr op))); go e1; go e2]
             | If e0 e1 e2 => GenNode 4 [go e0; go e1; go e2]
             | Pair e1 e2 => GenNode 5 [go e1; go e2]
             | Fst e => GenNode 6 [go e]
             | Snd e => GenNode 7 [go e]
             | InjL e => GenNode 8 [go e]
             | InjR e => GenNode 9 [go e]
             | Case e0 e1 e2 => GenNode 10 [go e0; go e1; go e2]
             | Fork e => GenNode 11 [go e]
             | Alloc e => GenNode 12 [go e]
             | Load e => GenNode 13 [go e]
             | Store e1 e2 => GenNode 14 [go e1; go e2]
             | MakeAddress e1 e2 => GenNode 15 [go e1; go e2]
             | NewSocket e1 e2 e3 => GenNode 16 [go e1; go e2; go e3]
             | SocketBind e1 e2 => GenNode 17 [go e1; go e2]
             | SendTo e1 e2 e3 => GenNode 18 [go e1; go e2; go e3]
             | ReceiveFrom e => GenNode 19 [go e]
             | Start n i e => GenNode 20 [GenLeaf (inr (inl n));
                                          GenLeaf(inr (inl i));
                                          go e]
             | FindFrom e1 e2 e3 => GenNode 21 [go e1; go e2; go e3]
             | Substring e1 e2 e3 => GenNode 22 [go e1; go e2; go e3]
             | CAS e1 e2 e3 => GenNode 23 [go e1; go e2; go e3]
             end).
      set (dec := fix go e :=
             match e with
             | GenLeaf (inl (inl x)) => Var x
             | GenNode 0 [GenLeaf (inl (inr f));
                          GenLeaf (inl (inr x)); e] => Rec f x (go e)
             | GenNode 1 [e1; e2] => App (go e1) (go e2)
             | GenLeaf (inr (inl l)) => Lit l
             | GenNode 2 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
             | GenNode 3 [GenLeaf (inr (inr (inr op))); e1; e2] =>
               BinOp op (go e1) (go e2)
             | GenNode 4 [e0; e1; e2] => If (go e0) (go e1) (go e2)
             | GenNode 5 [e1; e2] => Pair (go e1) (go e2)
             | GenNode 6 [e] => Fst (go e)
             | GenNode 7 [e] => Snd (go e)
             | GenNode 8 [e] => InjL (go e)
             | GenNode 9 [e] => InjR (go e)
             | GenNode 10 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
             | GenNode 11 [e] => Fork (go e)
             | GenNode 12 [e] => Alloc (go e)
             | GenNode 13 [e] => Load (go e)
             | GenNode 14 [e1; e2] => Store (go e1) (go e2)
             | GenNode 15 [e1; e2] => MakeAddress (go e1) (go e2)
             | GenNode 16 [e1; e2; e3] => NewSocket (go e1) (go e2) (go e3)
             | GenNode 17 [e1; e2] => SocketBind (go e1) (go e2)
             | GenNode 18 [e1; e2; e3] => SendTo (go e1) (go e2) (go e3)
             | GenNode 19 [e] => ReceiveFrom (go e)
             | GenNode 20 [GenLeaf (inr (inl n));
                           GenLeaf (inr (inl i)); e2] => Start n i (go e2)
             | GenNode 21 [e1; e2; e3] => FindFrom (go e1) (go e2) (go e3)
             | GenNode 22 [e1; e2; e3] => Substring (go e1) (go e2) (go e3)
             | GenNode 23 [e1; e2; e3] => CAS (go e1) (go e2) (go e3)
             | _ => Lit LitUnit (* dummy *)
             end).
      refine (inj_countable' enc dec _). intros e. induction e; f_equal/=; auto.
    Qed.

  Global Instance val_countable : Countable val.
  Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

  Global Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
  Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

  Canonical Structure stateC := leibnizC state.
  Canonical Structure valC := leibnizC val.
  Canonical Structure exprC := leibnizC expr.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr)
  | FindFromLCtx (e1 e2 : expr)
  | FindFromMCtx (v0 : val) (e2 : expr)
  | FindFromRCtx (v0 v1 : val)
  | SubstringLCtx (e1 e2 : expr)
  | SubstringMCtx (v0 : val) (e2 : expr)
  | SubstringRCtx (v0 v1 : val)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr) (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | MakeAddressLCtx (e2 : expr)
  | MakeAddressRCtx (v1 : val)
  | NewSocketLCtx (e1 : expr) (e2 : expr)
  | NewSocketMCtx (v0 : val) (e2 : expr)
  | NewSocketRCtx (v0 : val) (v1 : val)
  | SocketBindLCtx (e2 : expr)
  | SocketBindRCtx (v1 : val)
  | SendToLCtx (e1 : expr) (e2 : expr)
  | SendToMCtx (v0 : val) (e2 : expr)
  | SendToRCtx (v0 : val) (v1 : val)
  | ReceiveFromCtx
  .

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | UnOpCtx op => UnOp op e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | IfCtx e1 e2 => If e e1 e2
    | FindFromLCtx e1 e2 => FindFrom e e1 e2
    | FindFromMCtx v0 e2 => FindFrom (of_val v0) e e2
    | FindFromRCtx v0 v1 => FindFrom (of_val v0) (of_val v1) e
    | SubstringLCtx e1 e2 => Substring e e1 e2
    | SubstringMCtx v0 e2 => Substring (of_val v0) e e2
    | SubstringRCtx v0 v1 => Substring (of_val v0) (of_val v1) e
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    | CasLCtx e1 e2 => CAS e e1 e2
    | CasMCtx v0 e2 => CAS (of_val v0) e e2
    | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
    | MakeAddressLCtx e2 => MakeAddress e e2
    | MakeAddressRCtx v1 => MakeAddress (of_val v1) e
    | NewSocketLCtx e1 e2 => NewSocket e e1 e2
    | NewSocketMCtx v0 e2 => NewSocket (of_val v0) e e2
    | NewSocketRCtx v0 v1 => NewSocket (of_val v0) (of_val v1) e
    | SocketBindLCtx e2 => SocketBind e e2
    | SocketBindRCtx v1 => SocketBind (of_val v1) e
    | SendToLCtx e1 e2 => SendTo e e1 e2
    | SendToMCtx v0 e2 => SendTo (of_val v0) e e2
    | SendToRCtx v0 v1 => SendTo (of_val v0) (of_val v1) e
    | ReceiveFromCtx => ReceiveFrom e
    end.

  (** Substitution *)
  Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
    match e with
    | Var y => if decide (x = y) then es else Var y
    | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x es e else e
    | App e1 e2 => App (subst x es e1) (subst x es e2)
    | Lit l => Lit l
    | UnOp op e => UnOp op (subst x es e)
    | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
    | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
    | FindFrom e0 e1 e2 => FindFrom (subst x es e0) (subst x es e1) (subst x es e2)
    | Substring e0 e1 e2 => Substring (subst x es e0) (subst x es e1) (subst x es e2)
    | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
    | Fst e => Fst (subst x es e)
    | Snd e => Snd (subst x es e)
    | InjL e => InjL (subst x es e)
    | InjR e => InjR (subst x es e)
    | Case e0 e1 e2 => Case (subst x es e0) (subst x es e1) (subst x es e2)
    | Fork e => Fork (subst x es e)
    | Alloc e => Alloc (subst x es e)
    | Load e => Load (subst x es e)
    | Store e1 e2 => Store (subst x es e1) (subst x es e2)
    | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
    | MakeAddress e1 e2 => MakeAddress (subst x es e1) (subst x es e2)
    | NewSocket e0 e1 e2 =>
      NewSocket (subst x es e0) (subst x es e1) (subst x es e2)
    | SocketBind e1 e2 => SocketBind (subst x es e1) (subst x es e2)
    | SendTo e0 e1 e2 => SendTo (subst x es e0) (subst x es e1) (subst x es e2)
    | ReceiveFrom e => ReceiveFrom (subst x es e)
    | Start n i e => Start n i (subst x es e)
    end.

  Definition subst' (mx : binder) (es : expr) : expr → expr :=
    match mx with BNamed x => subst x es | BAnon => id end.

  Definition StringOfZ (x : Z) :=
    match x with
    | 0 => "0"
    | Z.pos x0 => pretty (N.pos x0)
    | Z.neg x0 => "-" +:+ pretty (N.pos x0)
    end.

  Definition ZOfAscii (c : Ascii.ascii) : option N :=
    match c with
    | "0"%char => Some 0%N
    | "1"%char => Some 1%N
    | "2"%char => Some 2%N
    | "3"%char => Some 3%N
    | "4"%char => Some 4%N
    | "5"%char => Some 5%N
    | "6"%char => Some 6%N
    | "7"%char => Some 7%N
    | "8"%char => Some 8%N
    | "9"%char => Some 9%N
    | _ => None
    end.

  Fixpoint ZOfString' (x : string) (ac : N) : option N :=
    match x with
    | EmptyString => Some ac
    | String c x' =>
      match ZOfAscii c with
        None => None
      | Some d => (ZOfString' x' ((ac * 10) + d)%N)
      end
    end.

  Definition ZOfString (x : string) : option Z:=
    match x with
    | EmptyString => None
    | String "-"%char x' =>
      match (ZOfString' x' 0) with
      | Some z => Some (- (Z.of_N z))
      | None => None
      end
    | String c x' =>
      match (ZOfString' x 0) with
      | Some z => Some (Z.of_N z)
      | None => None
      end
    end.

  Lemma lt_acc (n : N) : Acc N.lt n.
  Proof.
    induction n using N.peano_ind; first by constructor; intros; lia.
    constructor => m Hlt.
    destruct (decide (m < n)%N); first by apply IHn.
      by replace m with n by lia.
  Qed.

  Lemma ZOfAscii_pretty x :
    (x < 10)%N →
    ZOfAscii (pretty_N_char x) = Some x.
  Proof.
    intros Hlt.
    inversion Hlt as [Hlt']; cbv in Hlt'.
    destruct x as [|p]; first done.
    destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; try done.
  Qed.

  Lemma ZOfString'_app s s' k :
    match ZOfString' s k with
    | None => ZOfString' (s +:+ s') k = None
    | Some m => ZOfString' (s +:+ s') k = ZOfString' s' m
    end.
  Proof.
    revert s' k; induction s.
    - induction s'; simpl; first done.
      intros k.
      destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s' ?A with _ => _ end =>
        specialize (IHs' A);
          destruct (ZOfString' s' A); trivial
      end.
    - intros s' k; rewrite /= -/append.
      destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s ?A with _ => _ end =>
        specialize (IHs s' A);
          destruct (ZOfString' s (k * 10 + 7)); auto
      end.
  Qed.

  Global Instance append_assoc : Assoc eq append.
  Proof.
    intros x.
    induction x.
    - induction y; auto with f_equal.
    - intros y z.
      rewrite /append -/append IHx. f_equal.
  Qed.

  Lemma pretty_N_go_app m s :
    (0 < m)%N → pretty_N_go m s = (pretty_N_go m "") +:+ s.
  Proof.
    intros Hlt. revert s.
    induction (lt_acc m) as [? ? IH] => s.
    rewrite !(pretty_N_go_step x) //.
    destruct (decide (x < 10)%N).
    - rewrite N.div_small // pretty_N_go_0 /=.
    - assert (x `div` 10 < x)%N as Hltdv.
      { apply N.div_lt; auto with lia. }
      assert (0 < x `div` 10)%N as Hdvp.
      { apply N.div_str_pos; lia. }
      pose proof (IH _ Hltdv Hdvp) as IH'.
      rewrite (IH' (String (pretty_N_char (x `mod` 10)) "")).
      rewrite IH'; simpl.
      by rewrite -assoc.
  Qed.

  Lemma ZOfString'_inv (n : nat) : ZOfString' (StringOfZ n) 0 = Some (N.of_nat n).
  Proof.
    destruct n; first done; simpl.
    unfold pretty, pretty_N.
    remember (N.pos (Pos.of_succ_nat n)) as m.
    replace (S n) with (N.to_nat m); last first.
    { by rewrite Heqm positive_N_nat SuccNat2Pos.id_succ. }
    assert (Hmlt : (0 < m)%N) by lia.
    clear dependent n.
    induction (lt_acc m) as [? ? IH].
    rewrite pretty_N_go_step; last done.
    destruct (decide (x < 10)%N).
    - rewrite N.mod_small //.
      rewrite N.div_small // pretty_N_go_0 /= ZOfAscii_pretty //.
    - assert (x `div` 10 < x)%N as Hltdv.
      { apply N.div_lt; auto with lia. }
      assert (0 < x `div` 10)%N as Hdvp.
      { apply N.div_str_pos; lia. }
      rewrite pretty_N_go_app //.
      pose proof (ZOfString'_app
                    (pretty_N_go (x `div` 10) "")
                    (String (pretty_N_char (x `mod` 10)) "") 0) as Hlp.
      rewrite (IH _ Hltdv Hdvp) in Hlp.
      rewrite Hlp.
      rewrite /= ZOfAscii_pretty; last by apply N.mod_lt.
      replace (x `div` 10 * 10)%N with (10 * x `div` 10)%N by lia.
      rewrite -N.div_mod' //.
  Qed.

  Lemma pretty_N_go_nnil m s :
    (0 < m)%N → pretty_N_go m s ≠ "".
  Proof.
    intros Hlt. revert s.
    induction (lt_acc m) as [? ? IH] => s.
    rewrite !(pretty_N_go_step x) //.
    destruct (decide (x < 10)%N).
    - rewrite N.div_small // pretty_N_go_0 /=.
    - assert (x `div` 10 < x)%N as Hltdv.
      { apply N.div_lt; auto with lia. }
      assert (0 < x `div` 10)%N as Hdvp.
      { apply N.div_str_pos; lia. }
      apply (IH _ Hltdv Hdvp).
  Qed.

  Lemma pretty_N_go_pos_nneg m s s':
    (0 < m)%N → pretty_N_go m s ≠ String "-" s'.
  Proof.
    intros Hlt. revert s.
    induction (lt_acc m) as [? ? IH] => s.
    rewrite !(pretty_N_go_step x) //.
    destruct (decide (x < 10)%N).
    - rewrite N.div_small // pretty_N_go_0 /=.
      destruct x as [|p]; first done.
      destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; done.
    - assert (x `div` 10 < x)%N as Hltdv.
      { apply N.div_lt; auto with lia. }
      assert (0 < x `div` 10)%N as Hdvp.
      { apply N.div_str_pos; lia. }
      apply (IH _ Hltdv Hdvp).
  Qed.

  Lemma StringOfZ_nnil m : StringOfZ m ≠ "".
  Proof.
    unfold StringOfZ; simpl.
    destruct m; auto.
    apply pretty_N_go_nnil; lia.
  Qed.

  Lemma ZOfString_inv (n : Z) : ZOfString (StringOfZ n) = Some n.
  Proof.
    unfold ZOfString.
    destruct (StringOfZ n) eqn:Heq;
      first by exfalso; eapply StringOfZ_nnil; eauto.
    destruct n as [|p|p] eqn:Heqn.
    - destruct a as [[] [] [] [] [] [] [] []]; try done.
      rewrite -?Heq //.
    - rewrite -?Heq.
      pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
      rewrite positive_nat_Z in HZSi.
      rewrite HZSi nat_N_Z positive_nat_Z.
      destruct a as [[] [] [] [] [] [] [] []]; auto.
      exfalso; eapply pretty_N_go_pos_nneg; eauto; lia.
    - simpl in Heq.
      assert (0 < 1)%nat as Hneq by omega.
      pose proof (append_correct1 "-" (pretty (N.pos p)) 0 Hneq) as Hf;
        simpl in Heq.
      rewrite Heq in Hf; inversion Hf; subst.
      rewrite -(@string_app_inj "-" (pretty (N.pos p)) s Heq).
      pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
      rewrite positive_nat_Z in HZSi.
      by rewrite HZSi nat_N_Z positive_nat_Z.
  Qed.

  (** The stepping relation *)
  Definition un_op_eval (op : un_op) (v : val) : option val :=
    match op, v with
    | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
    | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
    | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
    | StringOfInt, LitV (LitInt n) => Some $ LitV $ LitString (StringOfZ n)
    | IntOfString, LitV (LitString s) =>
      match ZOfString s with
        Some z => Some $ InjRV $ LitV (LitInt z)
      | None => Some $ InjLV (LitV (LitUnit))
      end
    | StringLength, LitV (LitString s) => Some $ LitV $ LitInt (String.length s)
    | _, _ => None
    end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  | StringApp => LitInt 0
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp | StringApp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2, op with
  | LitV (LitInt n1), LitV (LitInt n2), op => Some $ LitV $ bin_op_eval_int op n1 n2
  | LitV (LitBool b1), LitV (LitBool b2), op => LitV <$> bin_op_eval_bool op b1 b2
  | LitV (LitString s1), LitV (LitString s2), StringApp =>
    Some $ LitV $ LitString (String.append s1 s2)
  | v1, v2, op => guard (op = EqOp); Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  end.

Definition option_nat_to_val (v : option nat) :=
  match v with
    | None => InjLV (LitV LitUnit)
    | Some v' => InjRV (LitV $ LitInt (Z.of_nat v'))
  end.

Inductive head_step : expr → state → expr → state → list (expr) → Prop :=
  | BetaS f x e1 e2 v2 e' σ :
     to_val e2 = Some v2 →
     Closed (f :b: x :b: []) e1 →
     e' = subst' x (of_val v2) (subst' f (Rec f x e1) e1) →
     head_step (App (Rec f x e1) e2) σ e' σ []
  | UnOpS op e v v' σ :
     to_val e = Some v →
     un_op_eval op v = Some v' →
     head_step (UnOp op e) σ (of_val v') σ []
  | BinOpS op e1 e2 v1 v2 v' σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op e1 e2) σ (of_val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Lit $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
      head_step (If (Lit $ LitBool false) e1 e2) σ e2 σ []
  | FindFromS e0 v0 e1 v1 e2 v2 σ :
      to_val e0 = Some (LitV $ LitString v0) →
      to_val e1 = Some (LitV $ LitInt (Z.of_nat v1)) →
      to_val e2 = Some (LitV $ LitString v2) →
      head_step (FindFrom e0 e1 e2) σ
                (of_val (option_nat_to_val (index v1 v2 v0))) σ []
  | SubstringS e0 v0 e1 v1 e2 v2 σ :
      to_val e0 = Some (LitV $ LitString v0) →
      to_val e1 = Some (LitV $ LitInt (Z.of_nat v1)) →
      to_val e2 = Some (LitV $ LitInt (Z.of_nat v2)) →
      head_step (Substring e0 e1 e2) σ
                (Lit $ LitString (substring v1 v2 v0)) σ []
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ []
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ []
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ (App e1 e0) σ []
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ (App e2 e0) σ []
  | ForkS e σ:
     head_step (Fork e) σ (Lit LitUnit) σ [e]
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Lit $ LitLoc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Lit $ LitLoc l)) σ (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Lit $ LitLoc l) e) σ (Lit LitUnit) (<[l:=v]>σ) []
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool true) (<[l:=v2]>σ) []
  | MakeAddressS e1 e2 s p σ :
      to_val e1 = Some (LitV $ (LitString s)) →
      to_val e2 = Some (LitV $ (LitInt p)) →
      head_step (MakeAddress e1 e2) σ
                (Lit $ LitSocketAddress (SocketAddressInet s (Z.to_pos p))) σ []
.

  (** Basic properties about the language *)
  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
    head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
     repeat match goal with
            | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
            end; auto.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) σ) in
    to_val e = Some v → head_step (Alloc e) σ (Lit (LitLoc l)) (<[l:=v]>σ) [].
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  (* Misc *)
  Lemma to_val_rec f x e `{!Closed (f :b: x :b: []) e} :
    to_val (Rec f x e) = Some (RecV f x e).
  Proof. rewrite /to_val. case_decide=> //. do 2 f_equal; apply proof_irrel. Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x es es' :
  Closed [] es' → subst x es (subst x es' e) = subst x es' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x es es' :
  Closed [] es' → subst' x es (subst' x es' e) = subst' x es' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst x es (subst y es' e) = subst y es' (subst x es e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst' x es (subst' y es' e) = subst' y es' (subst' x es e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x es :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x es (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x es :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x es (Rec f y e) = Rec f y (subst' x es e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma base_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End ground_lang.

Module dist_lang.
  Import ground_lang.
  Import Network.

  Record expr := mkExpr { expr_n : node;
                          expr_e : ground_lang.expr }.

  Record val := mkVal { val_n : node;
                        val_e : ground_lang.val }.

  Global Instance expr_inhabited : Inhabited expr := populate {| expr_n := "";
                                                          expr_e := Lit LitUnit |}.
  Global Instance val_inhabited : Inhabited val := populate {| val_n := "";
                                                        val_e := LitV LitUnit |}.

  Notation fill_item Ki e :=
    {| expr_n := expr_n e; expr_e := (ground_lang.fill_item Ki (expr_e e)) |}.
  
  Definition of_val v : expr :=
    {| expr_n := val_n v; expr_e := ground_lang.of_val (val_e v) |}.
  Arguments of_val !v.
  Definition to_val e : option val :=
    (λ v, {| val_n := expr_n e; val_e := v |}) <$> ground_lang.to_val (expr_e e).

  (** The local state: heaps of vals and socket handles to sockets. *)
  Definition heap := gmap ground_lang.loc ground_lang.val.
  Definition sockets := gmap socket_handle socket.
  Definition ports_in_use := gmap ip_address (gset port).

  Record state := mkState { state_heaps : gmap node heap;
                            state_sockets : gmap node sockets;
                            state_lookup : lookup_table;
                            state_ports_in_use : ports_in_use;
                            state_ms : message_soup;
                          }.

  Definition option_socket_address_to_val (sa : option socket_address) :=
    match sa with
    | None => InjLV (LitV LitUnit)
    | Some addr => InjRV (LitV $ LitSocketAddress addr)
    end.

  Inductive socket_step (node : node) :
    ground_lang.expr -> sockets -> ports_in_use -> lookup_table -> message_soup ->
    ground_lang.expr -> sockets -> ports_in_use -> lookup_table -> message_soup ->
    Prop :=
  | NewSocketS e0 e1 e2 f s p handle S P L M :
      ground_lang.to_val e0 = Some (LitV $ LitAddressFamily f) →
      ground_lang.to_val e1 = Some (LitV $ LitSocketType s) →
      ground_lang.to_val e2 = Some (LitV $ LitProtocol p) →
      S !! handle = None →
      socket_step
        node
        (NewSocket e0 e1 e2) S P L M
        (Lit $ LitSocket handle)
        (<[handle:=Socket f s p None]>S) P L M
  | SocketBindSucS handle a s S P P' L M :
      (* The address is assigned to the node *)
      (* layout !! node = Some (ip_of_address a) → *)
      (* The socket handle is bound to a socket. *)
      S !! handle = Some s →
      (* The socket has no assigned address. *)
      (saddress s) = None →
      (* The port is not in use *)
      P !! (ip_of_address a) = Some P' →
      (port_of_address a) ∉ P' →
      (* The address does not exist in the lookup table. *)
      L !! a = None ->
      socket_step
        node
        (* layout *)
        (SocketBind (Lit $ LitSocket handle) (Lit $ LitSocketAddress a))
        S P L M
        (Lit $ LitInt 0)
        (<[handle:=Socket (sfamily s) (stype s) (sprotocol s) (Some a)]>S)
        (<[(ip_of_address a):={[ port_of_address a ]} ∪ P']> P)
        (<[a:=node]>L)
        M
  | SendToBoundS handle e1 e2 a mId mbody s S P L M f :
      (* Check that a socket has been allocated for the handle. *)
      S !! handle = Some s →
      M !! mId = None →
      saddress s = Some f ->
      ground_lang.to_val e1 = Some (LitV $ LitString mbody) →
      ground_lang.to_val e2 = Some (LitV $ LitSocketAddress a) →
      let: new_message := {| m_from_node := node;
                             m_sender := f;
                             m_destination := a;
                             m_protocol := (sprotocol s);
                             m_state := MS_SENT;
                             m_body := mbody;
                             m_sent := max_sent M + 1;
                             m_received := 0 |} in
      socket_step
        node
        (SendTo (Lit $ LitSocket handle) e1 e2)
        S P L M
        (Lit $ LitInt (String.length mbody))
        S P L
        (<[mId:=new_message]>M)
  | SendToUnboundS handle e1 e2 a mId mbody s S P L M P' f :
      (* Check that a socket has been allocated for the handle. *)
      S !! handle = Some s →
      M !! mId = None →
      saddress s = None ->
      P !! (ip_of_address f) = Some P' →
      (port_of_address f) ∉ P' →      
      L !! f = None ->
      ground_lang.to_val e1 = Some (LitV $ LitString mbody) →
      ground_lang.to_val e2 = Some (LitV $ LitSocketAddress a) →
      let: new_message := {| m_from_node := node;
                             m_sender := f;
                             m_destination := a;
                             m_protocol := (sprotocol s);
                             m_state := MS_SENT;
                             m_body := mbody;
                             m_sent := max_sent M + 1;
                             m_received := 0 |} in
      socket_step
        node
        (SendTo (Lit $ LitSocket handle) e1 e2)
        S P L M
        (Lit $ LitInt (String.length mbody))
        S P L
        (<[mId:=new_message]>M)
  | ReceiveFromSomeS handle s a mId m S P L M :
      S !! handle = Some s →
      saddress s = Some a →
      messages_to_receive_at a M !! mId = Some m →
      socket_step
        node
        (ReceiveFrom (Lit $ LitSocket handle))
        S P L M
        (InjR (Pair (Lit $ LitString (m_body m))
                    (Lit $ LitSocketAddress (m_sender m))))
        S P L (<[mId:={| m_from_node := m_from_node m;
                         m_sender := m_sender m;
                         m_destination := m_destination m;
                         m_protocol := m_protocol m;
                         m_state := MS_RECEIVED;
                         m_body := m_body m;
                         m_sent := m_sent m;
                         m_received := max_received M + 1
                      |}]>M)
  | ReceiveFromNoneS handle s a S L P M :
      S !! handle = Some s →
      saddress s = Some a →
      messages_to_receive_at a M = ∅ →
      socket_step
        node
        (ReceiveFrom (Lit $ LitSocket handle))
        S P L M
        (InjL (Lit $ LitUnit))
        S P L M
  .

  Fixpoint is_head_step_pure (e : ground_lang.expr) : bool :=
    match e with
    | Alloc _
    | Load _
    | Store _ _
    | CAS _ _ _
    | NewSocket _ _ _
    | SocketBind _ _
    | SendTo _ _ _
    | ReceiveFrom _ => false
    | _ => true
    end.

  Inductive head_step : expr → state → expr → state → list (expr) → Prop :=
  | LocalStepPureS n h e e' ef σ
                   (is_pure : is_head_step_pure e = true)
                   (BaseStep : ground_lang.head_step e h e' h ef)
    : head_step {| expr_n := n; expr_e := e |} σ
                {| expr_n := n; expr_e := e' |} σ
                (map (fun e => {| expr_n := n; expr_e := e |}) ef)
  | LocalStepS n h h' e e' ef σ
               (is_pure : is_head_step_pure e = false)
               (BaseStep : ground_lang.head_step e h e' h' ef)
    :
      state_heaps σ !! n = Some h →
      head_step {| expr_n := n; expr_e := e |}
                σ
                {| expr_n := n; expr_e := e' |}
                {|
                  state_heaps := <[n:=h']>(state_heaps σ);
                  state_sockets := state_sockets σ;
                  state_lookup := state_lookup σ;
                  state_ports_in_use := state_ports_in_use σ;
                  state_ms := state_ms σ;
                |}
                (map (fun e => {| expr_n := n; expr_e := e |}) ef)
  | StartStepS n h s e (i : ip_address) σ :
      n ≠ "system" →
      h = match state_heaps σ !! n with
          | Some h' => h'
          | None => ∅
          end →
      s = match state_sockets σ !! n with
          | Some s' => s'
          | None => ∅
          end →
      is_Some (state_ports_in_use σ !! i) →
      head_step {| expr_n := "system";
                   expr_e := Start (LitString n) (LitString i) e |} σ
                {| expr_n := "system";
                   expr_e := Lit $ LitUnit |}
                {|
                  state_heaps := <[n:=h]>(state_heaps σ);
                  state_sockets := <[n:=s]>(state_sockets σ);
                  state_lookup := state_lookup σ;
                  state_ports_in_use := state_ports_in_use σ;
                  state_ms := state_ms σ |}
                [{| expr_n := n;
                    expr_e := e |}]
  | SocketStepS n e e' S S' P' L' M' σ
                (SocketStep : socket_step n
                                          e S (state_ports_in_use σ)
                                          (state_lookup σ) (state_ms σ)
                                          e' S' P' L' M')
    : state_sockets σ !! n = Some S ->
      head_step {| expr_n := n; expr_e := e |}
                σ
                {| expr_n := n; expr_e := e' |}
                {| state_heaps := state_heaps σ;
                   state_sockets := <[n:=S']>(state_sockets σ);
                   state_lookup := L';
                   state_ports_in_use := P';
                   state_ms := M'|} []
  .

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof.
    destruct v.
    cbv -[ground_lang.to_val ground_lang.of_val];
      by rewrite ground_lang.to_of_val.
  Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    destruct e, v. cbv -[ground_lang.to_val ground_lang.of_val].
    case C : (ground_lang.to_val expr_e0) => //.
    move => [<- <-]. f_equal. exact: ground_lang.of_to_val.
  Qed.

  Lemma to_base_val e v:
    to_val e = Some v → ground_lang.to_val (expr_e e) = Some (val_e v).
  Proof. destruct e, v. cbv -[ground_lang.to_val]. case_match; naive_solver. Qed.

  Lemma to_base_val' n e v:
    to_val {| expr_n := n ; expr_e := e |} = Some {| val_n := n ; val_e := v |} →
    ground_lang.to_val e = Some v.
  Proof. cbv -[ground_lang.to_val]. case_match; naive_solver. Qed.

  Lemma to_base_val_inv e v n:
    ground_lang.to_val e = Some v → to_val (mkExpr n e) = Some (mkVal n v).
  Proof. cbv -[ground_lang.to_val]. by move => ->. Qed.

  Lemma of_base_val e v:
    of_val v = e → ground_lang.of_val (val_e v) = (expr_e e).
  Proof. destruct e,v. by inversion 1. Qed.

  Lemma val_head_stuck σ1 e1 σ2 e2 ef : head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof.
    inversion 1; subst; last inversion SocketStep; subst;
      try (cbv -[ground_lang.to_val];
               by erewrite ground_lang.val_head_stuck; last eassumption);
      eauto.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof.
    move/fmap_is_Some/ground_lang.fill_item_val => H.
    exact/fmap_is_Some.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    move => /fmap_None H1 /fmap_None H2 [] H3 H4.
    exact: ground_lang.fill_item_no_val_inj H1 H2 H4.
  Qed.

  Lemma head_ctx_step_val Ki e σ e2 σ2 ef :
    head_step (fill_item Ki e) σ e2 σ2 ef → is_Some (to_val e).
  Proof.
    inversion 1; subst; last inversion SocketStep; subst; simplify_option_eq;
     try
        (apply/fmap_is_Some; exact: ground_lang.head_ctx_step_val);
     apply/fmap_is_Some.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
    - destruct Ki; try (by eauto);
        inversion H0; subst; by eauto.
  Qed.

  Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (λ e, fill_item Ki e).
  Proof. destruct Ki; move => [? ?] [? ?] [? ?];
         simplify_eq/=; auto with f_equal. Qed.

  Definition is_closed (X : list string) (e : expr) : bool :=
    ground_lang.is_closed X (expr_e e).

  Class Closed (X : list string) (e : expr) := closed : is_closed X e.
  Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.
  Global Instance closed_decision env e : Decision (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.

  Lemma is_closed_ground_lang X e:
    Closed X e → ground_lang.Closed X (expr_e e).
  Proof.
    by rewrite /Closed /is_closed /ground_lang.Closed.
  Qed.

  Lemma closed_ground_lang X e:
    ground_lang.Closed X (expr_e e) → Closed X e.
  Proof.
    by rewrite /Closed /is_closed /ground_lang.Closed.
  Qed.
  
  Lemma is_closed_weaken X Y e : is_closed X e → X ⊆  Y → is_closed Y e.
  Proof.
    destruct e. cbv -[ground_lang.is_closed].
    exact: ground_lang.is_closed_weaken.
  Qed.

  Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
  Proof. intros. destruct e. exact: ground_lang.is_closed_weaken_nil. Qed.

  Definition subst x (es : ground_lang.expr) (e : expr) : expr :=
    mkExpr (expr_n e) (ground_lang.subst x es (expr_e e)).

  Lemma is_closed_subst X e x es :
      ground_lang.is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
  Proof.
    destruct e. unfold is_closed. simpl.
    exact: ground_lang.is_closed_subst.
  Qed.

  Lemma is_closed_of_val X v : is_closed X (of_val v).
  Proof. exact: ground_lang.is_closed_of_val. Qed.

  Lemma dist_lang_mixin : EctxiLanguageMixin of_val to_val (λ Ki e, fill_item Ki e) head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Global Instance state_inhabited : Inhabited state.
  Proof. exact {|
      inhabitant :=
        {|
          state_heaps := ∅;
          state_sockets := ∅;
          state_lookup := ∅;
          state_ports_in_use := ∅;
          state_ms := ∅;
        |}
    |}.
  Qed.

  Lemma newsocket_fresh n t p ms e1 v1 e2 v2 e3 v3 σ :
    let h := fresh (dom (gset socket_handle) σ) in
    ground_lang.to_val e1 = Some (LitV $ LitAddressFamily v1) →
    ground_lang.to_val e2 = Some (LitV $ LitSocketType v2) →
    ground_lang.to_val e3 = Some (LitV $ LitProtocol v3) →
    socket_step n
                (* l *)
                (NewSocket e1 e2 e3) σ p t ms
                (Lit (LitSocket h)) (<[h:={|
                                          sfamily := v1;
                                          stype := v2;
                                          sprotocol := v3;
                                          saddress := None
                                        |}]>σ) p t ms.
  Proof. intros; apply NewSocketS; try done.
         apply (not_elem_of_dom (D:=gset loc)), is_fresh.
  Qed.

  Lemma message_send_bound_fresh n h e1 e2 a m s σ p t ms f :
    let mId := fresh (dom (gset message_id) ms) in
    σ !! h = Some s →
    saddress s = Some f ->
    ground_lang.to_val e1 = Some (LitV $ LitString m) →
    ground_lang.to_val e2 = Some (LitV $ LitSocketAddress a) →
    socket_step n (SendTo (Lit $ LitSocket h) e1 e2) σ p t ms
                (Lit (LitInt (String.length m))) σ p t
                (<[mId:={| m_from_node := n;
                           m_sender := f;
                           m_destination := a;
                           m_protocol := sprotocol s;
                           m_state := MS_SENT;
                           m_body := m;
                           m_sent := max_sent ms + 1;
                           m_received := 0
                        |}]>ms).
  Proof.
    intros. apply SendToBoundS; try done.
    apply (not_elem_of_dom (D:=gset message_id)), is_fresh.
  Qed.

  Lemma message_send_unbound_fresh n h e1 e2 a m s σ p t ms
        (P' : gset port) ip :
    let mId := fresh (dom (gset message_id) ms) in
    σ !! h = Some s →
    saddress s = None ->
    p !! ip = Some P' ->    
    let port := fresh P' in
    t !! SocketAddressInet ip port = None ->
    ground_lang.to_val e1 = Some (LitV $ LitString m) →
    ground_lang.to_val e2 = Some (LitV $ LitSocketAddress a) →
    socket_step n (SendTo (Lit $ LitSocket h) e1 e2) σ p t ms
                (Lit (LitInt (String.length m))) σ p t
                (<[mId:={| m_from_node := n;
                           m_sender := SocketAddressInet ip port;
                           m_destination := a;
                           m_protocol := sprotocol s;
                           m_state := MS_SENT;
                           m_body := m;
                           m_sent := max_sent ms + 1;
                           m_received := 0
                        |}]>ms).
  Proof.
    intros. apply (SendToUnboundS _ _ _ _ a _ _ _ _ _ _ _ P'
                  (SocketAddressInet ip port0)); try done.
    apply (not_elem_of_dom (D:=gset message_id)), is_fresh. simpl.
    eapply is_fresh.
  Qed.
  
End dist_lang.

(** Language *)
Canonical Structure dist_ectxi_lang := EctxiLanguage dist_lang.dist_lang_mixin.
Canonical Structure dist_ectx_lang := EctxLanguageOfEctxi dist_ectxi_lang.
Canonical Structure dist_lang := LanguageOfEctx dist_ectx_lang.

(* Prefer base names over ectx_language names. *)
Export ground_lang.
Export dist_lang.

(** Define some derived forms *)
Notation Lam x e := (Rec BAnon x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV x e := (RecV BAnon x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)).
Notation i2s e := (UnOp StringOfInt e)%E.
Notation s2i e := (UnOp IntOfString e)%E.