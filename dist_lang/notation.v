From distris Require Export lang network.
From stdpp Require Export strings.
Set Default Proof Using "Type".

Import Network.

Notation "½" := (1/2)%Qp.
Notation "¼" := (1/4)%Qp.
Notation "¾" := (3/4)%Qp.

Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
Coercion LitAddressFamily : address_family >-> base_lit.
Coercion LitSocketType : socket_type >-> base_lit.
Coercion LitProtocol : protocol >-> base_lit.
Coercion LitSocketAddress : socket_address >-> base_lit.
Coercion LitString : string >-> base_lit.

Coercion App : ground_lang.expr >-> Funclass.
Coercion of_val : val >-> expr.
Coercion ground_lang.of_val : ground_lang.val >-> ground_lang.expr.

Coercion Var : string >-> ground_lang.expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : binder_scope.

(* Definition mkExpr (n : node) (e : ground_lang.expr) := (n,e) : expr. *)
(* Definition mkVal (n : node) (v : ground_lang.val) := (n,v) : val. *)

(* Note that the scope for expressions and values are NOT the same:
   Expressions have brackets that comes from the sequence \<, with name
   MATHEMATICAL LEFT ANGLE BRACKET where as values has brackets
   that come from \〈 (name: LEFT-POINTING ANGLE BRACKET) *)
Notation "⟨ n ; e ⟩" := (mkExpr n e)
                      (at level 0, right associativity). 
Notation "〈 n ; v 〉" := (mkVal n v%V).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%V) (at level 8, format "# l") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>

  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%bind e1 x2%bind e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%bind e2 x1%bind e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E)
  (at level 30, right associativity) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E)
  (at level 35, right associativity) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 ^^ e2" := (BinOp StringApp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) (at level 70) : expr_scope.
Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%bind x%bind e%E)
  (at level 102, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (locked (RecV f%bind x%bind e%E))
  (at level 102, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%bind x%bind (Lam y%bind .. (Lam z%bind e%E) ..))
  (at level 102, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (locked (RecV f%bind x%bind (Lam y%bind .. (Lam z%bind e%E) ..)))
  (at level 102, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%bind e%E)
  (at level 102, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%bind (Lam y%bind .. (Lam z%bind e%E) ..))
  (at level 102, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

(* When parsing lambdas, we want them to be locked (so as to avoid needless
unfolding by tactics and unification). However, unlocked lambda-values sometimes
appear as part of compound expressions, in which case we want them to be pretty
printed too. We achieve that by first defining the non-locked notation, and then
the locked notation. Both will be used for pretty-printing, but only the last
will be used for parsing. *)
Notation "λ: x , e" := (LamV x%bind e%E)
  (at level 102, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x , e" := (locked (LamV x%bind e%E))
  (at level 102, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%bind (Lam y%bind .. (Lam z%bind e%E) .. ))
  (at level 102, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (locked (LamV x%bind (Lam y%bind .. (Lam z%bind e%E) .. )))
  (at level 102, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.


Notation "'let:' x := e1 'in' e2" := (Lam x%bind e2%E e1%E)
  (at level 102, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']'  ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (Lit (LitBool false))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (Lit (LitBool true)) e2%E) (only parsing) : expr_scope.

(** Notations for option *)
Notation NONE := (InjL #()) (only parsing).
Notation SOME x := (InjR x) (only parsing).

Notation NONEV := (InjLV #()) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%bind e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%bind e2)
    (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
