From distris Require Export lang network notation tactics.

Definition assert : ground_lang.val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

Definition unSOME : ground_lang.val :=
  λ: "p",
     match: "p" with NONE => assert #false | SOME "p'" => "p'" end.

Definition listen : ground_lang.val :=
  (
    rec: "loop" "socket" "handle" :=
      match: ReceiveFrom "socket" with
        SOME "m" => let: "snd" := (Snd "m") in
                    "handle" (Fst "m") "snd"
      | NONE => "loop" "socket" "handle"
      end
  )%V.

Definition listen_wait : ground_lang.val :=
  (
    rec: "loop" "socket" :=
      match: ReceiveFrom "socket" with
        SOME "m" => "m"
      | NONE => "loop" "socket"
      end
  )%V.

Definition tag_of_message : ground_lang.val :=
  (
    λ: "msg",
    match: FindFrom "msg" #(0 : Z) #"_" with
      SOME "i" => Substring "msg" #0 "i"
    | NONE => #"UNDEFINED"
    end
  )%V.

Definition value_of_message : ground_lang.val :=
  (
    λ: "msg",
    match: FindFrom "msg" #(0 : Z) #"_" with
      SOME "i" => let: "length" := UnOp StringLength "msg" in
                  let: "start" := "i" + #1 in
                  Substring "msg" "start" ("length" - "start")
    | NONE => #"UNDEFINED"
    end
  )%V.

Definition list_make : ground_lang.val :=
  λ: <>, NONE.

Definition list_cons : ground_lang.val :=
  λ: "elem" "list", SOME (Pair "elem" "list").

Definition list_head : ground_lang.val :=
  λ: "l", match: "l" with
            SOME "a" => SOME (Fst "a")
          | NONE => NONE
          end.

Definition list_tail : ground_lang.val :=
  λ: "l", match: "l" with
            SOME "a" => (Snd "a")
          | NONE => NONE
          end.

Definition list_fold : ground_lang.val :=
  rec: "fold" "handler" "acc" "l" :=
    match: "l" with
      SOME "a" => let: "fst" := Fst "a" in
                 let: "snd" := Snd "a" in
                 let: "acc'" := ("handler" "acc" "fst") in
                 "fold" "handler" "acc'" "snd"
    | NONE => "acc"
    end.

(* Definition list_iter : ground_lang.val := *)
(*   λ: "handler" "l", list_fold (λ: "_" "elem", "handler" "elem" ;; #()) #() "l". *)

(* Definition list_length : ground_lang.val := *)
(*   λ: "l", list_fold (λ: "acc" "_", "acc" + #1) #0 "l". *)

Definition list_iter : ground_lang.val :=
  rec: "iter" "handler" "l" :=
    match: "l" with
      SOME "a" =>
        let: "tail" := Snd "a" in
        "handler" (Fst "a");;
        "iter" "handler" "tail"
    | NONE => #()
    end.

Definition list_length : ground_lang.val :=
  rec: "length" "l" :=
    match: "l" with
      SOME "a" => #1 + "length" (Snd "a")
    | NONE => #0
    end.
