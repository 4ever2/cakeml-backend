From MetaRocq.Utils Require Import bytestring ReflectEq utils.
From MetaRocq.Common Require Kernames.

From Stdlib Require Import String Ascii Bool Arith List.
(*Require Import Malfunction.Malfunction. *)
Set Warnings "-masking-absolute-name".
From Ceres Require Import Ceres CeresString CeresFormat CeresSerialize.
Import ListNotations.

From CakeML Require Import ast namespace semanticPrimitives functions bigstep.


Local Open Scope sexp.
Local Open Scope string.

(*  Fixpoint _escape_ident (_end s : String.t) : String.t :=
match s with
| ""%bs => _end
|  String.String c s' =>
	if (c == "'"%byte) || (c == " "%byte) || (c == "."%byte) then String.String "_" (_escape_ident _end s')
	else match s' with
			| String.String c2 s'' =>
				if (String.String c (String.String c2 String.EmptyString)) == "Γ"%bs
				then ("Gamma" ++ _escape_ident _end s'')%bs
				else if (String.String c (String.String c2 String.EmptyString)) == "φ"%bs
				then ("Phi" ++ _escape_ident _end s'')%bs
				else if (String.String c (String.String c2 String.EmptyString)) == "Δ"%bs
				then ("Delta" ++ _escape_ident _end s'')%bs
				else if (String.String c (String.String c2 String.EmptyString)) == "π"%bs
				then ("pi" ++ _escape_ident _end s'')%bs
				else if (String.String c (String.String c2 String.EmptyString)) == "ρ"%bs
				then ("rho" ++ _escape_ident _end s'')%bs
				else if (String.String c (String.String c2 String.EmptyString)) == "Σ"%bs
				then ("Sigma" ++ _escape_ident _end s'')%bs
				else String.String c (_escape_ident _end s')
			| _ => String.String c (_escape_ident _end s')
			end
end.  *)

(* #[export] Instance Serialize_Ident : Serialize varN :=
	fun a => Atom (append "$" (bytestring.String.to_string (_escape_ident ""%bs (String.of_string a)))).
 *)

Local Coercion of := String.of_string.

#[export] Instance Serialize_Ident : Serialize varN :=
	fun a => Atom (Str a).

#[export] Instance Serialize_Ident_bs : Serialize bs :=
fun a => [Atom (Str (String.to_string a))].

(*
Definition Cons x (l : sexp) :=
	match l with
	| List l => List (x :: l)
	| x => x
	end.
*)

Definition Cons x (l : sexp) :=
	match l with
	| List l => List (x :: l)
	| y => [x;y]
	end.


(*
Definition App_sexp (l1 : sexp) (l2 : sexp) :=
	match l1, l2 with
	| List l1, List l2 => List (l1 ++ l2)
	| x_, y => y
	end.
*)

Definition App_sexp (l1 : sexp) (l2 : sexp) :=
	match l1, l2 with
	| List l1, List l2 => List (l1 ++ l2)
	| x, List l2 =>  List (x::l2)
	| List l1, x => List (l1++[x])
	| x,y => [x;y]
	end.

(* Fixpoint split_dot accl accw (s : string) := *)
(* 	match s with *)
(* 	| EmptyString => (string_reverse accl, string_reverse accw) *)
(* 	| String c s => *)
(* 		  if (byte_of_ascii c =? ".")%char2 then *)
(* 		let accl' := match accl with EmptyString => accw *)
(* 								| accl => (accw ++ "." ++ accl) *)
(* 						end in *)
(* 		split_dot accl' EmptyString s *)
(* 		else *)
(* 		split_dot accl (String c accw) s *)
(* 	end. *)


(* Definition before_dot s := fst (split_dot EmptyString EmptyString s). *)
(* Definition after_dot s := snd (split_dot EmptyString EmptyString s). *)

(* Fixpoint id_to_list (i:id):list (sexp*string) := *)
(* 	match i with  *)
(* 	| Short n =>  [(Atom "Short",n)] *)
(* 	| Long n m => (Atom "Long",n) :: (id_to_list m) *)
(* 	end. *)

#[export] Instance Serialize_id : Serialize id :=
	fun a =>
    match a with
    | Short str => [Atom "Short" ; Atom (Str str)]
    | _ => Atom "notsupported"
    end.

#[export] Instance Serialize_id_option : Serialize (option id) :=
	fun a => match a with
			     | None => Atom "NONE"
			     | Some n => [Atom "SOME";to_sexp n]
			     end.

#[export] Instance Serialize_var_option : Serialize (option varN) :=
	fun a => match a with
			| None => Atom "NONE"
			| Some n => [Atom "SOME";to_sexp n]
			end.



Fixpoint  to_sexp_binding (a : pat) : sexp :=
	match a with
	| Pany => Atom "Pany"
	| Plit (StrLit l) => [Atom "Plit"; Atom "StrLit";to_sexp l]
	| Pvar v => [Atom "Pvar";to_sexp v]
  | Pcon n nil =>  [(Atom "Pcon"); (to_sexp n); Atom "nil"]
	| Pcon n p =>  [(Atom "Pcon"); (to_sexp n); ( @Serialize_list _ to_sexp_binding p)]
	| Pas p n =>    [Atom "Pas";to_sexp_binding p; to_sexp n]
	end.

Fixpoint to_sexp_t (a : exp) : sexp :=
	match a with
	| Lit (StrLit l) => [Atom "Lit"; Atom "Strlit"; to_sexp l]
	| Raise e => [Atom "Raise"; to_sexp_t e]
	| Handle e pes =>
		Cons (Atom "Handle") (Cons (to_sexp_t e) ( @Serialize_list _ (fun '(p,e) => App_sexp  (to_sexp_binding p) ([to_sexp_t e])) pes))
  | Con cn nil => [Atom "Con";  to_sexp cn; Atom "nil"]
  | Con cn es => [Atom "Con";  to_sexp cn; ( @Serialize_list _ (fun e =>to_sexp_t e) es)]
	| Var x => [Atom "Var"; to_sexp x]
	| App op es => List (Atom "App"::Atom "Opapp":: (map to_sexp_t es))
	| Fun x e =>   [Atom "Fun"; (to_sexp x); (to_sexp_t e)]
	| Let n e1 e2 => [Atom "Let"; to_sexp n; to_sexp_t e1; to_sexp_t e2]
	| Mat m p => [ (Atom "Mat") ; to_sexp_t m ; @Serialize_list _ (fun '(p,e) => [ to_sexp_binding p; Atom "Lannot"; to_sexp_t e; [Atom "unk"; Atom "unk"]  ]) p]
	| Letrec fs e =>
		[ (Atom "Letrec");
			(@Serialize_list _ (fun '(f,x,e') =>
				[ (to_sexp f);
					(to_sexp x);
					Atom "Lannot";
					to_sexp_t e';
					[Atom "unk"; Atom "unk"]
				]) fs);
			(to_sexp_t e)
		]
	end.

#[export] Instance Serialize_t : Serialize exp := to_sexp_t.

(* Fixpoint string_map (f : ascii -> ascii) (s : string) : string := *)
(*   match s with *)
(*   | EmptyString => EmptyString *)
(*   | String c s => String (f c)< (string_map f s) *)
(*   end. *)

(* Definition dot_to_underscore (id : string) := *)
(*   string_map (fun c =>  *)
(*     match c with *)
(*     | "."%char => "_"%char *)
(*     | _ => c *)
(*     end) id. *)
(*
Definition uncapitalize_char (c : Byte.byte) : Byte.byte :=
	let n := Byte.to_nat c in
	if (65 <=? n)%nat && (n <=? 90)%nat then match Byte.of_nat (n + 32) with Some c => c | _ => c end
	else c.

Definition uncapitalize (s : bytestring.string) : bytestring.string :=
	match s with
	| bytestring.String.EmptyString => bytestring.String.EmptyString
	| bytestring.String.String c s => bytestring.String.String (uncapitalize_char c) s
	end. *)
(*
 Definition encode_name (s : bytestring.string) : bytestring.string :=
  _escape_ident ""%bs s.  *)

(*
Definition exports (m : list (varN * option exp)) : list (varN * option exp) :=
  List.map (fun '(x, v) => (("def_" ++ encode_name x)%bs, Some (Mglobal x))) m. *)


Definition bytestring_atom s :=
  ("$" ++ s).

(*  Fixpoint find_prim (id : varN) (prims : primitives) : option (prim_def string) :=
  match prims with
  | nil%list => None
  | ((kn, primdef) :: prims)%list =>
    if ReflectEq.eqb id kn then
      match primdef with
      | Global modname label => Some (Global (bytestring_atom modname) (bytestring_atom label))
      | Primitive symbol arity => Some (Primitive symbol arity)
      | Erased => Some Erased
      end
    else find_prim id prims
  end. *)

(*Section binders.
  Context (x : bytestring.string).

  Definition add_suffix n := (x ++ MRString.string_of_nat n)%bs.

  Fixpoint binders n acc :=
    match n with
    | 0 => acc
    | S n => binders n (add_suffix n :: acc)%list
    end.
End binders.  *)

(* Definition mk_eta_exp n s :=
  let binders := binders "x"%bs n nil in
  [ A tom "lambda" ; to_sexp binders ; List (Atom s :: List.map to_sexp binders) ]. *)

Definition global_serializer : Serialize (bytestring.string * option exp) :=
	fun '(i, b) =>
	match b with
	| Some x => Cons (Atom "Dlet") (Cons ([Atom "unk"; Atom "unk"]) (to_sexp (String.to_string (i)%bs, x)))
	| None =>
		let na :=  (String.to_string (i)%bs) in
		List ( Atom (Raw ("$" ++ na)) :: [Atom "global" ; Atom (Raw ("$Axioms")) ; Atom (Raw ("$" ++ na)) ]:: nil)
	end.

(* Fixpoint filter_erased_prims prims (l : list (Ident.t * option t)) : list (Ident.t * option t) :=
  match l with
  | nil => nil
  | cons ((id, Some _) as x) xs => x :: filter_erased_prims prims xs
  | cons ((id, None) as x) xs =>
    match find_prim id prims with
    | Some Erased => filter_erased_prims prims xs
    | _ => x :: filter_erased_prims prims xs
    end
  end.   *)

 Fixpoint thename a (s : bytestring.String.t) :=
  match s with
  | String.EmptyString => bytestring.String.of_string (string_of_list_byte (List.rev a))
  | String.String b s => if b == "."%byte
                        then thename nil s
                        else thename (b :: a)%list s
  end.


(* Variant program_type : Set :=
  | Standalone
  | Shared_lib (modname : bytestring.String.t) (register : bytestring.String.t). (* Reference to a plugin registration function*)
 *)
(* Eval compute in to_sexp (Mapply (Mglobal "foo"%bs, [Mglobal "bar"%bs]%list)). *)

(* Definition shared_lib_register modname label '(name, export) :=
  let code := (List [Atom "apply"; List [Atom "global" ;
  Atom ("$" ++ String.to_string modname)%string ; Atom ("$" ++ String.to_string label)%string]%list;
  Atom (Str (bytestring.String.to_string name));
  Atom ("$" ++ bytestring.String.to_string export)]) in
  Cons (Atom "_") (List (code :: nil)).
 *)
(* Eval compute in
  to_string (shared_lib_register "malfunction"%bs "register"%bs ("foo.test", "test")%bs). *)


Definition Serialize_module (names : list bytestring.string) :=
  fun '(m, x) =>
    let name : bs := match m with
							| (x :: l)%list => fst x
							| nil => ""%bs
						end in
    let main := "main"%bs in
    (* let names := (names ++ ["main"%bs])%list in *)
    (* let shortnames : list bs := List.map (fun name => (* uncapitalize *) (thename nil name)) names in *)
    (* let longnames : list sexp := List.map (fun name => (to_sexp ("def_" ++ name)%bs)) names in *)
    (* let allnames := List.combine shortnames longnames in *)
    (* let exports : list sexp := List.map (fun shortname => Atom ( String.to_string shortname)%string) shortnames in *)
		 ( @Serialize_list _ global_serializer (List.rev (((main, Some x) :: m)%list))).
