From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import Ascii.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import NArith.

(* Locations *)
Inductive locn :=
| UNKNOWNpt
| EOFpt
| POSN : nat -> nat -> locn.

Notation locs := ((locn * locn) : Type) (only parsing).

(* TODO: Ensure size bound? *)
Definition word64 : Type := N.

(* Literal constants *)
Inductive lit :=
| IntLit : Z -> lit
| Char : ascii -> lit (* Are CakeML chars one byte ascii? *)
| StrLit : string -> lit
| Word8 : N -> lit
| Word64 : word64 -> lit
| Float64 : word64 -> lit.

Variant shift :=
| Lsl | Lsr | Asr | Ror.

Variant arith :=
| Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA.

(* Module names *)
Notation modN := string (only parsing).
(* Variable names *)
Notation varN := string (only parsing).
(* Constructor names (from datatype definitions) *)
Notation conN := string (only parsing).
(* Type names *)
Notation typeN := string (only parsing).
(* Type variable names *)
Notation tvarN := string (only parsing).

Variant word_size :=
| W8 | W64.

Variant thunk_mode :=
| Evaluated | NotEvaluated.

Inductive thunk_op :=
| AllocThunk : thunk_mode -> thunk_op
| UpdateThunk : thunk_mode -> thunk_op
| ForceThunk.

Variant opb :=
| Lt | Gt | Leq | Geq.

Inductive test :=
| Equal
| Compare : opb -> test
| AltCompare : opb -> test.

Inductive prim_type :=
| BoolT
| IntT
| CharT
| StrT
| WordT : word_size -> prim_type
| Float64T.

Inductive op :=
(* primitive operations for the primitive types: +, -, and, sqrt, etc. *)
| Arith : arith -> prim_type -> op
(* conversions between primitive types: char<->int, word<->double, word<->int *)
| FromTo : prim_type -> prim_type -> op
(* Operations on words *)
| Shift : word_size -> shift -> nat -> op
| Equality
| Test : test -> prim_type -> op
(* Function application *)
| Opapp
(* Reference operations *)
| Opassign
| Opref
| Opderef
(* Word8Array operations *)
| Aw8alloc
| Aw8sub
| Aw8length
| Aw8update
(* string/bytearray conversions *)
| CopyStrStr
| CopyStrAw8
| CopyAw8Str
| CopyAw8Aw8
| XorAw8Str_unsafe
(* String operations *)
| Implode
| Explode
| Strsub
| Strlen
| Strcat
(* Vector operations *)
| VfromList
| Vsub
| Vlength
(* Array operations *)
| Aalloc
| AallocEmpty
| AallocFixed
| Asub
| Alength
| Aupdate
(* Unsafe vector/array accesses *)
| Vsub_unsafe
| Asub_unsafe
| Aupdate_unsafe
| Aw8sub_unsafe
| Aw8update_unsafe
(* thunk operations *)
| ThunkOp : thunk_op -> op
(* List operations *)
| ListAppend
(* Configure the GC *)
| ConfigGC
(* Call a given foreign function *)
| FFI : string -> op
(* Evaluate new code in a given env *)
| Eval
(* Get the identifier of an env object *)
| Env_id.

(* Define operator classes, that allow to group their behavior later *)
Variant op_class :=
| EvalOp (* Eval primitive *)
| FunApp (* function application *)
| Force (* forcing a thunk *)
| Simple. (* arithmetic operation, no finite-precision/reals *)

Inductive cml_id (A : Type) :=
| Short : A -> cml_id A
| Long : modN -> cml_id A -> cml_id A.

(* Types used in type annotations *)
Inductive ast_t :=
(* Type variables that the user writes down ('a, 'b, etc.) *)
| Atvar : tvarN -> ast_t
(* Function type *)
| Atfun : ast_t -> ast_t -> ast_t
(* Tuple type *)
| Attup : (list ast_t) -> ast_t
(* Type constructor applications.
  0-ary type applications represent unparameterised types (e.g., num or string) *)
| Atapp : (list ast_t) -> (cml_id typeN) -> ast_t.

(* Patterns *)
Inductive pat :=
| Pany
| Pvar : varN -> pat
| Plit : lit -> pat
(* Constructor applications.
    A Nothing constructor indicates a tuple pattern. *)
| Pcon : option (cml_id conN) -> list pat -> pat
| Pref : pat -> pat
(* Pattern alias. *)
| Pas : pat -> varN -> pat
| Ptannot : pat -> ast_t -> pat.

(* Short circuiting logical operations *)
Variant lop :=
| Andalso | Orelse.

(* Expressions *)
Inductive exp :=
| Raise : exp -> exp
| Handle : exp -> list (pat * exp) -> exp
| Lit : lit -> exp
(* Constructor application.
    A Nothing constructor indicates a tuple pattern. *)
| Con : option (cml_id conN) -> list exp -> exp
| Var : cml_id varN -> exp
| Fun : varN -> exp -> exp
(* Application a primitive operator to arguments.
    Includes function application. *)
| App : op -> list exp -> exp
(* Logical operations (and, or) *)
| Log : lop -> exp -> exp -> exp
| If : exp -> exp -> exp -> exp
(* Pattern matching *)
| Mat : exp -> list (pat * exp) -> exp
(* A let expression
    A Nothing value for the binding indicates that this is a
    sequencing expression, that is: (e1; e2). *)
| Let : option varN -> exp -> exp -> exp
(* Local definition (potentially) mutually recursive
    functions.
    The first varN is the function's name, and the second varN
    is its parameter. *)
| Letrec : list (varN * (varN * exp)) -> exp -> exp
| Tannot : exp -> ast_t -> exp
(* Location annotated expressions, not expected in source programs *)
| Lannot : exp -> locs -> exp.

(* Constructor type definition,
  a tuple of a constructor name and a list of constructor argument types *)
Definition type_def_constructor : Type :=
  conN * list ast_t.

Definition type_def_variants : Type :=
  list tvarN.

(* Single type definition consisting of a tuple of:
  1) a list of named variants
  2) type name
  3) a list of constructors *)
Definition single_type_def : Type :=
  type_def_variants * (typeN * (list type_def_constructor)).

(* List of mutual type definitions *)
Definition type_def : Type :=
  (* list ((list tvarN) * (typeN * (list (conN * list ast_t)))) *)
  list single_type_def.

(* Declarations *)
Inductive dec :=
(* Top-level bindings
  * The pattern allows several names to be bound at once *)
| Dlet : locs -> pat -> exp -> dec
(* Mutually recursive function definition *)
| Dletrec : locs -> list (varN * (varN * exp)) -> dec
(* Type definition
    Defines several data types, each which has several
    named variants, which can in turn have several arguments.
  *)
| Dtype : locs -> type_def -> dec
(* Type abbreviations *)
| Dtabbrev : locs -> list tvarN -> typeN -> ast_t -> dec
(* New exceptions *)
| Dexn : locs -> conN -> list ast_t -> dec
(* Module *)
| Dmod : modN -> list dec -> dec
(* Local: local part, visible part *)
| Dlocal : list dec -> list dec -> dec
(* Store current lexical env in an env value *)
| Denv : tvarN -> dec.
