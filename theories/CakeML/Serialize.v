From MetaRocq.Utils Require Import bytestring utils.
From Stdlib Require Import String Ascii Bool ZArith List.
From Ceres Require Import Ceres CeresString CeresFormat CeresSerialize.
Import ListNotations.

From CakeML Require Import FullAst.


Local Open Scope sexp.
Local Open Scope bs_scope.



Instance Serialize_cakeml_option {A : Type} `{Serialize A} : Serialize (option A) :=
  fun a =>
    match a with
    | None => Atom "NONE"
    | Some n => [Atom "SOME"; to_sexp n]
    end.

Instance Serialize_cakeml_list {A : Type} `{serA : Serialize A} : Serialize (list A) :=
  fun a =>
    match a with
    | []%list => Atom "nil"
    | l => @Serialize_list A serA l
    end.


Instance Serialize_cakeml_pair {A B : Type} `{Serialize A} `{Serialize B} : Serialize (A * B) :=
  fun '(a,b) =>
    let sexp_a := to_sexp a in
    let sexp_b := to_sexp b in
    match sexp_b with
    | Atom_ "nil" => [sexp_a]
    | Atom_ _ =>
      (* If both are atoms we serialize as expected *)
      [sexp_a; sexp_b]
    | List l =>
      (* If b is a list then CakeML sexp parser expects it to not be nested.
        Only a is allowed to be a nested list *)
      List (sexp_a :: l)
    end.

Instance Serialize_cml_id {A : Type} `{Serialize A} : Serialize (cml_id A) :=
  fix sz id : sexp :=
    match id with
    | Short n => [Atom "Short"; to_sexp n]
    | Long mn id => [Atom "Long"; to_sexp mn; sz id]
    end.

Instance Serialize_ast_t : Serialize ast_t :=
  fix sz tp : sexp :=
    match tp with
    | Atvar n => [Atom "Atvar"; to_sexp n]
    | Atfun tp_p tp_r => [Atom "Atfun"; sz tp_p; sz tp_r]
    | Attup tps => [Atom "Attup"; @Serialize_cakeml_list _ sz tps]
    | Atapp tps id => [Atom "Atapp"; @Serialize_cakeml_list _ sz tps; to_sexp id]
    end.

Instance Serialize_word64 : Serialize word64 :=
  fun n => to_sexp n.

Instance Serialize_ascii : Serialize ascii :=
  fun a => Atom (Str (String.String (byte_of_ascii a) "")).

Instance Serialize_lit : Serialize lit :=
  fun x =>
    match x with
    | IntLit i =>
        if (0 <=? i)%Z then to_sexp i else [Atom "-"; to_sexp (Z.abs i)]
    | StrLit s => to_sexp s
    | Char c => [Atom "char"; to_sexp c]
    | Word8 w => [Atom "word8"; to_sexp w]
    | Word64 w => [Atom "word64"; to_sexp w]
    | Float64 f => [Atom "float64"; to_sexp f]
    end.

Instance Serialize_pat : Serialize pat :=
  fix sz pt :=
    match pt with
    | Pany => [Atom "Pany"]
    | Pvar v => to_sexp v
    | Plit l => [Atom "Plit"; to_sexp l]
    | Pcon id pts =>
      [ Atom "Pcon";
        @Serialize_cakeml_option _ _ id;
        @Serialize_cakeml_list _ sz pts
      ]
    | Pref pt => [Atom "Pref"; sz pt]
    | Pas pt v => [Atom "Pas"; sz pt; to_sexp v]
    | Ptannot pt tp => [Atom "Ptannot"; sz pt; to_sexp tp]
    end.

Instance Serialize_arith : Serialize arith :=
  fun op =>
    match op with
    | Add => Atom "Add"
    | Sub => Atom "Sub"
    | Mul => Atom "Mul"
    | Div => Atom "Div"
    | Mod => Atom "Mod"
    | Neg => Atom "Neg"
    | And => Atom "And"
    | Xor => Atom "Xor"
    | Or => Atom "Or"
    | Not => Atom "Not"
    | Abs => Atom "Abs"
    | Sqrt => Atom "Sqrt"
    | FMA => Atom "FMA"
    end.

Instance Serialize_lop : Serialize lop :=
  fun op =>
    match op with
    | Andalso => Atom "Andalso"
    | Orelse => Atom "Orelse"
    end.

Instance Serialize_thunk_mode : Serialize thunk_mode :=
  fun m =>
    match m with
    | Evaluated => Atom "Evaluated"
    | NotEvaluated => Atom "NotEvaluated"
    end.

Instance Serialize_thunk_op : Serialize thunk_op :=
  fun op =>
    match op with
    | AllocThunk m => [Atom "AllocThunk"; to_sexp m]
    | UpdateThunk m => [Atom "UpdateThunk"; to_sexp m]
    | ForceThunk => Atom "ForceThunk"
    end.

Instance Serialize_ws_shift : Serialize ((word_size * shift) * nat) :=
  fun '(s, n) =>
    match s with
    | (W8, Lsl) => [Atom "Shift8Lsl"; to_sexp n]
    | (W8, Lsr) => [Atom "Shift8Lsr"; to_sexp n]
    | (W8, Asr) => [Atom "Shift8Asr"; to_sexp n]
    | (W8, Ror) => [Atom "Shift8Ror"; to_sexp n]
    | (W64, Lsl) => [Atom "Shift64Lsl"; to_sexp n]
    | (W64, Lsr) => [Atom "Shift64Lsr"; to_sexp n]
    | (W64, Asr) => [Atom "Shift64Asr"; to_sexp n]
    | (W64, Ror) => [Atom "Shift64Ror"; to_sexp n]
    end.


Instance Serialize_test : Serialize test :=
  fun t =>
    match t with
    | Equal => Atom "Equal"
    | Compare Lt => Atom "Less"
    | Compare Gt => Atom "Greater"
    | Compare Leq => Atom "LessEq"
    | Compare Geq => Atom "GreaterEq"
    | AltCompare Lt => Atom "AltLess"
    | AltCompare Gt => Atom "AltGreater"
    | AltCompare Leq => Atom "AltLessEq"
    | AltCompare Geq => Atom "AltGreaterEq"
    end.

Instance Serialize_prim_type : Serialize prim_type :=
  fun pt =>
    match pt with
    | BoolT => Atom "BoolT"
    | IntT => Atom "IntT"
    | CharT => Atom "CharT"
    | StrT => Atom "StrT"
    | WordT W8 => Atom "Word8T"
    | WordT W64 => Atom "Word64T"
    | Float64T => Atom "Float64T"
    end.

Instance Serialize_op : Serialize op :=
  fun op =>
    match op with
    | Arith a pt => [Atom "Arith"; to_sexp a; to_sexp pt]
    | FromTo pt1 pt2 => [Atom "FromTo"; to_sexp pt1; to_sexp pt2]
    | Shift ws s n => @Serialize_ws_shift (ws, s, n)
    | Equality => Atom "Equality"
    | Test t pt => [Atom "Test"; to_sexp t; to_sexp pt]
    | Opapp => Atom "Opapp"
    | Opassign => Atom "Opassign"
    | Opref => Atom "Opref"
    | Opderef => Atom "Opderef"
    | Aw8alloc => Atom "Aw8alloc"
    | Aw8sub => Atom "Aw8sub"
    | Aw8length => Atom "Aw8length"
    | Aw8update => Atom "Aw8update"
    | CopyStrStr => Atom "CopyStrStr"
    | CopyStrAw8 => Atom "CopyStrAw8"
    | CopyAw8Str => Atom "CopyAw8Str"
    | CopyAw8Aw8 => Atom "CopyAw8Aw8"
    | XorAw8Str_unsafe => Atom "XorAw8Strunsafe"
    | Implode => Atom "Implode"
    | Explode => Atom "Explode"
    | Strsub => Atom "Strsub"
    | Strlen => Atom "Strlen"
    | Strcat => Atom "Strcat"
    | VfromList => Atom "VfromList"
    | Vsub => Atom "Vsub"
    | Vlength => Atom "Vlength"
    | Aalloc => Atom "Aalloc"
    | AallocEmpty => Atom "AallocEmpty"
    | AallocFixed => Atom "AallocFixed"
    | Asub => Atom "Asub"
    | Alength => Atom "Alength"
    | Aupdate => Atom "Aupdate"
    | Vsub_unsafe => Atom "Vsub_unsafe"
    | Asub_unsafe => Atom "Asubunsafe"
    | Aupdate_unsafe => Atom "Aupdateunsafe"
    | Aw8sub_unsafe => Atom "Aw8subunsafe"
    | Aw8update_unsafe => Atom "Aw8updateunsafe"
    | ThunkOp t_op => to_sexp t_op
    | ListAppend => Atom "ListAppend"
    | ConfigGC => Atom "ConfigGC"
    | FFI s => [Atom "FFI"; to_sexp s]
    | Eval => Atom "Eval"
    | Env_id => Atom "Envid"
    end.

Instance Serialize_locn : Serialize locn :=
  fun l =>
    match l with
    | UNKNOWNpt => Atom "unk"
    | EOFpt => Atom "eof"
    | POSN x y => [to_sexp x; to_sexp y]
    end.

Instance Serialize_locs : Serialize locs :=
  fun '(l1, l2) =>
    [to_sexp l1; to_sexp l2].

Instance Serialize_exp : Serialize exp :=
  fix sz e' :=
    match e' with
    | Raise e => [Atom "Raise"; sz e]
    | Handle e ps =>
      [ Atom "Handle";
        sz e;
        @Serialize_cakeml_list _ (@Serialize_cakeml_pair _ _ _ sz) ps
      ]
    | Lit l => [Atom "Lit"; to_sexp l]
    | Con n es =>
      [ Atom "Con";
        @Serialize_cakeml_option _ _ n;
        @Serialize_cakeml_list _ sz es
      ]
    | Var n => [Atom "Var"; to_sexp n]
    | Fun n e => [Atom "Fun"; to_sexp n; sz e]
    | App op es => [Atom "App"; to_sexp op; @Serialize_cakeml_list _ sz es]
    | Log op e1 e2 => [Atom "Log"; to_sexp op; sz e1; sz e2]
    | If c t e => [Atom "If"; sz c; sz t; sz e]
    | Mat m brs =>
      [ Atom "Mat";
        sz m;
        @Serialize_cakeml_list _ (@Serialize_cakeml_pair _ _ _ sz) brs
      ]
    | Let n e1 e2 => [Atom "Let"; @Serialize_cakeml_option _ _ n; sz e1; sz e2]
    | Letrec fs e =>
      [ Atom "Letrec";
        @Serialize_cakeml_list _
          (@Serialize_cakeml_pair _ _ _
            (@Serialize_cakeml_pair _ _ _ sz)) fs;
        sz e
      ]
    | Tannot e tp => [Atom "Tannot"; sz e; to_sexp tp]
    | Lannot e l => [Atom "Lannot"; sz e; to_sexp l]
    end.

Instance Serialize_type_def : Serialize type_def :=
  fun tp =>
    @Serialize_cakeml_list _ (
      @Serialize_cakeml_pair _ _
        (@Serialize_cakeml_list tvarN _)
        (@Serialize_cakeml_pair typeN _
          _
          (@Serialize_cakeml_list _
            (@Serialize_cakeml_pair conN _
              _
              (@Serialize_cakeml_list ast_t Serialize_ast_t)
            )
          )
        )
    ) tp.

Instance Serialize_dec : Serialize dec :=
  fix sz d :=
    match d with
    | Dlet l pt e => [Atom "Dlet"; to_sexp l; to_sexp pt; to_sexp e]
    | Dletrec l fs =>
      [ Atom "Dletrec";
        to_sexp l;
        @Serialize_cakeml_list _ (
          @Serialize_cakeml_pair _ _ _ (
            @Serialize_cakeml_pair _ _ _ Serialize_exp
          )) fs
      ]
    | Dtype l tp => [Atom "Dtype"; to_sexp l; to_sexp tp]
    | Dtabbrev l vs n tp =>
      [ Atom "Dtabbrev";
        to_sexp l;
        @Serialize_cakeml_list _ _ vs;
        to_sexp n;
        to_sexp tp
      ]
    | Dexn l n tps =>
      [ Atom "Dexn";
        to_sexp l;
        to_sexp n;
        @Serialize_cakeml_list _ _ tps
      ]
    | Dmod n ds => [Atom "Dmod"; to_sexp n; @Serialize_cakeml_list _ sz ds]
    | Dlocal lds vds =>
      [ Atom "Dlocal";
        @Serialize_cakeml_list _ sz lds;
        @Serialize_cakeml_list _ sz vds
      ]
    | Denv n => [Atom "Denv"; to_sexp n]
    end.

Definition string_of_program (p : (list dec)) : String.t :=
  @to_string (list dec) (@Serialize_cakeml_list _ Serialize_dec) p.
