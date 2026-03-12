From MetaRocq.Utils Require Import bytestring utils.
From Stdlib Require Import String Ascii Bool ZArith List.
From Ceres Require Import Ceres CeresUtils CeresString CeresFormat CeresDeserialize.
Import ListNotations.

From CakeML Require Import FullAst.


Local Open Scope bs_scope.
Local Open Scope sexp.
Local Open Scope list_scope.



Definition err {A : Type} l : error + A :=
  inl (DeserError l "error").

Instance Deserialize_cakeml_option {A : Type} `{Deserialize A} : Deserialize (option A) :=
  Deser.match_con "option"
    [ ("NONE", None) ]
    [ ("SOME", Deser.con1_ Some) ].

Instance Deserialize_cakeml_list {A : Type} `{desA : Deserialize A} : Deserialize (list A) :=
  fun l e =>
    match e with
    | List es => @Deserialize_list A desA l e
    | Atom_ (Raw "nil") => inr []
    | _ => inl (DeserError l "could not read 'list', expected list, got atom")
    end.

Instance Deserialize_cakeml_pair {A B : Type} `{Deserialize A} `{Deserialize B} : Deserialize (A * B) :=
  fun l e =>
    match e with
    | List (e1 :: e2) =>
      _bind_sum (_from_sexp (0 :: l) e1) (fun a =>
      _bind_sum (_from_sexp (1 :: l) (List e2)) (fun b =>
      inr (a, b)))
    | List _ => inl (DeserError l "could not read 'prod', expected list of length 2, got list of a different length")
    | Atom_ _ => inl (DeserError l "could not read 'prod', expected list of length 2, got atom")
    end.

Instance Deserialize_cml_id {A : Type} `{Deserialize A} : Deserialize (cml_id A) :=
  fix ds (l : loc) (e : sexp) : error + (cml_id A) :=
    Deser.match_con "cml_id"
      [ ]
      [ ("Short", Deser.con1_ (Short A));
        ("Long", Deser.con2 (Long A) _from_sexp ds)
      ] l e.

Instance Deserialize_ast_t : Deserialize ast_t :=
  fix ds (l : loc) (e : sexp) : error + ast_t :=
    Deser.match_con "ast_t"
      [ ]
      [ ("Atvar", Deser.con1_ Atvar);
        ("Atfun", Deser.con2 Atfun ds ds);
        ("Attup", Deser.con1 Attup (@Deserialize_cakeml_list _ ds));
        ("Atapp", Deser.con2 Atapp (@Deserialize_cakeml_list _ ds) _from_sexp)
      ] l e.

Instance Deserialize_word64 : Deserialize word64 :=
  _from_sexp.

Instance Deserialize_ascii : Deserialize ascii :=
  fun l e =>
    match e with
    | Atom_ (Str (c :: "")%bs) => inr (ascii_of_byte c)
    | Atom_ (Str "") => inl (DeserError l "could not read 'ascii', got empty string")
    | Atom_ (Str (_ :: _ :: _)%bs) =>
      inl (DeserError l "could not read 'ascii', got string of length greater than 1")
    | Atom_ _ => inl (DeserError l "could not read 'ascii', got non-string atom")
    | List _ => inl (DeserError l "could not read 'ascii', got lost")
    end.

Instance Deserialize_lit : Deserialize lit :=
  fun l e =>
    match e with
    | Atom_ (Num i) => inr (IntLit i)
    | Atom_ (Str s) => inr (StrLit s)
    | _ =>
      Deser.match_con "lit"
        [ ]
        [ ("-", Deser.con1_ (fun z => IntLit (-z)));
          ("char", Deser.con1_ Char);
          ("word8", Deser.con1_ Word8);
          ("word64", Deser.con1_ Word64); (* TODO: validate word size *)
          ("float64", Deser.con1_ Float64) (* TODO: validate word size *)
        ] l e
    end.


#[bypass_check(guard)]
Definition Deserialize_pat_aux : Deserialize pat :=
  fix ds (l : loc) (e : sexp) {struct e} : error + pat :=
    match e with
    | Atom_ (Str s) => inr (Pvar s)
    | _ =>
      Deser.match_con "pat"
        [ ("Pany", Pany) ]
        [ ("Plit", Deser.con1_ Plit);
          ("Pcon", Deser.con2 Pcon (@Deserialize_cakeml_option _ (@Deserialize_cml_id String.t _))
                                   (@Deserialize_cakeml_list _ ds));
          ("Pref", Deser.con1 Pref ds);
          ("Pas", Deser.con2 Pas ds _from_sexp);
          ("Ptannot", Deser.con2 Ptannot ds _from_sexp)
        ] l e
    end.
Instance Deserialize_pat : Deserialize pat := Deserialize_pat_aux.

Instance Deserialize_arith : Deserialize arith :=
  Deser.match_con "arith"
    [ ("Add", Add);
      ("Sub", Sub);
      ("Mul", Mul);
      ("Div", Div);
      ("Mod", Mod);
      ("Neg", Neg);
      ("And", And);
      ("Xor", Xor);
      ("Or", Or);
      ("Not", Not);
      ("Abs", Abs);
      ("Sqrt", Sqrt);
      ("FMA", FMA)
    ]
    [ ].

Instance Deserialize_lop : Deserialize lop :=
  Deser.match_con "lop"
    [ ("Andalso", Andalso);
      ("Orelse", Orelse)
    ]
    [ ].

Instance Deserialize_thunk_mode : Deserialize thunk_mode :=
  Deser.match_con "thunk_mode"
    [ ("Evaluated", Evaluated);
      ("NotEvaluated", NotEvaluated)
    ]
    [ ].

Instance Deserialize_thunk_op : Deserialize thunk_op :=
  Deser.match_con "thunk_op"
    [ ("ForceThunk", ForceThunk) ]
    [ ("AllocThunk", Deser.con1_ AllocThunk);
      ("UpdateThunk", Deser.con1_ UpdateThunk)
    ].

Instance Deserialize_ws_shift : Deserialize ((word_size * shift) * nat) :=
  Deser.match_con "ws_shift"
    [ ]
    [ ("Shift8Lsl", Deser.con1_ (fun n => ((W8,Lsl),n)));
      ("Shift8Lsr", Deser.con1_ (fun n => ((W8,Lsr),n)));
      ("Shift8Asr", Deser.con1_ (fun n => ((W8,Asr),n)));
      ("Shift8Ror", Deser.con1_ (fun n => ((W8,Ror),n)));
      ("Shift64Lsl", Deser.con1_ (fun n => ((W64,Lsl),n)));
      ("Shift64Lsr", Deser.con1_ (fun n => ((W64,Lsr),n)));
      ("Shift64Asr", Deser.con1_ (fun n => ((W64,Asr),n)));
      ("Shift64Ror", Deser.con1_ (fun n => ((W64,Ror),n)))
    ].

Instance Deserialize_test : Deserialize test :=
  Deser.match_con "test"
    [ ("Equal", Equal);
      ("Less", Compare Lt);
      ("Greater", Compare Gt);
      ("LessEq", Compare Leq);
      ("GreaterEq", Compare Geq);
      ("AltLess", AltCompare Lt);
      ("AltGreater", AltCompare Gt);
      ("AltLessEq", AltCompare Leq);
      ("AltGreaterEq", AltCompare Geq)
    ]
    [ ].

Instance Deserialize_prim_type : Deserialize prim_type :=
  Deser.match_con "prim_type"
    [ ("BoolT", BoolT);
      ("IntT", IntT);
      ("CharT", CharT);
      ("StrT", StrT);
      ("Word8T", WordT W8);
      ("Word64T", WordT W64);
      ("Float64T", Float64T)
    ]
    [ ].

Instance Deserialize_op : Deserialize op :=
  fun l e =>
    match Deserialize_thunk_op l e with
    | inr t_op => inr (ThunkOp t_op)
    | inl _ =>
      match Deserialize_ws_shift l e with
      | inr (w, s, n) => inr (Shift w s n)
      | inl _ =>
        Deser.match_con "op"
          [ ("Equality", Equality);
            ("Opapp", Opapp);
            ("Opassign", Opassign);
            ("Opref", Opref);
            ("Opderef", Opderef);
            ("Aw8alloc", Aw8alloc);
            ("Aw8sub", Aw8sub);
            ("Aw8length", Aw8length);
            ("Aw8update", Aw8update);
            ("CopyStrStr", CopyStrStr);
            ("CopyStrAw8", CopyStrAw8);
            ("CopyAw8Str", CopyAw8Str);
            ("CopyAw8Aw8", CopyAw8Aw8);
            ("XorAw8Strunsafe", XorAw8Str_unsafe);
            ("Implode", Implode);
            ("Explode", Explode);
            ("Strsub", Strsub);
            ("Strlen", Strlen);
            ("Strcat", Strcat);
            ("VfromList", VfromList);
            ("Vsub", Vsub);
            ("Vlength", Vlength);
            ("Aalloc", Aalloc);
            ("AallocEmpty", AallocEmpty);
            ("AallocFixed", AallocFixed);
            ("Asub", Asub);
            ("Alength", Alength);
            ("Aupdate", Aupdate);
            ("Vsub_unsafe", Vsub_unsafe);
            ("Asubunsafe", Asub_unsafe);
            ("Aupdateunsafe", Aupdate_unsafe);
            ("Aw8subunsafe", Aw8sub_unsafe);
            ("Aw8updateunsafe", Aw8update_unsafe);
            ("ListAppend", ListAppend);
            ("ConfigGC", ConfigGC);
            ("Envid", Env_id);
            ("Eval", Eval)
          ]
          [ ("Arith", Deser.con2_ Arith);
            ("FromTo", Deser.con2_ FromTo);
            ("Test", Deser.con2_ Test);
            ("FFI", Deser.con1_ FFI)
          ] l e
      end
    end.

Instance Deserialize_locn : Deserialize locn :=
  fun l e =>
    match e with
    | Atom_ (Raw "unk") => inr UNKNOWNpt
    | Atom_ (Raw "eof") => inr EOFpt
    | List (e1 :: e2 :: nil) =>
      _bind_sum (_from_sexp (0 :: l) e1) (fun a =>
      _bind_sum (_from_sexp (1 :: l) e2) (fun b =>
      inr (POSN a b)))
    | List _ => inl (DeserError l "could not read 'locn', expected list of length 2, got list of a different length")
    | Atom_ _ => inl (DeserError l "could not read 'locn', expected list of length 2, got atom")
    end.

Instance Deserialize_locs : Deserialize locs :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      _bind_sum (_from_sexp (0 :: l) e1) (fun a =>
      _bind_sum (_from_sexp (1 :: l) e2) (fun b =>
      inr (a, b)))
    | List _ => inl (DeserError l "could not read 'locs', expected list of length 2, got list of a different length")
    | Atom_ _ => inl (DeserError l "could not read 'locs', expected list of length 2, got atom")
    end.

#[bypass_check(guard)]
Definition Deserialize_exp_aux : Deserialize exp :=
  fix ds (l : loc) (e : sexp) {struct e} : error + exp :=
    Deser.match_con "exp"
      [ ]
      [ ("Raise", Deser.con1 Raise ds);
        ("Handle", Deser.con2 Handle ds
          (@Deserialize_cakeml_list _ (@Deserialize_cakeml_pair _ _ _ ds)));
        ("Lit", Deser.con1_ Lit);
        ("Con", Deser.con2 Con
          Deserialize_cakeml_option
          (@Deserialize_cakeml_list _ ds));
        ("Var", Deser.con1_ Var);
        ("Fun", Deser.con2 Fun _from_sexp ds);
        ("App", Deser.con2 App _from_sexp (@Deserialize_cakeml_list _ ds));
        ("Log", Deser.con3 Log _from_sexp ds ds);
        ("If", Deser.con3 If ds ds ds);
        ("Mat", Deser.con2 Mat ds
          (@Deserialize_cakeml_list _ (@Deserialize_cakeml_pair _ _ _ ds)));
        ("Let", Deser.con3 Let Deserialize_cakeml_option ds ds);
        ("Letrec", Deser.con2 Letrec
          (@Deserialize_cakeml_list _
            (@Deserialize_cakeml_pair _ _ _
              (@Deserialize_cakeml_pair _ _ _ ds)))
          ds);
        ("Tannot", Deser.con2 Tannot ds _from_sexp);
        ("Lannot", Deser.con2 Lannot ds _from_sexp)
      ] l e.
Instance Deserialize_exp : Deserialize exp := Deserialize_exp_aux.

Instance Deserialize_type_def : Deserialize type_def :=
    @Deserialize_cakeml_list _ (
      @Deserialize_cakeml_pair _ _
        (@Deserialize_cakeml_list tvarN _)
        (@Deserialize_cakeml_pair typeN _
          _
          (@Deserialize_cakeml_list _
            (@Deserialize_cakeml_pair conN _
              _
              (@Deserialize_cakeml_list ast_t Deserialize_ast_t)
            )
          )
        )
    ).

#[bypass_check(guard)]
Definition Deserialize_dec_aux : Deserialize dec :=
  fix ds (l : loc) (e : sexp) {struct e} : error + dec :=
    let ds_exp_list := @Deserialize_cakeml_list _ ds in
    Deser.match_con "dec"
      [ ]
      [ ("Dlet", Deser.con3_ Dlet);
        ("Dletrec", Deser.con2 Dletrec _from_sexp
          (@Deserialize_cakeml_list _ (
           @Deserialize_cakeml_pair _ _ _ (
             @Deserialize_cakeml_pair _ _ _ Deserialize_exp))));
        ("Dtype", Deser.con2_ Dtype);
        ("Dtabbrev", Deser.con4 Dtabbrev
          _from_sexp Deserialize_cakeml_list _from_sexp _from_sexp);
        ("Dexn", Deser.con3 Dexn
          _from_sexp _from_sexp Deserialize_cakeml_list);
        ("Dmod", Deser.con2 Dmod _from_sexp ds_exp_list);
        ("Dlocal", Deser.con2 Dlocal ds_exp_list ds_exp_list);
        ("Denv", Deser.con1_ Denv)
      ] l e.
Instance Deserialize_dec : Deserialize dec := Deserialize_dec_aux.

Definition program_of_string (s : String.t) : error + list dec :=
  @from_string (list dec) (@Deserialize_cakeml_list _ Deserialize_dec) s.
