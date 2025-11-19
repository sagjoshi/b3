module Expr {
  import opened Utils
  import opened State
  import M = Model
  import opened Std.Wrappers

  datatype Operator =
    // ternary operators
    | IfThenElse
    // binary operators
    | Equiv
    | LogicalImp
    | LogicalAnd | LogicalOr
    | Eql | Neql
    | Less | AtMost
    | Plus | Minus | Times | Div | Mod
    // unary operators
    | LogicalNot
    | UnaryMinus
  {
    function Type(): M.Type 
      requires !IfThenElse?
      requires !Eql?
      requires !Neql?
    {
      match this {
        case LogicalNot | Equiv | LogicalImp | LogicalAnd | LogicalOr => M.Bool
        case _ => M.Int
      }
    }

    function Arity() : nat {
      match this
      case IfThenElse => 3
      case LogicalNot | UnaryMinus => 1
      case _ => 2
    }

    function ToBinaryFunc(m: M.Model): (M.Any, M.Any) --> M.Any
      requires Arity() == 2
    {
      match this {
        case Equiv => m.Equiv
        case LogicalImp => m.Implies
        case LogicalAnd => m.LogicAnd
        case LogicalOr => m.Or
        case Eql => m.Eql
        case Neql => m.Neql
        case Less => m.Less
        case AtMost => m.AtMost
        case Plus => m.Plus
        case Minus => m.Minus
        case Times => m.Times
        case Div => m.Div
        case Mod => m.Mod
      }
    }

    function ToUnaryFunc(m: M.Model): M.Any --> M.Any
      requires Arity() == 1
    {
      match this {
        case LogicalNot => m.Not
        case UnaryMinus => m.Negate
      }
    }

    predicate CompatibleWith(args: seq<M.Any>, m: M.Model) {
      |args| == Arity() &&
      match this
      case IfThenElse => m.IsBool(args[0])
      case Eql | Neql => true 
      case _ => 
        if Type() == M.Int then
          && (forall i :: 0 <= i < |args| ==> m.IsInt(args[i]))
          && (Div? || Mod? ==> m.ToInt(args[1]) != 0)
        else if Type() == M.Bool then
          forall i :: 0 <= i < |args| ==> m.IsBool(args[i])
        else false
    }

    opaque function Eval(args: seq<M.Any>, m: M.Model): Option<M.Any>
    {
      if !CompatibleWith(args, m) then None
      else if Arity() == 3 then
        if m.IsBool(args[0]) then Some(args[0]) else Some(args[1])
      else if Arity() == 1 then
        Some(ToUnaryFunc(m)(args[0]))
      else if Arity() == 2 then
        Some(ToBinaryFunc(m)(args[0], args[1]))
      else None
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>, m: M.Model)
    {
      Eval(args, m).Some? && Eval(args, m).value in outs
    }
  }

  lemma EqlEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    ensures Eql.Eval([v1, v2], m) == Some(m.InterpBool(v1 == v2))
  {
    reveal Eql.Eval;
  }

  lemma AndEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    requires m.IsBool(v1)
    requires m.IsBool(v2)
    ensures LogicalAnd.Eval([v1, v2], m) == Some(m.LogicAnd(v1, v2))
  {
    reveal LogicalAnd.Eval;
  }

  lemma ImpliesEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    requires m.IsBool(v1)
    ensures LogicalImp.Eval([v1, v2], m) == 
      if m.IsBool(v2) then Some(m.Implies(v1, v2)) else None
  {
    reveal LogicalImp.Eval;
  }

  datatype Type = 
    | BType 
    | IType 
    | CustomType(typ: M.Type)
  {
    function ToType(): M.Type {
      match this
      case BType => M.Bool
      case IType => M.Int
      case CustomType(typ) => typ
    }
  }

  datatype Literal = Literal(value: string, typ: Type) {
    function ToLiteral(): M.Literal {
      M.Literal(value, typ.ToType())
    }
  }

  datatype FParameter = FParameter(typ: Type)

  datatype FunctionDefinition = FunctionDefinition(when: seq<Expr>, body: Expr)

  class Function {
    const Name: string
    const Parameters: seq<FParameter>
    const ResultType: Type
    var Definition: Option<FunctionDefinition>

    predicate IsUninterpreted() 
      reads this`Definition
    {
      Definition == None
    }

    function GetDef(): Expr
      requires !IsUninterpreted()
      reads this`Definition
    {
      Definition.value.body
    }

    predicate ArgsCompatibleWith(args: seq<M.Any>, m: M.Model) {
      |args| == |Parameters| && forall i :: 0 <= i < |args| ==> m.HasType(args[i], Parameters[i].typ.ToType())
    }

    function ToFunction(): M.Function {
      M.Function(Name, seq(|Parameters|, (i: nat) requires i < |Parameters| => Parameters[i].typ.ToType()), ResultType.ToType())
    }

    function EvalArgs(args: seq<M.Any>, m: M.Model): Option<M.Any> {
      if ArgsCompatibleWith(args, m) then 
        Some(m.InterpFunctionOn(ToFunction(), args)) 
      else None
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      && ArgsCompatibleWith(args, m)
      && var fval := m.InterpFunctionOn(ToFunction(), args);
        && fval in outs
        && (!IsUninterpreted() ==> GetDef().RefEval(ToState(args), iset{fval}, m))
    }

    predicate Valid()
      reads *
    {
      !IsUninterpreted() ==> GetDef().IsDefinedOn(|Parameters|)
    }

    // function BodyAxiom'(params: seq<FParameter>): Expr {
    //   if params == [] then 
    //     Eq
    // }

    ghost predicate IsSound(m: M.Model)
      // requires Valid()
      reads *
    {
      !IsUninterpreted() ==> 
        forall args: seq<M.Any> | ArgsCompatibleWith(args, m) :: 
          GetDef().RefEval(ToState(args), iset{m.InterpFunctionOn(ToFunction(), args)}, m)
    }

    function FunctionsCalled(): set<Function>
      reads *
    {
      if IsUninterpreted() then {} else GetDef().FunctionsCalled()
    }

    lemma EvalSound(args: seq<M.Any>, funs: set<Function>, outs: iset<M.Any>, m: M.Model)
      requires EvalArgs(args, m).Some?
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      requires this in funs
      requires EvalArgs(args, m).value in outs
      ensures RefEval(args, outs, m)
    {
      if !IsUninterpreted() {
        assert ArgsCompatibleWith(args, m);
        // GetDef().EvalSound(ToState(args), funs);
        // calc {
        //   RefEval(args, iset{EvalArgs(args).value});
        //   == 
        //   GetDef().RefEval(ToState(args), iset{EvalArgs(args).value});
        // }
      }
    }
  }

  datatype Expr =
    | BConst(bvalue: bool)
    | IConst(ivalue: int)
    | CustomConst(value: Literal)
    | BVar(id: Idx)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | FunctionCallExpr(func: Function, args: seq<Expr>)
    | LetExpr(v: Variable, rhs: Expr, body: Expr)
    | QuantifierExpr(univ: bool, v: Variable, tp: Type, body: Expr) 
  {
    function Depth(): Idx {
      match this
      case BConst(_) => 0
      case IConst(_) => 0
      case CustomConst(_) => 0
      case OperatorExpr(op, args) => SeqExprDepth(args)
      case FunctionCallExpr(func, args) => SeqExprDepth(args)
      case BVar(id) => id + 1
      case QuantifierExpr(univ, v, tp, body) => if body.Depth() == 0 then 0 else body.Depth() - 1
      case LetExpr(v, rhs, body) => if body.Depth() == 0 then rhs.Depth() else 
        max(rhs.Depth(), body.Depth() - 1)
    }

    predicate IsDefinedOn(d: Idx) 
    {
      Depth() <= d
    }

    function FunctionsCalled(): set<Function>
    {
      match this
      case FunctionCallExpr(func, args) => {func} + SeqExprFunctionsCalled(args)
      case OperatorExpr(op, args) => SeqExprFunctionsCalled(args)
      case QuantifierExpr(univ, v, tp, body) => body.FunctionsCalled()
      case LetExpr(v, rhs, body) => rhs.FunctionsCalled() + body.FunctionsCalled()
      case _ => {}
    }

    predicate ValidCalls()
      reads *
    {
      forall func <- FunctionsCalled() :: func.Valid()
    }

    ghost function Eval(s: State, m: M.Model): Option<M.Any>
      requires IsDefinedOn(|s|)
    {
      match this
      case BConst(bvalue)  => Some(m.InterpBool(bvalue))
      case IConst(ivalue)  => Some(m.InterpInt(ivalue))
      case BVar(id) => Some(s[id])
      case CustomConst(value) => Some(m.InterpLiteral(value.ToLiteral()))
      case OperatorExpr(op, args) => 
        var args :- SeqEval(args, s, m);
        op.Eval(args, m)
      case FunctionCallExpr(func, args) => 
        var args :- SeqEval(args, s, m);
        func.EvalArgs(args, m)
      case QuantifierExpr(true, v, typ, body) =>
        if (forall x: M.Any | m.HasType(x, typ.ToType()) :: 
            SomeBVal?(body.Eval(s.Update([x]), m), m)) then 
          Some(m.InterpBool(forall x: M.Any | m.HasType(x, typ.ToType()) :: 
            body.Eval(s.Update([x]), m) == Some(m.True())
          ))
        else None
      case QuantifierExpr(false, v, typ, body) =>
        if (forall x: M.Any | m.HasType(x, typ.ToType()) :: 
            SomeBVal?(body.Eval(s.Update([x]), m), m)) then 
          Some(m.InterpBool(exists x: M.Any | m.HasType(x, typ.ToType()) :: 
            body.Eval(s.Update([x]), m) == Some(m.True())
          ))
        else None
      case LetExpr(v, rhs, body) => 
        var x :- rhs.Eval(s, m);
        body.Eval(s.Update([x]), m)
    }

    greatest predicate RefEval(s: State, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      match this
      case BConst(bvalue) => m.InterpBool(bvalue) in outs
      case IConst(ivalue) => m.InterpInt(ivalue) in outs
      case CustomConst(value) => m.InterpLiteral(value.ToLiteral()) in outs
      case BVar(id) => id < |s| && s[id] in outs
      case OperatorExpr(op, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet, m)
          && forall outArgs <- CrossProduct(outArgsSet) :: op.RefEval(outArgs, outs, m)
      case FunctionCallExpr(func, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet, m)
          && forall outArgs <- CrossProduct(outArgsSet) :: func.RefEval(outArgs, outs, m)
      case LetExpr(v, rhs, body) => 
        exists outsRhs: iset<M.Any> :: 
          && rhs.RefEval(s, outsRhs, m)
          && forall out <- outsRhs :: body.RefEval(s.Update([out]), outs, m)
      case QuantifierExpr(true, v, tp, body) => 
        (forall x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), (iset v | m.IsBool(v)), m))
        &&
        ((m.True() in outs &&
          forall x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), iset{m.True()}, m))
        ||
        (m.False() in outs &&
          exists x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), iset{m.False()}, m)))
      case QuantifierExpr(false, v, tp, body) =>
        (forall x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), (iset v | m.IsBool(v)), m))
        &&
        ((m.True() in outs &&
          exists x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), iset{m.True()}, m))
        ||
        (m.False() in outs &&
          forall x: M.Any | m.HasType(x, tp.ToType()) :: 
            body.RefEval(s.Update([x]), iset{m.False()}, m)))
    }

    ghost predicate LetRefEval(s: State, rhs: Expr, body: Expr, outsRhs: iset<M.Any>, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      forall out <- outsRhs :: body.RefEval(s.Update([out]), outs, m)
    }

    lemma LetRefEvalUnfold(s: State, rhs: Expr, body: Expr, outs: iset<M.Any>, v: Variable, m: M.Model) returns (outsRhs: iset<M.Any>)
      requires LetExpr(v, rhs, body).RefEval(s, outs, m)
      ensures rhs.RefEval(s, outsRhs, m)
      ensures forall out <- outsRhs :: body.RefEval(s.Update([out]), outs, m)
    {
      var outsRhs' :| rhs.RefEval(s, outsRhs', m) &&
        LetRefEval(s, rhs, body, outsRhs', outs, m);
      outsRhs := outsRhs';
      forall out | out in outsRhs ensures body.RefEval(s.Update([out]), outs, m) {
        assert LetRefEval(s, rhs, body, outsRhs, outs, m) ==> forall out <- outsRhs :: body.RefEval(s.Update([out]), outs, m);
      }
    }

    lemma EvalComplete(s: State, outs: iset<M.Any>, m: M.Model)
      requires RefEval(s, outs, m)
      // ensures outs != iset{}
      ensures IsDefinedOn(|s|)
      ensures Eval(s, m).Some? 
      ensures Eval(s, m).value in outs
    {
      match this
      case OperatorExpr(op, args) => 
        var outArgsSet :| 
          && RefSeqEval(args, s, outArgsSet, m)
          && (forall outArgs <- CrossProduct(outArgsSet) :: op.RefEval(outArgs, outs, m));
        SeqEvalComplete(args, s, outArgsSet, m);
      case FunctionCallExpr(func, args) => 
        var outArgsSet :| 
          && RefSeqEval(args, s, outArgsSet, m)
          && (forall outArgs <- CrossProduct(outArgsSet) :: func.RefEval(outArgs, outs, m));
        SeqEvalComplete(args, s, outArgsSet, m);
      case LetExpr(v, rhs, body) => 
        var outsRhs := LetRefEvalUnfold(s, rhs, body, outs, v, m);
        rhs.EvalComplete(s, outsRhs, m);
      case QuantifierExpr(true, v, tp, body) => 
        var x := m.NoEmptyTypes(tp.ToType());
        if (forall x: M.Any | m.HasType(x, tp.ToType()) :: 
          body.RefEval(s.Update([x]), iset{m.True()}, m)) {
        }
      case QuantifierExpr(false, v, tp, body) => 
        var x := m.NoEmptyTypes(tp.ToType());
        if (exists x: M.Any | m.HasType(x, tp.ToType()) :: 
          body.RefEval(s.Update([x]), iset{m.True()}, m)) {
        }
      case _ => 
    }

    lemma EvalSound(s: State, funs: set<Function>, outs: iset<M.Any>, m: M.Model)
      requires FunctionsCalled() <= funs
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      requires IsDefinedOn(|s|)
      requires Eval(s, m).Some?
      requires Eval(s, m).value in outs
      ensures RefEval(s, outs, m)
    {
      match this
      case OperatorExpr(op, args) => 
        SeqEvalSound(args, s, funs, SeqSingleton(SeqEval(args, s, m).value), m);
        CrossProductSeqSingleton(SeqEval(args, s, m).value);
      case FunctionCallExpr(func, args) => 
        SeqEvalSound(args, s, funs, SeqSingleton(SeqEval(args, s, m).value), m);
        CrossProductSeqSingleton(SeqEval(args, s, m).value);
        func.EvalSound(SeqEval(args, s, m).value, funs, outs, m );
      case LetExpr(v, rhs, body) => rhs.EvalSound(s, funs, iset{rhs.Eval(s, m).value}, m);
      case QuantifierExpr(true, v, typ, body) => 
        assert forall x: M.Any | m.HasType(x, typ.ToType()) :: 
          SomeBVal?(body.Eval(s.Update(Singleton(x)), m), m);
        if !(forall x: M.Any | m.HasType(x, typ.ToType()) :: 
          body.Eval(s.Update(Singleton(x)), m) == Some(m.True())) {
          var x: M.Any :| m.HasType(x, typ.ToType()) &&
            body.Eval(s.Update(Singleton(x)), m) != Some(m.True());
          m.BoolIsTrueOrFalse(body.Eval(s.Update(Singleton(x)), m).value);
        }
      case QuantifierExpr(false, v, tp, body) => 
        assert forall x: M.Any | m.HasType(x, tp.ToType()) :: 
          SomeBVal?(body.Eval(s.Update(Singleton(x)), m), m);
        if !(exists x: M.Any | m.HasType(x, tp.ToType()) :: 
          body.Eval(s.Update(Singleton(x)), m) == Some(m.True())) {
          forall x: M.Any | m.HasType(x, tp.ToType()) {
            m.BoolIsTrueOrFalse(body.Eval(s.Update(Singleton(x)), m).value);
          }
        }
      case _ =>
    }

    ghost predicate HoldsOn(s: State, m: M.Model) 
      requires IsDefinedOn(|s|)
    {
      Eval(s, m) == Some(m.True())
    }

    ghost predicate RefHoldsOn(s: State, m: M.Model)
      reads *
    {
      RefEval(s, iset{m.True()}, m)
    }

    lemma HoldsOnSound(s: State, funs: set<Function>, m: M.Model)
      requires FunctionsCalled() <= funs
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      ensures (IsDefinedOn(|s|) && HoldsOn(s, m)) == RefHoldsOn(s, m)
    {
      if IsDefinedOn(|s|) && HoldsOn(s, m) {
        EvalSound(s, funs, iset{m.True()}, m);
      }
      if RefHoldsOn(s, m) {
        EvalComplete(s, iset{m.True()}, m);
      }
    }

    lemma EvalDepthLemma(s1: State, s2: State, m: M.Model) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures Eval(s1, m) == Eval(s2, m)
    { 
      match this
      case QuantifierExpr(true, v, tp, body) => 
      case QuantifierExpr(false, v, tp, body) => 
      case FunctionCallExpr(func, args) => SeqEvalDepthLemma(args, s1, s2, m);
      case OperatorExpr(op, args) => SeqEvalDepthLemma(args, s1, s2, m);
      case _ =>
    } 

    ghost predicate Holds(md: M.Model) 
      // reads *
    {
      forall s: State :: IsDefinedOn(|s|) ==> HoldsOn(s, md)
    }

    ghost predicate RefHolds(md: M.Model)
      reads *
    {
      forall s: State :: IsDefinedOn(|s|) ==> RefHoldsOn(s, md)
    }

    ghost function Sem(m: M.Model): iset<State> 
      // reads *
    { 
      iset st: State | IsDefinedOn(|st|) && HoldsOn(st, m) 
    }
  }

  ghost predicate SeqHolds(ss: seq<Expr>, md: M.Model)
  {
    forall e <- ss :: e.Holds(md)
  }

  ghost predicate SeqRefHolds(ss: seq<Expr>, md: M.Model)
    reads *
  {
    forall e <- ss :: e.RefHolds(md)
  }

  function SeqExprFunctionsCalled(ss: seq<Expr>): set<Function>
  {
    if ss == [] then {} else ss[0].FunctionsCalled() + SeqExprFunctionsCalled(ss[1..])
  }

  lemma SeqExprFunctionsCalledIn(ss: seq<Expr>, s: Expr)
    requires s in ss
    ensures s.FunctionsCalled() <= SeqExprFunctionsCalled(ss)
  {
  }

  ghost function CrossProduct<T(!new)>(ss: seq<iset<T>>): iset<seq<T>> {
    iset s | 
      && |s| == |ss|
      && forall i: nat | i < |ss| :: s[i] in ss[i]
  }

  function SeqSingleton(s: seq): seq<iset> {
    seq(|s|, (i: nat) requires i < |s| => iset{s[i]})
  }

  lemma SeqSingletonCons<T>(s: T, ss: seq)
    ensures SeqSingleton([s] + ss) == [iset{s}] + SeqSingleton(ss)
  { }

  lemma CrossProductSeqSingleton<T(!new)>(ss: seq)
    ensures CrossProduct(SeqSingleton(ss)) == iset{ss}
  {
    forall s <- CrossProduct(SeqSingleton(ss)) ensures s == ss { }
  }

  greatest predicate RefSeqEval(ss: seq<Expr>, s: State, outSeqs: seq<iset<M.Any>>, m: M.Model) 
    reads *
  {
    if ss == [] then outSeqs == [] else
    && |outSeqs| > 0
    && ss[0].RefEval(s, outSeqs[0], m)
    && RefSeqEval(ss[1..], s, outSeqs[1..], m)
  }

  ghost function SeqEval(ss: seq<Expr>, s: State, m: M.Model): Option<seq<M.Any>>
    requires forall e <- ss :: e.IsDefinedOn(|s|)
    ensures SeqEval(ss, s, m).Some? ==> |SeqEval(ss, s, m).value| == |ss|
  {
    if ss == [] then Some([]) else
    var e :- ss[0].Eval(s, m);
    var es :- SeqEval(ss[1..], s, m);
    Some([e] + es)
  }

  predicate ISetOptionEq<T(!new)>(x: Option<T>, y: iset<T>, m: M.Model)
  {
    if x.None? then false else x.value in y
  }

  ghost predicate SeqISetOptionEq<T(!new)>(x: Option<seq<T>>, y: seq<iset<T>>, m: M.Model)
  {
    if x.None? then false else
    x.value in CrossProduct(y) 
  }

  lemma SeqEvalComplete(ss: seq<Expr>, s: State, outs: seq<iset<M.Any>>, m: M.Model)
    requires RefSeqEval(ss, s, outs, m)
    ensures SeqExprDepth(ss) <= |s|
    ensures SeqEval(ss, s, m).Some?
    ensures SeqEval(ss, s, m).value in CrossProduct(outs)
  {
    if ss != [] {
      ss[0].EvalComplete(s, outs[0], m);
      SeqEvalComplete(ss[1..], s, outs[1..], m);
      var o :| o in outs[0];
      var os :| os in CrossProduct(outs[1..]);
      assert [o] + os in CrossProduct(outs);
    } else {
      assert [] in CrossProduct(outs);
    }
  }

  lemma SeqEvalSound(ss: seq<Expr>, s: State, funs: set<Function>, outs: seq<iset<M.Any>>, m: M.Model)
    requires forall e <- ss :: e.IsDefinedOn(|s|)
    requires forall func <- funs :: func.IsSound(m)
    requires forall func <- funs :: func.FunctionsCalled() <= funs
    requires SeqEval(ss, s, m).Some?
    requires SeqExprFunctionsCalled(ss) <= funs
    requires SeqEval(ss, s, m).value in CrossProduct(outs)
    ensures RefSeqEval(ss, s, outs, m)
  {
    if ss != [] {
      ss[0].EvalSound(s, funs, outs[0], m);
      SeqEvalSound(ss[1..], s, funs, outs[1..], m);
      SeqSingletonCons(ss[0].Eval(s, m).value, SeqEval(ss[1..], s, m).value);
    }
  }

  lemma SeqEval1(e: Expr, s: State, m: M.Model)
    requires e.IsDefinedOn(|s|)
    requires e.Eval(s, m).Some?
    ensures SeqEval([e], s, m) == Some([e.Eval(s, m).value])
  {
    calc {
      SeqEval([e], s, m);
      == { assert [e][1..] == [];
           assert [e][0] == e; }
      Some([e.Eval(s, m).value] + []);
      == { assert [e.Eval(s, m).value] + [] == [e.Eval(s, m).value]; }
      Some([e.Eval(s, m).value]);
    }
  }

  lemma SeqEval2(e1: Expr, e2: Expr, s: State, m: M.Model)
    requires e1.IsDefinedOn(|s|)
    requires e2.IsDefinedOn(|s|)
    requires e1.Eval(s, m).Some?
    requires e2.Eval(s, m).Some?
    ensures SeqEval([e1, e2], s, m) == Some([e1.Eval(s, m).value, e2.Eval(s, m).value])
  {
    assert [e1, e2][1..] == [e2];
    assert [e1, e2][0] == e1;
    SeqEval1(e2, s, m); 
    calc {
      SeqEval([e1, e2], s, m);
      == { assert [e1, e2][1..] == [e2];
           assert [e1, e2][0] == e1;
           SeqEval1(e2, s, m); }
      Some([e1.Eval(s, m).value] + SeqEval([e2], s, m).value);
      == { SeqEval1(e2, s, m);
           assert [e1.Eval(s, m).value] + [e2.Eval(s, m).value] == [e1.Eval(s, m).value, e2.Eval(s, m).value]; }
      Some([e1.Eval(s, m).value, e2.Eval(s, m).value]);
    }
  }

  lemma SeqEvalDepthLemma(ss: seq<Expr>, s1: State, s2: State, m: M.Model)
    requires SeqExprDepth(ss) <= |s1|
    requires SeqExprDepth(ss) <= |s2|
    requires forall i: Idx :: i < SeqExprDepth(ss) ==> s1[i] == s2[i]
    ensures SeqEval(ss, s1, m) == SeqEval(ss, s2, m)
  {
    if ss != [] {
      ss[0].EvalDepthLemma(s1, s2, m);
      SeqEvalDepthLemma(ss[1..], s1, s2, m);
    }
  }

  function SeqExprDepth(ss: seq<Expr>): Idx 
    ensures forall e <- ss :: e.Depth() <= SeqExprDepth(ss)
  {
    if ss == [] then 0 else max(ss[0].Depth(), SeqExprDepth(ss[1..]))
  }

  function And(e0: Expr, e1: Expr): Expr {
    OperatorExpr(LogicalAnd, [e0, e1])
  }

  function Implies(e0: Expr, e1: Expr): Expr {
    OperatorExpr(LogicalImp, [e0, e1])
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    OperatorExpr(Eql, [e1, e2])
  }

  lemma SeqMaxPairLemma(e1: Expr, e2: Expr)
    ensures SeqExprDepth([e1, e2]) == max(e1.Depth(), e2.Depth())
  {
    calc {
      SeqExprDepth([e1, e2]);
      ==
      max(e1.Depth(), SeqExprDepth([e2]));
      ==
      max(e1.Depth(), e2.Depth());
    }
  }

  lemma EvalEqLemma(e1: Expr, e2: Expr, s: State, m: M.Model)
    requires e1.IsDefinedOn(|s|)
    requires e2.IsDefinedOn(|s|)
    requires e1.Eval(s, m) == e2.Eval(s, m)
    requires e1.Eval(s, m).Some?
    ensures Eq(e1, e2).Depth() == max(e1.Depth(), e2.Depth())
    ensures Eq(e1, e2).IsDefinedOn(|s|)
    ensures Eq(e1, e2).HoldsOn(s, m)
  { 
    SeqMaxPairLemma(e1, e2);
    calc {
      Eq(e1, e2).Eval(s, m);
      ==
      OperatorExpr(Eql, [e1, e2]).Eval(s, m);
      == { SeqEval2(e1, e2, s, m); }
      Eql.Eval([e1.Eval(s, m).value, e2.Eval(s, m).value], m);
      == { EqlEvalLemma(e1.Eval(s, m).value, e2.Eval(s, m).value, m); }
      Some(m.InterpBool(e1.Eval(s, m).value == e2.Eval(s, m).value));
      == { assert e1.Eval(s, m) == e2.Eval(s, m); }
      Some(m.InterpBool(true));
    }
  }

  lemma SeqExprDepthLemma(ss: seq<Expr>, s: Expr) 
    requires s in ss
    ensures s.Depth() <= SeqExprDepth(ss)
  {  }

  lemma SeqExprDepthLemma'(ss: seq<Expr>, d: Idx) 
    requires forall e <- ss :: e.Depth() <= d
    ensures SeqExprDepth(ss) <= d
  {
    if ss != [] {
      assert SeqExprDepth(ss) == max(ss[0].Depth(), SeqExprDepth(ss[1..]));
      assert ss[0].Depth() <= d;
      assert SeqExprDepth(ss[1..]) <= d;
    }
  }

  lemma IsDefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|) 
    requires e1.IsDefinedOn(|s|)
    ensures And(e0, e1).IsDefinedOn(|s|) 
  { 
    SeqMaxPairLemma(e0, e1);
  }

  lemma HoldsOnAndLemma(e0: Expr, e1: Expr, s: State, m: M.Model)
    requires e0.IsDefinedOn(|s|)
    requires e1.IsDefinedOn(|s|)
    requires e0.HoldsOn(s, m)
    requires e1.HoldsOn(s, m)
    ensures And(e0, e1).IsDefinedOn(|s|) 
    ensures And(e0, e1).HoldsOn(s, m)
  {
    SeqMaxPairLemma(e0, e1);
    SeqEval2(e0, e1, s, m);
    AndEvalLemma(e0.Eval(s, m).value, e1.Eval(s, m).value, m);
  }

  lemma HoldsOnImpliesLemma(e0: Expr, e1: Expr, s: State, m: M.Model)
    requires e0.IsDefinedOn(|s|)
    requires e1.IsDefinedOn(|s|)
    requires e0.HoldsOn(s, m)
    requires (
      IsDefinedOnImpliesLemma(e0, e1, s);
      Implies(e0, e1).HoldsOn(s, m))
    ensures e1.HoldsOn(s, m)
  {
    IsDefinedOnImpliesLemma(e0, e1, s);
    assert e0.Eval(s, m).Some?;
    assert SeqEval([e0, e1], s, m).Some?;
    if e1.Eval(s, m).Some? {
      SeqEval2(e0, e1, s, m);
      calc {
        Implies(e0, e1).Eval(s, m).value;
        == { SeqEval2(e0, e1, s, m);
             ImpliesEvalLemma(e0.Eval(s, m).value, e1.Eval(s, m).value, m); }
        m.Implies(e0.Eval(s, m).value, e1.Eval(s, m).value);
        ==
        m.Implies(m.True(), e1.Eval(s, m).value);
        ==
         m.InterpBool(true ==> m.ToBool(e1.Eval(s, m).value));
      }
    }
  }

  lemma IsDefinedOnImpliesLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|)
    requires e1.IsDefinedOn(|s|)
    ensures Implies(e0, e1).IsDefinedOn(|s|)
  { 
    SeqMaxPairLemma(e0, e1);
  }

  function Conj(ctx: seq<Expr>): Expr 
  {
    if ctx == [] then BConst(true) else And(ctx[0], Conj(ctx[1..]))
  }

  lemma DepthConjUnionLemma(ctx1: seq<Expr>, ctx2: seq<Expr>)
    ensures Conj(ctx1 + ctx2).Depth() == max(Conj(ctx1).Depth(), Conj(ctx2).Depth())
  {
    if ctx1 == [] {
      assert [] + ctx2 == ctx2;
    } else {
      assert ctx1 + ctx2 == [ctx1[0]] + (ctx1[1..] + ctx2);
      calc {
        Conj(ctx1 + ctx2).Depth();
        ==
        And(ctx1[0], Conj(ctx1[1..] + ctx2)).Depth();
        == { SeqMaxPairLemma(ctx1[0], Conj(ctx1[1..] + ctx2)); }
        max(ctx1[0].Depth(), Conj(ctx1[1..] + ctx2).Depth());
        == { SeqMaxPairLemma(ctx1[0], Conj(ctx1[1..])); }
        max(Conj(ctx1).Depth(), Conj(ctx2).Depth());
      }
    }
  }

  lemma EvalConjLemma(ctx: seq<Expr>, s: State, m: M.Model)
    requires forall e <- ctx :: e.IsDefinedOn(|s|)
    requires forall e <- ctx :: e.HoldsOn(s, m)
    ensures Conj(ctx).IsDefinedOn(|s|)
    ensures Conj(ctx).HoldsOn(s, m)
  {  
    if ctx != [] { 
      IsDefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); 
      HoldsOnAndLemma(ctx[0], Conj(ctx[1..]), s, m);
    }  
  }

}