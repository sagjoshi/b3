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
    function ArgumentCount(): nat {
      match this
      case IfThenElse => 3
      case LogicalNot | UnaryMinus => 1
      case _ => 2
    }

    function Arity() : nat {
      match this
      case IfThenElse => 3
      case LogicalNot | UnaryMinus => 1
      case _ => 2
    }

    function ToBinaryFunc(): (M.Any, M.Any) --> M.Any
      requires Arity() == 2
    {
      match this {
        case Equiv => M.Equiv
        case LogicalImp => M.Implies
        case LogicalAnd => M.LogicAnd
        case LogicalOr => M.Or
        case Eql => M.Eql
        case Neql => M.Neql
        case Less => M.Less
        case AtMost => M.AtMost
        case Plus => M.Plus
        case Minus => M.Minus
        case Times => M.Times
        case Div => M.Div
        case Mod => M.Mod
      }
    }

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

    function ToUnaryFunc(): M.Any --> M.Any
      requires Arity() == 1
    {
      match this {
        case LogicalNot => M.Not
        case UnaryMinus => M.Negate
      }
    }

    predicate IsIntOperator() {
      match this
      case Plus | Minus | Times | Div | Mod | Less | AtMost | UnaryMinus => true
      case _ => false
    }

    predicate IsBoolOperator() {
      match this
      case Equiv | LogicalImp | LogicalAnd | LogicalOr | LogicalNot => true
      case _ => false
    }

    predicate IsPolymorphicOperator() {
      match this
      case Eql | Neql => true
      case _ => false
    }


    predicate CompatibleWith(args: seq<M.Any>) {
      |args| == Arity() &&
      match this
      case IfThenElse => M.IsBool(args[0])
      case Eql | Neql => true 
      case _ => 
        if Type() == M.Int then
          && (forall i :: 0 <= i < |args| ==> M.IsInt(args[i]))
          && (Div? || Mod? ==> M.ToInt(args[1]) != 0)
        else if Type() == M.Bool then
          forall i :: 0 <= i < |args| ==> M.IsBool(args[i])
        else false
    }

    opaque function Eval(args: seq<M.Any>): Option<M.Any>
    {
      if !CompatibleWith(args) then None
      else if Arity() == 3 then
        if M.IsBool(args[0]) then Some(args[0]) else Some(args[1])
      else if Arity() == 1 then
        Some(ToUnaryFunc()(args[0]))
      else if Arity() == 2 then
        Some(ToBinaryFunc()(args[0], args[1]))
      else None
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>)
    {
      Eval(args).Some? ==> Eval(args).value in outs
    }
  }

  lemma EqlEvalLemma(v1: M.Any, v2: M.Any)
    ensures Eql.Eval([v1, v2]) == Some(M.InterpBool(v1 == v2))
  {
    reveal Eql.Eval;
  }

  lemma AndEvalLemma(v1: M.Any, v2: M.Any)
    requires M.IsBool(v1)
    requires M.IsBool(v2)
    ensures LogicalAnd.Eval([v1, v2]) == Some(M.LogicAnd(v1, v2))
  {
    reveal LogicalAnd.Eval;
  }

  lemma ImpliesEvalLemma(v1: M.Any, v2: M.Any)
    requires M.IsBool(v1)
    ensures LogicalImp.Eval([v1, v2]) == 
      if M.IsBool(v2) then Some(M.Implies(v1, v2)) else None
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

    predicate ArgsCompatibleWith(args: seq<M.Any>) {
      |args| == |Parameters| && forall i :: 0 <= i < |args| ==> M.HasType(args[i], Parameters[i].typ.ToType())
    }

    function ToFunction(): M.Function {
      M.Function(Name, seq(|Parameters|, (i: nat) requires i < |Parameters| => Parameters[i].typ.ToType()), ResultType.ToType())
    }

    function EvalArgs(args: seq<M.Any>): Option<M.Any> {
      if ArgsCompatibleWith(args) then 
        Some(M.InterpFunctionOn(ToFunction(), args)) 
      else None
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>)
      reads *
    {
      && ArgsCompatibleWith(args)
      && if IsUninterpreted() then
          M.InterpFunctionOn(ToFunction(), args) in outs
        else
          GetDef().RefEval(args as State, outs)
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

    ghost function Eval(s: State): Option<M.Any>
      requires IsDefinedOn(|s|)
    {
      match this
      case BConst(bvalue)  => Some(M.InterpBool(bvalue))
      case IConst(ivalue)  => Some(M.InterpInt(ivalue))
      case BVar(id) => Some(s[id])
      case CustomConst(value) => Some(M.InterpLiteral(value.ToLiteral()))
      case OperatorExpr(op, args) => 
        var args :- SeqEval(args, s);
        op.Eval(args)
      case FunctionCallExpr(func, args) => 
        var args :- SeqEval(args, s);
        func.EvalArgs(args)
      case QuantifierExpr(true, v, typ, body) =>
        Some(M.InterpBool(forall x: M.Any | M.HasType(x, typ.ToType()) :: 
          body.Eval(s.Update([x])) == Some(M.True)
        ))
      case QuantifierExpr(false, v, typ, body) =>
        Some(M.InterpBool(exists x: M.Any | M.HasType(x, typ.ToType()) :: 
          body.Eval(s.Update([x])) == Some(M.True)
        ))
      case LetExpr(v, rhs, body) => 
        var x :- rhs.Eval(s);
        body.Eval(s.Update([x]))
    }

    greatest predicate RefEval(s: State, outs: iset<M.Any>)
      reads *
    {
      match this
      case BConst(bvalue) => M.InterpBool(bvalue) in outs
      case IConst(ivalue) => M.InterpInt(ivalue) in outs
      case CustomConst(value) => M.InterpLiteral(value.ToLiteral()) in outs
      case BVar(id) => id < |s| && s[id] in outs
      case OperatorExpr(op, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet)
          && forall outArgs <- CrossProduct(outArgsSet) :: op.RefEval(outArgs, outs)
      case FunctionCallExpr(func, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet)
          && forall outArgs <- CrossProduct(outArgsSet) :: func.RefEval(outArgs, outs)
      case LetExpr(v, rhs, body) => 
        exists outsRhs: iset<M.Any> :: 
          && rhs.RefEval(s, outsRhs)
          && forall out <- outsRhs :: body.RefEval(s.Update([out]), outs)
      case QuantifierExpr(true, v, tp, body) => 
        forall x: M.Any | M.HasType(x, tp.ToType()) :: 
          body.RefEval(s.Update([x]), outs * iset{M.True, M.False})
      case QuantifierExpr(false, v, tp, body) =>
        exists x: M.Any | M.HasType(x, tp.ToType()) :: 
          body.RefEval(s.Update([x]), outs * iset{M.True, M.False})
    }

    lemma EvalSound(s: State)
      requires IsDefinedOn(|s|)
      ensures RefEval(s, iset v: M.Any | Eval(s) == Some(v))
    {

    }

    ghost predicate HoldsOn(s: State) 
      requires IsDefinedOn(|s|)
    {
      Eval(s) == Some(M.True)
    }

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures Eval(s1) == Eval(s2)
    { 
      match this
      case QuantifierExpr(true, v, tp, body) => 
      case QuantifierExpr(false, v, tp, body) => 
      case FunctionCallExpr(func, args) => SeqEvalDepthLemma(args, s1, s2);
      case OperatorExpr(op, args) => SeqEvalDepthLemma(args, s1, s2);
      case _ =>
    } 

    ghost predicate Holds() 
      // reads *
    {
      forall s: State :: IsDefinedOn(|s|) ==> HoldsOn(s)
    }

    ghost function Sem(): iset<State> 
      // reads *
    { 
      iset st: State | IsDefinedOn(|st|) && HoldsOn(st) 
    }
  }

  ghost function CrossProduct<T(!new)>(ss: seq<iset<T>>): iset<seq<T>> {
    iset s | 
      && |s| == |ss|
      && forall i: nat | i < |ss| :: s[i] in ss[i]
  }

  greatest predicate RefSeqEval(ss: seq<Expr>, s: State, outSeqs: seq<iset<M.Any>>) 
    reads *
  {
    if ss == [] then outSeqs == [] else
    && |outSeqs| > 0
    && ss[0].RefEval(s, outSeqs[0])
    && RefSeqEval(ss[1..], s, outSeqs[1..])
  }

  ghost function SeqEval(ss: seq<Expr>, s: State): Option<seq<M.Any>>
    requires forall e <- ss :: e.IsDefinedOn(|s|)
    // ensures |SeqEval(ss, s)| == |ss|
  {
    if ss == [] then Some([]) else
    var e :- ss[0].Eval(s);
    var es :- SeqEval(ss[1..], s);
    Some([e] + es)
  }

  lemma SeqEval1(e: Expr, s: State)
    requires e.IsDefinedOn(|s|)
    requires e.Eval(s).Some?
    ensures SeqEval([e], s) == Some([e.Eval(s).value])
  {
    calc {
      SeqEval([e], s);
      == { assert [e][1..] == [];
           assert [e][0] == e; }
      Some([e.Eval(s).value] + []);
      == { assert [e.Eval(s).value] + [] == [e.Eval(s).value]; }
      Some([e.Eval(s).value]);
    }
  }

  lemma SeqEval2(e1: Expr, e2: Expr, s: State)
    requires e1.IsDefinedOn(|s|)
    requires e2.IsDefinedOn(|s|)
    requires e1.Eval(s).Some?
    requires e2.Eval(s).Some?
    ensures SeqEval([e1, e2], s) == Some([e1.Eval(s).value, e2.Eval(s).value])
  {
    assert [e1, e2][1..] == [e2];
    assert [e1, e2][0] == e1;
    SeqEval1(e2, s); 
    calc {
      SeqEval([e1, e2], s);
      == { assert [e1, e2][1..] == [e2];
           assert [e1, e2][0] == e1;
           SeqEval1(e2, s); }
      Some([e1.Eval(s).value] + SeqEval([e2], s).value);
      == { SeqEval1(e2, s);
           assert [e1.Eval(s).value] + [e2.Eval(s).value] == [e1.Eval(s).value, e2.Eval(s).value]; }
      Some([e1.Eval(s).value, e2.Eval(s).value]);
    }
  }

  lemma SeqEvalDepthLemma(ss: seq<Expr>, s1: State, s2: State)
    requires SeqExprDepth(ss) <= |s1|
    requires SeqExprDepth(ss) <= |s2|
    requires forall i: Idx :: i < SeqExprDepth(ss) ==> s1[i] == s2[i]
    ensures SeqEval(ss, s1) == SeqEval(ss, s2)
  {
    if ss != [] {
      ss[0].EvalDepthLemma(s1, s2);
      SeqEvalDepthLemma(ss[1..], s1, s2);
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

  lemma EvalEqLemma(e1: Expr, e2: Expr, s: State)
    requires e1.IsDefinedOn(|s|)
    requires e2.IsDefinedOn(|s|)
    requires e1.Eval(s) == e2.Eval(s)
    requires e1.Eval(s).Some?
    ensures Eq(e1, e2).Depth() == max(e1.Depth(), e2.Depth())
    ensures Eq(e1, e2).IsDefinedOn(|s|)
    ensures Eq(e1, e2).HoldsOn(s)
  { 
    SeqMaxPairLemma(e1, e2);
    calc {
      Eq(e1, e2).Eval(s);
      ==
      OperatorExpr(Eql, [e1, e2]).Eval(s);
      == { SeqEval2(e1, e2, s); }
      Eql.Eval([e1.Eval(s).value, e2.Eval(s).value]);
      == { EqlEvalLemma(e1.Eval(s).value, e2.Eval(s).value); }
      Some(M.InterpBool(e1.Eval(s).value == e2.Eval(s).value));
      == { assert e1.Eval(s) == e2.Eval(s); }
      Some(M.InterpBool(true));
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

  lemma HoldsOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|)
    requires e1.IsDefinedOn(|s|)
    requires e0.HoldsOn(s)
    requires e1.HoldsOn(s)
    ensures And(e0, e1).IsDefinedOn(|s|) 
    ensures And(e0, e1).HoldsOn(s)
  {
    SeqMaxPairLemma(e0, e1);
    SeqEval2(e0, e1, s);
    AndEvalLemma(e0.Eval(s).value, e1.Eval(s).value);
  }

  lemma HoldsOnImpliesLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|)
    requires e1.IsDefinedOn(|s|)
    requires e0.HoldsOn(s)
    requires (
      IsDefinedOnImpliesLemma(e0, e1, s);
      Implies(e0, e1).HoldsOn(s))
    ensures e1.HoldsOn(s)
  {
    IsDefinedOnImpliesLemma(e0, e1, s);
    assert e0.Eval(s).Some?;
    assert SeqEval([e0, e1], s).Some?;
    if e1.Eval(s).Some? {
      SeqEval2(e0, e1, s);
      calc {
        Implies(e0, e1).Eval(s).value;
        == { SeqEval2(e0, e1, s);
             ImpliesEvalLemma(e0.Eval(s).value, e1.Eval(s).value); }
        M.Implies(e0.Eval(s).value, e1.Eval(s).value);
        ==
        M.Implies(M.True, e1.Eval(s).value);
        ==
         M.InterpBool(true ==> M.ToBool(e1.Eval(s).value));
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

  lemma EvalConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.IsDefinedOn(|s|)
    requires forall e <- ctx :: e.HoldsOn(s)
    ensures Conj(ctx).IsDefinedOn(|s|)
    ensures Conj(ctx).HoldsOn(s)
  {  
    if ctx != [] { 
      IsDefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); 
      HoldsOnAndLemma(ctx[0], Conj(ctx[1..]), s);
    }  
  }

}