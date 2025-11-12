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

    predicate IsBinaryOperator() {
      match this
      case Equiv | LogicalImp | LogicalAnd | LogicalOr | Eql | Neql | Less | AtMost => true
      case _ => false
    }

    predicate IsUnaryOperator() {
      match this
      case LogicalNot | UnaryMinus => true
      case _ => false
    }
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

    // ghost function EvalArgs(args: seq<M.Any>): M.Any
    //   requires !IsUninterpreted()
    //   requires GetDef().IsDefinedOn(|args|)
    //   reads *
    // {
    //   GetDef().Eval(args as State)
    // }

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

    ghost function Eval(s: State): M.Any
      requires IsDefinedOn(|s|)
      // reads *
    {
      match this
      case BConst(bvalue)  => M.InterpBool(bvalue)
      case IConst(ivalue)  => M.InterpInt(ivalue)
      case BVar(id) => s[id]
      case CustomConst(value) => M.InterpLiteral(value.ToLiteral())
      // ternary operators
      case OperatorExpr(op, ss) => 
        if op == IfThenElse then
          if |ss| != 3 then M.Bot
          else 
            var guard := ss[0].Eval(s);
            var thn := ss[1].Eval(s);
            var els := ss[2].Eval(s);
            if M.IsBool(guard) then 
              if M.ToBool(guard) then thn else els
            else M.Bot
        else if op.IsUnaryOperator() then
          if |ss| != 1 then M.Bot
          else
            var e := ss[0].Eval(s);
            if M.IsBool(e) && op == LogicalNot then
              M.Not(e)
            else if M.IsInt(e) && op == UnaryMinus then
              M.Negate(e)
            else M.Bot
        else if op.IsBinaryOperator() then
          if |ss| != 2 then M.Bot
          else
            var e0 := ss[0].Eval(s);
            var e1 := ss[1].Eval(s);
            match op {
              case Eql => M.InterpBool(e0 == e1)
              case Neql => M.InterpBool(e0 != e1)
              case _ =>
                if M.IsBool(e0) && M.IsBool(e1) then
                  match op {
                    case Equiv => M.Equiv(e0, e1)
                    case LogicalImp => M.Implies(e0, e1)
                    case LogicalAnd => M.And(e0, e1)
                    case LogicalOr => M.Or(e0, e1)
                    case _ => M.Bot
                  }
                else if M.IsInt(e0) && M.IsInt(e1) then
                  match op {
                    case Less => M.Less(e0, e1)
                    case AtMost => M.AtMost(e0, e1)
                    case Plus => M.Plus(e0, e1)
                    case Minus => M.Minus(e0, e1)
                    case Times => M.Times(e0, e1)
                    case Div => M.Div(e0, e1)
                    case Mod => M.Mod(e0, e1)
                    case _ => M.Bot
                  }
                else M.Bot
            }
        else M.Bot
      case FunctionCallExpr(func, args) => 
        var args := seq(|args|, (i: nat) requires i < |args| => 
          SeqExprDepthLemma(args, args[i]);
          args[i].Eval(s));
        // if func.IsUninterpreted() then
          if func.ArgsCompatibleWith(args) then
            M.InterpFunctionOn(func.ToFunction(), args)
          else M.Bot
        // else if func.GetDef().IsDefinedOn(|args|) then
        //   func.EvalArgs(args)
        // else M.Bot
      case QuantifierExpr(true, v, typ, body) =>
        M.InterpBool(forall x: M.Any | M.HasType(x, typ.ToType()) :: 
          body.Eval(s.Update([x])) == M.True
        )
      case QuantifierExpr(false, v, typ, body) =>
        M.InterpBool(exists x: M.Any | M.HasType(x, typ.ToType()) :: 
          body.Eval(s.Update([x])) == M.True
        )
      case LetExpr(v, rhs, body) => 
        var x := rhs.Eval(s);
        body.Eval(s.Update([x]))
    }

    ghost predicate HoldsOn(s: State) 
      requires IsDefinedOn(|s|)
      // reads *
    {
      Eval(s) == M.True
    }

    // lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr, model: Model)
    //   requires e1.IsDefinedOn(s1, + 1)
    //   requires e2.IsDefinedOn(|s2| + 1)
    //   requires forall b: bool :: e1.Eval(s1.Update([BVal(b)])) == e2.Eval(s2.Update([BVal(b)]))
    //   ensures (forall b: bool :: SomeBVal?(e1.Eval(s1.Update([BVal(b)])))) == (forall b: bool :: SomeBVal?(e2.Eval(s2.Update([BVal(b)]))))
    // {  }

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures Eval(s1) == Eval(s2)
    { 
      match this
      case QuantifierExpr(true, v, tp, body) => 
      case QuantifierExpr(false, v, tp, body) => 
      case FunctionCallExpr(func, args) => 
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
    ensures Eq(e1, e2).Depth() == max(e1.Depth(), e2.Depth())
    ensures Eq(e1, e2).IsDefinedOn(|s|)
    ensures Eq(e1, e2).HoldsOn(s)
  { 
    SeqMaxPairLemma(e1, e2);
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
    M.BoolNotBot(M.True);
    assert M.IsBool(e0.Eval(s));
    assert M.IsBool(e1.Eval(s));
    calc {
      Implies(e0, e1).Eval(s);
      ==
      M.Implies(e0.Eval(s), e1.Eval(s));
      ==
      M.Implies(M.True, e1.Eval(s));
      ==
      M.InterpBool(true ==> M.ToBool(e1.Eval(s)));
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