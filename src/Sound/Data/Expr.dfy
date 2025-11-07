module Expr {
  import opened Utils
  import opened State
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

  datatype Expr =
    | BConst(bvalue: bool)
    | IConst(ivalue: int)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | BVar(id: Idx)
    | QuantifierExpr(univ: bool, v: Variable, tp: Type, body: Expr) 
  {
    function Depth(): Idx {
      match this
      case BConst(_) => 0
      case IConst(_) => 0
      case OperatorExpr(op, args) => SeqExprDepth(args)
      case BVar(id) => id + 1
      case QuantifierExpr(univ, v, tp, body) => if body.Depth() == 0 then 0 else body.Depth() - 1
    }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }

    lemma IsDefinedOnTransitivity(d1: Idx, d2: Idx)
        requires d1 <= d2
        ensures IsDefinedOn(d1) ==> IsDefinedOn(d2)
    {  }

    ghost function Eval(s: State): Option<Val> 
      requires IsDefinedOn(|s|)
    {
      match this
      case BConst(bvalue)  => Some(BVal(bvalue))
      case IConst(ivalue)  => Some(IVal(ivalue))
      case BVar(id) => Some(s[id])
      // ternary operators
      case OperatorExpr(op, ss) => 
        if op == IfThenElse then
          if |ss| != 3 then None
          else 
            var guard :- ss[0].Eval(s);
            var thn :- ss[1].Eval(s);
            var els :- ss[2].Eval(s);
            match guard {
              case BVal(true) => Some(thn)
              case BVal(false) => Some(els)
              case _ => None
            }
        else if op.IsUnaryOperator() then
          if |ss| != 1 then None
          else
            var e :- ss[0].Eval(s);
            match (e, op) {
              case (BVal(v), LogicalNot) => Some(BVal(!v))
              case (IVal(v), UnaryMinus) => Some(IVal(-v))
              case _ => None
            }
        else if op.IsBinaryOperator() then
          if |ss| != 2 then None
          else
            var e0 :- ss[0].Eval(s);
            var e1 :- ss[1].Eval(s);
            match (e0, e1, op) {
              case (BVal(v0), BVal(v1), Equiv) => Some(BVal(v0 == v1))
              case (BVal(v0), BVal(v1), LogicalImp) => Some(BVal(v0 ==> v1))
              case (BVal(v0), BVal(v1), LogicalAnd) => Some(BVal(v0 && v1))
              case (BVal(v0), BVal(v1), LogicalOr) => Some(BVal(v0 || v1))
              case (v0, v1, Eql) => Some(BVal(v0 == v1))
              case (v0, v1, Neql) => Some(BVal(v0 != v1))
              case (IVal(v0), IVal(v1), Less) => Some(BVal(v0 < v1))
              case (IVal(v0), IVal(v1), AtMost) => Some(BVal(v0 <= v1))
              case (IVal(v0), IVal(v1), Plus) => Some(IVal(v0 + v1))
              case (IVal(v0), IVal(v1), Minus) => Some(IVal(v0 - v1))
              case (IVal(v0), IVal(v1), Times) => Some(IVal(v0 * v1))
              case (IVal(v0), IVal(v1), Div) => Some(IVal(v0 / v1))
              case (IVal(v0), IVal(v1), Mod) => Some(IVal(v0 % v1))
              case _ => None
            }
        else None
      case QuantifierExpr(true, v, BType, body) =>
        Some(BVal(forall b: bool :: 
          SomeBValTrue?(body.Eval(s.Update([BVal(b)])))
        ))
      case QuantifierExpr(false, v, BType, body) =>
        Some(BVal(exists b: bool :: 
          SomeBValTrue?(body.Eval(s.Update([BVal(b)])))
        ))
      case QuantifierExpr(true, v, IType, body) =>
        Some(BVal(forall i: int :: 
          SomeBValTrue?(body.Eval(s.Update([IVal(i)])))
        ))
      case QuantifierExpr(false, v, IType, body) =>
        Some(BVal(exists i: int :: 
          SomeBValTrue?(body.Eval(s.Update([IVal(i)])))
        ))
    }

    ghost predicate HoldsOn(s: State) 
      requires IsDefinedOn(|s|)
    {
      Eval(s) == Some(BVal(true))
    }

    ghost predicate IsSafe() 
    {
      forall s: State :: IsDefinedOn(|s|) ==> Eval(s).Some? 
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr)
      requires e1.IsDefinedOn(|s1| + 1)
      requires e2.IsDefinedOn(|s2| + 1)
      requires forall b: bool :: e1.Eval(s1.Update([BVal(b)])) == e2.Eval(s2.Update([BVal(b)]))
      ensures (forall b: bool :: SomeBVal?(e1.Eval(s1.Update([BVal(b)])))) == (forall b: bool :: SomeBVal?(e2.Eval(s2.Update([BVal(b)]))))
    {  }

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures Eval(s1) == Eval(s2)
    { 
      match this
      case QuantifierExpr(true, v, tp, body) => 
      case QuantifierExpr(false, v, tp, body) => 
      case _ =>
    } 

    ghost predicate Holds() {
      forall s: State :: IsDefinedOn(|s|) ==> HoldsOn(s)
    }

    ghost function Sem(): iset<State> { iset st: State | IsDefinedOn(|st|) && HoldsOn(st) }
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
    requires e1.Eval(s).Some?
    requires e1.Eval(s) == e2.Eval(s)
    ensures Eq(e1, e2).Depth() == max(e1.Depth(), e2.Depth())
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
    }  
  }

}