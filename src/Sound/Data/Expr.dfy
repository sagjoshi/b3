module Expr {
  import opened Utils
  import opened State
    datatype Expr =
    | BConst(bvalue: bool)
    | And(0: Expr, 1: Expr)
    | Or(0: Expr, 1: Expr)
    | Not(e: Expr)
    | Implies(0: Expr, 1: Expr)
    | BVar(id: Idx)
    | Forall(v: Variable, body: Expr) 
  {
    function Depth(): Idx {
      match this
      case BConst(_) => 0
      case And(e0, e1) => max(e0.Depth(), e1.Depth())
      case Or(e0, e1) => max(e0.Depth(), e1.Depth())
      case Not(e) => e.Depth()
      case Implies(e0, e1) => max(e0.Depth(), e1.Depth())
      case BVar(id) => id + 1
      case Forall(v, body) => if body.Depth() == 0 then 0 else body.Depth() - 1
    }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }

    lemma IsDefinedOnTransitivity(d1: Idx, d2: Idx)
        requires d1 <= d2
        ensures IsDefinedOn(d1) ==> IsDefinedOn(d2)
    {  }

    function Eval(s: State): Value 
      requires IsDefinedOn(|s|)
    {
      match this
      case BConst(bvalue)  => bvalue
      case And(e0, e1)     => e0.Eval(s) && e1.Eval(s)
      case Or(e0, e1)      => e0.Eval(s) || e1.Eval(s)
      case Not(e)          => !e.Eval(s)
      case Implies(e0, e1) => e0.Eval(s) ==> e1.Eval(s)
      case Forall(v, body) => forall x: bool :: body.Eval(s.Update([x]))
      case BVar(v)         => s[v]
    }

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures Eval(s1) == Eval(s2)

    { 
      match this
      case Forall(v, body) => 
        forall x: bool { 
          body.EvalDepthLemma(s1.Update([x]), s2.Update([x])); 
        }
      case _ =>
    } 

    ghost predicate Holds() {
      forall s: State :: IsDefinedOn(|s|) ==> Eval(s)
    }

    ghost function Sem(): iset<State> { iset st: State | IsDefinedOn(|st|) && Eval(st) }
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    And(Implies(e1, e2), Implies(e2, e1))
  }

  lemma DepthEqLemma(e1: Expr, e2: Expr)
    ensures Eq(e1, e2).Depth() == max(e1.Depth(), e2.Depth())
  {  }

  lemma EvalEqLemma(e1: Expr, e2: Expr, s: State)
    requires e1.IsDefinedOn(|s|)
    requires e2.IsDefinedOn(|s|)
    requires e1.Eval(s) == e2.Eval(s)
    ensures Eq(e1, e2).Eval(s) == true
  {  }

  function SeqExprDepth(ss: seq<Expr>): nat {
    if ss == [] then 0 else max(ss[0].Depth(), SeqExprDepth(ss[1..]))
  }

  lemma SeqExprDepthLemma(ss: seq<Expr>, s: Expr) 
    requires s in ss
    ensures s.Depth() <= SeqExprDepth(ss)
  {  }

    lemma IsDefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|) 
    requires e1.IsDefinedOn(|s|)
    ensures And(e0, e1).IsDefinedOn(|s|) 
  {  }

  function Conj(ctx: seq<Expr>): Expr 
  {
    if ctx == [] then BConst(true) else And(ctx[0], Conj(ctx[1..]))
  }

  lemma ConjDepthMonotonicity(ctx1: seq<Expr>, ctx2: seq<Expr>)
    requires ctx1 <= ctx2
    ensures Conj(ctx1).Depth() <= Conj(ctx2).Depth()
  {  }

  lemma DepthConjUnionLemma(ctx1: seq<Expr>, ctx2: seq<Expr>)
    ensures Conj(ctx1 + ctx2).Depth() == max(Conj(ctx1).Depth(), Conj(ctx2).Depth())
  {
    if ctx1 == [] {
      assert [] + ctx2 == ctx2;
    } else {
      assert ctx1 + ctx2 == [ctx1[0]] + (ctx1[1..] + ctx2);
    }
  }

  lemma IsDefinedOnConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.IsDefinedOn(|s|)
    ensures Conj(ctx).IsDefinedOn(|s|)
  {
    if ctx != [] { 
      IsDefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); 
    } 
  }

  lemma EvalConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.IsDefinedOn(|s|)
    requires forall e <- ctx :: e.Eval(s)
    ensures Conj(ctx).IsDefinedOn(|s|)
    ensures Conj(ctx).Eval(s)
  { IsDefinedOnConjLemma(ctx, s); }

}