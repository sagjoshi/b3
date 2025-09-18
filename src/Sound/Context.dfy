module Context {
  import opened Defs

    function SeqDepthExpr(ss: seq<Expr>): Idx 
    {
      if ss == [] then 0 else max(ss[0].Depth(), SeqDepthExpr(ss[1..]))
    }


  function SeqMax(ss: seq<Idx>): Idx 
    ensures forall i <- ss :: i <= SeqMax(ss)
    ensures forall i: nat :: i < |ss| ==> ss[i] <= SeqMax(ss)
  {
    if ss == [] then 
      0 
    else
      assert ss == [ss[0]] + (ss[1..]);
      max(ss[0], SeqMax(ss[1..]))
  }

  datatype Context = Context(
    ctx: seq<Expr>,
    incarnation: seq<nat>) 
  {
    ghost const Models : iset<State> := iset st: State | IsSatisfiedOn(st)

    ghost const AdjustedModels : iset<State> := 
      iset st: State | exists st' <- Models {:InAdjustedModelsLemma(st')} :: AdjustState(st') == st

    lemma InAdjustedModelsLemma(st: State, st': State)
      requires IsSatisfiedOn(st')
      requires st == AdjustState(st')
      ensures st in AdjustedModels
    {

    }

    function Depth(): Idx 
    {
      max(SeqDepthExpr(ctx), SeqMax(incarnation))
    }

    function FreshIdx(): Idx
      ensures forall i <- incarnation :: i < FreshIdx()
    {
      SeqMax(incarnation) + 1
    }

    

    function AdjustState(s: State): State
      requires forall i <- incarnation :: i < |s|
    { 
      // Q: how to get rid of `if`?
      seq(|incarnation|, (i: nat) requires i < |incarnation| => 
        assert incarnation[i] in incarnation;
        s[incarnation[i]])
    }

    function SubstituteIdx(e: Expr, i: Idx): Expr
      requires e.IsDefinedOn(|incarnation| + i)
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case BVar(v) =>
        if v >= i then  
          BVar(incarnation[v - i] + i) 
        else e
      case And(e0, e1) => 
        And(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Or(e0, e1) => 
        Or(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Not(e) => 
        Not(SubstituteIdx(e, i))
      case Implies(e0, e1) => 
        Implies(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Forall(v, body) => 
        Forall(v, SubstituteIdx(body, i + 1))
    }

    function Substitute(e: Expr): Expr
      requires e.IsDefinedOn(|incarnation|)
    {
      SubstituteIdx(e, 0)
    }

    function MkEntailment(e: Expr): Expr
      requires e.IsDefinedOn(|incarnation|)
    {
      Implies(Conj(ctx), Substitute(e))
    }

    function Add(e: Expr): Context
      requires e.IsDefinedOn(|incarnation|)
    {
      this.(ctx := ctx + [Substitute(e)])
    }

    method AddEq(v: Idx, e: Expr) returns (ghost vNew: Idx, context: Context)
      requires v < |incarnation|
      requires e.IsDefinedOn(|incarnation|)
      ensures |incarnation| == |context.incarnation|
      ensures ctx + [Eq(BVar(vNew), Substitute(e))] == context.ctx
      ensures incarnation[v := vNew] == context.incarnation
      ensures forall i <- incarnation :: i < vNew 
      ensures vNew == SeqMax(incarnation) + 1
      ensures SeqMax(incarnation) + 1 == SeqMax(context.incarnation)
    {
      var v' := FreshIdx();
      var ctx' := ctx + [Eq(BVar(v'), Substitute(e))];
      // FVarsEqLemma(Var(v'), Substitute(e));
      // FVarsConjUnionLemma(ctx, [Eq(Var(v'), Substitute(e))]);
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation');
      vNew := v';
    }

    method AddVar() returns (ghost vNew: Idx, context: Context)
      ensures context.incarnation == [vNew] + incarnation
      ensures context.ctx         == ctx

      ensures forall i <- incarnation :: i < vNew 
      ensures vNew == SeqMax(incarnation) + 1
      ensures SeqMax(incarnation) + 1 == SeqMax(context.incarnation)
    {
      var v' := FreshIdx();
      var incarnation' :=  [v'] + incarnation;
      context := Context(ctx, incarnation');
      vNew := v';
    }

    ghost predicate IsDefinedOn(d: Idx)
    {
      forall e <- ctx :: e.IsDefinedOn(d)
    }

    ghost predicate IsSatisfiedOn(s: State) 
    {
      && IsDefinedOn(|s|) 
      && (|s| == SeqMax(incarnation) + 1)
      && (forall i <- incarnation :: i < |s|)
      && (forall e <- ctx :: s.Eval(e))
    }

    ghost predicate Entails(e: Expr) 
    {
      forall s: State ::  
        e.IsDefinedOn(|s|) && IsSatisfiedOn(s) ==> s.Eval(e)
    }

    lemma SubstituteIdxIsDefinedOnLemma(e: Expr, i: Idx, d: Idx)
      requires e.IsDefinedOn(|incarnation| + i)
      requires forall ic <- incarnation :: ic + i < d
      requires i <= d
      ensures SubstituteIdx(e, i).IsDefinedOn(d)
      decreases e
    {
      match e 
      case BVar(v) => if v >= i { assert incarnation[v - i] in incarnation; }
      case Forall(v, body) => SubstituteIdxIsDefinedOnLemma(body, i + 1, d + 1);
      case _ =>
    }

    lemma SubstituteIsDefinedOnLemma(e: Expr, d: Idx)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < d
      ensures Substitute(e).IsDefinedOn(d)
      decreases e
    {
      SubstituteIdxIsDefinedOnLemma(e, 0, d);
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr)
      requires e1.IsDefinedOn(|s1| + 1)
      requires e2.IsDefinedOn(|s2| + 1)
      requires forall b: bool :: s1.Update(b).Eval(e1) == s2.Update(b).Eval(e2)
      ensures (forall b: bool :: s1.Update(b).Eval(e1)) == (forall b: bool :: s2.Update(b).Eval(e2))
    {  }

    lemma AdjustStateSubstituteIdxLemma(s: State, e: Expr, i: Idx)
      requires e.IsDefinedOn(|incarnation| + i)
      requires forall ic <- incarnation :: ic + i < |s|
      requires i <= |s|
      ensures (SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        (s[..i] + AdjustState(s[i..])).Eval(e)) == s.Eval(SubstituteIdx(e, i))
      decreases e
    {
      match e 
      case Forall(v, body) =>
        SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        assert forall b: bool :: 
          ((s[..i] + AdjustState(s[i..])).Update(b)).Eval(body) == 
          (s.Update(b)).Eval(SubstituteIdx(body, i + 1)) by {
          forall b: bool 
            ensures ((s[..i] + AdjustState(s[i..])).Update(b)).Eval(body) == (s.Update(b)).Eval(SubstituteIdx(body, i + 1)) {
            assert ([b] + s)[..i+1] == [b] + s[..i];
            assert ([b] + s)[i+1..] == s[i..];
            assert ((s[..i] + AdjustState(s[i..])).Update(b)) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
            AdjustStateSubstituteIdxLemma([b] + s, body, i + 1);
          }
        }
        ForallPush(s[..i] + AdjustState(s[i..]), s, body, SubstituteIdx(body, i + 1));
      case BVar(v) => if v >= i { assert incarnation[v - i] in incarnation; }
      case _  => 
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < |s|
      ensures Substitute(e).IsDefinedOn(|s|)
      ensures AdjustState(s).Eval(e) == s.Eval(Substitute(e))
    {
      SubstituteIsDefinedOnLemma(e, |s|);
      AdjustStateSubstituteIdxLemma(s, e, 0);
      assert [] + AdjustState(s) == AdjustState(s);
    }

  }
}

  /*datatype Context = Context(P
    ctx: seq<Expr>, 
    incarnation: seq<Variable>,
    bVars: set<Variable>) 
  {

    /*ghost const Models : iset<State> := iset st: State | IsSatisfiedOn(st)
    // Q: is it correct way to set a trigger?
    ghost const AdjustedModels : iset<State> := 
      iset st: State | exists st' <- Models {:InAdjustedModelsLemma(st')} :: AdjustState(st') == st

    lemma InAdjustedModelsLemma(st: State, st': State)
      requires IsSatisfiedOn(st')
      requires st == AdjustState(st')
      ensures st in AdjustedModels
    {

    }

    function CtxFVars(): set<Variable> 
      ensures CtxFVars() == Conj(ctx).FVars()
      ensures forall e <- ctx :: e.FVars() <= CtxFVars()
      decreases ctx
    {
      if ctx == [] then {} else ctx[0].FVars() + Context(ctx[1..], incarnation, bVars).CtxFVars()
    }

    function FVars(): set<Variable> 
    {
      CtxFVars() + incarnation.Values
    }

    ghost predicate Valid() 
    {
      forall b <- bVars :: b !in incarnation.Values
    }

    function FreshVar(): Variable
      ensures {:axiom} FreshVar() !in incarnation.Keys
      ensures {:axiom} FreshVar() !in bVars
      ensures {:axiom} FreshVar() !in FVars()


    function AdjustState(s: State): State
      requires incarnation.Values <= s.Keys
    { 
      map x: Variable | x in incarnation.Keys :: s[incarnation[x]] 
    }

    function Substitute(e: Expr): Expr 
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case Var(v) =>
        if v in incarnation then  
          Var(incarnation[v]) 
        else e
      case And(e0, e1) => 
        And(Substitute(e0), Substitute(e1))
      case Or(e0, e1) => 
        Or(Substitute(e0), Substitute(e1))
      case Not(e) => 
        Not(Substitute(e))
      case Implies(e0, e1) => 
        Implies(Substitute(e0), Substitute(e1))
      case Forall(v, body) => 
        Forall(v, Context(ctx, incarnation[v := v], bVars).Substitute(body))
    }

    function MkEntailment(e: Expr): Expr 
    {
      Implies(Conj(ctx), Substitute(e))
    }


    function Add(e: Expr): Context
      requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      ensures Add(e).Valid()
    {
      ghost var ctx' := ctx;
      var ctx := ctx + [Substitute(e)];
      FVarsConjUnionLemma(ctx', [Substitute(e)]);
      Context(ctx, incarnation, bVars)
    }

    method AddEq(v: Variable, e: Expr) returns (ghost vNew: Variable, context: Context)
      requires v in incarnation.Keys
      requires Valid()
      ensures context.Valid()
      ensures incarnation.Keys == context.incarnation.Keys
      ensures ctx + [Eq(Var(vNew), Substitute(e))] == context.ctx
      ensures incarnation[v := vNew] == context.incarnation
      ensures bVars == context.bVars
      ensures vNew !in incarnation.Keys
      ensures vNew !in bVars
      ensures vNew !in FVars()
    {
      var v' := FreshVar();
      var ctx' := ctx + [Eq(Var(v'), Substitute(e))];
      FVarsEqLemma(Var(v'), Substitute(e));
      FVarsConjUnionLemma(ctx, [Eq(Var(v'), Substitute(e))]);
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation', bVars);
      vNew := v';
    }
    
    method AddVar(v: Variable) returns (ghost vNew: Variable, context: Context)
      requires Valid()
      ensures context.Valid()

      ensures context.incarnation == incarnation[v := vNew]
      ensures context.ctx         == ctx
      ensures context.bVars       == bVars

      ensures vNew !in incarnation.Keys
      ensures vNew !in bVars
      ensures vNew !in FVars()
    {
      var v' := FreshVar();
      var incarnation' := incarnation[v := v'];
      context := Context(ctx, incarnation', bVars);
      vNew := v';
    }
    
    ghost predicate IsDefinedOn(s: set<Variable>) 
    {
      FVars() <= s
    }

    lemma FVarsLemma(s: set<Variable>)
      requires IsDefinedOn(s)
      ensures forall e <- ctx :: e.IsDefinedOn(s)
    {  }

    ghost predicate IsSatisfiedOn(s: State) 
    {
      && IsDefinedOn(s.Keys) 
      && incarnation.Values <= s.Keys
      && forall e <- ctx :: s.Eval(e)
    }

    ghost predicate Entails(e: Expr) 
    {
      forall s: State ::  
        e.IsDefinedOn(s.Keys) && IsSatisfiedOn(s) ==> s.Eval(e)
    }

    lemma SubstituteIsDefinedOnLemma(e: Expr)
      requires e.IsDefinedOn(incarnation.Keys)
      ensures Substitute(e).IsDefinedOn(incarnation.Values)
      decreases e
    {
      assert e.FVars() <= incarnation.Keys;
      match e 
      case Forall(v, body) => Context(ctx, incarnation[v := v], bVars).SubstituteIsDefinedOnLemma(body);
      case _ => 
    }


    lemma AdjustStateSubstituteLemma'(s: State, e: Expr)
      requires forall b <- e.BVars(), x <- incarnation.Keys :: incarnation[x] == b ==> x == b
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= s.Keys
      ensures Substitute(e).IsDefinedOn(s.Keys)
      ensures (
        SubstituteIsDefinedOnLemma(e); 
        AdjustState(s).Eval(e) == s.Eval(Substitute(e)))
      decreases e
    {
      match e 
      case Forall(v, body) => 
        var ctx' := Context(ctx, incarnation[v := v], bVars);
        SubstituteIsDefinedOnLemma(Forall(v, body)); 
        assert forall b: bool :: 
          AdjustState(s).Update(v, b).Eval(body) == 
          s.Update(v, b).Eval(ctx'.Substitute(body)) by 
        {
          forall b: bool 
            ensures AdjustState(s).Update(v, b).Eval(body) == 
              s.Update(v, b).Eval(ctx'.Substitute(body)) 
            {
              assert AdjustState(s)[v:=b] == ctx'.AdjustState(s[v:=b]) by {
                assert AdjustState(s)[v:=b].Keys == ctx'.AdjustState(s[v:=b]).Keys;
                forall x: Variable {:trigger} | x in AdjustState(s)[v:=b].Keys
                  ensures AdjustState(s)[v:=b][x] == ctx'.AdjustState(s[v:=b])[x] {
                  if x != v {
                    if incarnation[x] == v {
                      assert v in e.BVars();
                    }
                  }
                }
              }
              assert forall b <- body.BVars() {:trigger}, x <- incarnation[v:=v].Keys :: 
                incarnation[v:=v][x] == b ==> x == b by 
              {
                forall b <- body.BVars() {:trigger}, x <- incarnation[v:=v].Keys
                ensures incarnation[v:=v][x] == b ==> x == b {
                  if x != v {
                    assert e.BVars() == body.BVars() + {v};
                  }
                }
              }
              ctx'.AdjustStateSubstituteLemma'(s.Update(v, b), body);
            }
        }
      case Var(v) =>
      case BConst(bvalue) =>
      case Not(ne) => 
        assert ne.BVars() == e.BVars();
      case And(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
      case Or(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
      case Implies(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr)
      requires e.BVars() <= bVars
      requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      requires IsDefinedOn(s.Keys)
      ensures Substitute(e).IsDefinedOn(s.Keys)
      ensures (
        SubstituteIsDefinedOnLemma(e); 
        AdjustState(s).Eval(e) == s.Eval(Substitute(e)))
    { AdjustStateSubstituteLemma'(s, e); }*/
  }

}*/