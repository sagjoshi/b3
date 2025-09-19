module Context {
  import opened Defs

    function SeqDepthExpr(ss: seq<Expr>): Idx 
    {
      if ss == [] then 0 else max(ss[0].Depth(), SeqDepthExpr(ss[1..]))
    }


  function SeqMax(ss: seq<Idx>): Idx 
    ensures forall i <- ss :: i <= SeqMax(ss)
    ensures forall i: nat :: i < |ss| ==> ss[i] <= SeqMax(ss)
    ensures ss != [] ==> SeqMax(ss) in ss
  {
    if ss == [] then 
      0 
    else
      assert ss == [ss[0]] + (ss[1..]);
      max(ss[0], SeqMax(ss[1..]))
  }

  lemma MaxInsertLemma(ss: seq<Idx>, i: nat, x: Idx)
    requires forall s <- ss :: s < x
    requires i < |ss|
    ensures SeqMax(ss[i := x]) == x 
  {
    assert forall x :: x in ss[1..] ==> x in ss;
    assert ss[0] in ss;
    if ss != [] {
      if i != 0 {
        MaxInsertLemma(ss[1..], i - 1, x);
      }
    }
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
      MaxInsertLemma(incarnation, v, v');
      var ctx' := ctx + [Eq(BVar(v'), Substitute(e))];
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation');
      vNew := v';
    }

    function Delete(n: nat): Context
      requires n <= |incarnation|
    {
      Context(ctx, incarnation[n..])
    }
      

    function AddVars(n: nat): Context
      ensures incarnation <= AddVars(n).incarnation 
      ensures AddVars(n).ctx         == ctx
      ensures |AddVars(n).incarnation| == |incarnation| + n
    {
      var add_on := seq(n, (i: nat) => SeqMax(incarnation) + 1 + i);
      Context(ctx, incarnation + add_on)
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
      requires forall b: bool :: s1.Update([b]).Eval(e1) == s2.Update([b]).Eval(e2)
      ensures (forall b: bool :: s1.Update([b]).Eval(e1)) == (forall b: bool :: s2.Update([b]).Eval(e2))
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
          ((s[..i] + AdjustState(s[i..])).Update([b])).Eval(body) == 
          (s.Update([b])).Eval(SubstituteIdx(body, i + 1)) by {
          forall b: bool 
            ensures ((s[..i] + AdjustState(s[i..])).Update([b])).Eval(body) == (s.Update([b])).Eval(SubstituteIdx(body, i + 1)) {
            assert ([b] + s)[..i+1] == [b] + s[..i];
            assert ([b] + s)[i+1..] == s[i..];
            assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
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