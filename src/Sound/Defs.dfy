module Defs { 

  function Tail(ss: State): State {
    if ss == [] then [] else ss[1..]
  }

  ghost function UpdateSet(post: iset<State>): iset<State> 
  {
    iset st: State | Tail(st) in post 
  }

  ghost function DeleteSet(post: iset<State>): iset<State> {
    iset st: State | exists st' <- post :: st == Tail(st')
  }

  function max(x: nat, y: nat): nat {
    if x > y then x else y
  }

  ghost const AllStates: iset<State> := iset st: State | true

  datatype Except<+T> =
    | Ok(res: T)
    | Error
  {
    predicate IsFailure() {
      Error?
    }
    function PropagateFailure<U>(): Except<U>
      requires IsFailure()
    {
      Error
    }
    function Extract() : T 
      requires !IsFailure()
    {
      res
    }
  }
  type Variable = string
  type Idx = nat

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

    ghost predicate Holds() {
      forall s: State :: IsDefinedOn(|s|) ==> s.Eval(this)
    }

    // lemma IsDefinedOnFVarsLemma(s: State, v: Variable)
    //   requires v !in FVars()
    //   ensures IsDefinedOn(s.Keys + {v}) ==> IsDefinedOn(s.Keys)
    // {  }

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures s1.Eval(this) == s2.Eval(this)

    { 
      match this
      case Forall(v, body) => 
        forall x: bool { 
          body.EvalDepthLemma(s1.Update(x), s2.Update(x)); 
        }
      case _ =>
    }

    function ShiftFVars(i: Idx): Expr {
      match this
      case Forall(v, body) => Forall(v, body.ShiftFVars(i + 1))
      case BVar(v) => if v >= i then BVar(v + 1) else BVar(v)
      case And(e0, e1) => And(e0.ShiftFVars(i), e1.ShiftFVars(i))
      case Or(e0, e1) => Or(e0.ShiftFVars(i), e1.ShiftFVars(i))
      case Not(e) => Not(e.ShiftFVars(i))
      case Implies(e0, e1) => Implies(e0.ShiftFVars(i), e1.ShiftFVars(i))
      case _ => this
    }

    // lemma ShiftFVarsDepthLemma(i: Idx)
    //   ensures ShiftFVars(i).Depth() == Depth() + i
    // {
    //   match this 
    //   case Forall(v, body) => body.ShiftFVarsDepthLemma(i + 1);
    //   case BVar(v) => 
    //   if v >= i {

    //   } else {
    //   }
    //   case _ =>
    // }
      
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
    requires s.Eval(e1) == s.Eval(e2)
    ensures s.Eval(Eq(e1, e2))
  {  }
    
  datatype Stmt =
    | Check(e: Expr)
    | Assume(e: Expr)
    | Seq(ss: seq<Stmt>)
    | Assign(lhs: Idx, rhs: Expr)
    | VarDecl(v: Variable, s: Stmt)
    // | Loop(inv: Expr, body: Stmt)
    // | While(guard: Expr, inv: Expr, body: Stmt)
    | Choice(0: Stmt, 1: Stmt)
  {
    function Size(): nat {
      match this
      case Check(_) => 1
      case Assume(_) => 1
      case Seq(ss) => 1 + SeqSize(ss)
      case Assign(_, _) => 1
      case Choice(s0, s1) => 1 + s0.Size() + s1.Size()
      case VarDecl(_, s) => 1 + s.Size()
    }

    function Depth(): Idx {
      match this
      case Check(e) => e.Depth()
      case Assume(e) => e.Depth()
      case Seq(ss) => SeqDepth(ss)
      case Assign(id, rhs) => max(id + 1, rhs.Depth())
      case VarDecl(_, s) => if s.Depth() == 0 then 0 else s.Depth() - 1
      case Choice(s0, s1) => max(s0.Depth(), s1.Depth())
    }

    function ShiftFVars(i: Idx): Stmt {
      match this
      case Check(e) => Check(e.ShiftFVars(i))
      case Assume(e) => Assume(e.ShiftFVars(i))
      case Seq(ss) => Seq(SeqShiftFVars(ss, i))
      case Assign(id, rhs) =>
        if id >= i then 
          Assign(id + 1, rhs.ShiftFVars(i)) 
        else Assign(id, rhs.ShiftFVars(i))
      case VarDecl(v, s) => VarDecl(v, s.ShiftFVars(i + 1))
      case Choice(s0, s1) => Choice(s0.ShiftFVars(i), s1.ShiftFVars(i))
    }

    lemma ShiftFVarsSizeLemma(i: Idx)
      ensures ShiftFVars(i).Size() == Size()
    {
      match this 
      case Seq(ss) => SeqShiftFVarsSizeLemma(ss, i);
      case _ =>
    }

    // lemma ShiftFVarsDepthLemma(i: Idx)
    //   ensures ShiftFVars(i).Depth() == Depth() + i
    // {
    //   match this 
    //   case Seq(ss) => SeqShiftFVarsDepthLemma(ss, i);
    //   case _ =>
    // }

    // function FVars(): set<Variable> {
    //   match this
    //   case Check(e) => e.FVars()
    //   case Assume(e) => e.FVars()
    //   case Seq(ss) => SeqFVars(ss)
    //   case Assign(lhs, rhs) => {lhs} + rhs.FVars()
    //   case VarDecl(v, s) => s.FVars() - {v}
    //   case Choice(s0, s1) => s0.FVars() + s1.FVars()
    // }

    // function BVars(): set<Variable> {
    //   match this
    //   case Check(e) => e.BVars()
    //   case Assume(e) => e.BVars()
    //   case Seq(ss) => SeqBVars(ss)
    //   case Assign(lhs, rhs) => rhs.BVars()
    //   case VarDecl(v, s) => s.BVars() + {v}
    //   case Choice(s0, s1) => s0.BVars() + s1.BVars()
    // }

    // predicate NoShadowing() {
    //   match this
    //   case Check(e) => e.NoShadowing()
    //   case Assume(e) => e.NoShadowing()
    //   case Seq(ss) => SeqNoShadowing(ss, this)
    //     // && SeqNoShadowingNested(ss)
    //     // && (forall i, j :: 0 <= i < j < |ss| ==> ss[i].BVars() !* ss[j].BVars())
    //   case Assign(lhs, rhs) => rhs.NoShadowing()
    //   case VarDecl(v, s) => v !in s.BVars() && s.NoShadowing()
    //   case Choice(s0, s1) => s0.NoShadowing() && s1.NoShadowing()
    // }

    // predicate WellFormed() {
    //   NoShadowing() && FVars() !! BVars()
    // }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }
    lemma IsDefinedOnTransitivity(d1: Idx, d2: Idx)
      requires d1 <= d2
      ensures IsDefinedOn(d1) ==> IsDefinedOn(d2)
    {  }

    predicate Single() {
      match this
      case Assign(_, _) => true
      case Check(_) => true
      case Assume(_) => true
      case _ => false
    }
  }

  function SeqSize(ss: seq<Stmt>): nat {
    if ss == [] then 0 else ss[0].Size() + SeqSize(ss[1..])
  }

  lemma SeqSizeSplitLemma(ss: seq<Stmt>)
    requires ss != []
    ensures SeqSize(ss) == ss[0].Size() + SeqSize(ss[1..])
  {  }

  function SeqDepth(ss: seq<Stmt>): nat {
    if ss == [] then 0 else max(ss[0].Depth(), SeqDepth(ss[1..]))
  }

  function SeqShiftFVars(ss: seq<Stmt>, i: Idx): seq<Stmt> {
    if ss == [] then [] else [ss[0].ShiftFVars(i)] + SeqShiftFVars(ss[1..], i)
  }

  lemma SeqShiftFVarsSizeLemma(ss: seq<Stmt>, i: Idx)
    ensures SeqSize(SeqShiftFVars(ss, i)) == SeqSize(ss)
  {
    if ss != [] {
      assert ss == [ss[0]] + (ss[1..]);
      ss[0].ShiftFVarsSizeLemma(i);
    }
  }

  // lemma SeqShiftFVarsDepthLemma(ss: seq<Stmt>, i: Idx)
  //   ensures SeqDepth(SeqShiftFVars(ss, i)) == SeqDepth(ss) + i
  // {
  //   if ss != [] {
  //     assert ss == [ss[0]] + (ss[1..]);
  //     ss[0].ShiftFVarsDepthLemma(i);
  //   }
  // }

  // function SeqFVars(ss: seq<Stmt>): set<Variable> 
  //   decreases ss
  // {
  //   if ss == [] then {} else ss[0].FVars() + SeqFVars(ss[1..])
  // }

  // function SeqBVars(ss: seq<Stmt>): set<Variable> {
  //   if ss == [] then {} else ss[0].BVars() + SeqBVars(ss[1..])
  // }

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

  predicate SeqIsDefinedOn(ss: seq<Stmt>, d: nat) 
    ensures SeqIsDefinedOn(ss, d) <==> SeqDepth(ss) <= d
  {
    if ss == [] then true else ss[0].IsDefinedOn(d) && SeqIsDefinedOn(ss[1..], d)
  }

  lemma IsDefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(|s|) 
    requires e1.IsDefinedOn(|s|)
    ensures And(e0, e1).IsDefinedOn(|s|) 
  {  }

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
    requires forall e <- ctx :: s.Eval(e)
    ensures Conj(ctx).IsDefinedOn(|s|)
    ensures s.Eval(Conj(ctx))
  { IsDefinedOnConjLemma(ctx, s); }

  // predicate SeqNoShadowingNested(ss: seq<Stmt>, ghost parent: Stmt := Seq(ss)) 
  //   requires forall s <- ss :: s < parent
  //   decreases parent, |ss|
  // {
  //   forall s <- ss :: s.NoShadowing()
  // }

  // predicate SeqNoShadowing(ss: seq<Stmt>, ghost parent: Stmt := Seq(ss)) 
  //   requires forall s <- ss :: s < parent
  //   decreases parent, |ss| + 1
  // {
  //   && SeqNoShadowingNested(ss, parent)
  //   && (forall i, j :: 0 <= i < j < |ss| ==> ss[i].BVars() !! ss[j].BVars())
  // }

  // predicate SeqWellFormed(ss: seq<Stmt>) {
  //   if ss == [] then 
  //     true 
  //   else 
  //     && ss[0].WellFormed()
  //     && ss[0].BVars() !! SeqFVars(ss[1..]) 
  //     && ss[0].BVars() !! SeqBVars(ss[1..])
  //     && SeqWellFormed(ss[1..])
  // }

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqDepth(ss1 + ss2) == max(SeqDepth(ss1), SeqDepth(ss2))
  {
    if ss1 == [] {
      assert ss1 + ss2 == ss2;
    } else {
      assert (ss1 + ss2)[0] == ss1[0];
      assert (ss1 + ss2)[1..] == ss1[1..] + ss2;
    }
  }

  type Value = bool

  newtype State = seq<Value> {
    
    function Eval(e: Expr): Value 
      requires e.IsDefinedOn(|this|)
      decreases e
    {
      match e
      case BConst(bvalue)  => bvalue
      case And(e0, e1)     => Eval(e0) && Eval(e1)
      case Or(e0, e1)      => Eval(e0) || Eval(e1)
      case Not(e)          => !Eval(e)
      case Implies(e0, e1) => Eval(e0) ==> Eval(e1)
      case Forall(v, body) => forall x: bool :: Update(x).Eval(body)
      case BVar(v)         => this[v]
    }
    function Update(val: Value): State {
      [val] + this
    }
  }
}

