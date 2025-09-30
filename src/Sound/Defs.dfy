module Defs { 

  function Max(s: set<nat>): (m: nat)
    requires s != {}
    ensures m in s && forall z :: z in s ==> z <= m
  {
    var x :| x in s;
    if s == {x} then
      x
    else
      var s' := s - {x};
      assert s == s' + {x};
      var y := Max(s');
      max(x, y)
  } by method {
    m :| m in s;
    var r := s - {m};
    while r != {}
      invariant r < s
      invariant m in s && forall z :: z in s - r ==> z <= m
    {
      var x :| x in r;
      assert forall z :: z in s - (r - {x}) ==> z in s - r || z == x;
      r := r - {x};
      if m < x {
        m := x;
      }
    }
    assert s - {} == s;
  }

  function Max'(s: set<nat>): (m: nat)
    ensures (s == {} || m in s) && forall z :: z in s ==> z <= m
  {
    if s == {} then 0 else Max(s)
  }

  lemma MaxLemma(s: set<Idx>, i: Idx, m: Idx)
    requires i + m in s
    ensures i <= Max(s) - m
  {
    if s != {} {
      var x :| x in s;
    }
  }

  function Tail(n: nat, ss: State): State {
    if |ss| <= n then [] else ss[n..]
  }

  function SeqTail<T>(n: nat, ss: seq<T>): seq<T> {
    if |ss| <= n then [] else ss[n..]
  }

  ghost function UpdateSet(n: nat, post: iset<State>): iset<State> 
  {
    iset st: State | Tail(n, st) in post 
  }

  ghost function DeleteSet(n: nat, post: iset<State>): iset<State> {
    iset st: State {:trigger} | exists st' <- post :: st == Tail(n, st')
  }

  function max(x: nat, y: nat): nat {
    if x > y then x else y
  }
  function min(x: nat, y: nat): nat {
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

    ghost function Sem(): iset<State> { iset st: State | IsDefinedOn(|st|) && st.Eval(this) }

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

    lemma EvalDepthLemma(s1: State, s2: State) 
      requires IsDefinedOn(|s1|)
      requires IsDefinedOn(|s2|)
      requires forall i: Idx :: i < Depth() ==> s1[i] == s2[i]
      ensures s1.Eval(this) == s2.Eval(this)

    { 
      match this
      case Forall(v, body) => 
        forall x: bool { 
          body.EvalDepthLemma(s1.Update([x]), s2.Update([x])); 
        }
      case _ =>
    } 
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
    | NewScope(n: nat, s: Stmt)
    | Escape(l: nat)
    | Choice(0: Stmt, 1: Stmt)
    | Loop(inv: Expr, body: Stmt)
  {
    function Size(): nat {
      match this
      case Check(_) => 1
      case Assume(_) => 1
      case Seq(ss) => 1 + SeqSize(ss)
      case Assign(_, _) => 1
      case Choice(s0, s1) => 1 + s0.Size() + s1.Size()
      case NewScope(n, s) => 2 + s.Size()
      case Escape(l) => 2
      case Loop(inv, body) => 4 + body.Size()
    }

    function Depth(): Idx {
      match this
      case Check(e) => e.Depth()
      case Assume(e) => e.Depth()
      case Seq(ss) => SeqDepth(ss)
      case Assign(id, rhs) => max(id + 1, rhs.Depth())
      case Choice(s0, s1) => max(s0.Depth(), s1.Depth())
      case NewScope(n, s) => if s.Depth() <= n then 0 else s.Depth() - n
      case Escape(l) => 0
      case Loop(inv, body) => max(inv.Depth(), body.Depth())
    }

    function JumpDepth() : Idx {
      match this
      case Check(e) => 0
      case Assume(e) => 0
      case Assign(id, rhs) => 0
      case Seq(ss) => SeqJumpDepth(ss)
      case Choice(s0, s1) => max(s0.JumpDepth(), s1.JumpDepth())
      case NewScope(n, s) => if s.JumpDepth() == 0 then 0 else s.JumpDepth() - 1
      case Escape(l) => l
      case Loop(inv, body) => body.JumpDepth()
    }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }

    predicate JumpsDefinedOn(d: Idx) {
      JumpDepth() <= d
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

  function SeqJumpDepth(ss: seq<Stmt>): nat {
    if ss == [] then 0 else max(ss[0].JumpDepth(), SeqJumpDepth(ss[1..]))
  }

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

  predicate SeqJumpsDefinedOn(ss: seq<Stmt>, d: nat) 
    ensures SeqJumpsDefinedOn(ss, d) <==> SeqJumpDepth(ss) <= d
  {
    if ss == [] then true else ss[0].JumpsDefinedOn(d) && SeqJumpsDefinedOn(ss[1..], d)
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

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqDepth(ss1 + ss2) == max(SeqDepth(ss1), SeqDepth(ss2))
    ensures SeqJumpDepth(ss1 + ss2) == max(SeqJumpDepth(ss1), SeqJumpDepth(ss2))
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
      case Forall(v, body) => forall x: bool :: Update([x]).Eval(body)
      case BVar(v)         => this[v]
    }


    function Update(vals: State): State {
      vals + this
    }

    function UpdateMapShift(i: Idx, vals: map<Idx, Value>): State  
      ensures |UpdateMapShift(i, vals)| > i
      ensures |UpdateMapShift(i, vals)| >= |this|
      ensures forall v <- vals.Keys :: |UpdateMapShift(i, vals)| > v + i
      ensures |UpdateMapShift(i, vals)| > Max'(vals.Keys) + i
      ensures forall j: Idx :: j < |this| && (j < i || j - i !in vals.Keys) ==> UpdateMapShift(i, vals)[j] == this[j]
      ensures forall j: Idx :: j in vals.Keys ==> UpdateMapShift(i, vals)[j + i] == vals[j]
    {
      var m := Max'(vals.Keys);
      seq(max(i + m + 1, |this|), (j: nat) requires j < max(i + m + 1, |this|) => 
        if j - i in vals.Keys then 
          vals[j - i] 
        else if j < |this| then
          this[j]
        else false
      )
    }

    function UpdateOrAdd(i: Idx, val: Value): State 
      ensures |UpdateOrAdd(i, val)| > i
      ensures |UpdateOrAdd(i, val)| >= |this|
      ensures forall j: Idx :: j < |this| ==> j != i ==> UpdateOrAdd(i, val)[j] == this[j]
      ensures UpdateOrAdd(i, val)[i] == val
    {
      UpdateMapShift(i, map[0 := val])
    }

    function MergeAt(i: Idx, vals: State): State 
      ensures |MergeAt(i, vals)| >= i + |vals|
      ensures |MergeAt(i, vals)| >= |this|
      ensures forall j: Idx :: j < |this| ==> j < i || j >= i + |vals| ==> MergeAt(i, vals)[j] == this[j]
      ensures forall j: Idx :: i <= j < i + |vals| ==> MergeAt(i, vals)[j] == vals[j - i]
    {
      var m := map j: Idx | j < |vals| :: vals[j];
      ghost var m' := if m.Keys == {} then 0 else Max(m.Keys);
      assert m' + 1 >= |vals| by {
        if vals != [] {
          assert |vals| - 1 in m.Keys;
        }
      }
      UpdateMapShift(i, m)
    }
  }
}

