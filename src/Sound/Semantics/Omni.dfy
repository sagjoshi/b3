module Omni {
  import opened Defs
  export
    provides Defs, 
      SeqLemma, SemNest, SemCons, SeqSemCons, SeqSemSingle, 
      RefSem, SemSound, SeqRefSem, SeqSemSound, 
      SemLoopWithCont, InvSem
    reveals 
      Sem, SeqSem, WP, SeqWP, SemSingle, 
      Continuation, Continuation.Update, Continuation.UpdateAndAdd, Continuation.head, Continuation.Leq,
      Continuation.UpdateHead, PreservesInv, Continuation.Get

  /**
  
  Loop(inv, body(x))
  ---
  cc

  check inv;
  x := *
  assume inv;
  body(x);
  check inv;
  ----
  cc
   */

  newtype Continuation = s: seq<iset<State>> | |s| > 0 witness [iset{}] {

    function Get(i: nat): iset<State> 
      requires i < |this|
    {
      this[i]
    }

    ghost const head : iset<State> := this[0]

    function Cons(post: iset<State>): Continuation {
      [post] + this
    }

    ghost function UpdateHead(post: iset<State>): Continuation {
      this[0 := post]
    }

    ghost function Update(variablesInScope: nat): Continuation 
      ensures |this| == |Update(variablesInScope)|
      ensures forall l: nat :: l < |this| ==> Update(variablesInScope)[l] == UpdateSet(variablesInScope, this[l])
    {
      var head' := UpdateSet(variablesInScope, head);
      if |this| == 1 then [head'] else [head'] + this[1..].Update(variablesInScope)
    }

    ghost function UpdateAndAdd(variablesInScope: nat): Continuation {
      ([head] + this).Update(variablesInScope)
    }

    predicate Leq(cont2: Continuation) {
      && |this| == |cont2|
      && forall i: nat :: i < |this| ==> this[i] <= cont2[i]
    }

    lemma LeqUpdate(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures Update(variablesInScope).Leq(cont.Update(variablesInScope))
    {

    }

    lemma LeqUpdateAndAdd(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures UpdateAndAdd(variablesInScope).Leq(cont.UpdateAndAdd(variablesInScope))
    {
      ([head] + this).LeqUpdate(variablesInScope, [cont.head] + cont);
    }

    lemma LeqUpdateHead(post: iset<State>, cont: Continuation) 
      requires Leq(cont) 
      ensures UpdateHead(post).Leq(cont.UpdateHead(post))
    {
    }
  }

  /**
    wp ( (1 :: (1 :: 2 := A; exit(1)); 1 := B);) [post] st == 
    wp ((1 :: 2 := A; exit(1)); 1 := B) [Upd(post), Upd(post)] st ==
    wp (1 :: 2 := A; exit(1)) [Upd(post)[1/B], Upd(post)] st == 
    wp (2 := A; exit(1)) [Upd(Upd(post)[1/B]), Upd(Upd(post)[1/B]), Upd2(post)] st ==
    wp (exit(1)) [[Upd(Upd(post)[1/B])[2/A]], Upd(Upd(post)[1/B]), Upd2(post)] st ==
    st in Upd(Upd(post)[1/B])

   */ 

  ghost predicate SemSingle(s: Stmt, st: State, post: iset<State>) 
    requires s.Single()
  {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) &&  st in post)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) ==> st in post)
    case Assign(x, v)   => 
      && x < |st|
      && v.IsDefinedOn(|st|) 
      && st[x := st.Eval(v)] in post
    case Call(proc, args) =>
      // var Pre := SeqSubstitute(proc.Pre, args.ToExpr());
      // var Post := SeqSubstitute(proc.Post, args.ToExpr());
      // var outVars := args.OutArgs();
      // && (forall v <- outVars :: v < |st|)
      // && (forall e <- Pre :: e.IsDefinedOn(|st|) && st.Eval(e))
      // && forall st': State :: (
      //   && st' in st.EqExcept(outVars)
      //   && (forall e <- Post :: e.IsDefinedOn(|st'|) && st'.Eval(e)))
      //     ==> st' in post
      && args.IsDefinedOn(|st|)
      && var callSt := args.EvalOn(st);
        && (forall e <- proc.Pre :: e.IsDefinedOn(|callSt|) && callSt.Eval(e))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.EvalOn(st');
            (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && callSt'.Eval(e)))
              ==> st' in post
  }

  ghost predicate PreservesInv(inv: iset<State>, body: Stmt, posts: Continuation)
  { 
    forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  }

  ghost predicate Sem(s: Stmt, st: State, posts: Continuation) {
    if s.Single() then SemSingle(s, st, posts.head) else
    match s
    case Seq(ss)        => SeqSem(ss, st, posts)
    case Choice(s0, s1) => Sem(s0, st, posts) && Sem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> Sem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(_, body) => 
      exists inv: iset<State> :: 
        && st in inv
        && forall st': State :: 
          st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  }

  greatest predicate RefSem(s: Stmt, st: State, posts: Continuation) {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) &&  st in posts.head)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) ==> st in posts.head)
    case Assign(x, v)   => 
      && x < |st|
      && v.IsDefinedOn(|st|) 
      && st[x := st.Eval(v)] in posts.head
    case Call(proc, args) => 
      && args.IsDefinedOn(|st|)
      && var callSt := args.EvalOn(st);
        && (forall e <- proc.Pre :: e.IsDefinedOn(|callSt|) && callSt.Eval(e))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.EvalOn(st');
            (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && callSt'.Eval(e)))
              ==> st' in posts.head
    case Seq(ss)        => SeqRefSem(ss, st, posts)
    case Choice(s0, s1) => RefSem(s0, st, posts) && RefSem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> RefSem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(inv, body) => RefSem(Seq([body, Loop(inv, body)]), st, posts)
  }

  greatest predicate SeqRefSem(ss: seq<Stmt>, st: State, posts: Continuation) {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqRefSem(ss[1..], st, posts) ==> st in post') ==> RefSem(ss[0], st, posts.UpdateHead(post'))
  }

  ghost function WP(s: Stmt, posts: Continuation) : iset<State> {
    iset st: State | Sem(s, st, posts)
  }

  ghost predicate SeqSem(ss: seq<Stmt>, st: State, posts: Continuation) {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, posts) ==> st in post') ==> Sem(ss[0], st, posts.UpdateHead(post'))
  }

  ghost function SeqWP(ss: seq<Stmt>, cont: Continuation): iset<State> {
    iset st: State | SeqSem(ss, st, cont)
  }

  lemma SemCons(s: Stmt, st: State, posts: Continuation, posts': Continuation)
    requires Sem(s, st, posts)
    requires posts.Leq(posts')
    ensures Sem(s, st, posts')
  {
    match s
    case Seq(ss) => SeqSemCons(ss, st, posts, posts');
    case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
    case Loop(_, body) => forall inv { posts.LeqUpdateHead(inv, posts'); }
    case _ =>
  }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation)
    requires SeqSem(ss, st, posts)
    requires posts.Leq(posts')
    ensures SeqSem(ss, st, posts')
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall post': iset<State> | (forall st: State :: SeqSem(ss[1..], st, posts') ==> st in post') {
        SemCons(ss[0], st, posts.UpdateHead(post'), posts'.UpdateHead(post'));
      }
    }
  }

  lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
    requires Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
    ensures SeqSem([s] + ss, st, posts)
  {
    forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts) ==> st in post') {
      SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts)), posts.UpdateHead(post'));
    }
  }

  // lemma SemUnNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
  //   requires SeqSem([s] + ss, st, posts)
  //   ensures Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
  // {
  //   // assert ([s] + ss)[0] == s;
  //   // assert ([s] + ss)[1..] == ss; 
  // }

  lemma SeqSemSingle(s: Stmt, st: State, posts: Continuation)
    requires SeqSem([s], st, posts)
    ensures Sem(s, st, posts)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts == posts.UpdateHead(posts.head);
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation) 
    requires SeqSem(ss1 + ss2, st, posts)
    ensures SeqSem(ss1, st, posts.UpdateHead(SeqWP(ss2, posts)))
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
      assert forall post': iset<State> :: posts.UpdateHead(SeqWP(ss2, posts)).UpdateHead(post') == posts.UpdateHead(post');
    }
  }

  lemma SeqLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation)
    requires Sem(Seq(ss1 + ss2), st, posts)
    ensures SeqSem([Seq(ss1)] + ss2, st, posts)
  {
    SeqSemNest(ss1, ss2, st, posts);
    SemNest(Seq(ss1), ss2, st, posts);
  }

  function StateSize(st: State): nat {
    |st|
  }

  lemma SemSeqLemma(ss: seq<Stmt>, st: State, posts: Continuation)
    requires SeqSem(ss, st, posts)
    ensures Sem(Seq(ss), st, posts)
  {

  }

  lemma SeqSemSingle'(s: Stmt, st: State, posts: Continuation)
    requires Sem(s, st, posts)
    ensures SeqSem([s], st, posts)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts.UpdateHead(posts.head) == posts;
    forall post': iset<State> | (forall st: State :: SeqSem([], st, posts) ==> st in post') 
      ensures Sem(s, st, posts.UpdateHead(post')) {
      SemCons(s, st, posts, posts.UpdateHead(post'));
    }
  }

  lemma SemLoopLemma(inv: Expr, body: Stmt, st: State, posts: Continuation, inv': iset<State>)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'))
    ensures Sem(Loop(inv, body), st, posts)
  {  }

  lemma PreservesInvLemma(inv: iset<State>, body: Stmt, posts: Continuation)
    requires PreservesInv(inv, body, posts)
    ensures forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  {  } 

  lemma SemLoopUnroll(s: Stmt, inv: Expr, body: Stmt, st: State, posts: Continuation)
    requires Sem(Loop(inv, body), st, posts)
    ensures Sem(Seq([body, Loop(inv, body)]), st, posts)
  {
    var invEx :| st in invEx && PreservesInv(invEx, body, posts);
    PreservesInvLemma(invEx, body, posts);
    SemNest(body, [Loop(inv, body)], st, posts) by {
      SemCons(body, st, posts.UpdateHead(invEx), posts.UpdateHead(SeqWP([Loop(inv, body)], posts))) by {
        forall st: State | st in invEx ensures SeqSem([Loop(inv, body)], st, posts) {
          SeqSemSingle'(Loop(inv, body), st, posts) by {
            SemLoopLemma(inv, body, st, posts, invEx);
          }
        }
      }
    }
  }

  greatest lemma SemSound(s: Stmt, st: State, posts: Continuation)
    requires Sem(s, st, posts)
    ensures RefSem(s, st, posts)
  {
    match s
    case Seq(ss) => SeqSemSound(ss, st, posts);
    case Loop(inv, body) => SemLoopUnroll(s, inv, body, st, posts);
    case _ =>
  }

  greatest lemma SeqSemSound(ss: seq<Stmt>, st: State, posts: Continuation)
    requires SeqSem(ss, st, posts)
    ensures SeqRefSem(ss, st, posts)
  {
    if ss != [] {
      forall post': iset<State> | (forall st: State :: SeqRefSem(ss[1..], st, posts) ==> st in post') 
        ensures RefSem(ss[0], st, posts.UpdateHead(post')) {
        SemSound(ss[0], st, posts.UpdateHead(post'));
      }
    }
  } 

  lemma SemLoopWithCont(inv: Expr, body: Stmt, cont: seq<Stmt>, st: State, posts: Continuation, inv': iset<State>)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'))
    ensures SeqSem([Loop(inv, body)] + cont, st, posts)
  {
    SemNest(Loop(inv, body), cont, st, posts) by {
      SemLoopLemma(inv, body, st, posts.UpdateHead(SeqWP(cont, posts)), inv') by {
        assert posts.UpdateHead(SeqWP(cont, posts)).UpdateHead(inv') == posts.UpdateHead(inv');
      }
    }
  }
  
  lemma SemDepthLemma(s: Stmt, st: State, posts: Continuation)
    requires Sem(s, st, posts)
    

  lemma InvSem(inv: Expr, body: Stmt, st: State, posts: Continuation, stmt: Stmt)
    requires SeqSem([Assume(inv), body, Check(inv), stmt], st, posts)
    requires st in inv.Sem()
    ensures Sem(body, st, posts.UpdateHead(inv.Sem()))
  {
    SeqSemNest([Assume(inv)], [body, Check(inv), stmt], st, posts);
    SeqSemSingle(Assume(inv), st, posts.UpdateHead(SeqWP([body, Check(inv), stmt], posts)));
    assert SeqSem([body, Check(inv), stmt], st, posts);
    SeqSemNest([body], [Check(inv), stmt], st, posts);
    SeqSemSingle(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts)));
    SemCons(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts)), posts.UpdateHead(inv.Sem())) by {
      forall st': State | SeqSem([Check(inv), stmt], st', posts) ensures st' in inv.Sem() {
        SeqSemNest([Check(inv)], [stmt], st', posts);
        SeqSemSingle(Check(inv), st', posts.UpdateHead(SeqWP([stmt], posts)));
      }
    }
  }
}