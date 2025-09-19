module Omni {
  import opened Defs
  export
    provides Defs, SeqLemma, SemNest, WP, SemCons//, SeqFrameLemmaAll
    reveals 
      Sem, SeqSem, SeqWP, SemSingle,
      Continuation, Continuation.Update, Continuation.UpdateAndAdd, Continuation.head, Continuation.Leq,
      Continuation.UpdateHead
  
  // datatype Point = Point(post: iset<State>, variablesInScope: nat)
  newtype Continuation = s : seq<iset<State>> | |s| > 0 witness [iset{}] {

    ghost const head : iset<State> := this[0]

    ghost function UpdateHead(post: iset<State>): Continuation {
      this[0 := post]
    }

    ghost function Update(variablesInScope: nat): Continuation {
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
  }

  ghost predicate Sem(s: Stmt, st: State, posts: Continuation) {
    if s.Single() then SemSingle(s, st, posts.head) else
    match s
    case Seq(ss)        => SeqSem(ss, st, posts)
    case Choice(s0, s1) => Sem(s0, st, posts) && Sem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> Sem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
  }

  ghost function WP(s: Stmt, posts: Continuation) : iset<State> {
    iset st: State | Sem(s, st, posts)
  }

  ghost predicate SeqSem(ss: seq<Stmt>, st: State, posts: Continuation) {
    if ss == [] then st in posts.head else
    // Q: how to make trigger
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
    // case VarDecl(v, s) => assert UpdateSet(post) <= UpdateSet(post');
    case Seq(ss) => SeqSemCons(ss, st, posts, posts');
    case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
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
  // SeqSem([s] + ss, st, post + posts) == Sem(s, st, [SeqWP(ss, posts)] + posts)
  lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
    requires Sem(s, st, posts[0 := SeqWP(ss, posts)])
    ensures SeqSem([s] + ss, st, posts)
  {
    forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts) ==> st in post') {
      SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts)), posts.UpdateHead(post'));
    }
  }

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
    ensures SeqSem(ss1, st, posts[0 := SeqWP(ss2, posts)])
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

  // lemma FrameLemma(s: Stmt, st: State, post: iset<State>)
  //   requires Sem(WithPop(s), st, post)
  //   ensures Sem(s, Tail(st), DeleteSet(post))
  // {
  //   // match s 
  //   // case Assign(x, e) => e.EvalFVarsLemma(st, st - {v});
  //   // case Check(e) => e.EvalFVarsLemma(st, st - {v});
  //   // case Assume(e) =>  e.EvalFVarsLemma(st, st - {v});
  //   // case Seq(ss) => SeqFrameLemma(ss, v, st, post);
  //   // case VarDecl(u, s) =>
  //   //   forall c: Value {: trigger}
  //   //     ensures Sem(s, (st - {v}).Update(u, c), UpdateSet(u, DeleteSet(v, post))) { 
  //   //     FrameLemma(s, v, st.Update(u, c), UpdateSet(u, post));
  //   //     assert forall c :: (st - {v}).Update(u, c) == st.Update(u, c) - {v};        
  //   //     SemCons(s, (st - {v}).Update(u, c), DeleteSet(v, UpdateSet(u, post)), UpdateSet(u, DeleteSet(v, post))) by {
  //   //       forall st | st in DeleteSet(v, UpdateSet(u, post)) 
  //   //         ensures st in UpdateSet(u, DeleteSet(v, post)) {
  //   //         assert forall b :: (st - {u}).Update(v, b) == st.Update(v, b) - {u};
  //   //       }
  //   //     }
  //   //   }
  //   // case Choice(s0, s1) => FrameLemma(s0, v, st, post); FrameLemma(s1, v, st, post);
  // }

  // lemma SeqFrameLemma(ss: seq<Stmt>, st: State, post: iset<State>)
  //   requires SeqSem(WithPop(ss), st, post)
  //   ensures SeqSem(ss, Tail(st), DeleteSet(post))
  // {
  //   if ss == [] {
  //   } else {
  //     assert ([ss[0]] + ss[1..])[0] == ss[0];
  //     assert SeqShiftFVars(ss, 0) == [ss[0].ShiftFVars(0)] + SeqShiftFVars(ss[1..], 0);
  //     FrameLemma(ss[0], st, SeqWP(SeqShiftFVars(ss[1..], 0), post)) by {
  //       assert Sem(ss[0].ShiftFVars(0), st, SeqWP(SeqShiftFVars(ss[1..], 0), post));
  //     }
  //     SemNest(ss[0], ss[1..], Tail(st), DeleteSet(post)) by {
  //       SemCons(ss[0], Tail(st), DeleteSet(SeqWP(SeqShiftFVars(ss[1..], 0), post)), SeqWP(ss[1..], DeleteSet(post))) by {
  //         forall st | st in DeleteSet(SeqWP(SeqShiftFVars(ss[1..], 0), post)) 
  //           ensures SeqSem(ss[1..], st, DeleteSet(post)) {
  //           var st': State :| st == Tail(st') && SeqSem(SeqShiftFVars(ss[1..], 0), st', post);
  //           SeqFrameLemma(ss[1..], st', post);
  //         }
  //       }
  //     }
  //   }
  // }

  // lemma SeqFrameLemmaAll(ss: seq<Stmt>, v: Variable, st: State)
  //   requires SeqSem([WithPop(ss)], st, AllStates)
  //   ensures SeqSem(ss, Tail(st), AllStates)
  // {
  //   // SeqSemNest([Pop], ss, st, AllStates);
  //   // SemSingle(Pop, st, SeqWP(ss, AllStates));
  // }
}