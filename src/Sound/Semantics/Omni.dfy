module Omni {
  import opened Defs
  export
    provides Defs, SeqLemma, SemNest, WP, SemCons, SeqFrameLemmaAll
    reveals Sem, SeqSem, SeqWP

  least predicate Sem(s: Stmt, st: State, post: iset<State>) {
    match s
    case Check(e)       => e.IsDefinedOn(|st|) && (st.Eval(e) &&  st in post)
    case Assume(e)      => e.IsDefinedOn(|st|) && (st.Eval(e) ==> st in post)
    case Seq(ss)        => SeqSem(ss, st, post)
    case Assign(x, v)   => 
      && v.IsDefinedOn(|st|) 
      && x < |st|
      && st[x := st.Eval(v)] in post
    case VarDecl(v, s)  => forall b: Value :: Sem(s, st.Update(b), UpdateSet(post))
    case Choice(s0, s1) => Sem(s0, st, post) && Sem(s1, st, post)
    case WithPop(ss) => SeqSem(ss, Tail(st), post)
  }

  ghost function WP(s: Stmt, post: iset<State>) : iset<State> {
    iset st: State | Sem(s, st, post)
  }

  least predicate SeqSem(ss: seq<Stmt>, st: State, post: iset<State>) {
    if ss == [] then st in post else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, post) ==> st in post') ==> Sem(ss[0], st, post')
  }

  ghost function SeqWP(ss: seq<Stmt>, post: iset<State>): iset<State> {
    iset st: State | SeqSem(ss, st, post)
  }

  least lemma SemCons(s: Stmt, st: State, post: iset<State>, post': iset<State>)
    requires Sem(s, st, post)
    requires post <= post'
    ensures Sem(s, st, post')
  {
    match s
    case VarDecl(v, s) => assert UpdateSet(post) <= UpdateSet(post');
    case Seq(ss) => SeqSemCons(ss, st, post, post');
    case _ =>
  }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, post: iset<State>, post': iset<State>)
    requires SeqSem(ss, st, post)
    requires post <= post'
    ensures SeqSem(ss, st, post')
  {  }

  least lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, post: iset<State>) 
    requires Sem(s, st, SeqWP(ss, post))
    ensures SeqSem([s] + ss, st, post)
  {
    forall post': iset<State> | SeqWP(ss, post) <= post' {
      SemCons(s, st, SeqWP(ss, post), post');
    }
  }

  lemma SemSingle(s: Stmt, st: State, post: iset<State>)
    requires SeqSem([s], st, post)
    ensures Sem(s, st, post)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, post: iset<State>) 
    requires SeqSem(ss1 + ss2, st, post)
    ensures SeqSem(ss1, st, SeqWP(ss2, post))
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    }
  }

  lemma SeqLemma(ss: seq<Stmt>, cont: seq<Stmt>, st: State, post: iset<State>)
    requires Sem(Seq(ss + cont), st, post)
    ensures SeqSem([Seq(ss)] + cont, st, post)
  {
    SeqSemNest(ss, cont, st, post);
    SemNest(Seq(ss), cont, st, post);
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

  lemma SeqFrameLemmaAll(ss: seq<Stmt>, v: Variable, st: State)
    requires SeqSem([WithPop(ss)], st, AllStates)
    ensures SeqSem(ss, Tail(st), AllStates)
  {
    // SeqSemNest([Pop], ss, st, AllStates);
    // SemSingle(Pop, st, SeqWP(ss, AllStates));
  }
}