module AssignmentTarget {
  import opened Defs
  import Omni

  export
    provides Defs, Omni, Process, Correct
    reveals EqsTo
  
  predicate ShiftedIn(s: set<Idx>, n: nat, i: Idx) {
    i + n in s
  }

  datatype VarsJumps = VarJumps(vars: set<Idx>, jumps: set<nat>) {

    function Merge(m1: VarsJumps): VarsJumps {
      VarJumps(vars + m1.vars, jumps + m1.jumps)
    }

    function SeqMerge(m: VarsJumps): VarsJumps {
      if 0 in this.jumps then
        VarJumps(vars + m.vars, jumps - {0} + m.jumps) 
      else 
        this
    }

    function SubstractSet(n: nat, s: set<Idx>): set<Idx> 
      ensures forall i: Idx :: i + n in s ==> i in SubstractSet(n, s)
    {
      set i: Idx {:trigger i + n in s} | i <= Max'(s) - n && i + n in s 
    }

    lemma InSubstractSet(s: set<Idx>, n: nat, i: Idx) 
      requires i + n in s 
      ensures i in SubstractSet(n, s)
    {

    }

    function Substract(n: nat): VarsJumps {
      VarJumps(SubstractSet(n, vars), 
        jumps * {0} +
        set i: nat {:trigger i + 1 in jumps} |
          && i <= Max'(jumps) - 1
          && i + 1 in jumps)
    }

    function Remove0(): VarsJumps {
      VarJumps(vars, jumps - {0})
    }

    ghost function ToEqs(st: State, posts: Omni.Continuation): Omni.Continuation 
    {
      seq(|posts|, (k : nat) requires k < |posts| => 
        if k !in jumps then iset{} else
        iset st' |
          && st' in posts[k]
          && |st'| == |st|
          && forall i: Idx :: i < |st| && i !in vars ==> st[i] == st'[i]
      )
    }
  }

  ghost function ToEqs(vars: set<Idx>, st: State, posts: Omni.Continuation): Omni.Continuation 
    {
      seq(|posts|, (k : nat) requires k < |posts| => 
        iset st' |
          && st' in posts[k]
          && |st'| == |st|
          && forall i: Idx :: i < |st| && i !in vars ==> st[i] == st'[i]
      )
    }

  function Pred(n: nat): nat {
    if n == 0 then 0 else n - 1
  }
  
  function Process'(stmt: Stmt): VarsJumps 
    ensures forall v <- Process'(stmt).vars :: v < stmt.Depth()
    decreases stmt
  {
    match stmt
    case Seq(ss) => SeqProcess'(ss)
    case Choice(s0, s1) => 
      var vs0 := Process'(s0);
      var vs1 := Process'(s1);
      vs0.Merge(vs1)
    case NewScope(n, s) => 
      var vs := Process'(s);
      vs.Substract(n)
    case Escape(n) => VarJumps({}, {n})
    case Loop(inv, body) => 
      VarJumps(Process'(body).vars, Process'(body).jumps - {0})
    case Assign(x, _) => VarJumps({x}, {0})
    case _ => VarJumps({}, {0})
  }

  function SeqProcess'(ss: seq<Stmt>): VarsJumps 
    ensures forall v <- SeqProcess'(ss).vars :: v < SeqDepth(ss)
    decreases ss
  {
    if ss == [] then VarJumps({}, {0}) else
      var v0 := Process'(ss[0]);
      if 0 in v0.jumps then
        v0.SeqMerge(SeqProcess'(ss[1..]))
      else v0
  }

  lemma Process'Correct(stmt: Stmt, st: State, m: VarsJumps, posts: Omni.Continuation) 
    requires Process'(stmt) == m
    ensures forall v <- m.vars :: v < stmt.Depth()
    requires Omni.Sem(stmt, st, posts)
    ensures Omni.Sem(stmt, st, m.ToEqs(st, posts))
  {
    match stmt 
    case Choice(s0, s1) => 
      var m0 := Process'(s0);
      var m1 := Process'(s1);
      Omni.SemCons(s0, st, m0.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts)) by {
        Process'Correct(s0, st, m0, posts);
      }
      Omni.SemCons(s1, st, m1.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts)) by {
        Process'Correct(s1, st, m1, posts);
      }
    case Loop(_, body) =>  
      var inv :| 
        && st in inv
        && Omni.PreservesInv(inv, body, posts);
      var m' := Process'(body);
      var inv' := inv * ToEqs(m'.vars, st, posts.UpdateHead(inv)).head;
      assert st in inv';
      forall st': State | st' in inv' ensures Omni.Sem(body, st', m'.Remove0().ToEqs(st, posts).UpdateHead(inv')) {
        Omni.SemCons(body, st', m'.ToEqs(st', posts.UpdateHead(inv)), m'.Remove0().ToEqs(st, posts).UpdateHead(inv')) by {
          Process'Correct(body, st', m', posts.UpdateHead(inv)) by {
            assert Omni.PreservesInv(inv, body, posts);
          }
        }
      }
    case NewScope(n, body) => 
      forall vs: State | |vs| == n ensures Omni.Sem(body, st.Update(vs), m.ToEqs(st, posts).UpdateAndAdd(n)) {
        var m' := Process'(body);
        Omni.SemCons(body, st.Update(vs), m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n)), m.ToEqs(st, posts).UpdateAndAdd(n)) by {
          Process'Correct(body, st.Update(vs), m', posts.UpdateAndAdd(n));
          forall i: Idx | i < |posts| + 1 
            ensures m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n))[i] <=
              m'.Substract(n).ToEqs(st, posts).UpdateAndAdd(n)[i]
          {
            forall st': State | st' in m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n))[i] 
              ensures st' in m'.Substract(n).ToEqs(st, posts).UpdateAndAdd(n)[i]
            {
              if i == 0 {
                assert st'[n..] in m'.Substract(n).ToEqs(st, posts).head by {
                  assert Pred(0) in m'.jumps;
                  assert 0 in m'.Substract(n).jumps;
                }
              } else {
                assert st'[n..] in m'.Substract(n).ToEqs(st, posts)[i - 1] by {
                  assert i - 1 <= Max'(m'.jumps) - 1;
                }
              }
            }
          }
        }
      }
    case Seq(ss) => SeqProcess'Correct(ss, st, m, posts);
    case _ =>
  }

  lemma SeqProcess'Correct(ss: seq<Stmt>, st: State, m: VarsJumps, posts: Omni.Continuation) 
    requires SeqProcess'(ss) == m
    ensures forall v <- m.vars :: v < SeqDepth(ss)
    requires Omni.SeqSem(ss, st, posts)
    ensures Omni.SeqSem(ss, st, m.ToEqs(st, posts))
  {
    if ss != [] {
      Omni.SemNest(ss[0], ss[1..], st, m.ToEqs(st, posts)) by {
        assert Omni.Sem(ss[0], st, m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..],  m.ToEqs(st, posts)))) by {
          assert Omni.Sem(ss[0], st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts)));
          var m' := Process'(ss[0]);
          Process'Correct(ss[0], st, m', posts.UpdateHead(Omni.SeqWP(ss[1..], posts)));
          assert Omni.Sem(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts))));
          if 0 !in m'.jumps {
            Omni.SemCons(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts))), 
              m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts))));
          } else {
            var m'' := SeqProcess'(ss[1..]);
            assert m == m'.SeqMerge(m'');
            Omni.SemCons(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts))), 
              m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts)))) by {
              forall i: Idx | i < |posts| 
                ensures m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts)))[i] <=
                      m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts)))[i]
              {
                forall st': State | st' in m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts)))[i] 
                  ensures st' in m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts)))[i] 
                {
                  if i == 0 {
                    SeqProcess'Correct(ss[1..], st', m'', posts);
                    Omni.SeqSemCons(ss[1..], st', m''.ToEqs(st', posts), m.ToEqs(st, posts));
                  } 
                }
              }
            }
          }
        }
      }
    } 
  }

  function Process(stmt: Stmt): set<Idx> 
    ensures forall v <- Process(stmt) :: v < stmt.Depth()

  {
    var VarJumps(vs, jumps) := Process'(stmt);
    if 0 in jumps then vs else {}
  } 

  ghost function EqsTo(vars: set<Idx>, st: State): iset<State> 
    requires forall v <- vars :: v < |st|
  {
    iset st': State | 
      && |st'| == |st|
      && forall i: Idx :: i < |st| && i !in vars ==> st'[i] == st[i]
  }


  lemma Correct'(stmt: Stmt, st: State, vars: set<Idx>, posts: Omni.Continuation) 
    requires forall v <- vars :: v < |st|
    requires Omni.Sem(stmt, st, posts)
    requires Process(stmt) == vars
    ensures Omni.Sem(stmt, st, posts.UpdateHead(posts.head * EqsTo(vars, st)))
  {
    Process'Correct(stmt, st, Process'(stmt), posts);
    Omni.SemCons(stmt, st, Process'(stmt).ToEqs(st, posts), posts.UpdateHead(posts.head * EqsTo(vars, st)));
  }

  lemma Correct(stmt: Stmt, st: State, st': State, vars: set<Idx>, posts: Omni.Continuation, post: iset<State>) 
    requires forall v <- vars :: v < |st'|
    requires Omni.Sem(stmt, st, posts.UpdateHead(post))
    requires Process(stmt) == vars
    requires st in EqsTo(vars, st')
    ensures Omni.Sem(stmt, st, posts.UpdateHead(post * EqsTo(vars, st')))
  {
    Correct'(stmt, st, vars, posts.UpdateHead(post));
    assert posts.UpdateHead(post).UpdateHead(posts.UpdateHead(post).head * EqsTo(vars, st)) == posts.UpdateHead(post * EqsTo(vars, st));
    Omni.SemCons(stmt, st, posts.UpdateHead(post * EqsTo(vars, st)), posts.UpdateHead(post * EqsTo(vars, st')));
  }
}