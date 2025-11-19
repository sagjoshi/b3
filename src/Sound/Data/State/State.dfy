module State {
  import opened Utils
  import opened Std.Wrappers
  import opened Model

  function SomeBVal?(o: Option<Any>, m: Model): bool {
    match o
    case Some(b) => m.IsBool(b)
    case _ => false
  }

  // function SomeBValTrue?(o: Option<M.Any>): bool {
  //   match o
  //   case Some(b) => b == True
  //   case _ => false
  // }

  function Singleton(val: Any): State
  {
    [val]
  }

  function ToState(args: seq<Any>): State
  {
    args as State
  }

  newtype State = seq<Any> {
    function Update(vals: State): State 
    {
      vals + this
    }

    function Size(): Idx {
      |this|
    }

    function UpdateAt(i: Idx, val: Any): State
      requires i < |this|
    {
      this[i := val]
    }

    function UpdateMapShift(i: Idx, vals: map<Idx, Any>): State  
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
        else Bot()
      )
    }

    function UpdateOrAdd(i: Idx, val: Any): State 
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

    ghost function EqExcept(vars: set<Idx>) : iset<State>
    {
      iset st': State | 
        && |st'| == |this|
        && forall i: Idx :: i < |this| && i !in vars ==> st'[i] == this[i]
    }

    ghost function EqOn(vars: set<Idx>) : iset<State>
    {
      iset st': State | 
        && |st'| == |this|
        && forall i: Idx :: i < |this| && i !in vars ==> st'[i] == this[i]
    }
  }

  function Tail(n: nat, ss: State): State {
    if |ss| <= n then [] else ss[n..]
  }

  ghost function UpdateSet(n: nat, post: iset<State>): iset<State> 
  {
    iset st: State | Tail(n, st) in post 
  }

  ghost const AllStates: iset<State> := iset st: State | true

  ghost function DeleteSet(n: nat, post: iset<State>): iset<State> {
    iset st: State {:trigger} | exists st' <- post :: st == Tail(n, st')
  }

}