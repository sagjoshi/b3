module Block {
  import opened Defs
  
  datatype Point = Point(cont: seq<Stmt>, varsInScope: nat)

  newtype Continuation = seq<Point> {
    function Update(cont: seq<Stmt>, varsInScope: nat): Continuation {
      [Point(cont, varsInScope)] + this
    }

    function VarsInScope(l: nat): nat 
      requires l <= |this|
    {
      if l == 0 then 0 else this[0].varsInScope + this[1..].VarsInScope(l - 1)
    }

    function AllVarsInScope(): nat {
      if this == [] then 0 else this[0].varsInScope + this[1..].AllVarsInScope()
    }

    lemma VarsInScopeLeqAll(l: nat)
      requires l <= |this|
      ensures VarsInScope(l) + this[l..].AllVarsInScope() == AllVarsInScope()
    {

    }

    function Size(): nat {
      if this == [] then 0 else SeqSize(this[0].cont) + 1 + this[1..].Size()
    }

    lemma UpdateSize(cont: seq<Stmt>, varsInScope: nat)
      ensures Update(cont, varsInScope).Size() == SeqSize(cont) + Size() + 1
    {

    }

    lemma SizePrefix(l: nat)
      requires l <= |this|
      ensures this[l..].Size() <= Size()
    {
      assert this[..l] + this[l..] == this;
      SizeConcat(this[..l], this[l..]);
    }

    predicate IsDefinedOn(d: nat) {
      AllVarsInScope() <= d
    }

    predicate JumpsDefined() {
      if this == [] then true else
        SeqJumpsDefinedOn(this[0].cont, |this[1..]|) && this[1..].JumpsDefined()
    }

    predicate VarsDefined() {
      if this == [] then true else
        SeqIsDefinedOn(this[0].cont, this[1..].AllVarsInScope()) && this[1..].VarsDefined()
    }

    lemma DefinedPrefix'(l: nat)
      requires l < |this|
      requires JumpsDefined()
      requires VarsDefined()
      ensures SeqJumpsDefinedOn(this[l].cont, |this[l+1..]|) 
      ensures SeqIsDefinedOn(this[l].cont, this[l+1..].AllVarsInScope())
      // ensures SeqIsDefinedOn(this[l].cont, 1000) /*SOUNDNESS BUG:*/
    {
      if this != [] {
        if l != 0 {
          this[1..].DefinedPrefix'(l - 1);
          assert this[1..][l - 1] == this[l];
          assert this[1..][l - 1..] == this[l..];
        }
      }
    }

    lemma DefinedPrefix(l: nat)
      requires l <= |this|
      requires JumpsDefined()
      requires VarsDefined()
      ensures this[l..].JumpsDefined()
      ensures this[l..].VarsDefined()
      decreases |this| - l
    {
      if l != 0 {
        if |this| != l {
          assert this[l + 1..] == this[l..][1..];
          DefinedPrefix(l + 1);
          DefinedPrefix'(l);
        }
      }
    }
  }

    lemma SizeConcat(cont1: Continuation, cont2: Continuation)
      ensures (cont1 + cont2).Size() == cont1.Size() + cont2.Size()
    {
      if cont1 == [] {
        assert cont1 + cont2 == cont2;
      } else {
        assert (cont1 + cont2)[0] == cont1[0];
        assert (cont1 + cont2)[1..] == cont1[1..] + cont2;
        SizeConcat(cont1[1..], cont2);
      }
    }

}