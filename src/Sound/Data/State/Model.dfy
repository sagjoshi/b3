module Model {
  import opened Utils
  export
    provides Utils,
      InterpLiteral, InferType, Bot,
      InterpInt, InterpBool, ToInt, ToBool,
      Not, Equiv, Or, Negate, Plus, Minus, Times, Div, Mod, Less, 
      AtMost, NoEmptyTypes, InterpFunctionOn
    reveals Any, True, False, LogicAnd, IsBool, IsInt, HasType, Implies, 
      Literal, FunctionSig, Function, Type, Int, Bool, Eql, Neql, IsBoolSet, IsIntSet,
      HaveTypes
      ,BoolUnaryFunc, BoolBinaryFunc, IntUnaryFunc, IntBinaryFunc, BinaryFunc,
      InterpretBoolUnaryFuncISet, InterpretBoolBinaryFuncISet, InterpretIntUnaryFuncISet, InterpretIntBinaryFuncISet, InterpretBinaryFuncISet

  type Type = string
  const Int : Type := "int"
  const Bool : Type := "bool"
  datatype Literal = Literal(value: string, typ: Type)
  type FunctionSig = seq<Type>
  datatype Function = Function(name: string, sig: FunctionSig, resultType: Type)

  type Any(!new, ==)

  function {:axiom} Bot(): Any

  function {:axiom} InferType(x: Any): Type
  
  predicate HasType(x: Any, typ: Type) {
    InferType(x) == typ
  }

  lemma {:axiom} NoEmptyTypes(typ: Type) returns (x: Any)
    ensures HasType(x, typ)

  function {:axiom} InterpLiteral(x: Literal): Any
    ensures HasType(InterpLiteral(x), x.typ)
  
  predicate IsInt(x: Any) {
    HasType(x, Int)
  }

  predicate IsBool(x: Any) {
    HasType(x, Bool)
  }

  ghost predicate IsBoolSet(xs: iset<Any>) {
    forall x <- xs :: IsBool(x)
  }

  ghost predicate IsIntSet(xs: iset<Any>) {
    forall x <- xs :: IsInt(x)
  }

  function {:axiom} InterpInt(x: int): Any
    ensures HasType(InterpInt(x), Int)

  function {:axiom} InterpBool(x: bool): Any
    ensures HasType(InterpBool(x), Bool)

  function {:axiom} ToInt(x: Any): int
    requires IsInt(x)
    ensures InterpInt(ToInt(x)) == x

  function {:axiom} ToBool(x: Any): bool
    requires IsBool(x)
    ensures InterpBool(ToBool(x)) == x

  const True: Any := InterpBool(true)
  const False: Any := InterpBool(false)

  function Eql(x: Any, y: Any): Any
  {
    InterpBool(x == y)
  }

  function Neql(x: Any, y: Any): Any
  {
    InterpBool(x != y)
  }

  function Not(x: Any): Any
    requires IsBool(x) 
  {
    InterpBool(!ToBool(x))
  }

  function LogicAnd(x: Any, y: Any): Any
    requires IsBool(x)
    requires IsBool(y)
  {
    InterpBool(ToBool(x) && ToBool(y))
  }

  function Implies(x: Any, y: Any): Any
    requires IsBool(x) 
    requires IsBool(y)
  {
    InterpBool(ToBool(x) ==> ToBool(y))
  }

  function Equiv(x: Any, y: Any): Any
    requires IsBool(x) 
    requires IsBool(y)
  {
    InterpBool(ToBool(x) <==> ToBool(y))
  }

  function Or(x: Any, y: Any): Any
    requires IsBool(x) 
    requires IsBool(y)
  {
    InterpBool(ToBool(x) || ToBool(y))
  }

  function Negate(x: Any): Any
    requires IsInt(x) 
  {
    InterpInt(-ToInt(x))
  }

  function Plus(x: Any, y: Any): Any
    requires IsInt(x) 
    requires IsInt(y)
  {
    InterpInt(ToInt(x) + ToInt(y))
  }

  function Minus(x: Any, y: Any): Any
    requires IsInt(x) && IsInt(y) 
  {
    InterpInt(ToInt(x) - ToInt(y))
  }

  function Times(x: Any, y: Any): Any
    requires IsInt(x) && IsInt(y) 
  {
    InterpInt(ToInt(x) * ToInt(y))
  }

  function Div(x: Any, y: Any): Any
    requires IsInt(x) 
    requires IsInt(y) 
    requires ToInt(y) != 0
  {
    InterpInt(ToInt(x) / ToInt(y))
  }

  function Mod(x: Any, y: Any): Any
    requires IsInt(x) 
    requires IsInt(y) 
    requires ToInt(y) != 0
  {
    InterpInt(ToInt(x) % ToInt(y))
  }

  function Less(x: Any, y: Any): Any
    requires IsInt(x) 
    requires IsInt(y)
  {
    InterpBool(ToInt(x) < ToInt(y))
  }

  function AtMost(x: Any, y: Any): Any
    requires IsInt(x) 
    requires IsInt(y)
  {
    InterpBool(ToInt(x) <= ToInt(y))
  }

  predicate HaveTypes(args: seq<Any>, sig: FunctionSig) {
    |args| == |sig| && forall i :: 0 <= i < |args| ==> HasType(args[i], sig[i])
  }

  function {:axiom} InterpFunctionOn(func: Function, args: seq<Any>): Any
    requires HaveTypes(args, func.sig)
    ensures HasType(InterpFunctionOn(func, args), func.resultType)

  // type BoolFunc = f: seq<Any> --> Any | forall ss: seq<Any> :: (forall s <- ss :: IsBool(s)) ==> f.requires(ss)
  // type IntFunc = f: seq<Any> --> Any | forall ss: seq<Any> :: (forall s <- ss :: IsInt(s)) ==> f.requires(ss)
  // type PolymorphicFunc = f: seq<Any> -> Any

  function InterpretBinaryBoolFunc(f: BoolBinaryFunc, ss: seq<Any>): Any
    requires forall s <- ss :: IsBool(s)
  {
    f(ss[0], ss[1])
  }



  type BinaryFunc = (Any, Any) -> Any
  type BoolUnaryFunc = f: Any --> Any | forall x :: IsBool(x) ==> f.requires(x)
    witness Not

  type BoolBinaryFunc = f: (Any, Any) --> Any | forall x, y :: IsBool(x) && IsBool(y) == f.requires(x, y)
    witness LogicAnd

  type IntUnaryFunc = f: Any --> Any | forall x :: IsInt(x) ==> f.requires(x)
    witness Negate

  type IntBinaryFunc = f: (Any, Any) --> Any | forall x, y :: IsInt(x) && IsInt(y) ==> f.requires(x, y)
    witness Plus

  ghost predicate InterpretBinaryFuncISet(f: BinaryFunc, xs: iset<Any>, ys: iset<Any>, outs: iset<Any>) {
    forall x <- xs, y <- ys :: f(x, y) in outs
  }

  ghost predicate InterpretBoolUnaryFuncISet(f: BoolUnaryFunc, xs: iset<Any>, outs: iset<Any>) 
    requires forall x <- xs :: IsBool(x)
  {
    forall x <- xs :: f(x) in outs
  }

  ghost predicate InterpretBoolBinaryFuncISet(f: BoolBinaryFunc, xs: iset<Any>, ys: iset<Any>, outs: iset<Any>) 
    requires forall x <- xs :: IsBool(x)
    requires forall y <- ys :: IsBool(y)
  {
    forall x <- xs, y <- ys :: f(x, y) in outs
  }

  ghost predicate InterpretIntUnaryFuncISet(f: IntUnaryFunc, xs: iset<Any>, outs: iset<Any>) 
    requires forall x <- xs :: IsInt(x)
  {
    forall x <- xs :: f(x) in outs
  }

  ghost predicate InterpretIntBinaryFuncISet(f: IntBinaryFunc, xs: iset<Any>, ys: iset<Any>, outs: iset<Any>) 
    requires forall x <- xs :: IsInt(x)
    requires forall y <- ys :: IsInt(y)
  {
    forall x <- xs, y <- ys :: f(x, y) in outs
  }
}