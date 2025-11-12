module Model {
  import opened Utils
  export
    provides Utils,
      Bot, InterpLiteral, InferType,
      InterpInt, InterpBool, ToInt, ToBool,
      Not, Equiv, Or, Negate, Plus, Minus, Times, Div, Mod, Less, 
      AtMost, NoEmptyTypes, BoolNotBot, InterpFunctionOn
    reveals Any, True, False, And, IsBool, IsInt, HasType, Implies, 
      Literal, FunctionSig, Function, Type, Int, Bool, BotType, 
      HaveTypes
  type Type = string
  const Int : Type := "int"
  const Bool : Type := "bool"
  const BotType : Type := "bot"
  datatype Literal = Literal(value: string, typ: Type)
  type FunctionSig = seq<Type>
  datatype Function = Function(name: string, sig: FunctionSig, resultType: Type)



  type Any(!new, ==)

  function getBot(): Any

  const Bot: Any := getBot()

  function {:axiom} InferType(x: Any): Type
  
  lemma {:axiom} BotTypeLemma(x: Any)
    ensures InferType(x) == BotType <==> x == Bot

  lemma BoolNotBot(x: Any)
    requires IsBool(x)
    ensures x != Bot
  {
    BotTypeLemma(x);
  }

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

  function Not(x: Any): Any
    requires IsBool(x) 
  {
    InterpBool(!ToBool(x))
  }

  function And(x: Any, y: Any): Any
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
}