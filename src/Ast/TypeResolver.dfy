module TypeResolver {
  import opened Std.Wrappers
  import opened Ast
  import opened Types

  export
    provides ResolveType
    provides Ast, Types, Wrappers

  method ResolveType(typename: string, typeMap: map<string, TypeDecl>) returns (r: Result<Type, string>)
    ensures r.Success? ==> typename in BuiltInTypes || typename in typeMap
  {
    if typename == BoolTypeName {
      return Success(BoolType);
    } else if typename == IntTypeName {
      return Success(IntType);
    } else if typename == TagTypeName {
      return Success(TagType);
    }

    if typename !in typeMap {
      return Failure("unknown type: " + typename);
    }
    return Success(UserType(typeMap[typename]));
  }
}