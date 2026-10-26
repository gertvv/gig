import gig/core as t
import gig/core_closure as u
import gig/gen_names
import gleam/dict
import gleam/io
import gleam/list
import gleam/result
import gleam/set
import gleam/string

pub type Context {
  Context(
    in_types: dict.Dict(String, t.CustomType),
    in_functions: dict.Dict(String, u.Closure),
    in_externals: dict.Dict(String, t.External),
    in_constants: dict.Dict(String, u.Constant),
    types: List(CustomType),
    functions: List(Closure),
    externals: List(External),
    used_types: set.Set(String),
    used_functions: set.Set(String),
    used_externals: set.Set(String),
    used_modules: set.Set(String),
    used_builtin: set.Set(String),
  )
}

pub type Type {
  NamedType(id: String, parameters: List(Type))
  FunctionType(parameters: List(Type), return: Type)
}

pub type External {
  External(
    typ: Type,
    module: String,
    internal_name: String,
    external_name: String,
    parameters: List(Field),
    builtin: Bool,
  )
}

pub type CustomType {
  CustomType(
    name: String,
    untyped_name: String,
    display_name: String,
    variants: List(Variant),
  )
}

pub type Variant {
  Variant(
    name: String,
    untyped_name: String,
    display_name: String,
    fields: List(Field),
  )
}

pub type Field {
  Field(name: String, typ: Type)
}

pub type Closure {
  Closure(
    name: String,
    environment: List(Field),
    parameters: List(Field),
    return: Type,
    body: Exp,
  )
}

pub type FieldAccessKind {
  StructAccess
  StructPointerAccess
  TaggedUnionAccess
}

pub type Op {
  FieldAccess(kind: FieldAccessKind, variant: String, field: String)
  VariantCheck(variant: String)
}

pub type Exp {
  Literal(typ: Type, val: t.LiteralKind)
  Local(typ: Type, var: String)
  ConstantGlobal(typ: Type, id: String)
  CallGlobal(typ: Type, id: String, args: List(Exp))
  BindClosure(typ: Type, id: String, environment: List(Exp))
  CallClosure(typ: Type, fun: Exp, arg: List(Exp))
  Op(typ: Type, op: Op, arg: List(Exp))
  Let(typ: Type, var: String, val: Exp, exp: Exp)
  If(typ: Type, cond: Exp, then_exp: Exp, else_exp: Exp)
  Panic(typ: Type, value: Exp)
}

pub fn init_context(in: List(u.Module)) -> Context {
  let in = merge_modules(in)

  let in_types =
    list.fold(in.types, dict.new(), fn(d, i) { dict.insert(d, i.id, i) })
  let in_functions =
    list.fold(in.functions, dict.new(), fn(d, i) { dict.insert(d, i.id, i) })
  let in_externals =
    list.fold(in.externals, dict.new(), fn(d, i) {
      dict.insert(d, i.internal_name, i)
    })
  let in_constants =
    list.fold(in.constants, dict.new(), fn(d, i) { dict.insert(d, i.id, i) })
  Context(
    in_types:,
    in_functions:,
    in_externals:,
    in_constants:,
    types: [],
    functions: [],
    externals: [],
    used_types: set.new(),
    used_functions: set.new(),
    used_externals: set.new(),
    used_modules: set.new(),
    used_builtin: set.new(),
  )
}

pub fn run(in: List(u.Module), main_name: String) {
  let c = init_context(in)

  let main = case dict.get(c.in_functions, main_name) {
    Ok(main) -> main
    Error(_) -> panic as "main function not found"
  }

  // instantiate types and functions reachable from main
  let typ = sub_type([], main.typ.typ)
  let #(c, main_name) = instantiate_function(c, main_name, typ)

  // instantiate types used by externals
  let c =
    dict.values(c.in_externals)
    |> list.filter(fn(x) { set.contains(c.used_modules, x.module) })
    |> list.filter(fn(x) { !x.builtin })
    |> list.fold(c, fn(c, external) {
      let used_externals = set.insert(c.used_externals, external.internal_name)
      let c = Context(..c, used_externals:)
      instantiate_type(c, sub_type([], external.typ.typ))
    })

  #(c, main_name)
}

fn merge_modules(in: List(u.Module)) -> u.Module {
  list.fold(
    in,
    u.Module(
      name: "app",
      types: [],
      functions: [],
      externals: [],
      constants: [],
    ),
    fn(a, b) {
      u.Module(
        name: a.name,
        types: list.append(a.types, b.types),
        functions: list.append(a.functions, b.functions),
        externals: list.append(a.externals, b.externals),
        constants: list.append(a.constants, b.constants),
      )
    },
  )
}

pub fn sub_type(sub: List(#(t.TypeVarId, Type)), typ: t.Type) -> Type {
  case typ {
    t.Unbound(id) ->
      case list.find(sub, fn(sub) { sub.0 == id }) {
        Ok(sub) -> sub.1
        Error(_) -> NamedType("Nil", [])
      }
    t.NamedType(name, args) -> NamedType(name, list.map(args, sub_type(sub, _)))
    t.FunctionType(args, ret) ->
      FunctionType(list.map(args, sub_type(sub, _)), sub_type(sub, ret))
  }
}

fn unify_poly(
  c: Context,
  poly: t.Poly,
  mono: Type,
) -> List(#(t.TypeVarId, Type)) {
  let sub = unify_type(c, poly.typ, mono)
  list.map(poly.vars, fn(x) {
    case list.find(sub, fn(s) { s.0 == x }) {
      Ok(s) -> #(x, s.1)
      Error(Nil) -> {
        panic as "could not unify poly type"
      }
    }
  })
}

fn unify_type(
  c: Context,
  poly: t.Type,
  mono: Type,
) -> List(#(t.TypeVarId, Type)) {
  case poly, mono {
    t.Unbound(id), _ -> [#(id, mono)]
    t.NamedType(a, aa), NamedType(b, ba) ->
      case a == b {
        True ->
          list.zip(aa, ba)
          |> list.flat_map(fn(x) { unify_type(c, x.0, x.1) })
        False -> {
          panic as "could not unify types"
        }
      }
    t.FunctionType(aa, ar), FunctionType(ba, br) ->
      list.append(
        unify_type(c, ar, br),
        list.zip(aa, ba)
          |> list.flat_map(fn(x) { unify_type(c, x.0, x.1) }),
      )
    _, _ -> {
      echo poly
      echo mono
      panic as "could not unify types"
    }
  }
}

pub fn type_name(typ: Type) -> String {
  case typ {
    NamedType(name, args) ->
      string.join([name, ..list.map(args, type_name)], "_")
    FunctionType(..) -> "Closure"
  }
}

fn get_type_string(sub: List(#(t.TypeVarId, Type))) {
  // TODO only include typed that are actually used
  // e.g. variant that only uses part of the params
  // e.g. phantom type
  list.map(sub, fn(s) { "_" <> type_name(s.1) })
  |> string.concat()
}

pub fn instantiate_type(c: Context, mono: Type) {
  case mono {
    NamedType(name, _args) -> {
      case dict.get(c.in_types, name) {
        Ok(custom) -> {
          let sub = unify_poly(c, custom.typ, mono)
          let type_string = get_type_string(sub)
          let mono_name = custom.id <> type_string

          case set.contains(c.used_types, mono_name) {
            True -> c
            False -> {
              // instantiate variants
              let variants =
                list.map(custom.variants, fn(v) {
                  let mono_name = v.id <> type_string
                  let fields =
                    list.map(v.fields, fn(field) {
                      Field(field.name, sub_type(sub, field.typ))
                    })
                  Variant(mono_name, v.id, v.display_name, fields)
                })

              // create new custom type
              let custom =
                CustomType(mono_name, custom.id, custom.display_name, variants)

              // add to module
              let types = [custom, ..c.types]
              let used_types = set.insert(c.used_types, mono_name)

              let c = Context(..c, types:, used_types:)

              // also instantiate any types referenced by this type
              list.fold(variants, c, fn(c, variant) {
                list.fold(variant.fields, c, fn(c, field) {
                  instantiate_type(c, field.typ)
                })
              })
            }
          }
        }
        Error(_) -> c
      }
    }
    FunctionType(args, ret) -> {
      let c = list.fold(args, c, instantiate_type)
      instantiate_type(c, ret)
    }
  }
}

fn instantiate_function(
  c: Context,
  name: String,
  mono: Type,
) -> #(Context, String) {
  let result =
    {
      dict.get(c.in_functions, name)
      |> result.map(fn(fun) {
        let sub = unify_poly(c, fun.typ, mono)
        let type_string = get_type_string(sub)
        let mono_name = fun.id <> type_string

        case fun.body {
          u.Panic(_, _) -> {
            io.println_error("missing function " <> fun.id <> " in " <> name)
          }
          _ -> Nil
        }

        case set.contains(c.used_functions, mono_name) {
          True -> #(c, mono_name)
          False -> {
            let used_functions = set.insert(c.used_functions, mono_name)
            let c = Context(..c, used_functions:)

            // instantiate function
            let #(c, mono_body) = typed_to_mono_exp(c, sub, fun.body)
            let params =
              list.map(fun.parameters, fn(p) {
                let typ = sub_type(sub, p.typ)
                Field(p.name, typ)
              })
            let environment =
              list.map(fun.environment, fn(p) {
                let typ = sub_type(sub, p.typ)
                Field(p.name, typ)
              })
            let assert FunctionType(_, ret) = mono
            let fun =
              Closure(
                name: mono_name,
                environment:,
                parameters: params,
                return: ret,
                body: mono_body,
              )

            let c = Context(..c, functions: [fun, ..c.functions])
            #(c, mono_name)
          }
        }
      })
    }
    |> result.lazy_or(fn() {
      dict.get(c.in_externals, name)
      |> result.map(fn(external) {
        case external.builtin {
          True -> {
            let sub = unify_poly(c, external.typ, mono)
            let type_string = get_type_string(sub)
            let lookup_name = external.external_name <> type_string
            case set.contains(c.used_builtin, lookup_name) {
              True -> #(c, lookup_name)
              False -> {
                // also instantiate builtins used by this builtin
                let source_type = case mono {
                  // this happens with unary constructors
                  NamedType(..) -> mono
                  FunctionType([], ret) -> ret
                  FunctionType([a, ..], _ret) -> a
                }
                let c = case name {
                  "lt" -> {
                    let c = instantiate_builtin(c, "eq", source_type)
                    instantiate_builtin(c, name, source_type)
                  }
                  "eq" | "inspect" -> {
                    instantiate_builtin(c, name, source_type)
                  }
                  _constructor -> {
                    let used_builtin = set.insert(c.used_builtin, lookup_name)
                    Context(..c, used_builtin:)
                  }
                }

                #(c, lookup_name)
              }
            }
          }
          False -> {
            let lookup_name = external.external_name
            case set.contains(c.used_externals, lookup_name) {
              True -> #(c, lookup_name)
              False -> {
                let typ = sub_type([], external.typ.typ)
                let c = instantiate_type(c, typ)

                let params =
                  list.map(external.parameters, fn(param) {
                    Field(param.name, sub_type([], param.typ))
                  })

                // add the external to output
                let external =
                  External(
                    internal_name: external.internal_name,
                    external_name: external.external_name,
                    module: external.module,
                    parameters: params,
                    builtin: external.builtin,
                    typ: typ,
                  )

                let externals = [external, ..c.externals]
                let used_modules = set.insert(c.used_modules, external.module)
                let used_externals = set.insert(c.used_externals, lookup_name)

                let c = Context(..c, externals:, used_modules:, used_externals:)
                #(c, lookup_name)
              }
            }
          }
        }
      })
    })

  case result {
    Ok(rval) -> rval
    Error(_) -> panic as { "invalid reference " <> name }
  }
}

/// Mark the builtin as used and also transitive builtins
fn instantiate_builtin(c: Context, fun_name: String, mono: Type) -> Context {
  let lookup_name = fun_name <> "_" <> type_name(mono)
  case set.contains(c.used_builtin, lookup_name) {
    True -> c
    False -> {
      // mark as used
      let used_builtin = set.insert(c.used_builtin, lookup_name)
      let c = Context(..c, used_builtin:)

      // also instantiate builtins used by this builtin
      let assert NamedType(custom_type_name, _) = mono
      case dict.get(c.in_types, custom_type_name) {
        Ok(custom) -> {
          let sub = unify_poly(c, custom.typ, mono)
          list.fold(custom.variants, c, fn(c, v) {
            list.fold(v.fields, c, fn(c, f) {
              let field_typ = sub_type(sub, f.typ)
              case field_typ {
                NamedType(..) -> instantiate_builtin(c, fun_name, field_typ)
                _ -> c
              }
            })
          })
        }
        Error(_) -> c
      }
    }
  }
}

fn typed_to_mono_exp(
  c: Context,
  sub: List(#(t.TypeVarId, Type)),
  e: u.Expr,
) -> #(Context, Exp) {
  let c = instantiate_type(c, sub_type(sub, e.typ))
  case e {
    u.Literal(typ, v) -> #(c, Literal(sub_type(sub, typ), v))
    u.Local(typ, name) -> {
      let typ = sub_type(sub, typ)
      #(c, Local(typ, name))
    }
    u.ConstantGlobal(typ, name) -> {
      case dict.get(c.in_constants, name) {
        Ok(constant) -> {
          // inline constants
          typed_to_mono_exp(c, sub, constant.value)
        }
        Error(_) -> {
          // zero-arg constructor
          let typ = sub_type(sub, typ)
          let #(c, name) = instantiate_function(c, name, typ)
          #(c, ConstantGlobal(typ:, id: name))
        }
      }
    }
    u.CallGlobal(typ: return, id:, arguments: args) -> {
      let typ = t.FunctionType(list.map(args, fn(arg) { arg.typ }), return)
      let typ = sub_type(sub, typ)
      let #(c, name) = instantiate_function(c, id, typ)
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = typed_to_mono_exp(c, sub, arg)
          #(c, [arg, ..args])
        })
      let args = list.reverse(args)
      let return = sub_type(sub, return)
      #(c, CallGlobal(return, name, args))
    }
    u.BindClosure(typ:, id: name, environment: env) -> {
      let typ = sub_type(sub, typ)
      let #(c, name) = instantiate_function(c, name, typ)
      let #(c, env) =
        list.fold(env, #(c, []), fn(acc, arg) {
          let #(c, env) = acc
          let #(c, var) = typed_to_mono_exp(c, sub, arg)
          #(c, [var, ..env])
        })
      #(c, BindClosure(typ, name, env))
    }
    u.CallClosure(typ:, closure: exp, arguments: args) -> {
      let typ = sub_type(sub, typ)
      let #(c, exp) = typed_to_mono_exp(c, sub, exp)
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = typed_to_mono_exp(c, sub, arg)
          #(c, [arg, ..args])
        })
      let args = list.reverse(args)
      #(c, CallClosure(typ, exp, args))
    }
    u.Op(typ, op, args) -> {
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = typed_to_mono_exp(c, sub, arg)
          #(c, [arg, ..args])
        })
      let args = list.reverse(args)
      let typ = sub_type(sub, typ)
      let op = case op {
        t.FieldAccess(variant:, index:) -> {
          let assert [arg, ..] = args
          let assert NamedType(name, _) = arg.typ
          let assert Ok(custom) = dict.get(c.in_types, name)
          let kind = case custom.variants {
            [_] -> StructAccess
            _ -> TaggedUnionAccess
          }
          let assert Ok(t.Variant(fields:, display_name: variant, ..)) =
            list.find(custom.variants, fn(v) {
              // TODO: for tuple indexing, variant is set to "#", but the variant.id to "TupleN"
              v.id == variant || variant == "#"
            })
          let assert Ok(field) = list.drop(fields, index) |> list.first
          FieldAccess(
            kind:,
            variant:,
            field: gen_names.field_name(field.name, index),
          )
        }
        t.VariantCheck(variant:) -> VariantCheck(variant:)
      }
      #(c, Op(typ, op, args))
    }
    u.Let(typ, var, val, exp) -> {
      let #(c, val) = typed_to_mono_exp(c, sub, val)
      let #(c, exp) = typed_to_mono_exp(c, sub, exp)
      let typ = sub_type(sub, typ)
      #(c, Let(typ, var, val, exp))
    }
    u.If(typ, cond, then_e, else_e) -> {
      let #(c, cond) = typed_to_mono_exp(c, sub, cond)
      let #(c, then_e) = typed_to_mono_exp(c, sub, then_e)
      let #(c, else_e) = typed_to_mono_exp(c, sub, else_e)
      let typ = sub_type(sub, typ)
      #(c, If(typ, cond, then_e, else_e))
    }
    u.Panic(typ, arg) -> {
      let #(c, arg) = typed_to_mono_exp(c, sub, arg)
      let typ = sub_type(sub, typ)
      #(c, Panic(typ, arg))
    }
  }
}
