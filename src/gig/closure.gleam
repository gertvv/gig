import gig/core
import gig/mono
import gleam/set

import gleam/list

type CC {
  CC(mod: Module, uid: Int)
}

pub type Module {
  Module(
    types: List(CustomType),
    functions: List(Function),
    externals: List(Function),
    used_builtin: set.Set(String),
  )
}

pub type CustomType {
  CustomType(
    name: String,
    untyped_name: String,
    display_name: String,
    variants: List(Variant),
    pointer: Bool,
  )
}

pub type Variant {
  Variant(
    name: String,
    untyped_name: String,
    display_name: String,
    fields: List(mono.Field),
  )
}

pub type Function {
  Function(
    name: String,
    parameters: List(mono.Field),
    return: mono.Type,
    body: Exp,
  )
}

pub type Exp {
  Literal(typ: mono.Type, val: core.LiteralKind)
  Var(typ: mono.Type, var: String)
  Call(typ: mono.Type, fun: Exp, arg: List(Exp))
  Op(typ: mono.Type, op: mono.Op, arg: List(Exp))
  CallClosure(typ: mono.Type, fun: Exp, arg: List(Exp))
  Let(typ: mono.Type, var: String, val: Exp, exp: Exp)
  If(typ: mono.Type, cond: Exp, then_exp: Exp, else_exp: Exp)
  Panic(typ: mono.Type, arg: Exp)
}

pub fn cc_module(mod: mono.Context) {
  let c = CC(Module([], [], [], mod.used_builtin), 1)

  let c =
    list.fold(mod.functions, c, fn(c, fun) {
      let #(c, e) = cc(c, fun.body)

      let parameters =
        list.map(fun.parameters, fn(x) { mono.Field(x.name, x.typ) })

      let function = Function(fun.name, parameters, fun.return, e)

      let mod = Module(..c.mod, functions: [function, ..c.mod.functions])
      CC(..c, mod: mod)
    })

  let c =
    list.fold(mod.closures, c, fn(c, closure) {
      let mono.Closure(name: id, environment:, parameters:, return:, body:) =
        closure
      let name = id
      case environment {
        [] -> {
          let #(c, body) = cc(c, body)
          let fun = Function(name:, parameters:, return:, body:)
          let functions = [fun, ..c.mod.functions]
          CC(..c, mod: Module(..c.mod, functions:))
        }
        _ -> {
          let env_type_name = "Env_" <> id
          let env_type = mono.NamedType(env_type_name, [])
          let parameters = [mono.Field("ENV", env_type), ..parameters]
          let #(c, body) = cc(c, body)
          let body =
            environment
            |> list.fold(body, fn(exp, field) {
              let mono.Field(name, typ) = field
              // function from env -> field
              let access =
                Op(
                  typ,
                  mono.FieldAccess(
                    mono.StructPointerAccess,
                    env_type_name,
                    name,
                  ),
                  [Var(env_type, "ENV")],
                )
              Let(exp.typ, name, access, exp)
            })
          let fun = Function(name:, parameters:, return:, body:)
          let functions = [fun, ..c.mod.functions]
          let variant =
            Variant(env_type_name, env_type_name, env_type_name, environment)
          let typedef =
            CustomType(
              env_type_name,
              env_type_name,
              env_type_name,
              [variant],
              True,
            )
          let types = [typedef, ..c.mod.types]
          CC(..c, mod: Module(..c.mod, types:, functions:))
        }
      }
    })

  let c =
    list.fold(mod.types, c, fn(c, custom) {
      let variants =
        list.map(custom.variants, fn(v) {
          let fields = list.map(v.fields, fn(f) { mono.Field(f.name, f.typ) })
          Variant(v.name, v.untyped_name, v.display_name, fields)
        })
      let pointer = case variants {
        [v] ->
          case v.fields {
            [] -> True
            _ -> False
          }
        _ -> True
      }
      let custom =
        CustomType(
          name: custom.name,
          untyped_name: custom.untyped_name,
          display_name: custom.display_name,
          variants: variants,
          pointer: pointer,
        )

      let mod = Module(..c.mod, types: [custom, ..c.mod.types])
      CC(..c, mod: mod)
    })

  let externals =
    mod.externals
    |> list.filter(fn(ext) { !ext.builtin })
    |> list.map(fn(external) {
      let assert mono.FunctionType(_, ret) = external.typ
      let params =
        list.map(external.parameters, fn(param) {
          mono.Field(param.name, param.typ)
        })
      let string_type = mono.NamedType("String", [])
      let todo_val = Literal(string_type, core.String(""))
      let body = Panic(ret, todo_val)
      Function(
        name: external.external_name,
        parameters: params,
        return: ret,
        body: body,
      )
    })

  Module(..c.mod, externals:)
}

fn cc(c: CC, e: mono.Exp) -> #(CC, Exp) {
  case e {
    mono.Literal(typ, var) -> #(c, Literal(typ, var))
    mono.Local(typ, var) -> #(c, Var(typ, var))
    mono.ConstantGlobal(typ:, id:) -> {
      // zero-arg constructor
      #(c, Var(typ, id))
    }
    mono.CallGlobal(typ:, id: fun_name, args:) -> {
      let fun_type = mono.FunctionType(list.map(args, fn(arg) { arg.typ }), typ)
      // TODO: add the fun_type to CallGlobal?
      let fun = Var(fun_type, fun_name)
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = cc(c, arg)
          #(c, [arg, ..args])
        })
      let args = list.reverse(args)
      #(c, Call(typ, fun, args))
    }
    mono.CallClosure(typ, fun, args) -> {
      let #(c, fun) = cc(c, fun)
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = cc(c, arg)
          #(c, [arg, ..args])
        })
      // let args = list.reverse(args)
      #(c, CallClosure(typ, fun, args))
    }
    mono.Op(typ, op, args) -> {
      let #(c, args) =
        list.fold(args, #(c, []), fn(acc, arg) {
          let #(c, args) = acc
          let #(c, arg) = cc(c, arg)
          #(c, [arg, ..args])
        })
      let args = list.reverse(args)
      #(c, Op(typ, op, args))
    }
    mono.BindClosure(typ:, id:, environment:) -> {
      case environment {
        [] -> {
          let name = id
          let fun_pointer = Var(mono.NamedType("void*", []), name)
          let closure =
            Call(typ, Var(typ, "create_function"), [
              fun_pointer,
            ])
          #(c, closure)
        }
        _ -> {
          let name = id
          let env_type_name = "Env_" <> id
          let env_type = mono.NamedType(env_type_name, [])
          let #(c, env_args) =
            list.fold(environment, #(c, []), fn(acc, arg) {
              let #(c, args) = acc
              let #(c, arg) = cc(c, arg)
              #(c, [arg, ..args])
            })
          // let env_args = list.reverse(env_args)
          let fun_pointer = Var(mono.NamedType("void*", []), name)
          let env_arg_types = list.map(environment, fn(x) { x.typ })
          let new_env_fun_type = mono.FunctionType(env_arg_types, env_type)
          let env_constructor_call =
            Call(
              env_type,
              Var(new_env_fun_type, "new_" <> env_type_name),
              env_args,
            )
          let closure =
            Call(typ, Var(typ, "create_closure"), [
              fun_pointer,
              env_constructor_call,
            ])
          #(c, closure)
        }
      }
    }
    mono.Let(typ, var, val, exp) -> {
      let #(c, val) = cc(c, val)
      let #(c, exp) = cc(c, exp)
      #(c, Let(typ, var, val, exp))
    }
    mono.If(typ, cond, then_e, else_e) -> {
      let #(c, cond) = cc(c, cond)
      let #(c, then_e) = cc(c, then_e)
      let #(c, else_e) = cc(c, else_e)
      #(c, If(typ, cond, then_e, else_e))
    }
    mono.Panic(typ, arg) -> {
      let #(c, arg) = cc(c, arg)
      #(c, Panic(typ, arg))
    }
  }
}
