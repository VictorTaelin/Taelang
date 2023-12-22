// Lists
type List<A> =
  | { tag: "Cons"; head: A; tail: List<A> }
  | { tag: "Nil"; };
const Cons = <A>(head: A, tail: List<A>): List<A> => ({ tag: "Cons", head, tail });
const Nil  = <A>(): List<A>                       => ({ tag: "Nil" });

export function fold<A,P>(list: List<A>, cons: (head: A, tail: P) => P, nil: P): P {
  switch (list.tag) {
    case "Cons": return cons(list.head, fold(list.tail, cons, nil));
    case "Nil" : return nil;
  }
}

// Terms
export type Term =
  | { tag: "Var"; val: number }
  | { tag: "Set"; } // *
  | { tag: "All"; inp: Term; bod: (x: Term) => Term }  // ∀(<x>: <term>) <term>
  | { tag: "Lam"; bod: (x: Term) => Term } // λx <term>
  | { tag: "App"; fun: Term; arg: Term } // (<term> <term>)
  | { tag: "Slf"; bod: (x: Term) => Term } // $<x> <term>
  | { tag: "Ins"; val: Term } // ~<term>
  | { tag: "Ann"; chk: boolean; val: Term; typ: Term } // {<term> : <term>}
  | { tag: "Let"; val: Term; bod: (x: Term) => Term } // let x = val; body
  | { tag: "Def"; val: Term; bod: (x: Term) => Term } // def x = val; body
  | { tag: "Ref"; nam: string } // @term
  | { tag: "Hol"; nam: string, ctx: Context, got: List<Term> } // ? hole
export const Var = (val: number): Term => ({ tag: "Var", val });
export const Set = (): Term => ({ tag: "Set" });
export const All = (inp: Term, bod: (x: Term) => Term): Term  => ({ tag: "All", inp, bod });
export const Lam = (bod: (x: Term) => Term): Term => ({ tag: "Lam", bod });
export const App = (fun: Term, arg: Term): Term => ({ tag: "App", fun, arg });
export const Slf = (bod: (x: Term) => Term): Term => ({ tag: "Slf", bod });
export const Ins = (val: Term): Term => ({ tag: "Ins", val });
export const Ann = (chk: boolean, val: Term, typ: Term): Term => ({ tag: "Ann", chk, val, typ });
export const Let = (val: Term, bod: (x: Term) => Term): Term => ({ tag: "Let", val, bod });
export const Def = (val: Term, bod: (x: Term) => Term): Term => ({ tag: "Def", val, bod });
export const Ref = (nam: string): Term => ({ tag: "Ref", nam });
export const Hol = (nam: string, ctx: Context, got: List<Term>): Term => ({ tag: "Hol", nam, ctx, got });

// A type context
export type Context = List<[string, Term]>;

// A book of definitions
export type Book = {[key: string]: {typ: Term, val: Term}};
export type Load = (key: string) => ({typ: Term, val: Term}) | null;

// Checker
// -------

var FRESH = 0;

// Reduces to weak normal form
export function reduce(load: Load, term: Term, dep: number): Term {
  if (term.tag === "App") {
    var fun = reduce(load, term.fun, dep);
    if (fun.tag === "Lam") {
      return reduce(load, fun.bod(term.arg), dep);
    }
    if (fun.tag === "Hol") {
      return reduce(load, Hol(fun.nam, fun.ctx, Cons(term.arg, fun.got)), dep);
    }
    return term;
  }
  if (term.tag === "Ann") {
    return reduce(load, term.val, dep);
  }
  if (term.tag === "Ins") {
    return reduce(load, term.val, dep);
  }
  if (term.tag === "Let") {
    return reduce(load, term.bod(term.val), dep);
  }
  if (term.tag === "Def") {
    return reduce(load, term.bod(term.val), dep);
  }
  if (term.tag === "Ref") {
    var loaded = load(term.nam);
    if (loaded !== null) {
      return reduce(load, loaded.val, dep);
    }
  }
  return term;
}

// Checks if two terms are definitionaly equal.
export function equal(load: Load, a: Term, b: Term, dep: number): boolean {
  //console.log("eq?", show_term(a, dep));
  //console.log("...", show_term(b, dep));
  var eq = false;
  if (a.tag === "Var" && b.tag === "Var") {
    eq = a.val === b.val;
  } else if (a.tag === "Set" && b.tag === "Set") {
    eq = true;
  } else if (a.tag === "All" && b.tag === "All") {
    eq = equal(load, a.inp, b.inp, dep) && equal(load, a.bod(Var(dep)), b.bod(Var(dep)), dep+1);
  } else if (a.tag === "Lam" && b.tag === "Lam") {
    eq = equal(load, a.bod(Var(dep)), b.bod(Var(dep)), dep+1);
  } else if (a.tag === "App" && b.tag === "App") {
    eq = equal(load, a.fun, b.fun, dep) && equal(load, a.arg, b.arg, dep);
  } else if (a.tag === "Slf" && b.tag === "Slf") {
    eq = equal(load, a.bod(Var(dep)), b.bod(Var(dep)), dep + 1);
  } else if (a.tag === "Ins" && b.tag === "Ins") {
    eq = equal(load, a.val, b.val, dep);
  } else if (a.tag === "Ref" && b.tag === "Ref" && a.nam === b.nam) {
    eq = true;
  } else if (a.tag === "Hol" && b.tag === "Hol" && a.nam === b.nam) {
    eq = true;
  } else if (a.tag === "Lam") {
    eq = equal(load, a, Lam(x => App(b, x)), dep);
  } else if (b.tag === "Lam") {
    eq = equal(load, Lam(x => App(a, x)), b, dep);
  } else if (a.tag === "Hol") {
    console.log("NOTE: " + show_term(a, dep) + " = " + show_term(b, dep));
    eq = true;
  } else if (b.tag === "Hol") {
    console.log("NOTE: " + show_term(b, dep) + " = " + show_term(a, dep));
    eq = true;
  }
  if (!eq) {
    var a2 = reduce(load, a, dep);
    if (a2 !== a) {
      return equal(load, a2, b, dep);
    }
    var b2 = reduce(load, b, dep);
    if (b2 !== b) {
      return equal(load, a, b2, dep);
    }
  }
  return eq;
}

// Evaluates a term to normal form.
export function normal(load: Load, term: Term, dep: number = 0): Term {
  var orig = term;
  var term = reduce(load, term, dep);
  switch (term.tag) {
    case "Lam": return Lam(x => normal(load, term.bod(x), dep+1));
    case "App": return App(normal(load, term.fun, dep), normal(load, term.arg, dep));
    case "All": return All(normal(load, term.inp, dep), x => normal(load, term.bod(x), dep+1));
    case "Ann": return normal(load, term.val, dep);
    case "Let": return normal(load, term.bod(term.val), dep);
    case "Def": return normal(load, term.bod(term.val), dep);
    default   : return orig;
  }
}

// Infers the type of a term.
export function infer(load: Load, val: Term, dep: number = 0): Term {
  //console.log("inf", show_term(val, dep));
  switch (val.tag) {
    case "Var": {
      throw "Can't infer var.";
    }
    case "Ref": {
      var loaded = load(val.nam);
      return loaded !== null ? loaded.typ : Ref(val.nam);
    }
    case "Hol": {
      return Hol(val.nam+"_T", val.ctx, val.got);
    }
    case "Set": {
      return Set();
    }
    case "All": {
      check(load, val.inp, Set(), true, dep);
      check(load, val.bod(Ann(false, Var(dep), val.inp)), Set(), true, dep+1);
      return Set();
    }
    case "Lam": {
      return All(
        Hol(num_to_str(FRESH++), Nil(), Nil()), x =>
        Hol(num_to_str(FRESH++), Cons([num_to_str(dep),x], Nil()), Nil()));
    }
    case "App": {
      var fun_ty = reduce(load, infer(load, val.fun, dep), dep);
      if (fun_ty.tag === "Hol") {
        var ctx = fun_ty.ctx;
        var got = fun_ty.got;
        fun_ty = All(
          Hol(num_to_str(FRESH++), ctx, got), x =>
          Hol(num_to_str(FRESH++), Cons([num_to_str(dep),x], ctx), got));
      }
      if (fun_ty.tag === "All") {
        check(load, val.arg, fun_ty.inp, true, dep);
        return fun_ty.bod(val.arg);
      } else {
        console.log("- " + show_term(val.fun, dep));
        console.log("- " + show_term(fun_ty, dep));
        throw "NonFunApp";
      }
    }
    case "Ins": {
      var val_ty = reduce(load, infer(load, val.val, dep), dep);
      if (val_ty.tag === "Slf") {
        return val_ty.bod(val);
      } else {
        throw "NonSlfIns";
      }
    }
    case "Slf": {
      check(load, val.bod(Ann(false, Var(dep), val)), Set(), true, dep);
      return Set();
    }
    case "Ann": {
      return check(load, val.val, val.typ, val.chk, dep);
    }
    case "Let": {
      throw "NonAnnLet";
    }
    case "Def": {
      throw "NonAnnDef";
    }
  }
}

// Checks if a type of a term is correct.
export function check(load: Load, val: Term, tty: Term, chk: boolean, dep: number = 0): Term {
  //console.log("chk", show_term(val, dep));
  //console.log(" ::", show_term(tty, dep));
  var typ = reduce(load, tty, dep);
  //var typ = typ.tag === "Slf" ? typ.bod(val) : typ;
  if (!chk) {
    return typ;
  } else {
    if (val.tag === "Lam") {
      if (typ.tag === "All") {
        check(load, val.bod(Ann(false, Var(dep), typ.inp)), typ.bod(Var(dep)), chk, dep+1);
        return typ;
      } else {
        //console.log("- ", show_term(val, dep));
        //console.log("- ", show_term(typ, dep));
        throw "NonFunLam";
      }
    } else if (val.tag === "Ins") {
      if (typ.tag === "Slf") {
        check(load, val.val, typ.bod(val), chk, dep);
        return typ;
      } else {
        throw "NonSlfIns";
      }
    } else if (val.tag === "Hol") {
      console.log("HOLE: ?" + val.nam);
      console.log("GOAL: " + show_term(normal(x => null, tty, dep), dep));
      console.log(fold(val.ctx, ([nam,val],str) => str + "- " + nam + " = " + show_term(val, dep) + "\n", "").trim());
      return typ;
    } else if (val.tag === "Let") {
      var val_typ = infer(load, val.val, dep);
      check(load, val.bod(Ann(false, val.val, val_typ)), typ, chk, dep + 1);
      return typ;
    } else if (val.tag === "Def") {
      check(load, val.bod(val.val), typ, chk, dep + 1);
      return typ;
    } else {
      var inf = infer(load, val, dep);
      var inf = reduce(load, inf, dep);
      //var inf = inf.tag === "Slf" ? inf.bod(val) : inf;
      if (!equal(load, typ, inf, dep)) {
        var exp = show_term(typ, dep);
        var det = show_term(inf, dep);
        var msg = "TypeMismatch\n- expected: " + exp + "\n- detected: " + det;
        throw msg; 
      }
      return typ;
    }
  }
}

export function check_one(load: Load, name: string) {
  try {
    var loaded = load(name);
    if (loaded !== null) {
      var {val, typ} = loaded;
      check(load, val, typ, true);
      console.log("\x1b[32m✔ " + name + "\x1b[0m");
    } else {
      throw "Couldn't load '"+name+"'.";
    }
  } catch (e) {
    if (e instanceof RangeError) {
      console.log("\x1b[33m? " + name + "\x1b[0m");
      console.log(e);
    } else {
      console.log("\x1b[31m✘ " + name + "\x1b[0m");
      console.log(e);
    }
  }
}

export function check_all(book: Book) {
  for (var name in book) {
    check_one(x => book[x], name);
  }
}

// Syntax
// ------

export function cut(str: string): string {
  return str[0] === "(" ? str.slice(1, -1) : str;
}

export function show_term(term: Term, dep: number = 0): string {
  switch (term.tag) {
    case "Var": return num_to_str(term.val);
    //case "Var": return "@" + term.val;
    case "Set": return "*";
    case "All": return "∀(" + num_to_str(dep) + ":"+show_term(term.inp, dep)+") " + show_term(term.bod(Var(dep)), dep + 1);
    case "Lam": return "λ" + num_to_str(dep) + " " + show_term(term.bod(Var(dep)), dep + 1);
    case "App": return "(" + cut(show_term(term.fun, dep)) + " " + show_term(term.arg, dep) + ")";
    case "Slf": return "$" + num_to_str(dep) + " " + show_term(term.bod(Var(dep)), dep+1);
    case "Ins": return "~" + show_term(term.val, dep);
    case "Ann": return "{" + show_term(term.val, dep) + ":" + show_term(term.typ, dep) + "}";
    case "Let": return "let " + num_to_str(dep) + " = " + show_term(term.val, dep) + " " + show_term(term.bod(Var(dep)), dep + 1);
    case "Def": return "def " + num_to_str(dep) + " = " + show_term(term.val, dep) + " " + show_term(term.bod(Var(dep)), dep + 1);
    case "Ref": return term.nam;
    //case "Hol": return "?" + term.nam + "{" + fold(term.ctx, ([nam,val],str) => str + nam + "=" + show_term(val, dep) + ";", "") + "}";
    case "Hol": return "(?" + term.nam + fold(term.got, (val,str) => str + " " + show_term(val, dep), "") + ")";
  }
}

export function show_book(book: Book): string {
  var text = "";
  for (var name in book) {
    text += name + " : " + show_term(book[name].typ) + " = " + show_term(book[name].val) + "\n";
  }
  return text;
}

export function num_to_str(num: number): string {
  let txt = '';
  num += 1;
  while (num > 0) {
    txt += String.fromCharCode(((num-1) % 26) + 'a'.charCodeAt(0));
    num  = Math.floor((num-1) / 26);
  }
  return txt.split('').reverse().join('');
}

export function find<A>(list: Context, nam: string): Term {
  switch (list.tag) {
    case "Cons": return list.head[0] === nam ? list.head[1] : find(list.tail, nam);
    case "Nil" : return Ref(nam);
  }
}

export function gets<A>(list: Context, idx: number): Term {
  switch (list.tag) {
    case "Cons": return idx === 0 ? list.head[1] : gets(list.tail, idx - 1);
    case "Nil" : throw "unbound";
  }
}

export function skip(code: string): string {
  while (true) {
    if (code.slice(0, 2) === "//") {
      do { code = code.slice(1); } while (code.length != 0 && code[0] != "\n");
      continue;
    }
    if (code[0] === "\n" || code[0] === " ") {
      code = code.slice(1);
      continue;
    }
    break;
  }
  return code;
}

export function is_name_char(c: string): boolean {
  return /[a-zA-Z0-9_]/.test(c);
}

export function parse_name(code: string): [string, string] {
  code = skip(code);
  var name = "";
  while (is_name_char(code[0]||"")) {
    name = name + code[0];
    code = code.slice(1);
  }
  return [code, name];
}

export function parse_text(code: string, text: string): [string, null] {
  code = skip(code);
  if (text === "") {
    return [code, null];
  } else if (code[0] === text[0]) {
    return parse_text(code.slice(1), text.slice(1));
  } else {
    throw "parse error";
  }
}

export function parse_term(code: string): [string, (ctx: Context) => Term] {
  code = skip(code);
  // ALL: `∀(x: T) f`
  if (code[0] === "∀") {
    var [code, nam] = parse_name(code.slice(2));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, __ ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => All(typ(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // LAM: `λx f`
  if (code[0] === "λ" || code[0] === "∀") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(x => bod(Cons([nam,x], ctx)))];
  }
  // APP: `(f x y z ...)`
  if (code[0] === "(") {
    var [code, fun] = parse_term(code.slice(1));
    var args: ((ctx: Context) => Term)[] = [];
    while (code[0] !== ")") {
      var [code, arg] = parse_term(code);
      args.push(arg);
      code = skip(code);
    }
    var [code, _] = parse_text(code, ")");
    return [code, ctx => args.reduce((f, x) => App(f, x(ctx)), fun(ctx))];
  }
  // SET: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => Set()];
  }
  // SLF: `$x T`
  if (code[0] === "$") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Slf(x => bod(Cons([nam, x], ctx)))];
  }
  // INS: `~t`
  if (code[0] === "~") {
    var [code, val] = parse_term(code.slice(1));
    return [code, ctx => Ins(val(ctx))];
  }
  // ANN: `{x : T}`
  if (code[0] === "{") {
    var [code, val] = parse_term(code.slice(1));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, _  ] = parse_text(code, "}");
    return [code, ctx => Ann(true, val(ctx), typ(ctx))];
  }
  // LET: `let x = val; body`
  if (code.slice(0, 4) === "let ") {
    var [code, nam] = parse_name(code.slice(4));
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    var [code, bod] = parse_term(code);
    return [code, ctx => Let(val(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // DEF: `def x = val; body`
  if (code.slice(0, 4) === "def ") {
    var [code, nam] = parse_name(code.slice(4));
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    var [code, bod] = parse_term(code);
    return [code, ctx => Def(val(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // HOL: `?` `name`
  if (code[0] === "?") {
    var [code, nam] = parse_name(code.slice(1));
    return [code, ctx => Hol(nam, ctx, Nil())];
  }
  // VAR: `%idx`
  if (code[0] === "%") {
    var [code, idx] = parse_name(code.slice(1));
    return [code, ctx => gets(ctx, Number(idx))];
  }
  // VAR: `name`
  var [code, nam] = parse_name(code);
  if (nam.length > 0) {
    return [code, ctx => find(ctx, nam)];
  }
  throw "parse error";
}

export function do_parse_term(code: string): Term {
  return parse_term(code)[1](Nil());
}

export function parse_def(code: string): [string, {nam: string, typ: Term, val: Term}] {
  var [code, nam] = parse_name(skip(code));
  var [code, _  ] = parse_text(code, ":");
  var [code, typ] = parse_term(code);
  var [code, _  ] = parse_text(code, "=");
  var [code, val] = parse_term(code);
  return [code, {nam: nam, typ: typ(Nil()), val: val(Nil())}];
}

export function parse_book(code: string): Book {
  var book : Book = {};
  while (code.length > 0) {
    var [code, def] = parse_def(code);
    book[def.nam] = {typ: def.typ, val: def.val};
    code = skip(code);
  }
  return book;
}

export function do_parse_book(code: string): Book {
  return parse_book(code);
}

//var code = `
//Bool
//: *
//= $self
  //∀(P: ∀(x: Bool) *) 
  //∀(t: (P true))
  //∀(f: (P false))
  //(P self)

//true
//: Bool
//= ~ λP λt λf t

//false
//: Bool
//= ~ λP λt λf f
//`;

//var book = parse_book(code);

//check_all(book);

