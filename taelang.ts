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

// Push function for lists. Adds an element to the last position. Uses fold.
export function push<A>(elem: A, list: List<A>): List<A> {
  return fold(list, Cons, Cons(elem, Nil()));
}

// Terms
export type Term =
  | { tag: "Var"; nam: string; val: number }
  | { tag: "Set"; } // *
  | { tag: "All"; nam: string; inp: Term; bod: (x: Term) => Term }  // ∀(<x>: <term>) <term>
  | { tag: "Lam"; nam: string; bod: (x: Term) => Term } // λ(<x>: <term>) <term>
  | { tag: "App"; fun: Term; arg: Term } // (<term> <term>)
  | { tag: "Fix"; nam: string; typ: Term, bod: (x: Term) => Term } // μ(<x>: <term>) <term>
  | { tag: "Slf"; nam: string; bod: (x: Term) => Term } // $<x> <term>
  | { tag: "Ins"; val: Term } // ~<term>
  | { tag: "Ann"; chk: boolean; val: Term; typ: Term } // {<term> : <term>}
  | { tag: "Let"; nam: string; val: Term; bod: (x: Term) => Term } // let x = val; body
  | { tag: "Def"; nam: string; val: Term; bod: (x: Term) => Term } // def x = val; body
  | { tag: "Ref"; nam: string } // @term
  | { tag: "Hol"; nam: string; ctx: Context; cap: List<Term> } // ? hole
export const Var = (nam: string, val: number): Term => ({ tag: "Var", nam, val });
export const Set = (): Term => ({ tag: "Set" });
export const All = (nam: string, inp: Term, bod: (x: Term) => Term): Term  => ({ tag: "All", nam, inp, bod });
export const Lam = (nam: string, bod: (x: Term) => Term): Term => ({ tag: "Lam", nam, bod });
export const App = (fun: Term, arg: Term): Term => ({ tag: "App", fun, arg });
export const Fix = (nam: string, typ: Term, bod: (x: Term) => Term): Term => ({ tag: "Fix", nam, typ, bod });
export const Slf = (nam: string, bod: (x: Term) => Term): Term => ({ tag: "Slf", nam, bod });
export const Ins = (val: Term): Term => ({ tag: "Ins", val });
export const Ann = (chk: boolean, val: Term, typ: Term): Term => ({ tag: "Ann", chk, val, typ });
export const Let = (nam: string, val: Term, bod: (x: Term) => Term): Term => ({ tag: "Let", nam, val, bod });
export const Def = (nam: string, val: Term, bod: (x: Term) => Term): Term => ({ tag: "Def", nam, val, bod });
export const Ref = (nam: string): Term => ({ tag: "Ref", nam });
export const Hol = (nam: string, ctx: Context, cap: List<Term>): Term => ({ tag: "Hol", nam, ctx, cap });

// A type context
export type Context = List<[string, Term]>;

// A book of definitions
export type Book = {[key: string]: {typ: Term, val: Term}};
export type Load = (key: string) => ({typ: Term, val: Term}) | null;
export type Fill = {[key: string]: Term};

// Checker
// -------

// Reduces to weak normal form
export function reduce(load: Load, term: Term, dep: number): Term {
  if (term.tag === "App") {
    var fun = reduce(load, term.fun, dep);
    if (fun.tag === "Lam") {
      return reduce(load, fun.bod(term.arg), dep);
    }
    if (fun.tag === "Hol") {
      return reduce(load, Hol(fun.nam, fun.ctx, push(term.arg, fun.cap)), dep);
    }
    return term;
  }
  if (term.tag === "Fix") {
    return reduce(load, term.bod(term), dep);
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
export function equal(fill: Fill | null, load: Load, a: Term, b: Term, dep: number): boolean {
  //console.log("eq?", show_term(a, dep));
  //console.log("...", show_term(b, dep));
  var eq = false;
  if (a.tag === "Var" && b.tag === "Var") {
    eq = a.val === b.val;
  } else if (a.tag === "Set" && b.tag === "Set") {
    eq = true;
  } else if (a.tag === "All" && b.tag === "All") {
    eq = equal(fill, load, a.inp, b.inp, dep) && equal(fill, load, a.bod(Var(a.nam, dep)), b.bod(Var(b.nam, dep)), dep+1);
  } else if (a.tag === "Lam" && b.tag === "Lam") {
    eq = equal(fill, load, a.bod(Var(a.nam, dep)), b.bod(Var(b.nam, dep)), dep+1);
  } else if (a.tag === "App" && b.tag === "App") {
    eq = equal(fill, load, a.fun, b.fun, dep) && equal(fill, load, a.arg, b.arg, dep);
  } else if (a.tag === "Fix" && b.tag === "Fix") {
    eq = equal(fill, load, a.typ, b.typ, dep) && equal(fill, load, a.bod(Var(a.nam, dep)), b.bod(Var(b.nam, dep)), dep + 1);
  } else if (a.tag === "Slf" && b.tag === "Slf") {
    eq = equal(fill, load, a.bod(Var(a.nam, dep)), b.bod(Var(b.nam, dep)), dep + 1);
  } else if (a.tag === "Ins" && b.tag === "Ins") {
    eq = equal(fill, load, a.val, b.val, dep);
  } else if (a.tag === "Ref" && b.tag === "Ref" && a.nam === b.nam) {
    eq = true;
  } else if (a.tag === "Hol" && b.tag === "Hol" && a.nam === b.nam) {
    eq = true;
  //} else if (a.tag === "Lam") {
    //eq = equal(fill, load, a, Lam(a.nam, x => App(b, x)), dep);
  //} else if (b.tag === "Lam") {
    //eq = equal(fill, load, Lam(b.nam, x => App(a, x)), b, dep);
  } else if (a.tag === "Hol") {
    if (fill) {
      fill_valued_hole(fill, load, a.nam, a.ctx, a.cap, b, dep);
      eq = true;
    } else {
      // This is needed because, on non-fill-mode, we need `(?H T) == (P T)` to
      // return true, and `(?H T) == (P F)` to return false. Since holes capture
      // arguments, we need to un-capture them and compare. FIXME: we probably
      // want to remove the 'cap' feature from holes, and just treat app holes.
      var b_cap = (function get_args(fun: Term): List<Term> {
        if (fun.tag === "App") {
          return push(fun.arg, get_args(fun.fun));
        } else {
          return Nil();
        }
      })(b);
      eq = (function compare(xs: List<Term>, ys: List<Term>): boolean {
        if (xs.tag === "Cons" && ys.tag === "Cons") {
          var head_eq = equal(fill, load, xs.head, ys.head, dep);
          var tail_eq = compare(xs.tail, ys.tail);
          return head_eq && tail_eq;
        }
        if (xs.tag === "Nil" && ys.tag === "Nil") {
          return true;
        }
        return false;
      })(a.cap, b_cap);
    }
  } else if (b.tag === "Hol") {
    return equal(fill, load, b, a, dep);
  }
  if (!eq) {
    var a2 = reduce(load, a, dep);
    if (a2 !== a) {
      return equal(fill, load, a2, b, dep);
    }
    var b2 = reduce(load, b, dep);
    if (b2 !== b) {
      return equal(fill, load, a, b2, dep);
    }
  }
  return eq;
}

// Evaluates a term to normal form.
export function normal(load: Load, term: Term, dep: number = 0): Term {
  var term = reduce(load, term, dep);
  switch (term.tag) {
    case "All": return All(term.nam, normal(load, term.inp, dep), x => normal(load, term.bod(x), dep+1));
    case "Lam": return Lam(term.nam, x => normal(load, term.bod(x), dep+1));
    case "App": return App(normal(load, term.fun, dep), normal(load, term.arg, dep));
    case "Fix": return Fix(term.nam, normal(load, term.typ, dep), x => normal(load, term.bod(x), dep+1));
    case "Ann": return normal(load, term.val, dep);
    case "Let": return normal(load, term.bod(term.val), dep);
    case "Def": return normal(load, term.bod(term.val), dep);
    default   : return term;
  }
}

// Infers the type of a term.
export function infer(fill: Fill, load: Load, val: Term, dep: number = 0): Term {
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
      return Hol(val.nam+"_T", val.ctx, val.cap);
    }
    case "Set": {
      return Set();
    }
    case "All": {
      check(fill, load, val.inp, Set(), true, dep);
      check(fill, load, val.bod(Ann(false, Var(val.nam, dep), val.inp)), Set(), true, dep+1);
      return Set();
    }
    case "Lam": {
      return All(val.nam,
        Hol(val.nam+"_I", Nil(), Nil()), x =>
        Hol(val.nam+"_O", Cons([val.nam,x], Nil()), Nil()));
    }
    case "App": {
      var fun_ty = infer(fill, load, val.fun, dep);
      var fun_ty = reduce(load, fun_ty, dep);
      //var fun_ty = fun_ty.tag === "Slf" ? fun_ty.bod(val.fun) : fun_ty;
      if (fun_ty.tag === "Hol") {
        var ctx = fun_ty.ctx;
        var cap = fun_ty.cap;
        var nam = fun_ty.nam;
        fun_ty = All(nam,
          Hol(nam+"_I", ctx, cap), x =>
          Hol(nam+"_O", Cons([nam,x], ctx), cap));
      }
      if (fun_ty.tag === "All") {
        check(fill, load, val.arg, fun_ty.inp, true, dep);
        return fun_ty.bod(val.arg);
      } else {
        console.log("- fun: " + show_term(val.fun, dep));
        console.log("- typ: " + show_term(fun_ty, dep));
        throw "NonFunApp";
      }
    }
    case "Fix": {
      return infer(fill, load, val.bod(Ann(false, Var(val.nam, dep), val.typ)), dep+1);
    }
    case "Ins": {
      var val_ty = reduce(load, infer(fill, load, val.val, dep), dep);
      if (val_ty.tag === "Slf") {
        return val_ty.bod(val);
      } else {
        throw "NonSlfIns";
      }
    }
    case "Slf": {
      check(fill, load, val.bod(Ann(false, Var(val.nam, dep), val)), Set(), true, dep);
      return Set();
    }
    case "Ann": {
      return check(fill, load, val.val, val.typ, val.chk, dep);
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
export function check(fill: Fill, load: Load, val: Term, tty: Term, chk: boolean, dep: number = 0): Term {
  //console.log("chk", show_term(val, dep));
  //console.log(" ::", show_term(tty, dep));
  var typ = reduce(load, tty, dep);
  //var typ = typ.tag === "Slf" ? typ.bod(val) : typ;
  if (!chk) {
    return typ;
  } else {
    if (val.tag === "Lam") {
      if (typ.tag === "All") {
        check(fill, load, val.bod(Ann(false, Var(val.nam, dep), typ.inp)), typ.bod(Ann(false, Var(typ.nam, dep), typ.inp)), chk, dep+1);
        return typ;
      } else {
        console.log("- ", show_term(val, dep));
        console.log("- ", show_term(typ, dep));
        throw "NonFunLam";
      }
    } else if (val.tag === "Ins") {
      if (typ.tag === "Slf") {
        check(fill, load, val.val, typ.bod(val), chk, dep);
        return typ;
      } else {
        throw "NonSlfIns";
      }
    } else if (val.tag === "Hol") {
      fill_typed_hole(fill, load, val.nam, val.ctx, val.cap, tty, dep);
      return typ;
    } else if (val.tag === "Let") {
      var val_typ = infer(fill, load, val.val, dep);
      check(fill, load, val.bod(Ann(false, val.val, val_typ)), typ, chk, dep + 1);
      return typ;
    } else if (val.tag === "Def") {
      check(fill, load, val.bod(val.val), typ, chk, dep + 1);
      return typ;
    } else {
      var inf = infer(fill, load, val, dep);
      var inf = reduce(load, inf, dep);
      //var inf = inf.tag === "Slf" ? inf.bod(val) : inf;
      if (!equal(fill, load, typ, inf, dep)) {
        var exp = show_term(typ, dep);
        var det = show_term(inf, dep);
        var msg = "TypeMismatch\n- expected: " + exp + "\n- detected: " + det;
        throw msg; 
      }
      return typ;
    }
  }
}

export function check_def(load: Load, name: string): string {
  try {
    var loaded = load(name);
    if (loaded !== null) {
      var {val, typ} = loaded;
      //console.log("\n\ncheck", show_def(name, val, typ));
      var fill : Fill = {};
      check(fill, load, val, typ, true);
      if (Object.keys(fill).length > 0) {
        var new_val  = subst_holes(fill, val);
        var new_typ  = subst_holes(fill, typ);
        var new_def  = {val: new_val, typ: new_typ};
        var new_load = (k: string) => k === name ? new_def : load(k);
        console.log("FILL: " + show_term(new_val));
        return check_def(new_load, name);
      } else {
        var val = cleanup(val);
        var typ = cleanup(typ);
        console.log("\x1b[32m✔ " + name + "\x1b[0m");
        //console.log(show_def(name, val, typ));
        //console.log(": " + show_term(normal(x=>null, typ)));
        //console.log("= " + show_term(normal(x=>null, val)));
        return show_def(name, val, typ);
      }
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
    return "⊥";
  }
}

export function check_book(book: Book) {
  for (var name in book) {
    check_def(x => book[x], name);
  }
}

// Auto-Fill
// ---------

// Fill a hole when its value is known (found by equality).
export function fill_valued_hole(fill: Fill, load: Load, nam: string, ctx: Context, cap: List<Term>, val: Term, dep: number) {
  //console.log("fill_valued_hole", show_term(Hol(nam, ctx, cap), dep), show_term(val, dep));
  
  // Replaces all sub-expressions that satisfy a 'rep' predicate in 'term'.
  function replace(rep: (x: Term) => Term | null, term: Term): Term {
    var replaced = rep(term);
    if (replaced) {
      return replaced;
    } else {
      switch (term.tag) {
        case "Var": return term;
        case "Set": return term;
        case "All": return All(term.nam, replace(rep, term.inp), x => replace(rep, term.bod(x)));
        case "Lam": return Lam(term.nam, x => replace(rep, term.bod(x)));
        case "App": return App(replace(rep, term.fun), replace(rep, term.arg));
        case "Fix": return Fix(term.nam, replace(rep, term.typ), x => replace(rep, term.bod(x)));
        case "Slf": return Slf(term.nam, x => replace(rep, term.bod(x)));
        case "Ins": return Ins(replace(rep, term.val));
        case "Ann": return Ann(term.chk, replace(rep, term.val), replace(rep, term.typ));
        case "Let": return Let(term.nam, replace(rep, term.val), x => replace(rep, term.bod(x)));
        case "Def": return Def(term.nam, replace(rep, term.val), x => replace(rep, term.bod(x)));
        case "Ref": return term;
        case "Hol": return fill[term.nam] ? subst_holes(fill, fill[term.nam]) : term;
      }
    }
  }
  // When a hole applied to arguments has a value, such as `(?H x y z ...) = F`,
  // then we can solidified it as `λX λY λZ F[x<-X][y<-Y][z<-Z]`. Note that, in
  // general, for this to work, the substitution must be performed on arbitrary
  // terms ('x', 'y', 'z'), rather than variables. For now, only variable
  // substitution is implemented.
  function solidify(cap: List<Term>, val: Term, dep: number): Term {
    switch (cap.tag) {
      case "Cons": {
        var arg = reduce(x=>null, cap.head, dep);
        if (arg.tag === "Var") {
          var idx = arg.val;
          return Lam("X", x => {
            var chk = (v: Term) => v.tag === "Var" && v.val === idx;
            var neo = replace(v => chk(v) ? x : null, val);
            return solidify(cap.tail, neo, dep+1);
          });
        } else {
          throw "Can't invert non-var predicate argument.";
        }
      }
      case "Nil": {
        return val;
      }
    }
  }

  var a = normal(x=>null, Hol(nam,ctx,cap), dep);
  var b = normal(x=>null, val, dep);
  console.log("NOTE: " + show_term(a,dep) + " = " + show_term(b,dep));

  fill[nam] = solidify(cap, val, dep);
  console.log("DONE: " + nam + " = " + show_term(fill[nam], dep));
}

// Fill a hole when its type is known (found by inference).
export function fill_typed_hole(fill: Fill, load: Load, nam: string, ctx: Context, cap: List<Term>, typ: Term, dep: number) {
  //console.log("fill_typed_hole", nam);

  // Eta-Expand: when a hole has a ∀ type, it can be expanded as a λ.
  var typ_nf = reduce(load, typ, dep);
  if (typ_nf.tag === "All") {
    var typ_nam = typ_nf.nam; // line needed due to TypeScript bug 🙄
    fill[nam] = Lam(typ_nam, x => Hol(nam+"_0", Cons([typ_nam,x], ctx), cap));
    return;
  }

  // Select: when a hole can't be expanded, we try to select a variable on
  // context that satisfies the goal. To do so, we check, for each context
  // variable, if its unrolled type is equal to the goal. The unrolled type of a
  // forall is obtained by applying the context variable to holes. For example:
  // If a context variable is `f : ∀(x: A) ∀(y: B) (P x y)`, then its expanded
  // value is `((f ?x) ?y)`, where `?x` and `?y` are fresh holes, and its
  // expanded type is `(P ?x ?y)`, which can then be checked against the goal.
  var hol_nam = nam;
  var hol_ctx = ctx;
  var hol_cap = cap;
  var candidates = [];
  console.log("GOAL: " + show_term(typ, dep));
  (function find(ctx: Context, typ: Term, dep: number, idx: number) {
    switch (ctx.tag) {
      case "Cons": {
        var ctx_nam = ctx.head[0];
        var ctx_ann = ctx.head[1];
        if (ctx_ann.tag === "Ann") {
          var ctx_val = ctx_ann.val; // FIXME: should be part of context?
          var ctx_typ = ctx_ann.typ;
          var [fill_val, fill_typ] =
            (function unroll(load: Load, var_val: Term, var_typ: Term, dep: number, idx: number): [Term,Term] {
              var var_typ = reduce(load, var_typ, dep);
              if (var_typ.tag === "All") {
                var fresh_hol_arg = Hol(hol_nam+"_"+idx, hol_ctx, hol_cap);
                return unroll(load, App(var_val, fresh_hol_arg), var_typ.bod(fresh_hol_arg), dep+1, idx+1);
              }
              if (var_typ.tag === "Slf") {
                return unroll(load, Ins(var_val), var_typ.bod(var_val), dep+1, idx);
              }
              return [var_val, var_typ];
            })(load, Ann(false, ctx_val, ctx_typ), ctx_typ, dep, 0);
          var is_valid = equal(null, load, fill_typ, typ, dep);
          console.log("TRY?: " + show_term(fill_val, dep) + " :: " + show_term(fill_typ, dep) + " ... " + is_valid);
          if (is_valid) {
            candidates.push([fill_val, fill_typ]);
          }
        }
        find(ctx.tail, typ, dep, idx+1);
        return;
      }
      case "Nil": {
        return;
      }
    }
  })(ctx, typ, dep, 0);

  // FIXME: this is using the first candidate, in order to avoid re-using
  // variables (since our heuristic is to try consuming variables linearly).
  // This isn't correct though. To make this right, we need to track variables
  // usage, and avoid selecting used variables from context.
  if (candidates.length > 0) {
    var chosen = candidates[0];
    fill[nam] = Ann(true, chosen[0], chosen[1]);
    return;
  }

  console.log("HOLE: " + nam);
  console.log("GOAL: " + show_term(normal(x => null, typ, dep), dep));
  var ctx_str = fold(ctx, ([nam,val],str) => str + "- " + show_ann(val, dep) + "\n", "").trim();
  if (ctx_str) {
    console.log(ctx_str);
  }
}

// Replaces all filled holes in a term.
export function subst_holes(fill: Fill, term: Term, dep: number = 0): Term {
  //console.log("subst_holes", show_term(term, 0));
  switch (term.tag) {
    case "Var": return term;
    case "Set": return term;
    case "All": return All(term.nam, subst_holes(fill, term.inp, dep), x => subst_holes(fill, term.bod(x), dep+1));
    case "Lam": return Lam(term.nam, x => subst_holes(fill, term.bod(x), dep));
    case "App": return App(subst_holes(fill, term.fun, dep), subst_holes(fill, term.arg, dep));
    case "Fix": return Fix(term.nam, subst_holes(fill, term.typ, dep), x => subst_holes(fill, term.bod(x), dep+1));
    case "Slf": return Slf(term.nam, x => subst_holes(fill, term.bod(x), dep));
    case "Ins": return Ins(subst_holes(fill, term.val, dep));
    case "Ann": return Ann(term.chk, subst_holes(fill, term.val, dep), subst_holes(fill, term.typ, dep));
    case "Let": return Let(term.nam, subst_holes(fill, term.val, dep), x => subst_holes(fill, term.bod(x), dep+1));
    case "Def": return Def(term.nam, subst_holes(fill, term.val, dep), x => subst_holes(fill, term.bod(x), dep+1));
    case "Ref": return term;
    case "Hol": {
      var filled = fill[term.nam];
      if (filled) {
        return subst_holes(fill, (function args(cap: List<Term>, filled: Term): Term {
          if (cap.tag === "Cons") {
            return args(cap.tail, App(filled, cap.head));
          } else {
            return filled;
          }
        })(term.cap, filled), dep);
      } else {
        return term;
      }
    }
  }
}

// Removes unecessary noise when filling holes.
export function cleanup(term: Term, dep: number = 0): Term {
  switch (term.tag) {
    case "All": return All(term.nam, cleanup(term.inp, dep), x => cleanup(term.bod(x), dep+1));
    case "Lam": return Lam(term.nam, x => cleanup(term.bod(x), dep+1));
    case "App": return App(cleanup(term.fun, dep), cleanup(term.arg, dep));
    case "Fix": return Fix(term.nam, cleanup(term.typ, dep), x => cleanup(term.bod(x), dep+1));
    case "Ann": return cleanup(term.val, dep);
    case "Let": return cleanup(term.bod(term.val), dep);
    case "Def": return cleanup(term.bod(term.val), dep);
    default   : return term;
  }
}


// Syntax
// ------

export function cut(str: string): string {
  return str[0] === "(" ? str.slice(1, -1) : str;
}

export function show_term(term: Term, dep: number = 0): string {
  switch (term.tag) {
    case "Var": return term.nam;// + "\x1b[2m%" + term.val + "\x1b[0m";
    case "Set": return "*";
    case "All": return "∀(" + term.nam + ":"+show_term(term.inp, dep)+") " + show_term(term.bod(Var(term.nam, dep)), dep + 1);
    case "Lam": return "λ" + term.nam + " " + show_term(term.bod(Var(term.nam, dep)), dep + 1);
    case "App": return "(" + cut(show_term(term.fun, dep)) + " " + show_term(term.arg, dep) + ")";
    case "Fix": return "μ(" + term.nam + ":" + show_term(term.typ, dep) + ") " + show_term(term.bod(Var(term.nam, dep)), dep+1);
    case "Slf": return "$" + term.nam + " " + show_term(term.bod(Var(term.nam, dep)), dep+1);
    case "Ins": return "~" + show_term(term.val, dep);
    case "Ann": return "{" + show_term(term.val, dep) + ":" + show_term(term.typ, dep) + "}";
    case "Let": return "let " + term.nam + " = " + show_term(term.val, dep) + " " + show_term(term.bod(Var(term.nam, dep)), dep + 1);
    case "Def": return "def " + term.nam + " = " + show_term(term.val, dep) + " " + show_term(term.bod(Var(term.nam, dep)), dep + 1);
    case "Ref": return term.nam;
    case "Hol": return "(" + term.nam + fold(term.cap, (val,str) => " " + show_term(val, dep) + str, "") + ")";
  }
}

export function show_ann(ann: Term, dep: number): string {
  if (ann.tag === "Ann") {
    return show_term(ann.val, dep) + ": " + show_term(normal(x => null, ann.typ, dep), dep);
  } else {
    return show_term(ann, dep);
  }
}

export function show_def(name: string, val: Term, typ: Term) { 
  var typ_str = (function show_typ(term: Term, dep: number = 0): string {
    var tab = dep === 0 ? "\n: " : "\n  ";
    if (term.tag === "All") {
      return tab + "∀("+term.nam+": "+show_term(term.inp, dep) + ") "+show_typ(term.bod(Var(term.nam, dep)), dep+1);
    }
    return tab + show_term(term, dep);
  })(typ);
  var val_str = "\n= " + (function show_val(term: Term, dep: number = 0): string {
    if (term.tag === "Lam") {
      return "λ"+term.nam+" "+show_val(term.bod(Var(term.nam,dep)),dep+1);
    }
    return (dep > 0 ? "\n  " : "") + show_term(term, dep);
  })(val);
  return name + typ_str + val_str;
}

export function show_book(book: Book): string {
  var text = "";
  for (var name in book) {
    text += show_def(name, book[name].val, book[name].typ);
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
    return [code, ctx => All(nam, typ(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // LAM: `λx f`
  if (code[0] === "λ") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(nam, x => bod(Cons([nam,x], ctx)))];
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
  // FIX: `μ(x: T) f`
  if (code[0] === "μ") {
    var [code, nam] = parse_name(code.slice(2));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, __ ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => Fix(nam, typ(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // SET: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => Set()];
  }
  // SLF: `$x T`
  if (code[0] === "$") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Slf(nam, x => bod(Cons([nam, x], ctx)))];
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
    return [code, ctx => Let(nam, val(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // DEF: `def x = val; body`
  if (code.slice(0, 4) === "def ") {
    var [code, nam] = parse_name(code.slice(4));
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    var [code, bod] = parse_term(code);
    return [code, ctx => Def(nam, val(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // HOL: `?` `name`
  if (code[0] === "?") {
    var [code, nam] = parse_name(code.slice(1));
    return [code, ctx => Hol("?"+nam, ctx, Nil())];
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

import * as fs from 'fs';

export function loader(book: Book) {
  return function load(name: string) {
    if (!book[name]) {
      try {
        var code = fs.readFileSync(name+".tl", 'utf8');
      } catch (e) {
        throw "Couldn't load '"+name+"'.";
      }
      var defs = parse_book(code);
      for (var name in defs) {
        book[name] = {typ: defs[name].typ, val: defs[name].val};
      }
    }
    return book[name];
  }
}
