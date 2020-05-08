var {
  Var, Ref, Typ, All,
  Lam, App, Let, Ann,
  Loc, Ext, Nil,
  reduce,
  normalize,
  Err,
  typeinfer,
  typecheck,
  equal,
  find,
} = require("./FormalityCore.js");

// Parsing
// =======

// Is this a space character?
function is_space(chr) {
  return chr === " " || chr === "\t" || chr === "\n";
};

// Is this a name-valid character?
function is_name(chr) {
  var val = chr.charCodeAt(0);
  return (val >= 46 && val < 47)   // .
      || (val >= 48 && val < 58)   // 0-9
      || (val >= 65 && val < 91)   // A-Z
      || (val >= 95 && val < 96)   // _
      || (val >= 97 && val < 123); // a-z
};

// Returns the first valid parser
function choose(fns, err) {
  for (var i = 0; i < fns.length; ++i) {
    var parsed = fns[i]();
    if (parsed !== null) {
      return parsed;
    }
  };
  return null;
};

// Chains two parsers
function chain(a, fn) {
  return a ? fn(a[0], a[1]) : null;
};

// Drop characters while a condition is met.
function drop_while(cond, code, indx) {
  while (indx < code.length && cond(code[indx])) {
    indx++;
  };
  return indx;
};

// Drop spaces
function drop_spaces(code, indx) {
  return drop_while(is_space, code, indx);
};

// Drops spaces and comments
function next(code, indx) {
  while (true) {
    indx = drop_spaces(code, indx);
    if (code[indx] === "/") {
      indx = drop_while(c => c !== "\n", code, indx);
    } else if (code[indx] === "#") {
      indx = drop_while(c => c !== "#", code, indx + 1) + 1;
    } else {
      break;
    }
  };
  return indx;
};

function parse_error(code, indx, expected, err) {
  if (err) {
    var expec = expected.replace(/\n/g, "<newline>");
    var found = (code[indx] || "<end-of-file>").replace(/\n/g, "<newline>");
    throw ( "Parse error: expected "+expec+", found '"+found+"'.\n"
          + highlight_code(code, indx, indx+1));
  } else {
    return null;
  }
};

// Drops spaces and parses an exact string
function parse_txt(code, indx, str, err = false) {
  if (str.length === 0) {
    return [indx, str];
  } else if (indx < code.length && code[indx] === str[0]) {
    return parse_txt(code, indx+1, str.slice(1), err);
  } else {
    return parse_error(code, indx, "'"+str+"'", err);
  };
};

// Parses one of two strings
function parse_one(code, indx, ch0, ch1, err) {
  return choose([
    () => chain(parse_txt(code, indx, ch0, false), (indx,_) => [indx, false]),
    () => chain(parse_txt(code, indx, ch1, err  ), (indx,_) => [indx, true]),
  ]);
};

// Parses an optional string
function parse_opt(code, indx, str, err) {
  return choose([
    () => chain(parse_txt(code, indx, str, false), (indx,_) => [indx, true]),
    () => [indx, false],
  ]);
};

// Parses a valid name, non-empty
function parse_nam(code, indx, size = 0, err = false) {
  if (indx < code.length && is_name(code[indx])) {
    var parsed_nam = parse_nam(code, indx + 1, size + 1, err);
    return parsed_nam ? [parsed_nam[0], code[indx] + parsed_nam[1]] : null;
  } else if (size > 0) {
    return [indx, ""];
  } else {
    return parse_error(code, indx, "a name", err);
  }
};

// Parses a parenthesis, `(<term>)`
function parse_par(code, indx, err = false) {
  return (
    chain(parse_txt(code, next(code, indx), "(", false), (indx, skip) =>
    chain(parse_trm(code, indx, err),                    (indx, term) =>
    chain(parse_txt(code, next(code, indx), ")", err),   (indx, skip) =>
    [indx, term]))));
};

// Parses a dependent function type, `(<name> : <term>) -> <term>`
function parse_all(code, indx, err = false) {
  var from = next(code, indx);
  return (
    chain(parse_nam(code, next(code, indx), 1, false),              (indx, self) =>
    chain(parse_one(code, indx, "(", "<", false),                   (indx, eras) =>
    chain(parse_nam(code, next(code, indx), 1, false),              (indx, name) =>
    chain(parse_txt(code, next(code, indx), ":", false),            (indx, skip) =>
    chain(parse_trm(code, indx, err),                               (indx, bind) =>
    chain(parse_txt(code, next(code, indx), eras ? ">" : ")", err), (indx, skip) =>
    chain(parse_txt(code, next(code, indx), "->", err),             (indx, skip) =>
    chain(parse_trm(code, indx, err),                               (indx, body) =>
    [indx, xs => {
      var tbind = bind(xs);
      var tbody = (s,x) => body(Ext([name,x],Ext([self,s],xs)));
      return Loc(from, indx, All(eras, self, name, tbind, tbody));
    }])))))))));
};

// Parses a dependent function value, `(<name>) => <term>`
function parse_lam(code, indx, err = false) {
  var from = next(code, indx);
  return (
    chain(parse_one(code, next(code, indx), "(", "<", false),         (indx, eras) =>
    chain(parse_nam(code, next(code, indx), 1, false),                (indx, name) =>
    chain(parse_txt(code, next(code, indx), eras ? ">" : ")", false), (indx, skip) =>
    chain(parse_trm(code, indx, err),                                 (indx, body) =>
    [indx, xs => {
      var tbody = (x) => body(Ext([name,x],xs));
      return Loc(from, indx, Lam(eras, name, tbody));
    }])))));
};

// Parses a local definition, `let x = val; body`
function parse_let(code, indx, err = false) {
  var from = next(code, indx);
  return (
    chain(parse_txt(code, next(code, indx), "let ", false), (indx, skip) =>
    chain(parse_nam(code, next(code, indx), 0, err),        (indx, name) =>
    chain(parse_txt(code, next(code, indx), "=", err),      (indx, skip) =>
    chain(parse_trm(code, indx, err),                       (indx, expr) =>
    chain(parse_opt(code, indx, ";", err),                  (indx, skip) =>
    chain(parse_trm(code, indx, err),(indx, body) =>
    [indx, xs => {
      var tbody = (x) => body(Ext([name,x],xs));
      return Loc(from, indx, Let(name, expr(xs), tbody));
    }])))))));
};

// Parses a monadic application, `use a = x; y` ~> `x((a) y)`
function parse_use(code, indx, err = false) {
  var from = next(code, indx);
  return (
    chain(parse_txt(code, next(code, indx), "use "), (indx, skip) =>
    chain(parse_nam(code, next(code, indx), 0, err), (indx, name) =>
    chain(parse_txt(code, next(code, indx), "="),    (indx, skip) =>
    chain(parse_trm(code, indx, err),                (indx, func) =>
    chain(parse_trm(code, indx, err),                (indx, body) =>
    [indx, xs => {
      var tbody = (x) => body(Ext([name,x],xs));
      return Loc(from, indx, App(false, func(xs), Lam(false, name, tbody)));
    }]))))));
};

// Parses the type of types, `Type`
function parse_typ(code, indx, err = false) {
  var from = next(code, indx);
  return (
    chain(parse_txt(code, next(code, indx), "Type", false), (indx, skip) =>
    [indx, xs => Loc(from, indx, Typ())]));
};

// Parses variables, `<name>`
function parse_var(code, indx, err = false) {
  var from = next(code, indx);
  return chain(parse_nam(code, next(code, indx), 0, false), (indx, name) => {
    return [indx, xs => {
      if (name.length === 0) {
        return parse_error(code, indx, "a variable", err);
      } else {
        var got = find(xs, (x,i) => x[0] === name);
        return Loc(from, indx, got ? got.value[1] : Ref(name));
      }
    }];
  });
};

// Parses a single-line application, `<term>(<term>)`
function parse_app(code, indx, from, func, err) {
  return (
    chain(parse_one(code, indx, "(", "<", false),                   (indx, eras) =>
    chain(parse_trm(code, indx, err),                               (indx, argm) =>
    chain(parse_txt(code, next(code, indx), eras ? ">" : ")", err), (indx, skip) =>
    [indx, xs => Loc(from, indx, App(eras, func(xs), argm(xs)))]))));
};

// Parses a multi-line application, `<term> | <term>;`
function parse_pip(code, indx, from, func, err) {
  return (
    chain(parse_txt(code, next(code, indx), "|", false), (indx, skip) =>
    chain(parse_trm(code, indx, err),                    (indx, argm) =>
    chain(parse_txt(code, next(code, indx), ";", err),   (indx, skip) =>
    [indx, xs => Loc(from, indx, App(false, func(xs), argm(xs)))]))));
};

// Parses a non-dependent function type, `<term> -> <term>`
function parse_arr(code, indx, from, bind, err) {
  return (
    chain(parse_txt(code, next(code, indx), "->", false), (indx, skip) =>
    chain(parse_trm(code, indx, err),                     (indx, body) =>
    [indx, xs => {
      var tbind = bind(xs);
      var tbody = (s,x) => body(Ext(["",x],Ext(["",s],xs)));
      return Loc(from, indx, All(false, "", "", tbind, tbody));
    }])));
};

// Parses an annotation, `<term> :: <term>`
function parse_ann(code, indx, from, expr, err) {
  return (
    chain(parse_txt(code, next(code, indx), "::", false), (indx, skip) =>
    chain(parse_trm(code, indx, err),                     (indx, type) =>
    [indx, xs => Loc(from, indx, Ann(false, expr(xs), type(xs)))])));
};

// Turns a character into a term
function make_chr(chr) {
  var cod = chr.charCodeAt(0);
  var chr = Ref("Char.new");
  for (var i = 15; i >= 0; --i) {
    chr = App(false, chr, Ref((cod >>> i) & 1 ? "Bit.1" : "Bit.0"));
  };
  return chr;
};

// Parses a char literal, 'f'
function parse_chr(code, indx, err) {
  var from = next(code, indx);
  return (
    chain(parse_txt(code, next(code, indx), "'"), (indx, skip) =>
    chain([indx+1, code[indx]],                   (indx, clit) =>
    chain(parse_txt(code, next(code, indx), "'"), (indx, skip) =>
    [indx, xs => Loc(from, indx, Ann(true, make_chr(clit), Ref("Char")))]
    ))));
};

// Parses a string literal, "foo"
function parse_str(code, indx, err) {
  var from = next(code, indx);
  return (
    chain(parse_txt(code, next(code, indx), "\""), (indx, skip) =>
    chain((function go(indx, slit) {
      if (indx < code.length) {
        if (code[indx] !== "\"") {
          var chr = make_chr(code[indx]);
          var [indx, slit] = go(indx + 1, slit);
          return [indx, App(false, App(false, Ref("String.cons"), chr), slit)];
        } else {
          return [indx+1, Ref("String.nil")];
        }
      } else if (err) {
        parse_error(code, indx, "string literal", true);
      } else {
        return null;
      }
    })(indx), (indx, slit) =>
    [indx, xs => Loc(from, indx, Ann(true, slit, Ref("String")))])));
};

// Parses a list literal, `[a, b, c]`
function parse_lst(code, indx, err) {
  var from = next(code, indx);
  function parse_els(code, indx, type) {
    return chain(parse_opt(code, next(code, indx), "]", false), (indx, done) => {
      if (done) {
        return [indx, xs => App(true, Ref("List.nil"), type(xs))];
      } else {
        return (
          chain(parse_trm(code, next(code, indx), err),        (indx, elem) =>
          chain(parse_opt(code, next(code, indx), ",", false), (indx, skip) =>
          chain(parse_els(code, next(code, indx), type),       (indx, tail) =>
          [indx, xs => App(false, App(false, App(true, Ref("List.cons"), type(xs)), elem(xs)), tail(xs))]))));
      }
    });
  };
  return (
    chain(parse_txt(code, next(code, indx), "[", false), (indx, skip) =>
    chain(parse_trm(code, next(code, indx), err),        (indx, type) =>
    chain(parse_txt(code, next(code, indx), ";", err),   (indx, skip) =>
    chain(parse_els(code, next(code, indx), type),       (indx, list) =>
    [indx, xs => Loc(from, indx, list(xs))])))));
};

// Parses a term
function parse_trm(code, indx = 0, err) {
  var indx = next(code, indx);
  var from = indx;

  // Parses the base term, trying each variant once
  var base_parse = choose([
    () => parse_all(code, indx, err),
    () => parse_lam(code, indx, err),
    () => parse_let(code, indx, err),
    () => parse_use(code, indx, err),
    () => parse_par(code, indx, err),
    () => parse_typ(code, indx, err),
    () => parse_chr(code, indx, err),
    () => parse_str(code, indx, err),
    () => parse_lst(code, indx, err),
    () => parse_var(code, indx, err),
  ], err);

  if (!base_parse && err) {
    parse_error(code, indx, "a term", err);
  } else {
    // Parses postfix extensions, trying each variant repeatedly
    var post_parse = base_parse;
    while (true) {
      var [indx, term] = post_parse;
      post_parse = choose([
        () => parse_app(code, indx, from, term, err),
        () => parse_pip(code, indx, from, term, err),
        () => parse_arr(code, indx, from, term, err),
        () => parse_ann(code, indx, from, term, err),
      ], err);
      if (!post_parse) {
        return base_parse;
      } else {
        base_parse = post_parse;
      }
    }
  }

  return null;
};

// Parses a defs
function parse(code, indx = 0) {
  var defs = {};
  function parse_defs(code, indx) {
    var indx = next(code, indx);
    if (indx === code.length) {
      return;
    } else {
      chain(parse_nam(code, next(code, indx), 0, true),           (indx, name) =>
      chain(parse_txt(code, next(code, indx), ":", true),         (indx, skip) =>
      chain(parse_trm(code, next(code, indx), true),              (indx, type) =>
      chain(parse_opt(code, drop_spaces(code, indx), "//loop//"), (indx, loop) =>
      chain(parse_opt(code, drop_spaces(code, indx), "//prim//"), (indx, prim) =>
      chain(parse_opt(code, drop_spaces(code, indx), "//data//"), (indx, data) =>
      chain(parse_trm(code, next(code, indx), true),              (indx, term) => {
        defs[name] = {type: type(Nil()), term: term(Nil()), meta: {loop,prim,data}};
        parse_defs(code, indx);
      })))))));
    };
  }
  parse_defs(code, indx);
  return defs;
};

// Stringification
// ===============

function fold(list, nil, cons) {
  switch (list.ctor) {
    case "Nil": return nil;
    case "Ext": return cons(list.head, fold(list.tail, nil, cons));
  }
};

function unloc(term) {
  switch (term.ctor) {
    case "Var": return term;
    case "Ref": return term;
    case "Typ": return term;
    case "All": return All(term.eras, term.self, term.name, unloc(term.bind), (s, x) => unloc(term.body(s, x)));
    case "Lam": return Lam(term.eras, term.name, x => unloc(term.body(x)));
    case "App": return App(term.eras, unloc(term.func), unloc(term.argm));
    case "Let": return Let(term.name, unloc(term.expr), x => unloc(term.body(x)));
    case "Ann": return Ann(term.done, unloc(term.expr), unloc(term.type));
    case "Loc": return unloc(term.expr);
  };
};

// Stringifies a character literal
function stringify_chr(chr) {
  var val = 0;
  for (var i = 0; i < 16; ++i) {
    if (chr.ctor === "App" && chr.argm.ctor === "Ref") {
      if (chr.argm.name === "Bit.0") {
        val = val;
        chr = chr.func;
      } else if (chr.argm.name === "Bit.1") {
        val = val | (1 << i);
        chr = chr.func;
      } else {
        return null;
      }
    } else {
      return null;
    }
  };
  if (chr.ctor === "Ref" && chr.name === "Char.new") {
    return String.fromCharCode(val);
  } else {
    return null;
  };
};

// Stringifies a string literal
function stringify_str(term) {
  if (term.ctor === "Ref" && term.name === "String.nil") {
    return "";
  } else if (term.ctor === "App"
    && term.func.ctor === "App"
    && term.func.func.ctor === "Ref"
    && term.func.func.name === "String.cons") {
    var chr = stringify_chr(term.func.argm);
    if (chr !== null) {
      return chr + stringify_str(term.argm);
    } else {
      return null;
    }
  }
};

function match(pattern, term, ret = {}) {
  if (typeof pattern === "string" && pattern[0] === "$") {
    ret[pattern.slice(1)] = term;
    return ret;
  } else if (typeof pattern === "object" && typeof term === "object") {
    for (var key in pattern) {
      if (!match(pattern[key], term[key], ret)) {
        return null;
      }
    }
    return ret;
  } else if (typeof pattern === "string" && typeof term === "string") {
    return pattern === term ? ret : null;
  } else if (typeof pattern === "boolean" && typeof term === "boolean") {
    return pattern === term ? ret : null;
  } else if (typeof pattern === "number" && typeof term === "number") {
    return pattern === term ? ret : null;
  } else {
    return null;
  }
};

function matching(term, patterns) {
  for (var [pattern, then] of patterns) {
    var got = match(pattern, term);
    if (got) {
      return then(got);
    };
  };
  return null;
};

// List.cons<T>(a)(List.cons<T>(b)(List.nil<T>))
function stringify_lst(term, type = null, vals = Nil()) {
  var cons = App(false, App(false, App(true, Ref("List.cons"), "$type"), "$head"), "$tail");
  var nil  = App(true, Ref("List.nil"), "$type");
  return matching(term, [
    [cons, ({type, head, tail}) => {
      return stringify_lst(tail, type, Ext(head, vals));
    }],
    [nil, ({type}) => {
      return "["
        + stringify_trm(type) + ";"
        + (vals.ctor === "Nil" ? "" : " ")
        + fold(vals, b=>"", (h,t) => b => (b ? "" : ", ")
        + stringify_trm(h)+t(0))(1)
        + "]";
    }]
  ]);
};

function stringify_run(term) {
  if (term.ctor === "Lam" && term.name === "strnil") {
    try {
      term = to_low_order(term);
//      console.log(term);
      term = term.body.body;
      var str = "";
      while (term.ctor !== "Var") {
        var val = 0;
        var chr = term.func.argm.body.argm;
        for (var i = 0; i < 16; ++i) {
          chr = chr.body.body.body;
          if (chr.func.indx === 0) {
            val = val | (1 << i);
          }
          chr = chr.argm;
        }
        term = term.argm.body.body;
        str += String.fromCharCode(val);
      }
      return "\""+str+"\"";
    } catch (e) {
      return null;
    }
  }
  return null;
};


function to_low_order(term, depth = 0) {
  switch (term.ctor) {
    case "Var":
      return Var(depth - term.indx - 1, term.locs);
    case "Ref":
      return Ref(term.name, term.locs);
    case "Typ":
      return Typ();
    case "All":
      var eras = term.eras;
      var self = term.self;
      var name = term.name;
      var bind = to_low_order(term.bind(Var(depth)), depth + 1);
      var body = to_low_order(term.body(Var(depth), Var(depth+1)), depth + 2);
      var locs = term.locs;
      return All(eras, self, name, bind, body, locs);
    case "Lam":
      var name = term.name;
      var body = to_low_order(term.body(Var(depth)), depth + 1);
      var locs = term.locs;
      return Lam(false, name, body, locs);
    case "App":
      var func = to_low_order(term.func, depth);
      var argm = to_low_order(term.argm, depth);
      var locs = term.locs;
      return App(false, func, argm, locs);
    case "Let":
      var name = term.name;
      var expr = to_low_order(term.expr, depth);
      var body = to_low_order(term.body(Var(depth)), depth + 1);
      var locs = term.locs;
      return Let(name, expr, body, locs);
    case "Ann":
      throw "Unreachable.";
  }
};

// Stringifies a term
function stringify_trm(term) {
  var lit;
  if (lit = stringify_chr(term)) {
    return "'"+lit+"'";
  } else if (lit = stringify_str(term)) {
    return "\""+lit+"\"";
  } else if (lit = stringify_lst(term)) {
    return lit;
  } else if (lit = stringify_run(term)) {
    return lit;
  } else {
    switch (term.ctor) {
      case "Var":
        return term.indx.split("#")[0];
      case "Ref":
        return term.name;
      case "Typ":
        return "Type";
      case "All":
        var self = term.self;
        var lpar = term.name === "" ? "" : (term.eras ? "<" : "(");
        var name = term.name;
        var colo = term.name === "" ? "" : ": ";
        var bind = stringify_trm(term.bind);
        var rpar = term.name === "" ? "" : (term.eras ? ">" : ")");
        var body = stringify_trm(term.body(Var(self+"#"), Var(name+"#")));
        return self+lpar+name+colo+bind+rpar+" -> "+body;
      case "Lam":
        var name = term.name;
        var lpar = term.eras ? "<" : "(";
        var body = stringify_trm(term.body(Var(name+"#")));
        var rpar = term.eras ? ">" : ")";
        return lpar+name+rpar+" "+body;
      case "App":
        var func = stringify_trm(term.func);
        var lpar = term.eras ? "<" : "(";
        var argm = stringify_trm(term.argm);
        var rpar = term.eras ? ">" : ")";
        if (func[0] === "(") {
          return "("+func+")"+lpar+argm+rpar;
        } else {
          return func+lpar+argm+rpar;
        }
      case "Let":
        var name = term.name;
        var expr = stringify_trm(term.expr);
        var body = stringify_trm(term.body(Var(name+"#")));
        return "let "+name+" = "+expr+"; "+body;
      case "Ann":
        if (term.done) {
          return stringify_trm(term.expr);
        } else {
          var expr = stringify_trm(term.expr);
          var type = stringify_trm(term.type);
          return expr+" :: "+type;
        }
      case "Loc":
        var expr = stringify_trm(term.expr);
        return expr;
    }
  }
};

// Stringifies a term
function stringify(term) {
  return stringify_trm(unloc(term));
};

// Stringifies a context
function stringify_ctx(ctx, text = "") {
  switch (ctx.ctor) {
    case "Ext":
      var name = ctx.head.name;
      var type = stringify(ctx.head.type, ctx.tail);
      var text = "- " + name + " : " + type + "\n" + text;
      return stringify_ctx(ctx.tail, text);
      return ;
    case "Nil":
      return text;
  };
};

// Stringifies all terms of a defs
function stringify_defs(defs) {
  var text = "";
  for (var name in defs) {
    var type = stringify(defs[name].type, Nil());
    var term = stringify(defs[name].term, Nil());
    text += name + " : " + type + "\n  " + term + "\n\n";
  }
  return text;
};

// Errors
// ======

function highlight_code(code, from, to) {
  var lines = [""];
  var from_line = 0;
  var to_line = Infinity;
  var err_line = null;
  lines.push("\x1b[2m     1| \x1b[0m");
  for (var i = 0; i < code.length + 1; ++i) {
    if (code[i] === "\n") {
      var line_num_str = ("      "+(lines.length)).slice(-6);
      lines.push("\x1b[2m" + line_num_str + "| \x1b[0m");
    } else {
      var chr = code[i] || "<eof>";
      if (from <= i && i < to) {
        if (err_line === null) {
          err_line = lines.length - 1;
        }
        var chr = "\x1b[4m\x1b[31m" + chr + "\x1b[0m";
      } else {
        var chr = "\x1b[2m" + chr + "\x1b[0m";
      }
      lines[lines.length - 1] += chr;
    };
    if (i === from) {
      from_line = lines.length - 1;
    };
    if (i === to) {
      to_line = lines.length - 1;
    };
  };
  from_line = Math.max(from_line - 4, 1);
  to_line = Math.min(to_line + 3, lines.length - 1);
  err_line = err_line || (lines.length - 2);
  var err = "On line " + err_line + ":\n";
  var err = err + lines.slice(from_line, to_line).join("\n");
  return err;
};

function stringify_err(err, code) {
  var index = 0;
  if (!err.ctx) {
    return "Undecidable.";
  } else {
    var str = "";
    str += err.msg+"\n";
    if (err.ctx.ctor !== "Nil") {
      str += "With context:\n";
      str += "\x1b[2m"+stringify_ctx(err.ctx)+"\x1b[0m";
    };
    if (err.loc && code) {
      str += highlight_code(code, err.loc.from, err.loc.upto);
    };
  };
  return str;
};

module.exports = {
  is_space,
  is_name,
  choose,
  chain,
  drop_while,
  drop_spaces,
  next,
  parse_error,
  parse_txt,
  parse_one,
  parse_opt,
  parse_nam,
  parse_par,
  parse_all,
  parse_lam,
  parse_let,
  parse_use,
  parse_typ,
  parse_var,
  parse_app,
  parse_pip,
  parse_arr,
  parse_ann,
  make_chr,
  parse_chr,
  parse_str,
  parse_trm,
  parse,
  stringify_chr,
  stringify_str,
  stringify,
  stringify_ctx,
  stringify_defs,
  highlight_code,
  stringify_err,
};
