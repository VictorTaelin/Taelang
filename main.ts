#!/usr/bin/env ts-node

import * as T from './taelang';
import * as fs from 'fs';

var BOOK : T.Book = {};

function load(name: string) {
  if (!BOOK[name]) {
    try {
      var code = fs.readFileSync(name+".tl", 'utf8');
    } catch (e) {
      throw "Couldn't load '"+name+"'.";
    }
    var def  = T.parse_def(code)[1];
    if (name !== def.nam) {
      throw "Incorrect definition name.\nExpected: ${name}\nDetected: ${def.nam}";
    }
    BOOK[name] = {typ: def.typ, val: def.val};
  }
  return BOOK[name];
}

const args = process.argv.slice(2);
const func = args[0];
const name = args[1];

switch (func) {
  case "check": {
    T.check_one(load, name);
    break;
  }
  case "normalize": {
    const normalized = T.normal(load, load(name).val);
    console.log(T.show_term(normalized));
  }
  default: {
    console.log("Usage: taelang [check|normalize] <name>");
  }
}
