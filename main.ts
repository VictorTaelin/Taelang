#!/usr/bin/env ts-node

import * as T from './taelang';
import * as fs from 'fs';

var BOOK : T.Book = {};

const args = process.argv.slice(2);
const func = args[0];
const name = args[1];
const load = T.loader(BOOK);

switch (func) {
  case "check": {
    var new_code = T.check_def(load, name);
    if (new_code !== "⊥") {
      fs.writeFileSync(name+".tl", new_code);
    }
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
