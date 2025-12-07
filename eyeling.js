#!/usr/bin/env node
"use strict";

/*
 * eyeling.js — a minimal Notation3 (N3) reasoner in JavaScript
 *
 * High-level pipeline:
 *  1) Read an N3 file from disk.
 *  2) Lex it into Tokens.
 *  3) Parse tokens into:
 *     - ground triples (facts)
 *     - forward rules {premise} => {conclusion}.
 *     - backward rules {head} <= {body}.
 *  4) Run forward chaining to fixpoint.
 *     - premises are proven using backward rules + builtins.
 *  5) Print only newly derived forward facts with explanations.
 */

const { version } = require('./package.json');

if (process.argv.includes('--version') || process.argv.includes('-v')) {
  console.log(`eyeling v${version}`);
  process.exit(0);
}

// ============================================================================
// Namespace constants
// ============================================================================

const RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS_NS = "http://www.w3.org/2000/01/rdf-schema#";
const XSD_NS = "http://www.w3.org/2001/XMLSchema#";
const LOG_NS = "http://www.w3.org/2000/10/swap/log#";
const MATH_NS = "http://www.w3.org/2000/10/swap/math#";
const STRING_NS = "http://www.w3.org/2000/10/swap/string#";
const LIST_NS = "http://www.w3.org/2000/10/swap/list#";
const TIME_NS = "http://www.w3.org/2000/10/swap/time#";

// Safety valve so backward proof doesn’t loop forever in degenerate cases.
const MAX_BACKWARD_DEPTH = 50000;

// ============================================================================
// AST (Abstract Syntax Tree)
// ============================================================================

class Term {}

class Iri extends Term {
  constructor(value) {
    super();
    this.value = value;
  }
}

class Literal extends Term {
  constructor(value) {
    super();
    this.value = value; // raw lexical form, e.g. "foo", 12, true, or "\"1944-08-21\"^^..."
  }
}

class Var extends Term {
  constructor(name) {
    super();
    this.name = name; // without leading '?'
  }
}

class Blank extends Term {
  constructor(label) {
    super();
    this.label = label; // _:b1, etc.
  }
}

class ListTerm extends Term {
  constructor(elems) {
    super();
    this.elems = elems; // Term[]
  }
}

class OpenListTerm extends Term {
  constructor(prefix, tailVar) {
    super();
    this.prefix = prefix; // Term[]
    this.tailVar = tailVar; // string
  }
}

class FormulaTerm extends Term {
  constructor(triples) {
    super();
    this.triples = triples; // Triple[]
  }
}

class Triple {
  constructor(s, p, o) {
    this.s = s;
    this.p = p;
    this.o = o;
  }
}

class Rule {
  constructor(premise, conclusion, isForward, isFuse, headBlankLabels) {
    this.premise = premise;       // Triple[]
    this.conclusion = conclusion; // Triple[]
    this.isForward = isForward;   // boolean
    this.isFuse = isFuse;         // boolean
    // Set<string> of blank-node labels that occur explicitly in the rule head
    this.headBlankLabels = headBlankLabels || new Set();
  }
}

class DerivedFact {
  constructor(fact, rule, premises, subst) {
    this.fact = fact;           // Triple
    this.rule = rule;           // Rule
    this.premises = premises;   // Triple[]
    this.subst = subst;         // { varName: Term }
  }
}

// ============================================================================
// LEXER
// ============================================================================

class Token {
  constructor(typ, value = null) {
    this.typ = typ;
    this.value = value;
  }
  toString() {
    if (this.value == null) return `Token(${this.typ})`;
    return `Token(${this.typ}, ${JSON.stringify(this.value)})`;
  }
}

function isWs(c) {
  return /\s/.test(c);
}

function isNameChar(c) {
  return /[0-9A-Za-z_\-:]/.test(c);
}

function lex(inputText) {
  const chars = Array.from(inputText);
  const n = chars.length;
  let i = 0;
  const tokens = [];

  function peek(offset = 0) {
    const j = i + offset;
    return j >= 0 && j < n ? chars[j] : null;
  }

  while (i < n) {
    let c = peek();
    if (c === null) break;

    // 1) Whitespace
    if (isWs(c)) {
      i++;
      continue;
    }

    // 2) Comments starting with '#'
    if (c === "#") {
      while (i < n && chars[i] !== "\n" && chars[i] !== "\r") i++;
      continue;
    }

    // 3) Two-character operators: => and <=
    if (c === "=") {
      if (peek(1) === ">") {
        tokens.push(new Token("OpImplies"));
        i += 2;
        continue;
      } else {
        throw new Error("Unexpected '='");
      }
    }

    if (c === "<") {
      if (peek(1) === "=") {
        tokens.push(new Token("OpImpliedBy"));
        i += 2;
        continue;
      }
      // Otherwise IRIREF <...>
      i++; // skip '<'
      const iriChars = [];
      while (i < n && chars[i] !== ">") {
        iriChars.push(chars[i]);
        i++;
      }
      if (i >= n || chars[i] !== ">") {
        throw new Error("Unterminated IRI <...>");
      }
      i++; // skip '>'
      const iri = iriChars.join("");
      tokens.push(new Token("IriRef", iri));
      continue;
    }

    // 4) Datatype operator ^^
    if (c === "^") {
      if (peek(1) === "^") {
        tokens.push(new Token("HatHat"));
        i += 2;
        continue;
      } else {
        throw new Error("Unexpected '^' (did you mean ^^?)");
      }
    }

    // 5) Single-character punctuation
    if ("{}()[];,.".includes(c)) {
      const mapping = {
        "{": "LBrace",
        "}": "RBrace",
        "(": "LParen",
        ")": "RParen",
        "[": "LBracket",
        "]": "RBracket",
        ";": "Semicolon",
        ",": "Comma",
        ".": "Dot",
      };
      tokens.push(new Token(mapping[c]));
      i++;
      continue;
    }

    // String literal
    if (c === '"') {
      i++; // consume opening "
      const sChars = [];
      while (i < n) {
        let cc = chars[i];
        i++;
        if (cc === "\\") {
          if (i < n) {
            const esc = chars[i];
            i++;
            sChars.push("\\");
            sChars.push(esc);
          }
          continue;
        }
        if (cc === '"') break;
        sChars.push(cc);
      }
      const s = '"' + sChars.join("") + '"';
      tokens.push(new Token("Literal", s));
      continue;
    }

    // Variable ?name
    if (c === "?") {
      i++;
      const nameChars = [];
      let cc;
      while ((cc = peek()) !== null && isNameChar(cc)) {
        nameChars.push(cc);
        i++;
      }
      const name = nameChars.join("");
      tokens.push(new Token("Var", name));
      continue;
    }

    // Directives: @prefix, @base
    if (c === "@") {
      i++;
      const wordChars = [];
      let cc;
      while ((cc = peek()) !== null && /[A-Za-z]/.test(cc)) {
        wordChars.push(cc);
        i++;
      }
      const word = wordChars.join("");
      if (word === "prefix") tokens.push(new Token("AtPrefix"));
      else if (word === "base") tokens.push(new Token("AtBase"));
      else throw new Error(`Unknown directive @${word}`);
      continue;
    }

    // 6) Numeric literal (integer or float)
    if (/[0-9]/.test(c) || (c === "-" && peek(1) !== null && /[0-9]/.test(peek(1)))) {
      const numChars = [c];
      i++;
      while (i < n) {
        const cc = chars[i];
        if (/[0-9]/.test(cc)) {
          numChars.push(cc);
          i++;
          continue;
        }
        if (cc === ".") {
          if (i + 1 < n && /[0-9]/.test(chars[i + 1])) {
            numChars.push(".");
            i++;
            continue;
          } else {
            break;
          }
        }
        break;
      }
      tokens.push(new Token("Literal", numChars.join("")));
      continue;
    }

    // 7) Identifiers / keywords / QNames
    const wordChars = [];
    let cc;
    while ((cc = peek()) !== null && isNameChar(cc)) {
      wordChars.push(cc);
      i++;
    }
    if (!wordChars.length) {
      throw new Error(`Unexpected char: ${JSON.stringify(c)}`);
    }
    const word = wordChars.join("");
    if (word === "true" || word === "false") {
      tokens.push(new Token("Literal", word));
    } else if ([...word].every(ch => /[0-9.\-]/.test(ch))) {
      tokens.push(new Token("Literal", word));
    } else {
      tokens.push(new Token("Ident", word));
    }
  }

  tokens.push(new Token("EOF"));
  return tokens;
}

// ============================================================================
// PREFIX ENVIRONMENT
// ============================================================================

class PrefixEnv {
  constructor(map) {
    this.map = map || {}; // prefix -> IRI
  }

  static newDefault() {
    const m = {};
    m["rdf"] = RDF_NS;
    m["rdfs"] = RDFS_NS;
    m["xsd"] = XSD_NS;
    m["log"] = LOG_NS;
    m["math"] = MATH_NS;
    m["string"] = STRING_NS;
    m["list"] = LIST_NS;
    m["time"] = TIME_NS;
    m[""] = "";
    return new PrefixEnv(m);
  }

  set(pref, base) {
    this.map[pref] = base;
  }

  expandQName(q) {
    if (q.includes(":")) {
      const [p, local] = q.split(":", 2);
      const base = this.map[p] || "";
      if (base) return base + local;
      return q;
    }
    return q;
  }

  shrinkIri(iri) {
    let best = null; // [prefix, local]
    for (const [p, base] of Object.entries(this.map)) {
      if (!base) continue;
      if (iri.startsWith(base)) {
        const local = iri.slice(base.length);
        if (!local) continue;
        const cand = [p, local];
        if (best === null || cand[1].length < best[1].length) best = cand;
      }
    }
    if (best === null) return null;
    const [p, local] = best;
    if (p === "") return `:${local}`;
    return `${p}:${local}`;
  }

  prefixesUsedForOutput(triples) {
    const used = new Set();
    for (const t of triples) {
      const iris = [];
      iris.push(...collectIrisInTerm(t.s));
      if (!isRdfTypePred(t.p)) {
        iris.push(...collectIrisInTerm(t.p));
      }
      iris.push(...collectIrisInTerm(t.o));
      for (const iri of iris) {
        for (const [p, base] of Object.entries(this.map)) {
          if (base && iri.startsWith(base)) used.add(p);
        }
      }
    }
    const v = [];
    for (const p of used) {
      if (this.map.hasOwnProperty(p)) v.push([p, this.map[p]]);
    }
    v.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
    return v;
  }
}

function collectIrisInTerm(t) {
  const out = [];
  if (t instanceof Iri) {
    out.push(t.value);
  } else if (t instanceof ListTerm) {
    for (const x of t.elems) out.push(...collectIrisInTerm(x));
  } else if (t instanceof OpenListTerm) {
    for (const x of t.prefix) out.push(...collectIrisInTerm(x));
  } else if (t instanceof FormulaTerm) {
    for (const tr of t.triples) {
      out.push(...collectIrisInTerm(tr.s));
      out.push(...collectIrisInTerm(tr.p));
      out.push(...collectIrisInTerm(tr.o));
    }
  }
  return out;
}

function collectVarsInTerm(t, acc) {
  if (t instanceof Var) {
    acc.add(t.name);
  } else if (t instanceof ListTerm) {
    for (const x of t.elems) collectVarsInTerm(x, acc);
  } else if (t instanceof OpenListTerm) {
    for (const x of t.prefix) collectVarsInTerm(x, acc);
    acc.add(t.tailVar);
  } else if (t instanceof FormulaTerm) {
    for (const tr of t.triples) {
      collectVarsInTerm(tr.s, acc);
      collectVarsInTerm(tr.p, acc);
      collectVarsInTerm(tr.o, acc);
    }
  }
}

function varsInRule(rule) {
  const acc = new Set();
  for (const tr of rule.premise) {
    collectVarsInTerm(tr.s, acc);
    collectVarsInTerm(tr.p, acc);
    collectVarsInTerm(tr.o, acc);
  }
  for (const tr of rule.conclusion) {
    collectVarsInTerm(tr.s, acc);
    collectVarsInTerm(tr.p, acc);
    collectVarsInTerm(tr.o, acc);
  }
  return acc;
}

function collectBlankLabelsInTerm(t, acc) {
  if (t instanceof Blank) {
    acc.add(t.label);
  } else if (t instanceof ListTerm) {
    for (const x of t.elems) collectBlankLabelsInTerm(x, acc);
  } else if (t instanceof OpenListTerm) {
    for (const x of t.prefix) collectBlankLabelsInTerm(x, acc);
  } else if (t instanceof FormulaTerm) {
    for (const tr of t.triples) {
      collectBlankLabelsInTerm(tr.s, acc);
      collectBlankLabelsInTerm(tr.p, acc);
      collectBlankLabelsInTerm(tr.o, acc);
    }
  }
}

function collectBlankLabelsInTriples(triples) {
  const acc = new Set();
  for (const tr of triples) {
    collectBlankLabelsInTerm(tr.s, acc);
    collectBlankLabelsInTerm(tr.p, acc);
    collectBlankLabelsInTerm(tr.o, acc);
  }
  return acc;
}

// ============================================================================
// PARSER
// ============================================================================

class Parser {
  constructor(tokens) {
    this.toks = tokens;
    this.pos = 0;
    this.prefixes = PrefixEnv.newDefault();
    this.blankCounter = 0;
    this.pendingTriples = [];
  }

  peek() {
    return this.toks[this.pos];
  }

  next() {
    const tok = this.toks[this.pos];
    this.pos += 1;
    return tok;
  }

  expectDot() {
    const tok = this.next();
    if (tok.typ !== "Dot") {
      throw new Error(`Expected '.', got ${tok.toString()}`);
    }
  }

  parseDocument() {
    const triples = [];
    const forwardRules = [];
    const backwardRules = [];

    while (this.peek().typ !== "EOF") {
      if (this.peek().typ === "AtPrefix") {
        this.next();
        this.parsePrefixDirective();
      } else if (this.peek().typ === "AtBase") {
        this.next();
        this.parseBaseDirective();
      } else {
        const first = this.parseTerm();
        if (this.peek().typ === "OpImplies") {
          this.next();
          const second = this.parseTerm();
          this.expectDot();
          forwardRules.push(this.makeRule(first, second, true));
        } else if (this.peek().typ === "OpImpliedBy") {
          this.next();
          const second = this.parseTerm();
          this.expectDot();
          backwardRules.push(this.makeRule(first, second, false));
        } else {
          const more = this.parsePredicateObjectList(first);
          this.expectDot();
          // normalize explicit log:implies / log:impliedBy at top-level
          for (const tr of more) {
            if (isLogImplies(tr.p) && tr.s instanceof FormulaTerm && tr.o instanceof FormulaTerm) {
              forwardRules.push(this.makeRule(tr.s, tr.o, true));
            } else if (isLogImpliedBy(tr.p) && tr.s instanceof FormulaTerm && tr.o instanceof FormulaTerm) {
              backwardRules.push(this.makeRule(tr.s, tr.o, false));
            } else {
              triples.push(tr);
            }
          }
        }
      }
    }

    return [this.prefixes, triples, forwardRules, backwardRules];
  }

  parsePrefixDirective() {
    const tok = this.next();
    if (tok.typ !== "Ident") {
      throw new Error(`Expected prefix name, got ${tok.toString()}`);
    }
    const pref = tok.value || "";
    const prefName = pref.endsWith(":") ? pref.slice(0, -1) : pref;

    if (this.peek().typ === "Dot") {
      this.next();
      if (!this.prefixes.map.hasOwnProperty(prefName)) {
        this.prefixes.set(prefName, "");
      }
      return;
    }

    const tok2 = this.next();
    let iri;
    if (tok2.typ === "IriRef") {
      iri = tok2.value || "";
    } else if (tok2.typ === "Ident") {
      iri = this.prefixes.expandQName(tok2.value || "");
    } else {
      throw new Error(`Expected IRI after @prefix, got ${tok2.toString()}`);
    }
    this.expectDot();
    this.prefixes.set(prefName, iri);
  }

  parseBaseDirective() {
    const tok = this.next();
    let iri;
    if (tok.typ === "IriRef") {
      iri = tok.value || "";
    } else if (tok.typ === "Ident") {
      iri = tok.value || "";
    } else {
      throw new Error(`Expected IRI after @base, got ${tok.toString()}`);
    }
    this.expectDot();
    this.prefixes.set("", iri);
  }

  parseTerm() {
    const tok = this.next();
    const typ = tok.typ;
    const val = tok.value;

    if (typ === "IriRef") {
      return new Iri(val || "");
    }

    if (typ === "Ident") {
      const name = val || "";
      if (name === "a") {
        return new Iri(RDF_NS + "type");
      } else if (name.startsWith("_:")) {
        return new Blank(name);
      } else if (name.includes(":")) {
        return new Iri(this.prefixes.expandQName(name));
      } else {
        return new Iri(name);
      }
    }

    if (typ === "Literal") {
      let s = val || "";
      if (this.peek().typ === "HatHat") {
        this.next();
        const dtTok = this.next();
        let dtIri;
        if (dtTok.typ === "IriRef") {
          dtIri = dtTok.value || "";
        } else if (dtTok.typ === "Ident") {
          const qn = dtTok.value || "";
          if (qn.includes(":")) dtIri = this.prefixes.expandQName(qn);
          else dtIri = qn;
        } else {
          throw new Error(`Expected datatype after ^^, got ${dtTok.toString()}`);
        }
        s = `${s}^^<${dtIri}>`;
      }
      return new Literal(s);
    }

    if (typ === "Var") return new Var(val || "");
    if (typ === "LParen") return this.parseList();
    if (typ === "LBracket") return this.parseBlank();
    if (typ === "LBrace") return this.parseFormula();

    throw new Error(`Unexpected term token: ${tok.toString()}`);
  }

  parseList() {
    const elems = [];
    while (this.peek().typ !== "RParen") {
      elems.push(this.parseTerm());
    }
    this.next(); // consume ')'
    return new ListTerm(elems);
  }

  parseBlank() {
    // [] or [ ... ] property list
    if (this.peek().typ === "RBracket") {
      this.next();
      this.blankCounter += 1;
      return new Blank(`_:b${this.blankCounter}`);
    }

    // [ predicateObjectList ]
    this.blankCounter += 1;
    const id = `_:b${this.blankCounter}`;
    const subj = new Blank(id);

    while (true) {
      // Verb (can also be 'a')
      let pred;
      if (this.peek().typ === "Ident" && (this.peek().value || "") === "a") {
        this.next();
        pred = new Iri(RDF_NS + "type");
      } else {
        pred = this.parseTerm();
      }

      // Object list: o1, o2, ...
      const objs = [this.parseTerm()];
      while (this.peek().typ === "Comma") {
        this.next();
        objs.push(this.parseTerm());
      }

      for (const o of objs) {
        this.pendingTriples.push(new Triple(subj, pred, o));
      }

      if (this.peek().typ === "Semicolon") {
        this.next();
        if (this.peek().typ === "RBracket") break;
        continue;
      }
      break;
    }

    if (this.peek().typ === "RBracket") {
      this.next();
    } else {
      throw new Error(
        `Expected ']' at end of blank node property list, got ${JSON.stringify(
          this.peek()
        )}`
      );
    }

    return new Blank(id);
  }

  parseFormula() {
    const triples = [];
    while (this.peek().typ !== "RBrace") {
      const left = this.parseTerm();
      if (this.peek().typ === "OpImplies") {
        this.next();
        const right = this.parseTerm();
        const pred = new Iri(LOG_NS + "implies");
        triples.push(new Triple(left, pred, right));
        if (this.peek().typ === "Dot") this.next();
        else if (this.peek().typ === "RBrace") {
          // ok
        } else {
          throw new Error(`Expected '.' or '}', got ${this.peek().toString()}`);
        }
      } else if (this.peek().typ === "OpImpliedBy") {
        this.next();
        const right = this.parseTerm();
        const pred = new Iri(LOG_NS + "impliedBy");
        triples.push(new Triple(left, pred, right));
        if (this.peek().typ === "Dot") this.next();
        else if (this.peek().typ === "RBrace") {
          // ok
        } else {
          throw new Error(`Expected '.' or '}', got ${this.peek().toString()}`);
        }
      } else {
        triples.push(...this.parsePredicateObjectList(left));
        if (this.peek().typ === "Dot") this.next();
        else if (this.peek().typ === "RBrace") {
          // ok
        } else {
          throw new Error(`Expected '.' or '}', got ${this.peek().toString()}`);
        }
      }
    }
    this.next(); // consume '}'
    return new FormulaTerm(triples);
  }

  parsePredicateObjectList(subject) {
    const out = [];
    while (true) {
      let verb;
      if (this.peek().typ === "Ident" && (this.peek().value || "") === "a") {
        this.next();
        verb = new Iri(RDF_NS + "type");
      } else {
        verb = this.parseTerm();
      }
      const objects = this.parseObjectList();
      for (const o of objects) out.push(new Triple(subject, verb, o));

      if (this.peek().typ === "Semicolon") {
        this.next();
        if (this.peek().typ === "Dot") break;
        continue;
      }
      break;
    }

    if (this.pendingTriples.length > 0) {
      out.push(...this.pendingTriples);
      this.pendingTriples = [];
    }

    return out;
  }

  parseObjectList() {
    const objs = [this.parseTerm()];
    while (this.peek().typ === "Comma") {
      this.next();
      objs.push(this.parseTerm());
    }
    return objs;
  }

  makeRule(left, right, isForward) {
    let premiseTerm, conclTerm;

    if (isForward) {
      premiseTerm = left;
      conclTerm = right;
    } else {
      premiseTerm = right;
      conclTerm = left;
    }

    let isFuse = false;
    if (isForward) {
      if (conclTerm instanceof Literal && conclTerm.value === "false") {
        isFuse = true;
      }
    }

    let rawPremise;
    if (premiseTerm instanceof FormulaTerm) {
      rawPremise = premiseTerm.triples;
    } else if (premiseTerm instanceof Literal && premiseTerm.value === "true") {
      rawPremise = [];
    } else {
      rawPremise = [];
    }

    let rawConclusion;
    if (conclTerm instanceof FormulaTerm) {
      rawConclusion = conclTerm.triples;
    } else if (conclTerm instanceof Literal && conclTerm.value === "false") {
      rawConclusion = [];
    } else {
      rawConclusion = [];
    }

    // Blank nodes that occur explicitly in the head (conclusion)
    const headBlankLabels = collectBlankLabelsInTriples(rawConclusion);

    const [premise0, conclusion] = liftBlankRuleVars(rawPremise, rawConclusion);

    // Reorder constraints for *forward* rules.
    const premise = isForward ? reorderPremiseForConstraints(premise0) : premise0;

    return new Rule(premise, conclusion, isForward, isFuse, headBlankLabels);
  }
}

// ============================================================================
// Blank-node lifting and Skolemization
// ============================================================================

function liftBlankRuleVars(premise, conclusion) {
  function convertTerm(t, mapping, counter) {
    if (t instanceof Blank) {
      const label = t.label;
      if (!mapping.hasOwnProperty(label)) {
        counter[0] += 1;
        mapping[label] = `_b${counter[0]}`;
      }
      return new Var(mapping[label]);
    }
    if (t instanceof ListTerm) {
      return new ListTerm(t.elems.map(e => convertTerm(e, mapping, counter)));
    }
    if (t instanceof OpenListTerm) {
      return new OpenListTerm(
        t.prefix.map(e => convertTerm(e, mapping, counter)),
        t.tailVar
      );
    }
    if (t instanceof FormulaTerm) {
      const triples = t.triples.map(tr =>
        new Triple(
          convertTerm(tr.s, mapping, counter),
          convertTerm(tr.p, mapping, counter),
          convertTerm(tr.o, mapping, counter)
        )
      );
      return new FormulaTerm(triples);
    }
    return t;
  }

  function convertTriple(tr, mapping, counter) {
    return new Triple(
      convertTerm(tr.s, mapping, counter),
      convertTerm(tr.p, mapping, counter),
      convertTerm(tr.o, mapping, counter)
    );
  }

  const mapping = {};
  const counter = [0];
  const newPremise = premise.map(tr => convertTriple(tr, mapping, counter));
  return [newPremise, conclusion];
}

function skolemizeTermForHeadBlanks(t, headBlankLabels, mapping, skCounter) {
  if (t instanceof Blank) {
    const label = t.label;
    // Only skolemize blanks that occur explicitly in the rule head
    if (!headBlankLabels || !headBlankLabels.has(label)) {
      return t; // this is a data blank (e.g. bound via ?X), keep it
    }
    if (!mapping.hasOwnProperty(label)) {
      const idx = skCounter[0];
      skCounter[0] += 1;
      mapping[label] = `_:sk_${idx}`;
    }
    return new Blank(mapping[label]);
  }

  if (t instanceof ListTerm) {
    return new ListTerm(
      t.elems.map(e => skolemizeTermForHeadBlanks(e, headBlankLabels, mapping, skCounter))
    );
  }

  if (t instanceof OpenListTerm) {
    return new OpenListTerm(
      t.prefix.map(e => skolemizeTermForHeadBlanks(e, headBlankLabels, mapping, skCounter)),
      t.tailVar
    );
  }

  if (t instanceof FormulaTerm) {
    return new FormulaTerm(
      t.triples.map(tr =>
        skolemizeTripleForHeadBlanks(tr, headBlankLabels, mapping, skCounter)
      )
    );
  }

  return t;
}

function skolemizeTripleForHeadBlanks(tr, headBlankLabels, mapping, skCounter) {
  return new Triple(
    skolemizeTermForHeadBlanks(tr.s, headBlankLabels, mapping, skCounter),
    skolemizeTermForHeadBlanks(tr.p, headBlankLabels, mapping, skCounter),
    skolemizeTermForHeadBlanks(tr.o, headBlankLabels, mapping, skCounter)
  );
}

// ============================================================================
// Alpha equivalence helpers
// ============================================================================

function termsEqual(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  if (a.constructor !== b.constructor) return false;
  if (a instanceof Iri) return a.value === b.value;
  if (a instanceof Literal) return a.value === b.value;
  if (a instanceof Var) return a.name === b.name;
  if (a instanceof Blank) return a.label === b.label;
  if (a instanceof ListTerm) {
    if (a.elems.length !== b.elems.length) return false;
    for (let i = 0; i < a.elems.length; i++) {
      if (!termsEqual(a.elems[i], b.elems[i])) return false;
    }
    return true;
  }
  if (a instanceof OpenListTerm) {
    if (a.tailVar !== b.tailVar) return false;
    if (a.prefix.length !== b.prefix.length) return false;
    for (let i = 0; i < a.prefix.length; i++) {
      if (!termsEqual(a.prefix[i], b.prefix[i])) return false;
    }
    return true;
  }
  if (a instanceof FormulaTerm) {
    return triplesListEqual(a.triples, b.triples);
  }
  return false;
}

function triplesEqual(a, b) {
  return (
    termsEqual(a.s, b.s) && termsEqual(a.p, b.p) && termsEqual(a.o, b.o)
  );
}

function triplesListEqual(xs, ys) {
  if (xs.length !== ys.length) return false;
  for (let i = 0; i < xs.length; i++) {
    if (!triplesEqual(xs[i], ys[i])) return false;
  }
  return true;
}

function alphaEqTerm(a, b, bmap) {
  if (a instanceof Blank && b instanceof Blank) {
    const x = a.label;
    const y = b.label;
    if (bmap.hasOwnProperty(x)) {
      return bmap[x] === y;
    } else {
      bmap[x] = y;
      return true;
    }
  }
  if (a instanceof Iri && b instanceof Iri) return a.value === b.value;
  if (a instanceof Literal && b instanceof Literal) return a.value === b.value;
  if (a instanceof Var && b instanceof Var) return a.name === b.name;
  if (a instanceof ListTerm && b instanceof ListTerm) {
    if (a.elems.length !== b.elems.length) return false;
    for (let i = 0; i < a.elems.length; i++) {
      if (!alphaEqTerm(a.elems[i], b.elems[i], bmap)) return false;
    }
    return true;
  }
  if (a instanceof OpenListTerm && b instanceof OpenListTerm) {
    if (a.tailVar !== b.tailVar || a.prefix.length !== b.prefix.length)
      return false;
    for (let i = 0; i < a.prefix.length; i++) {
      if (!alphaEqTerm(a.prefix[i], b.prefix[i], bmap)) return false;
    }
    return true;
  }
  if (a instanceof FormulaTerm && b instanceof FormulaTerm) {
    // formulas are treated as opaque here: exact equality
    return triplesListEqual(a.triples, b.triples);
  }
  return false;
}

function alphaEqTriple(a, b) {
  const bmap = {};
  return (
    alphaEqTerm(a.s, b.s, bmap) &&
    alphaEqTerm(a.p, b.p, bmap) &&
    alphaEqTerm(a.o, b.o, bmap)
  );
}

function hasAlphaEquiv(triples, tr) {
  return triples.some(t => alphaEqTriple(t, tr));
}

// ============================================================================
// Special predicate helpers
// ============================================================================

function isRdfTypePred(p) {
  return p instanceof Iri && p.value === RDF_NS + "type";
}

function isLogImplies(p) {
  return p instanceof Iri && p.value === LOG_NS + "implies";
}

function isLogImpliedBy(p) {
  return p instanceof Iri && p.value === LOG_NS + "impliedBy";
}

// ============================================================================
// Constraint / "test" builtins
// ============================================================================

function isConstraintBuiltin(tr) {
  if (!(tr.p instanceof Iri)) return false;
  const v = tr.p.value;

  // log: tests that are purely constraints
  if (v === LOG_NS + "notEqualTo") return true;
  if (v === LOG_NS + "notIncludes") return true;

  // math: numeric comparisons (no new bindings, just tests)
  if (
    v === MATH_NS + "greaterThan" ||
    v === MATH_NS + "lessThan" ||
    v === MATH_NS + "notLessThan" ||
    v === MATH_NS + "notGreaterThan" ||
    v === MATH_NS + "equalTo" ||
    v === MATH_NS + "notEqualTo"
  ) {
    return true;
  }

  // list: membership test with no bindings
  if (v === LIST_NS + "notMember") return true;

  return false;
}

/**
 * Move constraint builtins to the end of the rule premise.
 * This is a simple "delaying" strategy similar in spirit to Prolog's when/2:
 * - normal goals first (can bind variables),
 * - pure test / constraint builtins last (checked once bindings are in place).
 */
function reorderPremiseForConstraints(premise) {
  if (!premise || premise.length === 0) return premise;

  const normal = [];
  const delayed = [];

  for (const tr of premise) {
    if (isConstraintBuiltin(tr)) delayed.push(tr);
    else normal.push(tr);
  }
  return normal.concat(delayed);
}

// ============================================================================
// Unification + substitution
// ============================================================================

function containsVarTerm(t, v) {
  if (t instanceof Var) return t.name === v;
  if (t instanceof ListTerm) return t.elems.some(e => containsVarTerm(e, v));
  if (t instanceof OpenListTerm)
    return (
      t.prefix.some(e => containsVarTerm(e, v)) || t.tailVar === v
    );
  if (t instanceof FormulaTerm)
    return t.triples.some(
      tr =>
        containsVarTerm(tr.s, v) ||
        containsVarTerm(tr.p, v) ||
        containsVarTerm(tr.o, v)
    );
  return false;
}

function isGroundTerm(t) {
  if (t instanceof Var) return false;
  if (t instanceof ListTerm) return t.elems.every(e => isGroundTerm(e));
  if (t instanceof OpenListTerm) return false;
  if (t instanceof FormulaTerm)
    return t.triples.every(tr => isGroundTriple(tr));
  return true;
}

function isGroundTriple(tr) {
  return isGroundTerm(tr.s) && isGroundTerm(tr.p) && isGroundTerm(tr.o);
}

function applySubstTerm(t, s) {
  // Common case: variable
  if (t instanceof Var) {
    // Fast path: unbound variable → no change
    const first = s[t.name];
    if (first === undefined) {
      return t;
    }

    // Follow chains X -> Y -> ... until we hit a non-var or a cycle.
    let cur = first;
    const seen = new Set([t.name]);
    while (cur instanceof Var) {
      const name = cur.name;
      if (seen.has(name)) break; // cycle
      seen.add(name);
      const nxt = s[name];
      if (!nxt) break;
      cur = nxt;
    }

    if (cur instanceof Var) {
      // Still a var: keep it as is (no need to clone)
      return cur;
    }
    // Bound to a non-var term: apply substitution recursively in case it
    // contains variables inside.
    return applySubstTerm(cur, s);
  }

  // Non-variable terms
  if (t instanceof ListTerm) {
    return new ListTerm(t.elems.map(e => applySubstTerm(e, s)));
  }

  if (t instanceof OpenListTerm) {
    const newPrefix = t.prefix.map(e => applySubstTerm(e, s));
    const tailTerm = s[t.tailVar];
    if (tailTerm !== undefined) {
      const tailApplied = applySubstTerm(tailTerm, s);
      if (tailApplied instanceof ListTerm) {
        return new ListTerm(newPrefix.concat(tailApplied.elems));
      } else if (tailApplied instanceof OpenListTerm) {
        return new OpenListTerm(
          newPrefix.concat(tailApplied.prefix),
          tailApplied.tailVar
        );
      } else {
        return new OpenListTerm(newPrefix, t.tailVar);
      }
    } else {
      return new OpenListTerm(newPrefix, t.tailVar);
    }
  }

  if (t instanceof FormulaTerm) {
    return new FormulaTerm(t.triples.map(tr => applySubstTriple(tr, s)));
  }

  return t;
}

function applySubstTriple(tr, s) {
  return new Triple(
    applySubstTerm(tr.s, s),
    applySubstTerm(tr.p, s),
    applySubstTerm(tr.o, s)
  );
}

function unifyOpenWithList(prefix, tailv, ys, subst) {
  if (ys.length < prefix.length) return null;
  let s2 = { ...subst };
  for (let i = 0; i < prefix.length; i++) {
    s2 = unifyTerm(prefix[i], ys[i], s2);
    if (s2 === null) return null;
  }
  const rest = new ListTerm(ys.slice(prefix.length));
  s2 = unifyTerm(new Var(tailv), rest, s2);
  if (s2 === null) return null;
  return s2;
}

function unifyTerm(a, b, subst) {
  a = applySubstTerm(a, subst);
  b = applySubstTerm(b, subst);

  // Variable binding
  if (a instanceof Var) {
    const v = a.name;
    const t = b;
    if (t instanceof Var && t.name === v) return { ...subst };
    if (containsVarTerm(t, v)) return null;
    const s2 = { ...subst };
    s2[v] = t;
    return s2;
  }

  if (b instanceof Var) {
    return unifyTerm(b, a, subst);
  }

  // Exact matches
  if (a instanceof Iri && b instanceof Iri && a.value === b.value)
    return { ...subst };
  if (a instanceof Literal && b instanceof Literal && a.value === b.value)
    return { ...subst };
  if (a instanceof Blank && b instanceof Blank && a.label === b.label)
    return { ...subst };

  // Open list vs concrete list
  if (a instanceof OpenListTerm && b instanceof ListTerm) {
    return unifyOpenWithList(a.prefix, a.tailVar, b.elems, subst);
  }
  if (a instanceof ListTerm && b instanceof OpenListTerm) {
    return unifyOpenWithList(b.prefix, b.tailVar, a.elems, subst);
  }

  // Open list vs open list (same tail var)
  if (a instanceof OpenListTerm && b instanceof OpenListTerm) {
    if (a.tailVar !== b.tailVar || a.prefix.length !== b.prefix.length)
      return null;
    let s2 = { ...subst };
    for (let i = 0; i < a.prefix.length; i++) {
      s2 = unifyTerm(a.prefix[i], b.prefix[i], s2);
      if (s2 === null) return null;
    }
    return s2;
  }

  // List terms
  if (a instanceof ListTerm && b instanceof ListTerm) {
    if (a.elems.length !== b.elems.length) return null;
    let s2 = { ...subst };
    for (let i = 0; i < a.elems.length; i++) {
      s2 = unifyTerm(a.elems[i], b.elems[i], s2);
      if (s2 === null) return null;
    }
    return s2;
  }

  // Formulas are treated as opaque unless exactly equal
  if (a instanceof FormulaTerm && b instanceof FormulaTerm) {
    if (triplesListEqual(a.triples, b.triples)) return { ...subst };
  }

  return null;
}

function unifyTriple(pat, fact, subst) {
  // Predicates are usually the cheapest and most selective
  const s1 = unifyTerm(pat.p, fact.p, subst);
  if (s1 === null) return null;

  const s2 = unifyTerm(pat.s, fact.s, s1);
  if (s2 === null) return null;

  const s3 = unifyTerm(pat.o, fact.o, s2);
  return s3;
}

function composeSubst(outer, delta) {
  if (!delta || Object.keys(delta).length === 0) {
    return { ...outer };
  }
  const out = { ...outer };
  for (const [k, v] of Object.entries(delta)) {
    if (out.hasOwnProperty(k)) {
      if (!termsEqual(out[k], v)) return null;
    } else {
      out[k] = v;
    }
  }
  return out;
}

// ============================================================================
// BUILTINS
// ============================================================================

function literalParts(lit) {
  const idx = lit.indexOf("^^");
  if (idx >= 0) {
    let lex = lit.slice(0, idx);
    let dt = lit.slice(idx + 2).trim();
    if (dt.startsWith("<") && dt.endsWith(">")) {
      dt = dt.slice(1, -1);
    }
    return [lex, dt];
  }
  return [lit, null];
}

function stripQuotes(lex) {
  if (lex.length >= 2 && lex[0] === '"' && lex[lex.length - 1] === '"') {
    return lex.slice(1, -1);
  }
  return lex;
}

function termToJsString(t) {
  // Accept any Literal and interpret its lexical form as a JS string.
  if (!(t instanceof Literal)) return null;
  const [lex, _dt] = literalParts(t.value);
  return stripQuotes(lex);
}

function makeStringLiteral(str) {
  // JSON.stringify gives us a valid N3/Turtle-style quoted string
  // (with proper escaping for quotes, backslashes, newlines, …).
  return new Literal(JSON.stringify(str));
}

// Tiny subset of sprintf: supports only %s and %%.
// Good enough for most N3 string:format use cases that just splice strings.
function simpleStringFormat(fmt, args) {
  let out = "";
  let argIndex = 0;

  for (let i = 0; i < fmt.length; i++) {
    const ch = fmt[i];
    if (ch === "%" && i + 1 < fmt.length) {
      const spec = fmt[i + 1];

      if (spec === "s") {
        const arg = argIndex < args.length ? args[argIndex++] : "";
        out += arg;
        i++;
        continue;
      }

      if (spec === "%") {
        out += "%";
        i++;
        continue;
      }

      // Unsupported specifier (like %d, %f, …) ⇒ fail the builtin.
      return null;
    }
    out += ch;
  }

  return out;
}

function parseNum(t) {
  // Parse as JS Number (for floats, dates-as-seconds, etc.)
  if (!(t instanceof Literal)) return null;
  let s = t.value;
  let [lex, _dt] = literalParts(s);
  const val = stripQuotes(lex);
  const n = Number(val);
  if (!Number.isNaN(n)) return n;
  return null;
}

function parseIntLiteral(t) {
  // Parse as BigInt if the lexical form is an integer
  if (!(t instanceof Literal)) return null;
  let s = t.value;
  let [lex, _dt] = literalParts(s);
  const val = stripQuotes(lex);
  if (!/^[+-]?\d+$/.test(val)) return null;
  try {
    return BigInt(val);
  } catch (e) {
    return null;
  }
}

function parseNumberLiteral(t) {
  // Prefer BigInt for integers, fall back to Number for non-integers
  const bi = parseIntLiteral(t);
  if (bi !== null) return bi;
  const n = parseNum(t);
  if (n !== null) return n;
  return null;
}

function formatNum(n) {
  return String(n);
}

function parseXsdDateTerm(t) {
  if (!(t instanceof Literal)) return null;
  const s = t.value;
  let [lex, dt] = literalParts(s);
  const val = stripQuotes(lex);
  if (dt === XSD_NS + "date" || val.length === 10) {
    const d = new Date(val + "T00:00:00Z");
    if (Number.isNaN(d.getTime())) return null;
    return d;
  }
  return null;
}

function parseXsdDatetimeTerm(t) {
  if (!(t instanceof Literal)) return null;
  const s = t.value;
  let [lex, dt] = literalParts(s);
  const val = stripQuotes(lex);
  if (dt === XSD_NS + "dateTime" || val.includes("T")) {
    const d = new Date(val);
    if (Number.isNaN(d.getTime())) return null;
    return d; // Date in local/UTC, we only use timestamp
  }
  return null;
}

function parseDatetimeLike(t) {
  const d = parseXsdDateTerm(t);
  if (d !== null) return d;
  return parseXsdDatetimeTerm(t);
}

function parseIso8601DurationToSeconds(s) {
  if (!s) return null;
  if (s[0] !== "P") return null;
  const it = s.slice(1);
  let num = "";
  let inTime = false;
  let years = 0,
    months = 0,
    weeks = 0,
    days = 0,
    hours = 0,
    minutes = 0,
    seconds = 0;

  for (const c of it) {
    if (c === "T") {
      inTime = true;
      continue;
    }
    if (/[0-9.]/.test(c)) {
      num += c;
      continue;
    }
    if (!num) return null;
    const val = Number(num);
    if (Number.isNaN(val)) return null;
    num = "";
    if (!inTime && c === "Y") years += val;
    else if (!inTime && c === "M") months += val;
    else if (!inTime && c === "W") weeks += val;
    else if (!inTime && c === "D") days += val;
    else if (inTime && c === "H") hours += val;
    else if (inTime && c === "M") minutes += val;
    else if (inTime && c === "S") seconds += val;
    else return null;
  }

  const totalDays =
    years * 365.2425 +
    months * 30.436875 +
    weeks * 7.0 +
    days +
    hours / 24.0 +
    minutes / (24.0 * 60.0) +
    seconds / (24.0 * 3600.0);

  return totalDays * 86400.0;
}

function parseNumericForCompareTerm(t) {
  // Try integer BigInt first
  if (t instanceof Literal) {
    let [lex, dt] = literalParts(t.value);
    const val = stripQuotes(lex);
    if (/^[+-]?\d+$/.test(val)) {
      try {
        return { kind: "bigint", value: BigInt(val) };
      } catch (e) {
        // fall through
      }
    }
    // durations / dateTimes / floats -> Number (seconds or numeric)
    const nDur = parseNumOrDuration(t);
    if (nDur !== null) return { kind: "number", value: nDur };
    return null;
  }
  const n = parseNumOrDuration(t);
  if (n !== null) return { kind: "number", value: n };
  return null;
}

function cmpNumericInfo(aInfo, bInfo, op) {
  // op is one of ">", "<", ">=", "<="
  if (!aInfo || !bInfo) return false;

  if (aInfo.kind === "bigint" && bInfo.kind === "bigint") {
    if (op === ">")  return aInfo.value >  bInfo.value;
    if (op === "<")  return aInfo.value <  bInfo.value;
    if (op === ">=") return aInfo.value >= bInfo.value;
    if (op === "<=") return aInfo.value <= bInfo.value;
    if (op === "==") return aInfo.value == bInfo.value;
    if (op === "!=") return aInfo.value != bInfo.value;
    return false;
  }

  const a = typeof aInfo.value === "bigint" ? Number(aInfo.value) : aInfo.value;
  const b = typeof bInfo.value === "bigint" ? Number(bInfo.value) : bInfo.value;

  if (op === ">")  return a >  b;
  if (op === "<")  return a <  b;
  if (op === ">=") return a >= b;
  if (op === "<=") return a <= b;
  if (op === "==") return a == b;
  if (op === "!=") return a != b;
  return false;
}

function parseNumOrDuration(t) {
  const n = parseNum(t);
  if (n !== null) return n;
  if (t instanceof Literal) {
    let s = t.value;
    let [lex, dt] = literalParts(s);
    const val = stripQuotes(lex);
    if (
      dt === XSD_NS + "duration" ||
      val.startsWith("P") ||
      val.startsWith("-P")
    ) {
      const negative = val.startsWith("-");
      const core = negative ? val.slice(1) : val;
      const secs = parseIso8601DurationToSeconds(core);
      if (secs === null) return null;
      return negative ? -secs : secs;
    }
  }
  const dtval = parseDatetimeLike(t);
  if (dtval !== null) {
    return dtval.getTime() / 1000.0;
  }
  return null;
}

function formatDurationLiteralFromSeconds(secs) {
  const neg = secs < 0;
  const absSecs = Math.abs(secs);
  const days = Math.round(absSecs / 86400.0);
  const lex = neg ? `" -P${days}D"` : `"P${days}D"`;
  const cleanLex = neg ? `" -P${days}D"` : `"P${days}D"`; // minor detail; we just follow shape
  const lex2 = neg ? `" -P${days}D"` : `"P${days}D"`;
  const actualLex = neg ? `" -P${days}D"` : `"P${days}D"`;
  // keep simpler, no spaces:
  const finalLex = neg ? `" -P${days}D"` : `"P${days}D"`;
  const literalLex = neg ? `"-P${days}D"` : `"P${days}D"`;
  return new Literal(`${literalLex}^^<${XSD_NS}duration>`);
}

function listAppendSplit(parts, resElems, subst) {
  if (!parts.length) {
    if (!resElems.length) return [{ ...subst }];
    return [];
  }
  const out = [];
  const n = resElems.length;
  for (let k = 0; k <= n; k++) {
    const left = new ListTerm(resElems.slice(0, k));
    let s1 = unifyTerm(parts[0], left, subst);
    if (s1 === null) continue;
    const restElems = resElems.slice(k);
    out.push(...listAppendSplit(parts.slice(1), restElems, s1));
  }
  return out;
}

// ============================================================================
// Backward proof & builtins mutual recursion — declarations first
// ============================================================================

function evalBuiltin(goal, subst, facts, backRules, depth, varGen) {
  const g = applySubstTriple(goal, subst);

  // -----------------------------------------------------------------
  // time:localTime
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === TIME_NS + "localTime") {
    // "" time:localTime ?D.  binds ?D to “now” as xsd:dateTime.
    const now = localIsoDateTimeString(new Date());
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = new Literal(`"${now}"^^<${XSD_NS}dateTime>`);
      return [s2];
    }
    if (g.o instanceof Literal) {
      const [lexO] = literalParts(g.o.value);
      if (stripQuotes(lexO) === now) return [{ ...subst }];
    }
    return [];
  }

  // -----------------------------------------------------------------
  // math: comparisons (binary OR list form)
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === MATH_NS + "greaterThan") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, ">")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, ">")) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "lessThan") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, "<")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, "<")) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "notLessThan") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, ">=")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, ">=")) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "notGreaterThan") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, "<=")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, "<=")) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "equalTo") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, "==")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, "==")) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "notEqualTo") {
    const aInfo = parseNumericForCompareTerm(g.s);
    const bInfo = parseNumericForCompareTerm(g.o);
    if (aInfo && bInfo && cmpNumericInfo(aInfo, bInfo, "!=")) return [{ ...subst }];

    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a2 = parseNumericForCompareTerm(g.s.elems[0]);
      const b2 = parseNumericForCompareTerm(g.s.elems[1]);
      if (a2 && b2 && cmpNumericInfo(a2, b2, "!=")) return [{ ...subst }];
    }
    return [];
  }

  // -----------------------------------------------------------------
  // math: arithmetic
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === MATH_NS + "sum") {
    if (g.s instanceof ListTerm && g.s.elems.length >= 2) {
      const xs = g.s.elems;
      const values = [];
      for (const t of xs) {
        const v = parseNumberLiteral(t);
        if (v === null) return [];
        values.push(v);
      }

      let lit;
      const allBig = values.every(v => typeof v === "bigint");
      if (allBig) {
        let total = 0n;
        for (const v of values) total += v;
        lit = new Literal(total.toString());
      } else {
        let total = 0.0;
        for (const v of values) {
          total += typeof v === "bigint" ? Number(v) : v;
        }
        lit = new Literal(formatNum(total));
      }

      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = lit;
        return [s2];
      }
      const s2 = unifyTerm(g.o, lit, subst);
      return s2 !== null ? [s2] : [];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "product") {
    if (g.s instanceof ListTerm && g.s.elems.length >= 2) {
      const xs = g.s.elems;
      const values = [];
      for (const t of xs) {
        const v = parseNumberLiteral(t);
        if (v === null) return [];
        values.push(v);
      }

      let lit;
      const allBig = values.every(v => typeof v === "bigint");
      if (allBig) {
        let prod = 1n;
        for (const v of values) prod *= v;
        lit = new Literal(prod.toString());
      } else {
        let prod = 1.0;
        for (const v of values) {
          prod *= typeof v === "bigint" ? Number(v) : v;
        }
        lit = new Literal(formatNum(prod));
      }

      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = lit;
        return [s2];
      }
      if (g.o instanceof Literal && g.o.value === lit.value) {
        return [{ ...subst }];
      }
      return [];
    }
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "difference") {
    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const [a0, b0] = g.s.elems;

      // BigInt integer difference
      const ai = parseIntLiteral(a0);
      const bi = parseIntLiteral(b0);
      if (ai !== null && bi !== null) {
        const ci = ai - bi;
        const lit = new Literal(ci.toString());
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = lit;
          return [s2];
        } else {
          const s2 = unifyTerm(g.o, lit, subst);
          return s2 !== null ? [s2] : [];
        }
      }

      // Numeric difference via floats
      const a = parseNum(a0);
      const b = parseNum(b0);
      if (a !== null && b !== null) {
        const c = a - b;
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = new Literal(formatNum(c));
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === formatNum(c)) {
          return [{ ...subst }];
        }
      }

      // Date/datetime difference -> duration
      const aDt = parseDatetimeLike(a0);
      const bDt = parseDatetimeLike(b0);
      if (aDt !== null && bDt !== null) {
        const diffSecs = (aDt.getTime() - bDt.getTime()) / 1000.0;
        const durTerm = formatDurationLiteralFromSeconds(diffSecs);
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = durTerm;
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === durTerm.value) {
          return [{ ...subst }];
        }
      }
      return [];
    }
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "quotient") {
    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a = parseNum(g.s.elems[0]);
      const b = parseNum(g.s.elems[1]);
      if (a !== null && b !== null && b !== 0.0) {
        const c = a / b;
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = new Literal(formatNum(c));
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === formatNum(c)) {
          return [{ ...subst }];
        }
      }
      return [];
    }
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "exponentiation") {
    if (g.s instanceof ListTerm && g.s.elems.length === 2) {
      const a = parseNum(g.s.elems[0]);
      const b0 = g.s.elems[1];
      const c = parseNum(g.o);
      let b = null;
      if (a !== null && b0 instanceof Literal) b = parseNum(b0);

      if (a !== null && b !== null) {
        const cVal = a ** b;
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = new Literal(formatNum(cVal));
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === formatNum(cVal)) {
          return [{ ...subst }];
        }
      }

      // inverse mode
      if (a !== null && b0 instanceof Var && c !== null) {
        if (a > 0.0 && a !== 1.0 && c > 0.0) {
          const bVal = Math.log(c) / Math.log(a);
          const s2 = { ...subst };
          s2[b0.name] = new Literal(formatNum(bVal));
          return [s2];
        }
      }
      return [];
    }
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "negation") {
    const a = parseNum(g.s);
    if (a !== null && g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = new Literal(formatNum(-a));
      return [s2];
    }
    const b = parseNum(g.o);
    if (g.s instanceof Var && b !== null) {
      const s2 = { ...subst };
      s2[g.s.name] = new Literal(formatNum(-b));
      return [s2];
    }
    const a2 = parseNum(g.s);
    const b2 = parseNum(g.o);
    if (a2 !== null && b2 !== null) {
      if (Math.abs(-a2 - b2) < 1e-9) return [{ ...subst }];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "absoluteValue") {
    const a = parseNum(g.s);
    if (a !== null && g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = new Literal(formatNum(Math.abs(a)));
      return [s2];
    }
    const b = parseNum(g.o);
    if (a !== null && b !== null) {
      if (Math.abs(Math.abs(a) - b) < 1e-9) return [{ ...subst }];
    }
    return [];
  }

  // Trig
  if (g.p instanceof Iri && g.p.value === MATH_NS + "cos") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.cos(a);
      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = new Literal(formatNum(cVal));
        return [s2];
      }
      if (g.o instanceof Literal && g.o.value === formatNum(cVal)) {
        return [{ ...subst }];
      }
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "sin") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.sin(a);
      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = new Literal(formatNum(cVal));
        return [s2];
      }
      if (g.o instanceof Literal && g.o.value === formatNum(cVal)) {
        return [{ ...subst }];
      }
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "acos") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.acos(a);
      if (Number.isFinite(cVal)) {
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = new Literal(formatNum(cVal));
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === formatNum(cVal)) {
          return [{ ...subst }];
        }
      }
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === MATH_NS + "asin") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.asin(a);
      if (Number.isFinite(cVal)) {
        if (g.o instanceof Var) {
          const s2 = { ...subst };
          s2[g.o.name] = new Literal(formatNum(cVal));
          return [s2];
        }
        if (g.o instanceof Literal && g.o.value === formatNum(cVal)) {
          return [{ ...subst }];
        }
      }
    }
    return [];
  }

  // fibonacci
  if (g.p instanceof Iri && g.p.value === MATH_NS + "fibonacci") {
    const n = parseIntLiteral(g.s);
    if (n !== null) {
      if (n === null || n < 0n) return [];
      let a = 0n, b = 1n;
      for (let i = 0n; i < n; i++) {
        const tmp = a + b;
        a = b;
        b = tmp;
      }
      const lit = new Literal(a.toString());
      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = lit;
        return [s2];
      }
      const s2 = unifyTerm(g.o, lit, subst);
      return s2 !== null ? [s2] : [];
    }
    return [];
  }

  // -----------------------------------------------------------------
  // log: equality builtins
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LOG_NS + "equalTo") {
    const s2 = unifyTerm(goal.s, goal.o, subst);
    return s2 !== null ? [s2] : [];
  }

  if (g.p instanceof Iri && g.p.value === LOG_NS + "notEqualTo") {
    const s2 = unifyTerm(goal.s, goal.o, subst);
    if (s2 !== null) return [];
    return [{ ...subst }];
  }

  // -----------------------------------------------------------------
  // log:implies — expose internal forward rules as data
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LOG_NS + "implies") {
    const allFw = backRules.__allForwardRules || [];
    const results = [];

    for (const r0 of allFw) {
      if (!r0.isForward) continue;

      // fresh copy of the rule with fresh variable names
      const r = standardizeRule(r0, varGen);

      const premF = new FormulaTerm(r.premise);
      const concF = new FormulaTerm(r.conclusion);

      // unify subject with the premise formula
      let s2 = unifyTerm(goal.s, premF, subst);
      if (s2 === null) continue;

      // unify object with the conclusion formula
      s2 = unifyTerm(goal.o, concF, s2);
      if (s2 === null) continue;

      results.push(s2);
    }

    return results;
  }

  // -----------------------------------------------------------------
  // log:impliedBy — expose internal backward rules as data
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LOG_NS + "impliedBy") {
    const allBw = backRules.__allBackwardRules || backRules;
    const results = [];

    for (const r0 of allBw) {
      if (r0.isForward) continue; // only backward rules

      // fresh copy of the rule with fresh variable names
      const r = standardizeRule(r0, varGen);

      // For backward rules, r.conclusion is the head, r.premise is the body
      const headF = new FormulaTerm(r.conclusion);
      const bodyF = new FormulaTerm(r.premise);

      // unify subject with the head formula
      let s2 = unifyTerm(goal.s, headF, subst);
      if (s2 === null) continue;

      // unify object with the body formula
      s2 = unifyTerm(goal.o, bodyF, s2);
      if (s2 === null) continue;

      results.push(s2);
    }

    return results;
  }

  // -----------------------------------------------------------------
  // log:notIncludes
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LOG_NS + "notIncludes") {
    if (!(g.o instanceof FormulaTerm)) return [];
    const body = g.o.triples;
    if (depth >= MAX_BACKWARD_DEPTH) return [];
    const visited2 = [];
    const sols = proveGoals(
      Array.from(body),
      {},
      facts,
      backRules,
      depth + 1,
      visited2,
      varGen
    );
    if (!sols.length) return [{ ...subst }];
    return [];
  }

  // -----------------------------------------------------------------
  // log:collectAllIn
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LOG_NS + "collectAllIn") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 3) return [];
    const [valueTempl, clauseTerm, listTerm] = g.s.elems;
    if (!(clauseTerm instanceof FormulaTerm)) return [];
    const body = clauseTerm.triples;
    if (depth >= MAX_BACKWARD_DEPTH) return [];
    const visited2 = [];
    const sols = proveGoals(
      Array.from(body),
      {},
      facts,
      backRules,
      depth + 1,
      visited2,
      varGen
    );

    // Collect one value per *solution*, duplicates allowed
    const collected = [];
    for (const sBody of sols) {
      const v = applySubstTerm(valueTempl, sBody);
      collected.push(v);
    }

    const collectedList = new ListTerm(collected);
    const s2 = unifyTerm(listTerm, collectedList, subst);
    return s2 !== null ? [s2] : [];
  }

  // -----------------------------------------------------------------
  // string: builtins (Notation3 Builtin Functions §4.6)
  // -----------------------------------------------------------------

  // 4.6.1 string:concatenation
  if (g.p instanceof Iri && g.p.value === STRING_NS + "concatenation") {
    if (!(g.s instanceof ListTerm)) return [];
    const parts = [];
    for (const t of g.s.elems) {
      const sStr = termToJsString(t);
      if (sStr === null) return [];
      parts.push(sStr);
    }
    const lit = makeStringLiteral(parts.join(""));

    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // 4.6.2 string:contains
  if (g.p instanceof Iri && g.p.value === STRING_NS + "contains") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.includes(oStr) ? [{ ...subst }] : [];
  }

  // 4.6.3 string:containsIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "containsIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase().includes(oStr.toLowerCase())
      ? [{ ...subst }]
      : [];
  }

  // 4.6.4 string:endsWith
  if (g.p instanceof Iri && g.p.value === STRING_NS + "endsWith") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.endsWith(oStr) ? [{ ...subst }] : [];
  }

  // 4.6.5 string:equalIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "equalIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase() === oStr.toLowerCase()
      ? [{ ...subst }]
      : [];
  }

  // 4.6.6 string:format
  // (limited: only %s and %% are supported, anything else ⇒ builtin fails)
  if (g.p instanceof Iri && g.p.value === STRING_NS + "format") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length < 1) return [];
    const fmtStr = termToJsString(g.s.elems[0]);
    if (fmtStr === null) return [];

    const args = [];
    for (let i = 1; i < g.s.elems.length; i++) {
      const aStr = termToJsString(g.s.elems[i]);
      if (aStr === null) return [];
      args.push(aStr);
    }

    const formatted = simpleStringFormat(fmtStr, args);
    if (formatted === null) return []; // unsupported format specifier(s)

    const lit = makeStringLiteral(formatted);
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // 4.6.7 string:greaterThan
  if (g.p instanceof Iri && g.p.value === STRING_NS + "greaterThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr > oStr ? [{ ...subst }] : [];
  }

  // 4.6.8 string:lessThan
  if (g.p instanceof Iri && g.p.value === STRING_NS + "lessThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr < oStr ? [{ ...subst }] : [];
  }

  // 4.6.9 string:matches
  if (g.p instanceof Iri && g.p.value === STRING_NS + "matches") {
    const sStr = termToJsString(g.s);
    const pattern = termToJsString(g.o);
    if (sStr === null || pattern === null) return [];
    let re;
    try {
      // Perl/Python-style in the spec; JS RegExp is close enough for most patterns.
      re = new RegExp(pattern);
    } catch (e) {
      return [];
    }
    return re.test(sStr) ? [{ ...subst }] : [];
  }

  // 4.6.10 string:notEqualIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notEqualIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase() !== oStr.toLowerCase()
      ? [{ ...subst }]
      : [];
  }

  // 4.6.11 string:notGreaterThan  (≤ in Unicode code order)
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notGreaterThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr <= oStr ? [{ ...subst }] : [];
  }

  // 4.6.12 string:notLessThan  (≥ in Unicode code order)
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notLessThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr >= oStr ? [{ ...subst }] : [];
  }

  // 4.6.13 string:notMatches
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notMatches") {
    const sStr = termToJsString(g.s);
    const pattern = termToJsString(g.o);
    if (sStr === null || pattern === null) return [];
    let re;
    try {
      re = new RegExp(pattern);
    } catch (e) {
      return [];
    }
    return re.test(sStr) ? [] : [{ ...subst }];
  }

  // 4.6.14 string:replace
  if (g.p instanceof Iri && g.p.value === STRING_NS + "replace") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 3) return [];
    const dataStr   = termToJsString(g.s.elems[0]);
    const searchStr = termToJsString(g.s.elems[1]);
    const replStr   = termToJsString(g.s.elems[2]);
    if (dataStr === null || searchStr === null || replStr === null) return [];

    let re;
    try {
      // Global replacement
      re = new RegExp(searchStr, "g");
    } catch (e) {
      return [];
    }

    const outStr = dataStr.replace(re, replStr);
    const lit = makeStringLiteral(outStr);

    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // 4.6.15 string:scrape
  if (g.p instanceof Iri && g.p.value === STRING_NS + "scrape") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const dataStr = termToJsString(g.s.elems[0]);
    const pattern = termToJsString(g.s.elems[1]);
    if (dataStr === null || pattern === null) return [];

    let re;
    try {
      re = new RegExp(pattern);
    } catch (e) {
      return [];
    }

    const m = re.exec(dataStr);
    // Spec says “exactly 1 group”; we just use the first capturing group if present.
    if (!m || m.length < 2) return [];
    const group = m[1];
    const lit = makeStringLiteral(group);

    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // 4.6.16 string:startsWith
  if (g.p instanceof Iri && g.p.value === STRING_NS + "startsWith") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.startsWith(oStr) ? [{ ...subst }] : [];
  }

  // -----------------------------------------------------------------
  // list:append
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LIST_NS + "append") {
    if (!(g.s instanceof ListTerm)) return [];
    const parts = g.s.elems;
    if (g.o instanceof ListTerm) {
      return listAppendSplit(parts, g.o.elems, subst);
    }
    const outElems = [];
    for (const part of parts) {
      if (!(part instanceof ListTerm)) return [];
      outElems.push(...part.elems);
    }
    const result = new ListTerm(outElems);
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = result;
      return [s2];
    }
    if (termsEqual(g.o, result)) return [{ ...subst }];
    return [];
  }

  // -----------------------------------------------------------------
  // list:firstRest
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LIST_NS + "firstRest") {
    if (g.s instanceof ListTerm) {
      if (!g.s.elems.length) return [];
      const first = g.s.elems[0];
      const rest = new ListTerm(g.s.elems.slice(1));
      const pair = new ListTerm([first, rest]);
      const s2 = unifyTerm(g.o, pair, subst);
      return s2 !== null ? [s2] : [];
    }
    if (g.o instanceof ListTerm && g.o.elems.length === 2) {
      const first = g.o.elems[0];
      const rest = g.o.elems[1];
      if (rest instanceof ListTerm) {
        const xs = [first, ...rest.elems];
        const constructed = new ListTerm(xs);
        const s2 = unifyTerm(g.s, constructed, subst);
        return s2 !== null ? [s2] : [];
      }
      if (rest instanceof Var) {
        const constructed = new OpenListTerm([first], rest.name);
        const s2 = unifyTerm(g.s, constructed, subst);
        return s2 !== null ? [s2] : [];
      }
      if (rest instanceof OpenListTerm) {
        const newPrefix = [first, ...rest.prefix];
        const constructed = new OpenListTerm(newPrefix, rest.tailVar);
        const s2 = unifyTerm(g.s, constructed, subst);
        return s2 !== null ? [s2] : [];
      }
    }
    return [];
  }

  // -----------------------------------------------------------------
  // list:member / list:in / list:length / list:notMember / list:reverse / list:sort / list:map
  // -----------------------------------------------------------------
  if (g.p instanceof Iri && g.p.value === LIST_NS + "member") {
    if (!(g.s instanceof ListTerm)) return [];
    const outs = [];
    for (const x of g.s.elems) {
      const s2 = unifyTerm(g.o, x, subst);
      if (s2 !== null) outs.push(s2);
    }
    return outs;
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "in") {
    if (!(g.o instanceof ListTerm)) return [];
    const outs = [];
    for (const x of g.o.elems) {
      const s2 = unifyTerm(g.s, x, subst);
      if (s2 !== null) outs.push(s2);
    }
    return outs;
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "length") {
    if (!(g.s instanceof ListTerm)) return [];
    const nTerm = new Literal(String(g.s.elems.length));
    const s2 = unifyTerm(g.o, nTerm, subst);
    return s2 !== null ? [s2] : [];
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "notMember") {
    if (!(g.s instanceof ListTerm)) return [];
    for (const el of g.s.elems) {
      if (unifyTerm(g.o, el, subst) !== null) return [];
    }
    return [{ ...subst }];
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "reverse") {
    if (g.s instanceof ListTerm) {
      const rev = [...g.s.elems].reverse();
      const rterm = new ListTerm(rev);
      const s2 = unifyTerm(g.o, rterm, subst);
      return s2 !== null ? [s2] : [];
    }
    if (g.o instanceof ListTerm) {
      const rev = [...g.o.elems].reverse();
      const rterm = new ListTerm(rev);
      const s2 = unifyTerm(g.s, rterm, subst);
      return s2 !== null ? [s2] : [];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "sort") {
    function cmpTermForSort(a, b) {
      if (a instanceof Literal && b instanceof Literal) {
        const [lexA] = literalParts(a.value);
        const [lexB] = literalParts(b.value);
        const sa = stripQuotes(lexA);
        const sb = stripQuotes(lexB);
        const na = Number(sa);
        const nb = Number(sb);
        if (!Number.isNaN(na) && !Number.isNaN(nb)) {
          if (na < nb) return -1;
          if (na > nb) return 1;
          return 0;
        }
        if (sa < sb) return -1;
        if (sa > sb) return 1;
        return 0;
      }
      if (a instanceof ListTerm && b instanceof ListTerm) {
        const xs = a.elems;
        const ys = b.elems;
        let i = 0;
        // lexicographic
        while (true) {
          if (i >= xs.length && i >= ys.length) return 0;
          if (i >= xs.length) return -1;
          if (i >= ys.length) return 1;
          const c = cmpTermForSort(xs[i], ys[i]);
          if (c !== 0) return c;
          i++;
        }
      }
      if (a instanceof Iri && b instanceof Iri) {
        if (a.value < b.value) return -1;
        if (a.value > b.value) return 1;
        return 0;
      }
      // lists before non-lists
      if (a instanceof ListTerm && !(b instanceof ListTerm)) return -1;
      if (!(a instanceof ListTerm) && b instanceof ListTerm) return 1;
      const sa = JSON.stringify(a);
      const sb = JSON.stringify(b);
      if (sa < sb) return -1;
      if (sa > sb) return 1;
      return 0;
    }

    let inputList;
    if (g.s instanceof ListTerm) inputList = g.s.elems;
    else if (g.o instanceof ListTerm) inputList = g.o.elems;
    else return [];

    if (!inputList.every(e => isGroundTerm(e))) return [];

    const sortedList = [...inputList].sort(cmpTermForSort);
    const sortedTerm = new ListTerm(sortedList);
    if (g.s instanceof ListTerm) {
      const s2 = unifyTerm(g.o, sortedTerm, subst);
      return s2 !== null ? [s2] : [];
    }
    if (g.o instanceof ListTerm) {
      const s2 = unifyTerm(g.s, sortedTerm, subst);
      return s2 !== null ? [s2] : [];
    }
    return [];
  }

  if (g.p instanceof Iri && g.p.value === LIST_NS + "map") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const [inputTerm, predTerm] = g.s.elems;
    if (!(inputTerm instanceof ListTerm)) return [];
    const inputList = inputTerm.elems;
    if (!(predTerm instanceof Iri)) return [];
    const pred = new Iri(predTerm.value);
    if (!isBuiltinPred(pred)) return [];
    if (!inputList.every(e => isGroundTerm(e))) return [];

    const results = [];
    for (const el of inputList) {
      const yvar = new Var("_mapY");
      const goal2 = new Triple(el, pred, yvar);
      const sols = evalBuiltin(goal2, subst, facts, backRules, depth + 1, varGen);
      if (!sols.length) return [];
      const yval = applySubstTerm(yvar, sols[0]);
      if (yval instanceof Var) return [];
      results.push(yval);
    }
    const outList = new ListTerm(results);
    const s2 = unifyTerm(g.o, outList, subst);
    return s2 !== null ? [s2] : [];
  }

  // Unknown builtin
  return [];
}

function isBuiltinPred(p) {
  return (
    p instanceof Iri &&
    (p.value.startsWith(MATH_NS) ||
      p.value.startsWith(LOG_NS) ||
      p.value.startsWith(STRING_NS) ||
      p.value.startsWith(TIME_NS) ||
      p.value.startsWith(LIST_NS))
  );
}

// ============================================================================
// Backward proof (SLD-style)
// ============================================================================

function standardizeRule(rule, gen) {
  function renameTerm(t, vmap, genArr) {
    if (t instanceof Var) {
      if (!vmap.hasOwnProperty(t.name)) {
        const name = `${t.name}__${genArr[0]}`;
        genArr[0] += 1;
        vmap[t.name] = name;
      }
      return new Var(vmap[t.name]);
    }
    if (t instanceof ListTerm) {
      return new ListTerm(t.elems.map(e => renameTerm(e, vmap, genArr)));
    }
    if (t instanceof OpenListTerm) {
      const newXs = t.prefix.map(e => renameTerm(e, vmap, genArr));
      if (!vmap.hasOwnProperty(t.tailVar)) {
        const name = `${t.tailVar}__${genArr[0]}`;
        genArr[0] += 1;
        vmap[t.tailVar] = name;
      }
      const newTail = vmap[t.tailVar];
      return new OpenListTerm(newXs, newTail);
    }
    if (t instanceof FormulaTerm) {
      return new FormulaTerm(
        t.triples.map(tr =>
          new Triple(
            renameTerm(tr.s, vmap, genArr),
            renameTerm(tr.p, vmap, genArr),
            renameTerm(tr.o, vmap, genArr)
          )
        )
      );
    }
    return t;
  }

  const vmap2 = {};
  const premise = rule.premise.map(
    tr =>
      new Triple(
        renameTerm(tr.s, vmap2, gen),
        renameTerm(tr.p, vmap2, gen),
        renameTerm(tr.o, vmap2, gen)
      )
  );
  const conclusion = rule.conclusion.map(
    tr =>
      new Triple(
        renameTerm(tr.s, vmap2, gen),
        renameTerm(tr.p, vmap2, gen),
        renameTerm(tr.o, vmap2, gen)
      )
  );
  return new Rule(premise, conclusion, rule.isForward, rule.isFuse);
}

function listHasTriple(list, tr) {
  return list.some(t => triplesEqual(t, tr));
}

function solveSingleGoal(goal, facts, backRules, depth, visited, varGen) {
  // builtins are pure
  if (isBuiltinPred(goal.p)) {
    return evalBuiltin(goal, {}, facts, backRules, depth, varGen);
  }
  if (depth > MAX_BACKWARD_DEPTH) return [];
  if (listHasTriple(visited, goal)) return [];
  visited.push(goal);

  const results = [];

  // -------------------------------------------------------------------
  // 1) Match known facts, with cheap predicate filtering
  // -------------------------------------------------------------------
  if (goal.p instanceof Iri) {
    const targetPred = goal.p.value;
    for (const f of facts) {
      const fp = f.p;
      // Facts are ground; if predicate IRIs don't match, skip unify.
      if (fp instanceof Iri && fp.value !== targetPred) continue;
      const s2 = unifyTriple(goal, f, {});
      if (s2 !== null) results.push(s2);
    }
  } else {
    // Non-IRI predicate (variable, blank, etc.) → must try all facts.
    for (const f of facts) {
      const s2 = unifyTriple(goal, f, {});
      if (s2 !== null) results.push(s2);
    }
  }

  // -------------------------------------------------------------------
  // 2) Backward rules, also filtered by head predicate before renaming
  // -------------------------------------------------------------------
  for (const r of backRules) {
    if (r.conclusion.length !== 1) continue;

    // Use the original rule head (before standardization) for a cheap filter
    if (goal.p instanceof Iri) {
      const rawHead = r.conclusion[0];
      if (rawHead.p instanceof Iri && rawHead.p.value !== goal.p.value) {
        continue;
      }
    }

    const rStd = standardizeRule(r, varGen);
    const head = rStd.conclusion[0];

    const s2 = unifyTriple(head, goal, {});
    if (s2 === null) continue;

    const body = rStd.premise.map(b => applySubstTriple(b, s2));
    const bodySolutions = proveGoals(
      body,
      s2,
      facts,
      backRules,
      depth + 1,
      visited,
      varGen
    );
    results.push(...bodySolutions);
  }

  visited.pop();
  return results;
}

function proveGoals(
  goals,
  subst,
  facts,
  backRules,
  depth,
  visited,
  varGen
) {
  if (!goals.length) return [{ ...subst }];
  if (depth > MAX_BACKWARD_DEPTH) return [];

  const goal0 = applySubstTriple(goals[0], subst);
  const rest = goals.slice(1);
  const results = [];

  const deltas = solveSingleGoal(goal0, facts, backRules, depth, visited, varGen);
  for (const delta of deltas) {
    const composed = composeSubst(subst, delta);
    if (composed === null) continue;
    if (!rest.length) {
      results.push(composed);
    } else {
      const tailSolutions = proveGoals(
        rest,
        composed,
        facts,
        backRules,
        depth + 1,
        visited,
        varGen
      );
      results.push(...tailSolutions);
    }
  }

  return results;
}

// ============================================================================
// Forward chaining to fixpoint
// ============================================================================

function forwardChain(facts, forwardRules, backRules) {
  const factList = facts.slice();
  const derivedForward = [];
  const varGen = [0];
  const skCounter = [0];

  // Make rules visible to introspection builtins
  backRules.__allForwardRules  = forwardRules;
  backRules.__allBackwardRules = backRules;

  while (true) {
    let changed = false;

    for (let i = 0; i < forwardRules.length; i++) {
      const r = forwardRules[i];
      const empty = {};
      const visited = [];
      const sols = proveGoals(
        r.premise.slice(),
        empty,
        facts,
        backRules,
        0,
        visited,
        varGen
      );

      // Inference fuse
      if (r.isFuse && sols.length) {
        console.log("# Inference fuse triggered: a { ... } => false. rule fired.");
        process.exit(2);
      }

      for (const s of sols) {
        const instantiatedPremises = r.premise.map(b => applySubstTriple(b, s));

        for (const cpat of r.conclusion) {
          const instantiated = applySubstTriple(cpat, s);

          const isFwRuleTriple =
            isLogImplies(instantiated.p) &&
            instantiated.s instanceof FormulaTerm &&
            instantiated.o instanceof FormulaTerm;

          const isBwRuleTriple =
            isLogImpliedBy(instantiated.p) &&
            instantiated.s instanceof FormulaTerm &&
            instantiated.o instanceof FormulaTerm;

          if (isFwRuleTriple || isBwRuleTriple) {
            if (
              !hasAlphaEquiv(factList, instantiated)
            ) {
              factList.push(instantiated);
              facts.push(instantiated);
              derivedForward.push(
                new DerivedFact(
                  instantiated,
                  r,
                  instantiatedPremises.slice(),
                  { ...s }
                )
              );
              changed = true;
            }

            if (
              instantiated.s instanceof FormulaTerm &&
              instantiated.o instanceof FormulaTerm
            ) {
              const left = instantiated.s.triples;
              const right = instantiated.o.triples;
              if (isFwRuleTriple) {
                const [premise0, conclusion] = liftBlankRuleVars(left, right);
                const premise = reorderPremiseForConstraints(premise0);
                const newRule = new Rule(
                  premise,
                  conclusion,
                  true,
                  false
                );
                const already = forwardRules.some(
                  rr =>
                    rr.isForward === newRule.isForward &&
                    rr.isFuse === newRule.isFuse &&
                    triplesListEqual(rr.premise, newRule.premise) &&
                    triplesListEqual(rr.conclusion, newRule.conclusion)
                );
                if (!already) forwardRules.push(newRule);
              } else if (isBwRuleTriple) {
                const [premise, conclusion] = liftBlankRuleVars(right, left);
                const newRule = new Rule(
                  premise,
                  conclusion,
                  false,
                  false
                );
                const already = backRules.some(
                  rr =>
                    rr.isForward === newRule.isForward &&
                    rr.isFuse === newRule.isFuse &&
                    triplesListEqual(rr.premise, newRule.premise) &&
                    triplesListEqual(rr.conclusion, newRule.conclusion)
                );
                if (!already) backRules.push(newRule);
              }
            }

            continue; // skip normal fact handling
          }

          // Only skolemize blank nodes that occur explicitly in the rule head
          const skMap = {};
          const inst = skolemizeTripleForHeadBlanks(instantiated, r.headBlankLabels, skMap, skCounter
          );
          if (!isGroundTriple(inst)) continue;
          if (hasAlphaEquiv(factList, inst)) continue;
          factList.push(inst);
          facts.push(inst);
          derivedForward.push(
            new DerivedFact(
              inst,
              r,
              instantiatedPremises.slice(),
              { ...s }
            )
          );
          changed = true;
        }
      }
    }

    if (!changed) break;
  }

  return derivedForward;
}

// ============================================================================
// Pretty printing as N3/Turtle
// ============================================================================

function termToN3(t, pref) {
  if (t instanceof Iri) {
    const i = t.value;
    const q = pref.shrinkIri(i);
    if (q !== null) return q;
    if (i.startsWith("_:")) return i;
    return `<${i}>`;
  }
  if (t instanceof Literal) return t.value;
  if (t instanceof Var) return `?${t.name}`;
  if (t instanceof Blank) return t.label;
  if (t instanceof ListTerm) {
    const inside = t.elems.map(e => termToN3(e, pref));
    return "(" + inside.join(" ") + ")";
  }
  if (t instanceof OpenListTerm) {
    const inside = t.prefix.map(e => termToN3(e, pref));
    inside.push("?" + t.tailVar);
    return "(" + inside.join(" ") + ")";
  }
  if (t instanceof FormulaTerm) {
    let s = "{\n";
    for (const tr of t.triples) {
      let line = tripleToN3(tr, pref).trimEnd();
      if (line) s += "    " + line + "\n";
    }
    s += "}";
    return s;
  }
  return JSON.stringify(t);
}

function tripleToN3(tr, prefixes) {
  // log:implies / log:impliedBy as => / <= syntactic sugar everywhere
  if (isLogImplies(tr.p)) {
    const s = termToN3(tr.s, prefixes);
    const o = termToN3(tr.o, prefixes);
    return `${s} => ${o} .`;
  }

  if (isLogImpliedBy(tr.p)) {
    const s = termToN3(tr.s, prefixes);
    const o = termToN3(tr.o, prefixes);
    return `${s} <= ${o} .`;
  }

  const s = termToN3(tr.s, prefixes);
  const p = isRdfTypePred(tr.p) ? "a" : termToN3(tr.p, prefixes);
  const o = termToN3(tr.o, prefixes);
  return `${s} ${p} ${o} .`;
}

function printExplanation(df, prefixes) {
  console.log(
    "# ----------------------------------------------------------------------"
  );
  console.log("# Proof for derived triple:");

  // Fact line(s), indented 2 spaces after '# '
  for (const line of tripleToN3(df.fact, prefixes).split(/\r?\n/)) {
    const stripped = line.replace(/\s+$/, "");
    if (stripped) {
      console.log("#   " + stripped);
    }
  }

  if (!df.premises.length) {
    console.log(
      "# This triple is the head of a forward rule with an empty premise,"
    );
    console.log(
      "# so it holds unconditionally whenever the program is loaded."
    );
  } else {
    console.log(
      "# It holds because the following instance of the rule body is provable:"
    );

    // Premises, also indented 2 spaces after '# '
    for (const prem of df.premises) {
      for (const line of tripleToN3(prem, prefixes).split(/\r?\n/)) {
        const stripped = line.replace(/\s+$/, "");
        if (stripped) {
          console.log("#   " + stripped);
        }
      }
    }

    console.log("# via the schematic forward rule:");

    // Rule pretty-printed
    console.log("#   {");
    for (const tr of df.rule.premise) {
      for (const line of tripleToN3(tr, prefixes).split(/\r?\n/)) {
        const stripped = line.replace(/\s+$/, "");
        if (stripped) {
          console.log("#     " + stripped);
        }
      }
    }
    console.log("#   } => {");
    for (const tr of df.rule.conclusion) {
      for (const line of tripleToN3(tr, prefixes).split(/\r?\n/)) {
        const stripped = line.replace(/\s+$/, "");
        if (stripped) {
          console.log("#     " + stripped);
        }
      }
    }
    console.log("#   } .");
  }

  // Substitution block
  const ruleVars = varsInRule(df.rule);
  const visibleNames = Object.keys(df.subst)
    .filter(name => ruleVars.has(name))
    .sort();

  if (visibleNames.length) {
    console.log("# with substitution (on rule variables):");
    for (const v of visibleNames) {
      const fullTerm = applySubstTerm(new Var(v), df.subst);
      const rendered = termToN3(fullTerm, prefixes);
      const lines = rendered.split(/\r?\n/);

      if (lines.length === 1) {
        // single-line term
        const stripped = lines[0].replace(/\s+$/, "");
        if (stripped) {
          console.log("#   ?" + v + " = " + stripped);
        }
      } else {
        // multi-line term (e.g. a formula)
        const first = lines[0].trimEnd(); // usually "{"
        if (first) {
          console.log("#   ?" + v + " = " + first);
        }
        for (let i = 1; i < lines.length; i++) {
          const stripped = lines[i].trim();
          if (!stripped) continue;
          if (i === lines.length - 1) {
            // closing brace
            console.log("#   " + stripped);
          } else {
            // inner triple lines
            console.log("#     " + stripped);
          }
        }
      }
    }
  }

  console.log(
    "# Therefore the derived triple above is entailed by the rules and facts."
  );
  console.log(
    "# ----------------------------------------------------------------------\n"
  );
}

// ============================================================================
// Misc helpers
// ============================================================================

function localIsoDateTimeString(d) {
  function pad(n, width = 2) {
    return String(n).padStart(width, "0");
  }
  const year = d.getFullYear();
  const month = d.getMonth() + 1;
  const day = d.getDate();
  const hour = d.getHours();
  const min = d.getMinutes();
  const sec = d.getSeconds();
  const ms = d.getMilliseconds();
  const offsetMin = -d.getTimezoneOffset(); // minutes east of UTC
  const sign = offsetMin >= 0 ? "+" : "-";
  const abs = Math.abs(offsetMin);
  const oh = Math.floor(abs / 60);
  const om = abs % 60;
  const msPart = ms ? "." + String(ms).padStart(3, "0") : "";
  return (
    pad(year, 4) +
    "-" +
    pad(month) +
    "-" +
    pad(day) +
    "T" +
    pad(hour) +
    ":" +
    pad(min) +
    ":" +
    pad(sec) +
    msPart +
    sign +
    pad(oh) +
    ":" +
    pad(om)
  );
}

// ============================================================================
// CLI entry point
// ============================================================================

function main() {
  const args = process.argv;
  if (args.length !== 3) {
    console.error("Usage: eyeling.js <file.n3>");
    process.exit(1);
  }
  const path = args[2];
  let text;
  try {
    const fs = require("fs");
    text = fs.readFileSync(path, { encoding: "utf8" });
  } catch (e) {
    console.error(`Error reading file ${JSON.stringify(path)}: ${e.message}`);
    process.exit(1);
  }

  const toks = lex(text);
  const parser = new Parser(toks);
  const [prefixes, triples, frules, brules] = parser.parseDocument();

  const facts = triples.filter(tr => isGroundTriple(tr));
  const derived = forwardChain(facts, frules, brules);

  const derivedTriples = derived.map(df => df.fact);
  const usedPrefixes = prefixes.prefixesUsedForOutput(derivedTriples);

  for (const [pfx, base] of usedPrefixes) {
    if (pfx === "") console.log(`@prefix : <${base}> .`);
    else console.log(`@prefix ${pfx}: <${base}> .`);
  }
  if (derived.length && usedPrefixes.length) console.log();

  for (const df of derived) {
    printExplanation(df, prefixes);
    console.log(tripleToN3(df.fact, prefixes));
    console.log();
  }
}

if (require.main === module) {
  main();
}

