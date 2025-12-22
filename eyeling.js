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
const nodeCrypto = require("crypto");

// ============================================================================
// Namespace constants
// ============================================================================

const RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS_NS = "http://www.w3.org/2000/01/rdf-schema#";
const OWL_NS = "http://www.w3.org/2002/07/owl#";
const XSD_NS = "http://www.w3.org/2001/XMLSchema#";
const CRYPTO_NS = "http://www.w3.org/2000/10/swap/crypto#";
const MATH_NS = "http://www.w3.org/2000/10/swap/math#";
const TIME_NS = "http://www.w3.org/2000/10/swap/time#";
const LIST_NS = "http://www.w3.org/2000/10/swap/list#";
const LOG_NS = "http://www.w3.org/2000/10/swap/log#";
const STRING_NS = "http://www.w3.org/2000/10/swap/string#";
const SKOLEM_NS = "https://eyereasoner.github.io/.well-known/genid/";
const RDF_JSON_DT = RDF_NS + "JSON";

function isRdfJsonDatatype(dt) {
  // dt comes from literalParts() and may be expanded or prefixed depending on parsing/printing.
  return dt === null || dt === RDF_JSON_DT || dt === "rdf:JSON";
}

function termToJsonText(t) {
  if (!(t instanceof Literal)) return null;
  const [lex, dt] = literalParts(t.value);
  if (!isRdfJsonDatatype(dt)) return null;
  // decode escapes for short literals; long literals are taken verbatim
  return termToJsStringDecoded(t);
}

function makeRdfJsonLiteral(jsonText) {
  // Prefer a readable long literal when safe; fall back to short if needed.
  if (!jsonText.includes('"""')) {
    return new Literal('"""' + jsonText + '"""^^<' + RDF_JSON_DT + '>');
  }
  return new Literal(JSON.stringify(jsonText) + '^^<' + RDF_JSON_DT + '>');
}

// For a single reasoning run, this maps a canonical representation
// of the subject term in log:skolem to a Skolem IRI.
const skolemCache = new Map();

// Cache for string:jsonPointer: jsonText -> { parsed: any|null, ptrCache: Map<string, Term|null> }
const jsonPointerCache = new Map();

// Controls whether human-readable proof comments are printed.
let proofCommentsEnabled = true;

// ----------------------------------------------------------------------------
// Deterministic time support
// ----------------------------------------------------------------------------
// If set, overrides time:localTime across the whole run (and across runs if you
// pass the same value). Store as xsd:dateTime *lexical* string (no quotes).
let fixedNowLex = null;

// If not fixed, we still memoize one value per run to avoid re-firing rules.
let runNowLex = null;

function normalizeDateTimeLex(s) {
  // Accept: 2025-... , "2025-..." , "2025-..."^^xsd:dateTime , "..."^^<...>
  if (s == null) return null;
  let t = String(s).trim();
  const caret = t.indexOf("^^");
  if (caret >= 0) t = t.slice(0, caret).trim();
  if (t.startsWith('"') && t.endsWith('"') && t.length >= 2) t = t.slice(1, -1);
  return t.trim();
}

function utcIsoDateTimeStringFromEpochSeconds(sec) {
  const ms = sec * 1000;
  const d = new Date(ms);
  function pad(n, w = 2) { return String(n).padStart(w, "0"); }
  const year = d.getUTCFullYear();
  const month = d.getUTCMonth() + 1;
  const day = d.getUTCDate();
  const hour = d.getUTCHours();
  const min = d.getUTCMinutes();
  const s2 = d.getUTCSeconds();
  const ms2 = d.getUTCMilliseconds();
  const msPart = ms2 ? "." + String(ms2).padStart(3, "0") : "";
  return (
    pad(year, 4) + "-" + pad(month) + "-" + pad(day) + "T" +
    pad(hour) + ":" + pad(min) + ":" + pad(s2) + msPart +
    "+00:00"
  );
}

function getNowLex() {
  if (fixedNowLex) return fixedNowLex;
  if (runNowLex) return runNowLex;
  runNowLex = localIsoDateTimeString(new Date());
  return runNowLex;
}

// Deterministic pseudo-UUID from a string key (for log:skolem).
// Not cryptographically strong, but stable and platform-independent.
function deterministicSkolemIdFromKey(key) {
  // Four 32-bit FNV-1a style accumulators with slight variation
  let h1 = 0x811c9dc5;
  let h2 = 0x811c9dc5;
  let h3 = 0x811c9dc5;
  let h4 = 0x811c9dc5;

  for (let i = 0; i < key.length; i++) {
    const c = key.charCodeAt(i);

    h1 ^= c;
    h1 = (h1 * 0x01000193) >>> 0;

    h2 ^= c + 1;
    h2 = (h2 * 0x01000193) >>> 0;

    h3 ^= c + 2;
    h3 = (h3 * 0x01000193) >>> 0;

    h4 ^= c + 3;
    h4 = (h4 * 0x01000193) >>> 0;
  }

  const hex = [h1, h2, h3, h4]
    .map(h => h.toString(16).padStart(8, "0"))
    .join(""); // 32 hex chars

  // Format like a UUID: 8-4-4-4-12
  return (
    hex.slice(0, 8) + "-" +
    hex.slice(8, 12) + "-" +
    hex.slice(12, 16) + "-" +
    hex.slice(16, 20) + "-" +
    hex.slice(20)
  );
}

let runLocalTimeCache = null;

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
        // N3 syntactic sugar: '=' means owl:sameAs
        tokens.push(new Token("Equals"));
        i += 1;
        continue;
      }
    }

    if (c === "<") {
      if (peek(1) === "=") {
        tokens.push(new Token("OpImpliedBy"));
        i += 2;
        continue;
      }
      // N3 predicate inversion: "<-" (swap subject/object for this predicate)
      if (peek(1) === "-") {
        tokens.push(new Token("OpPredInvert"));
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

    // 4) Path + datatype operators: !, ^, ^^
    if (c === "!") {
      tokens.push(new Token("OpPathFwd"));
      i += 1;
      continue;
    }
    if (c === "^") {
      if (peek(1) === "^") {
        tokens.push(new Token("HatHat"));
        i += 2;
        continue;
      }
      tokens.push(new Token("OpPathRev"));
      i += 1;
      continue;
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

    // String literal: short "..." or long """..."""
    if (c === '"') {
      // Long string literal """ ... """
      if (peek(1) === '"' && peek(2) === '"') {
        i += 3; // consume opening """
        const sChars = [];
        let closed = false;
        while (i < n) {
          // closing delimiter?
          if (peek() === '"' && peek(1) === '"' && peek(2) === '"') {
            i += 3; // consume closing """
            closed = true;
            break;
          }
          let cc = chars[i];
          i++;
          if (cc === "\\") {
            // Preserve escapes verbatim (same behavior as short strings)
            if (i < n) {
              const esc = chars[i];
              i++;
              sChars.push("\\");
              sChars.push(esc);
            }
            continue;
          }
          sChars.push(cc);
        }
        if (!closed) throw new Error('Unterminated long string literal """..."""');
        const s = '"""' + sChars.join("") + '"""';
        tokens.push(new Token("Literal", s));
        continue;
      }

      // Short string literal " ... "
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

    // Directives: @prefix, @base (and language tags after string literals)
    if (c === "@") {
      const prevTok = tokens.length ? tokens[tokens.length - 1] : null;
      const prevWasQuotedLiteral =
        prevTok &&
        prevTok.typ === "Literal" &&
        typeof prevTok.value === "string" &&
        prevTok.value.startsWith('"');

      i++; // consume '@'

      if (prevWasQuotedLiteral) {
        // N3 grammar production LANGTAG:
        //   "@" [a-zA-Z]+ ("-" [a-zA-Z0-9]+)*
        const tagChars = [];
        let cc = peek();
        if (cc === null || !/[A-Za-z]/.test(cc)) {
          throw new Error("Invalid language tag (expected [A-Za-z] after '@')");
        }
        while ((cc = peek()) !== null && /[A-Za-z]/.test(cc)) {
          tagChars.push(cc);
          i++;
        }
        while (peek() === "-") {
          tagChars.push("-");
          i++; // consume '-'
          const segChars = [];
          while ((cc = peek()) !== null && /[A-Za-z0-9]/.test(cc)) {
            segChars.push(cc);
            i++;
          }
          if (!segChars.length) {
            throw new Error("Invalid language tag (expected [A-Za-z0-9]+ after '-')");
          }
          tagChars.push(...segChars);
        }
        tokens.push(new Token("LangTag", tagChars.join("")));
        continue;
      }

      // Otherwise, treat as a directive (@prefix, @base)
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
    m["genid"] = SKOLEM_NS;
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
  } else if (t instanceof Literal) {
    const [_lex, dt] = literalParts(t.value);
    if (dt) out.push(dt); // so rdf/xsd prefixes are emitted when only used in ^^...
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
          let more;

          if (this.peek().typ === "Dot") {
            // Allow a bare blank-node property list statement, e.g. `[ a :Statement ].`
            const lastTok = this.toks[this.pos - 1];
            if (this.pendingTriples.length > 0 && lastTok && lastTok.typ === "RBracket") {
              more = this.pendingTriples;
              this.pendingTriples = [];
              this.next(); // consume '.'
            } else {
              throw new Error(`Unexpected '.' after term; missing predicate/object list`);
            }
          } else {
            more = this.parsePredicateObjectList(first);
            this.expectDot();
          }

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
    let t = this.parsePathItem();

    while (this.peek().typ === "OpPathFwd" || this.peek().typ === "OpPathRev") {
      const dir = this.next().typ;      // OpPathFwd | OpPathRev
      const pred = this.parsePathItem();

      this.blankCounter += 1;
      const bn = new Blank(`_:b${this.blankCounter}`);

      this.pendingTriples.push(
        dir === "OpPathFwd"
          ? new Triple(t, pred, bn)
          : new Triple(bn, pred, t)
      );

      t = bn;
    }

    return t;
  }

  parsePathItem() {
    const tok = this.next();
    const typ = tok.typ;
    const val = tok.value;

    if (typ === "Equals") {
      return new Iri(OWL_NS + "sameAs");
    }

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

      // Optional language tag: "..."@en, per N3 LANGTAG production.
      if (this.peek().typ === "LangTag") {
        // Only quoted string literals can carry a language tag.
        if (!(s.startsWith('"') && s.endsWith('"'))) {
          throw new Error("Language tag is only allowed on quoted string literals");
        }
        const langTok = this.next();
        const lang = langTok.value || "";
        s = `${s}@${lang}`;

        // N3/Turtle: language tags and datatypes are mutually exclusive.
        if (this.peek().typ === "HatHat") {
          throw new Error("A literal cannot have both a language tag (@...) and a datatype (^^...)");
        }
      }

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
      let invert = false;
      if (this.peek().typ === "Ident" && (this.peek().value || "") === "a") {
        this.next();
        pred = new Iri(RDF_NS + "type");
      } else if (this.peek().typ === "OpPredInvert") {
        this.next(); // consume "<-"
        pred = this.parseTerm();
        invert = true;
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
        this.pendingTriples.push(invert ? new Triple(o, pred, subj)
                                       : new Triple(subj, pred, o));
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
        // Allow a bare blank-node property list statement inside a formula, e.g. `{ [ a :X ]. }`
        if (this.peek().typ === "Dot" || this.peek().typ === "RBrace") {
          const lastTok = this.toks[this.pos - 1];
          if (this.pendingTriples.length > 0 && lastTok && lastTok.typ === "RBracket") {
            triples.push(...this.pendingTriples);
            this.pendingTriples = [];
            if (this.peek().typ === "Dot") this.next();
            continue;
          }
        }

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

    // If the SUBJECT was a path, emit its helper triples first
    if (this.pendingTriples.length > 0) {
      out.push(...this.pendingTriples);
      this.pendingTriples = [];
    }

    while (true) {
      let verb;
      let invert = false;

      if (this.peek().typ === "Ident" && (this.peek().value || "") === "a") {
        this.next();
        verb = new Iri(RDF_NS + "type");
      } else if (this.peek().typ === "OpPredInvert") {
        this.next(); // "<-"
        verb = this.parseTerm();
        invert = true;
      } else {
        verb = this.parseTerm();
      }

      const objects = this.parseObjectList();

      // If VERB or OBJECTS contained paths, their helper triples must come
      // before the triples that consume the path results (Easter depends on this).
      if (this.pendingTriples.length > 0) {
        out.push(...this.pendingTriples);
        this.pendingTriples = [];
      }

      for (const o of objects) {
        out.push(new Triple(invert ? o : subject, verb, invert ? subject : o));
      }

      if (this.peek().typ === "Semicolon") {
        this.next();
        if (this.peek().typ === "Dot") break;
        continue;
      }
      break;
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
    return alphaEqFormulaTriples(a.triples, b.triples);
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

// Alpha-equivalence for quoted formulas, up to *variable* and blank-node renaming.
// Treats a formula as an unordered set of triples (order-insensitive match).
function alphaEqVarName(x, y, vmap) {
  if (vmap.hasOwnProperty(x)) return vmap[x] === y;
  vmap[x] = y;
  return true;
}

function alphaEqTermInFormula(a, b, vmap, bmap) {
  // Blank nodes: renamable
  if (a instanceof Blank && b instanceof Blank) {
    const x = a.label;
    const y = b.label;
    if (bmap.hasOwnProperty(x)) return bmap[x] === y;
    bmap[x] = y;
    return true;
  }

  // Variables: renamable (ONLY inside quoted formulas)
  if (a instanceof Var && b instanceof Var) {
    return alphaEqVarName(a.name, b.name, vmap);
  }

  if (a instanceof Iri && b instanceof Iri) return a.value === b.value;
  if (a instanceof Literal && b instanceof Literal) return a.value === b.value;

  if (a instanceof ListTerm && b instanceof ListTerm) {
    if (a.elems.length !== b.elems.length) return false;
    for (let i = 0; i < a.elems.length; i++) {
      if (!alphaEqTermInFormula(a.elems[i], b.elems[i], vmap, bmap)) return false;
    }
    return true;
  }

  if (a instanceof OpenListTerm && b instanceof OpenListTerm) {
    if (a.prefix.length !== b.prefix.length) return false;
    for (let i = 0; i < a.prefix.length; i++) {
      if (!alphaEqTermInFormula(a.prefix[i], b.prefix[i], vmap, bmap)) return false;
    }
    // tailVar is a var-name string, so treat it as renamable too
    return alphaEqVarName(a.tailVar, b.tailVar, vmap);
  }

  // Nested formulas: compare with fresh maps (separate scope)
  if (a instanceof FormulaTerm && b instanceof FormulaTerm) {
    return alphaEqFormulaTriples(a.triples, b.triples);
  }

  return false;
}

function alphaEqTripleInFormula(a, b, vmap, bmap) {
  return (
    alphaEqTermInFormula(a.s, b.s, vmap, bmap) &&
    alphaEqTermInFormula(a.p, b.p, vmap, bmap) &&
    alphaEqTermInFormula(a.o, b.o, vmap, bmap)
  );
}

function alphaEqFormulaTriples(xs, ys) {
  if (xs.length !== ys.length) return false;
  // Fast path: exact same sequence.
  if (triplesListEqual(xs, ys)) return true;

  // Order-insensitive backtracking match, threading var/blank mappings.
  const used = new Array(ys.length).fill(false);

  function step(i, vmap, bmap) {
    if (i >= xs.length) return true;
    const x = xs[i];
    for (let j = 0; j < ys.length; j++) {
      if (used[j]) continue;
      const y = ys[j];
      // Cheap pruning when both predicates are IRIs.
      if (x.p instanceof Iri && y.p instanceof Iri && x.p.value !== y.p.value) continue;

      const v2 = { ...vmap };
      const b2 = { ...bmap };
      if (!alphaEqTripleInFormula(x, y, v2, b2)) continue;

      used[j] = true;
      if (step(i + 1, v2, b2)) return true;
      used[j] = false;
    }
    return false;
  }

  return step(0, {}, {});
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
    // formulas are alpha-equivalent up to var/blank renaming
    return alphaEqFormulaTriples(a.triples, b.triples);
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
// Indexes (facts + backward rules)
// ============================================================================
//
// Facts:
//   - __byPred: Map<predicateIRI, Triple[]>
//   - __byPO:   Map<predicateIRI, Map<objectKey, Triple[]>>
//   - __keySet: Set<"S\tP\tO"> for IRI/Literal-only triples (fast dup check)
//
// Backward rules:
//   - __byHeadPred:   Map<headPredicateIRI, Rule[]>
//   - __wildHeadPred: Rule[] (non-IRI head predicate)

function termFastKey(t) {
  if (t instanceof Iri) return "I:" + t.value;
  if (t instanceof Literal) return "L:" + t.value;
  return null;
}

function tripleFastKey(tr) {
  const ks = termFastKey(tr.s);
  const kp = termFastKey(tr.p);
  const ko = termFastKey(tr.o);
  if (ks === null || kp === null || ko === null) return null;
  return ks + "\t" + kp + "\t" + ko;
}

function ensureFactIndexes(facts) {
  if (facts.__byPred && facts.__byPO && facts.__keySet) return;

  Object.defineProperty(facts, "__byPred", { value: new Map(), enumerable: false, writable: true });
  Object.defineProperty(facts, "__byPO",   { value: new Map(), enumerable: false, writable: true });
  Object.defineProperty(facts, "__keySet", { value: new Set(), enumerable: false, writable: true });

  for (const f of facts) indexFact(facts, f);
}

function indexFact(facts, tr) {
  if (tr.p instanceof Iri) {
    const pk = tr.p.value;

    let pb = facts.__byPred.get(pk);
    if (!pb) { pb = []; facts.__byPred.set(pk, pb); }
    pb.push(tr);

    const ok = termFastKey(tr.o);
    if (ok !== null) {
      let po = facts.__byPO.get(pk);
      if (!po) { po = new Map(); facts.__byPO.set(pk, po); }
      let pob = po.get(ok);
      if (!pob) { pob = []; po.set(ok, pob); }
      pob.push(tr);
    }
  }

  const key = tripleFastKey(tr);
  if (key !== null) facts.__keySet.add(key);
}

function candidateFacts(facts, goal) {
  ensureFactIndexes(facts);

  if (goal.p instanceof Iri) {
    const pk = goal.p.value;

    const ok = termFastKey(goal.o);
    if (ok !== null) {
      const po = facts.__byPO.get(pk);
      if (po) {
        const pob = po.get(ok);
        if (pob) return pob;
      }
    }

    return facts.__byPred.get(pk) || [];
  }

  return facts;
}

function hasFactIndexed(facts, tr) {
  ensureFactIndexes(facts);

  const key = tripleFastKey(tr);
  if (key !== null) return facts.__keySet.has(key);

  if (tr.p instanceof Iri) {
    const pk = tr.p.value;

    const ok = termFastKey(tr.o);
    if (ok !== null) {
      const po = facts.__byPO.get(pk);
      if (po) {
        const pob = po.get(ok) || [];
        return pob.some(t => alphaEqTriple(t, tr));
      }
    }

    const pb = facts.__byPred.get(pk) || [];
    return pb.some(t => alphaEqTriple(t, tr));
  }

  return hasAlphaEquiv(facts, tr);
}

function pushFactIndexed(facts, tr) {
  ensureFactIndexes(facts);
  facts.push(tr);
  indexFact(facts, tr);
}

function ensureBackRuleIndexes(backRules) {
  if (backRules.__byHeadPred && backRules.__wildHeadPred) return;

  Object.defineProperty(backRules, "__byHeadPred",   { value: new Map(), enumerable: false, writable: true });
  Object.defineProperty(backRules, "__wildHeadPred", { value: [], enumerable: false, writable: true });

  for (const r of backRules) indexBackRule(backRules, r);
}

function indexBackRule(backRules, r) {
  if (!r || !r.conclusion || r.conclusion.length !== 1) return;
  const head = r.conclusion[0];
  if (head && head.p instanceof Iri) {
    const k = head.p.value;
    let bucket = backRules.__byHeadPred.get(k);
    if (!bucket) { bucket = []; backRules.__byHeadPred.set(k, bucket); }
    bucket.push(r);
  } else {
    backRules.__wildHeadPred.push(r);
  }
}

// ============================================================================
// Special predicate helpers
// ============================================================================

function isRdfTypePred(p) {
  return p instanceof Iri && p.value === RDF_NS + "type";
}

function isOwlSameAsPred(t) {
  return t instanceof Iri && t.value === (OWL_NS + "sameAs");
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

  // math: numeric comparisons (no new bindings, just tests)
  if (
    v === MATH_NS + "equalTo"         ||
    v === MATH_NS + "greaterThan"     ||
    v === MATH_NS + "lessThan"        ||
    v === MATH_NS + "notEqualTo"      ||
    v === MATH_NS + "notGreaterThan"  ||
    v === MATH_NS + "notLessThan"
  ) {
    return true;
  }

  // list: membership test with no bindings
  if (v === LIST_NS + "notMember") {
    return true;
  }

  // log: tests that are purely constraints (no new bindings)
  if (
    v === LOG_NS + "forAllIn"     ||
    v === LOG_NS + "notEqualTo"   ||
    v === LOG_NS + "notIncludes"
  ) {
    return true;
  }

  // string: relational / membership style tests (no bindings)
  if (
    v === STRING_NS + "contains"             ||
    v === STRING_NS + "containsIgnoringCase" ||
    v === STRING_NS + "endsWith"             ||
    v === STRING_NS + "equalIgnoringCase"    ||
    v === STRING_NS + "greaterThan"          ||
    v === STRING_NS + "lessThan"             ||
    v === STRING_NS + "matches"              ||
    v === STRING_NS + "notEqualIgnoringCase" ||
    v === STRING_NS + "notGreaterThan"       ||
    v === STRING_NS + "notLessThan"          ||
    v === STRING_NS + "notMatches"           ||
    v === STRING_NS + "startsWith"
  ) {
    return true;
  }

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

function isGroundTermInFormula(t) {
  // EYE-style: variables inside formula terms are treated as local placeholders,
  // so they don't make the *surrounding triple* non-ground.
  if (t instanceof OpenListTerm) return false;
  if (t instanceof ListTerm) return t.elems.every(e => isGroundTermInFormula(e));
  if (t instanceof FormulaTerm) return t.triples.every(tr => isGroundTripleInFormula(tr));
  // Iri/Literal/Blank/Var are all OK inside formulas
  return true;
}

function isGroundTripleInFormula(tr) {
  return (
    isGroundTermInFormula(tr.s) &&
    isGroundTermInFormula(tr.p) &&
    isGroundTermInFormula(tr.o)
  );
}

function isGroundTerm(t) {
  if (t instanceof Var) return false;
  if (t instanceof ListTerm) return t.elems.every(e => isGroundTerm(e));
  if (t instanceof OpenListTerm) return false;
  if (t instanceof FormulaTerm) return t.triples.every(tr => isGroundTripleInFormula(tr));
  return true;
}

function isGroundTriple(tr) {
  return isGroundTerm(tr.s) && isGroundTerm(tr.p) && isGroundTerm(tr.o);
}

// Canonical JSON-ish encoding for use as a Skolem cache key.
// We only *call* this on ground terms in log:skolem, but it is
// robust to seeing vars/open lists anyway.
function skolemKeyFromTerm(t) {
  function enc(u) {
    if (u instanceof Iri)      return ["I", u.value];
    if (u instanceof Literal)  return ["L", u.value];
    if (u instanceof Blank)    return ["B", u.label];
    if (u instanceof Var)      return ["V", u.name];
    if (u instanceof ListTerm) return ["List", u.elems.map(enc)];
    if (u instanceof OpenListTerm)
      return ["OpenList", u.prefix.map(enc), u.tailVar];
    if (u instanceof FormulaTerm)
      return [
        "Formula",
        u.triples.map(tr => [
          enc(tr.s),
          enc(tr.p),
          enc(tr.o)
        ])
      ];
    return ["Other", String(u)];
  }
  return JSON.stringify(enc(t));
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

function unifyFormulaTriples(xs, ys, subst) {
  if (xs.length !== ys.length) return null;

  // Fast path: exact same sequence.
  if (triplesListEqual(xs, ys)) return { ...subst };

  // Backtracking match (order-insensitive), *threading* the substitution through.
  const used = new Array(ys.length).fill(false);

  function step(i, s) {
    if (i >= xs.length) return s;
    const x = xs[i];

    for (let j = 0; j < ys.length; j++) {
      if (used[j]) continue;
      const y = ys[j];

      // Cheap pruning when both predicates are IRIs.
      if (x.p instanceof Iri && y.p instanceof Iri && x.p.value !== y.p.value) continue;

      const s2 = unifyTriple(x, y, s);   // IMPORTANT: use `s`, not {}
      if (s2 === null) continue;

      used[j] = true;
      const s3 = step(i + 1, s2);
      if (s3 !== null) return s3;
      used[j] = false;
    }
    return null;
  }

  return step(0, { ...subst }); // IMPORTANT: start from the incoming subst
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

  // Formulas:
  // 1) If they are alpha-equivalent, succeed without leaking internal bindings.
  // 2) Otherwise fall back to full unification (may bind vars).
  if (a instanceof FormulaTerm && b instanceof FormulaTerm) {
    if (alphaEqFormulaTriples(a.triples, b.triples)) return { ...subst };
    return unifyFormulaTriples(a.triples, b.triples, subst);
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
  // Split a literal into lexical form and datatype IRI (if any).
  // Also strip an optional language tag from the lexical form:
  //   "\"hello\"@en"  -> "\"hello\""
  //   "\"hello\"@en^^<...>" is rejected earlier in the parser.
  const idx = lit.indexOf("^^");
  let lex = lit;
  let dt = null;

  if (idx >= 0) {
    lex = lit.slice(0, idx);
    dt = lit.slice(idx + 2).trim();
    if (dt.startsWith("<") && dt.endsWith(">")) {
      dt = dt.slice(1, -1);
    }
  }

  // Strip LANGTAG from the lexical form when present.
  if (lex.length >= 2 && lex[0] === '"') {
    const lastQuote = lex.lastIndexOf('"');
    if (lastQuote > 0 && lastQuote < lex.length - 1 && lex[lastQuote + 1] === "@") {
      const lang = lex.slice(lastQuote + 2);
      if (/^[A-Za-z]+(?:-[A-Za-z0-9]+)*$/.test(lang)) {
        lex = lex.slice(0, lastQuote + 1);
      }
    }
  }

  return [lex, dt];
}

function stripQuotes(lex) {
  if (lex.length >= 6 && lex.startsWith('"""') && lex.endsWith('"""')) {
    return lex.slice(3, -3);
  }
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

function termToJsStringDecoded(t) {
  // Like termToJsString, but for short literals it *also* interprets escapes
  // (\" \n \uXXXX …) by attempting JSON.parse on the quoted lexical form.
  if (!(t instanceof Literal)) return null;
  const [lex, _dt] = literalParts(t.value);

  // Long strings: """ ... """ are taken verbatim.
  if (lex.length >= 6 && lex.startsWith('"""') && lex.endsWith('"""')) {
    return lex.slice(3, -3);
  }

  // Short strings: try to decode escapes (this makes "{\"a\":1}" usable too).
  if (lex.length >= 2 && lex[0] === '"' && lex[lex.length - 1] === '"') {
    try { return JSON.parse(lex); } catch (e) { /* fall through */ }
    return stripQuotes(lex);
  }

  return stripQuotes(lex);
}

function jsonPointerUnescape(seg) {
  // RFC6901: ~1 -> '/', ~0 -> '~'
  let out = "";
  for (let i = 0; i < seg.length; i++) {
    const c = seg[i];
    if (c !== "~") { out += c; continue; }
    if (i + 1 >= seg.length) return null;
    const n = seg[i + 1];
    if (n === "0") out += "~";
    else if (n === "1") out += "/";
    else return null;
    i++;
  }
  return out;
}

function jsonToTerm(v) {
  if (v === null) return makeStringLiteral("null");
  if (typeof v === "string") return makeStringLiteral(v);
  if (typeof v === "number") return new Literal(String(v));
  if (typeof v === "boolean") return new Literal(v ? "true" : "false");
  if (Array.isArray(v)) return new ListTerm(v.map(jsonToTerm));

  if (v && typeof v === "object") {
    return makeRdfJsonLiteral(JSON.stringify(v));
  }
  return null;
}

function jsonPointerLookup(jsonText, pointer) {
  let ptr = pointer;

  // Support URI fragment form "#/a/b"
  if (ptr.startsWith("#")) {
    try { ptr = decodeURIComponent(ptr.slice(1)); } catch { return null; }
  }

  let entry = jsonPointerCache.get(jsonText);
  if (!entry) {
    let parsed = null;
    try { parsed = JSON.parse(jsonText); } catch { parsed = null; }
    entry = { parsed, ptrCache: new Map() };
    jsonPointerCache.set(jsonText, entry);
  }
  if (entry.parsed === null) return null;

  if (entry.ptrCache.has(ptr)) return entry.ptrCache.get(ptr);

  let cur = entry.parsed;

  if (ptr === "") {
    const t = jsonToTerm(cur);
    entry.ptrCache.set(ptr, t);
    return t;
  }
  if (!ptr.startsWith("/")) { entry.ptrCache.set(ptr, null); return null; }

  const parts = ptr.split("/").slice(1);
  for (const raw of parts) {
    const seg = jsonPointerUnescape(raw);
    if (seg === null) { entry.ptrCache.set(ptr, null); return null; }

    if (Array.isArray(cur)) {
      if (!/^(0|[1-9]\d*)$/.test(seg)) { entry.ptrCache.set(ptr, null); return null; }
      const idx = Number(seg);
      if (idx < 0 || idx >= cur.length) { entry.ptrCache.set(ptr, null); return null; }
      cur = cur[idx];
    } else if (cur !== null && typeof cur === "object") {
      if (!Object.prototype.hasOwnProperty.call(cur, seg)) { entry.ptrCache.set(ptr, null); return null; }
      cur = cur[seg];
    } else {
      entry.ptrCache.set(ptr, null);
      return null;
    }
  }

  const out = jsonToTerm(cur);
  entry.ptrCache.set(ptr, out);
  return out;
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

  function hashLiteral(t, algo) {
    // Accept only literals, interpret lexical form as UTF-8 string
    if (!(t instanceof Literal)) return null;
    const [lex, _dt] = literalParts(t.value);
    const input = stripQuotes(lex);
    try {
      const digest = nodeCrypto
        .createHash(algo)
        .update(input, "utf8")
        .digest("hex");
      // plain string literal with the hex digest
      return new Literal(JSON.stringify(digest));
    } catch (e) {
      return null;
    }
  }

  // -----------------------------------------------------------------
  // 4.1 crypto: builtins
  // -----------------------------------------------------------------

  // crypto:sha
  // true iff ?o is the SHA-1 hash of the subject string.
  if (g.p instanceof Iri && g.p.value === CRYPTO_NS + "sha") {
    const lit = hashLiteral(g.s, "sha1");
    if (!lit) return [];
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // crypto:md5
  if (g.p instanceof Iri && g.p.value === CRYPTO_NS + "md5") {
    const lit = hashLiteral(g.s, "md5");
    if (!lit) return [];
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // crypto:sha256
  if (g.p instanceof Iri && g.p.value === CRYPTO_NS + "sha256") {
    const lit = hashLiteral(g.s, "sha256");
    if (!lit) return [];
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // crypto:sha512
  if (g.p instanceof Iri && g.p.value === CRYPTO_NS + "sha512") {
    const lit = hashLiteral(g.s, "sha512");
    if (!lit) return [];
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // -----------------------------------------------------------------
  // 4.2 math: builtins
  // -----------------------------------------------------------------

  // math:greaterThan
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

  // math:lessThan
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

  // math:notLessThan
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

  // math:notGreaterThan
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

  // math:equalTo
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

  // math:notEqualTo
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

  // math:sum
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

  // math:product
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

  // math:difference
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

  // math:quotient
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

  // math:integerQuotient
  // Schema: ( $a $b ) math:integerQuotient $q
  // Cwm: divide first integer by second integer, ignoring remainder. :contentReference[oaicite:1]{index=1}
  if (g.p instanceof Iri && g.p.value === MATH_NS + "integerQuotient") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const [a0, b0] = g.s.elems;

    // Prefer exact integer division using BigInt when possible
    const ai = parseIntLiteral(a0);
    const bi = parseIntLiteral(b0);
    if (ai !== null && bi !== null) {
      if (bi === 0n) return [];
      const q = ai / bi; // BigInt division truncates toward zero
      const lit = new Literal(q.toString());
      if (g.o instanceof Var) {
        const s2 = { ...subst };
        s2[g.o.name] = lit;
        return [s2];
      }
      const s2 = unifyTerm(g.o, lit, subst);
      return s2 !== null ? [s2] : [];
    }

    // Fallback: allow Number literals that still represent integers
    const a = parseNum(a0);
    const b = parseNum(b0);
    if (a === null || b === null) return [];
    if (!Number.isFinite(a) || !Number.isFinite(b) || b === 0) return [];
    if (!Number.isInteger(a) || !Number.isInteger(b)) return [];

    const q = Math.trunc(a / b);
    const lit = new Literal(String(q));
    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // math:exponentiation
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

  // math:negation
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

  // math:absoluteValue
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

  // math:cos
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

  // math:sin
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

  // math:acos
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

  // math:asin
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

  // math:atan
  if (g.p instanceof Iri && g.p.value === MATH_NS + "atan") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.atan(a);
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

  // math:cosh
  // Hyperbolic cosine
  if (g.p instanceof Iri && g.p.value === MATH_NS + "cosh") {
    const a = parseNum(g.s);
    if (a !== null && typeof Math.cosh === "function") {
      const cVal = Math.cosh(a);
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

  // math:degrees
  // Convert radians -> degrees
  if (g.p instanceof Iri && g.p.value === MATH_NS + "degrees") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = (a * 180.0) / Math.PI;
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

  // math:remainder
  // Subject is a list (dividend divisor); object is the remainder.
  // Schema: ( $a $b ) math:remainder $r
  if (g.p instanceof Iri && g.p.value === MATH_NS + "remainder") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const a = parseNum(g.s.elems[0]);
    const b = parseNum(g.s.elems[1]);
    if (a === null || b === null || b === 0) return [];
    const rVal = a % b;
    if (!Number.isFinite(rVal)) return [];
    const lit = new Literal(formatNum(rVal));

    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // math:rounded
  // Round to nearest integer.
  // If there are two such numbers, then the one closest to positive infinity is returned.
  // Schema: $s math:rounded $o
  if (g.p instanceof Iri && g.p.value === MATH_NS + "rounded") {
    const a = parseNum(g.s);
    if (a === null) return [];
    const rVal = Math.round(a);
    const lit = new Literal(formatNum(rVal));

    if (g.o instanceof Var) {
      const s2 = { ...subst };
      s2[g.o.name] = lit;
      return [s2];
    }
    const s2 = unifyTerm(g.o, lit, subst);
    return s2 !== null ? [s2] : [];
  }

  // math:sinh
  if (g.p instanceof Iri && g.p.value === MATH_NS + "sinh") {
    const a = parseNum(g.s);
    if (a !== null && typeof Math.sinh === "function") {
      const cVal = Math.sinh(a);
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

  // math:tan
  if (g.p instanceof Iri && g.p.value === MATH_NS + "tan") {
    const a = parseNum(g.s);
    if (a !== null) {
      const cVal = Math.tan(a);
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

  // math:tanh
  if (g.p instanceof Iri && g.p.value === MATH_NS + "tanh") {
    const a = parseNum(g.s);
    if (a !== null && typeof Math.tanh === "function") {
      const cVal = Math.tanh(a);
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

  // -----------------------------------------------------------------
  // 4.3 time: builtins
  // -----------------------------------------------------------------

  // time:localTime
  // "" time:localTime ?D.  binds ?D to “now” as xsd:dateTime.
  if (g.p instanceof Iri && g.p.value === TIME_NS + "localTime") {
    const now = getNowLex();

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
  // 4.4 list: builtins
  // -----------------------------------------------------------------

  // list:append
  // true if and only if $o is the concatenation of all lists $s.i.
  // Schema: ( $s.i?[*] )+ list:append $o?
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

  // list:first
  // true iff $s is a list and $o is the first member of that list.
  // Schema: $s+ list:first $o-
  if (g.p instanceof Iri && g.p.value === LIST_NS + "first") {
    if (!(g.s instanceof ListTerm)) return [];
    if (!g.s.elems.length) return [];
    const first = g.s.elems[0];
    const s2 = unifyTerm(g.o, first, subst);
    return s2 !== null ? [s2] : [];
  }

  // list:rest
  // true iff $s is a (non-empty) list and $o is the rest (tail) of that list.
  // Schema: $s+ list:rest $o-
  if (g.p instanceof Iri && g.p.value === LIST_NS + "rest") {
    // Closed list: (a b c) -> (b c)
    if (g.s instanceof ListTerm) {
      if (!g.s.elems.length) return [];
      const rest = new ListTerm(g.s.elems.slice(1));
      const s2 = unifyTerm(g.o, rest, subst);
      return s2 !== null ? [s2] : [];
    }

    // Open list: (a b ... ?T) -> (b ... ?T)
    if (g.s instanceof OpenListTerm) {
      if (!g.s.prefix.length) return []; // can't compute rest without a known head

      if (g.s.prefix.length === 1) {
        // (a ... ?T) rest is exactly ?T
        const s2 = unifyTerm(g.o, new Var(g.s.tailVar), subst);
        return s2 !== null ? [s2] : [];
      }

      const rest = new OpenListTerm(g.s.prefix.slice(1), g.s.tailVar);
      const s2 = unifyTerm(g.o, rest, subst);
      return s2 !== null ? [s2] : [];
    }

    return [];
  }

  // rdf:first (alias of list:first)
  // Schema: $s+ rdf:first $o-
  if (g.p instanceof Iri && g.p.value === RDF_NS + "first") {
    if (!(g.s instanceof ListTerm)) return [];
    if (!g.s.elems.length) return [];
    const first = g.s.elems[0];
    const s2 = unifyTerm(g.o, first, subst);
    return s2 !== null ? [s2] : [];
  }

  // rdf:rest (alias of list:rest)
  // Schema: $s+ rdf:rest $o-
  if (g.p instanceof Iri && g.p.value === RDF_NS + "rest") {
    // Closed list: (a b c) -> (b c)
    if (g.s instanceof ListTerm) {
      if (!g.s.elems.length) return [];
      const rest = new ListTerm(g.s.elems.slice(1));
      const s2 = unifyTerm(g.o, rest, subst);
      return s2 !== null ? [s2] : [];
    }
    // Open list: (a b ... ?T) -> (b ... ?T)
    if (g.s instanceof OpenListTerm) {
      if (!g.s.prefix.length) return [];
      if (g.s.prefix.length === 1) {
        const s2 = unifyTerm(g.o, new Var(g.s.tailVar), subst);
        return s2 !== null ? [s2] : [];
      }
      const rest = new OpenListTerm(g.s.prefix.slice(1), g.s.tailVar);
      const s2 = unifyTerm(g.o, rest, subst);
      return s2 !== null ? [s2] : [];
    }
    return [];
  }

  // list:iterate
  // true iff $s is a list and $o is a list (index value),
  // where index is a valid 0-based index into $s and value is the element at that index.
  // Schema: $s+ list:iterate ( $o.1?[*] $o.2?[*] )?[*]
  if (g.p instanceof Iri && g.p.value === LIST_NS + "iterate") {
    if (!(g.s instanceof ListTerm)) return [];
    if (!(g.o instanceof ListTerm) || g.o.elems.length !== 2) return [];
    const [idxTerm, valTerm] = g.o.elems;
    const xs = g.s.elems;
    const outs = [];

    for (let i = 0; i < xs.length; i++) {
      const idxLit = new Literal(String(i)); // index starts at 0
      let s1 = unifyTerm(idxTerm, idxLit, subst);
      if (s1 === null) continue;
      let s2 = unifyTerm(valTerm, xs[i], s1);
      if (s2 === null) continue;
      outs.push(s2);
    }
    return outs;
  }

  // list:last
  // true iff $s is a list and $o is the last member of that list.
  // Schema: $s+ list:last $o-
  if (g.p instanceof Iri && g.p.value === LIST_NS + "last") {
    if (!(g.s instanceof ListTerm)) return [];
    const xs = g.s.elems;
    if (!xs.length) return [];
    const last = xs[xs.length - 1];
    const s2 = unifyTerm(g.o, last, subst);
    return s2 !== null ? [s2] : [];
  }

  // list:memberAt
  // true iff $s.1 is a list, $s.2 is a valid index, and $o is the member at that index.
  // Schema: ( $s.1+ $s.2?[*] )+ list:memberAt $o?[*]
  if (g.p instanceof Iri && g.p.value === LIST_NS + "memberAt") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const [listTerm, indexTerm] = g.s.elems;
    if (!(listTerm instanceof ListTerm)) return [];
    const xs = listTerm.elems;
    const outs = [];

    for (let i = 0; i < xs.length; i++) {
      const idxLit = new Literal(String(i)); // index starts at 0
      let s1 = unifyTerm(indexTerm, idxLit, subst);
      if (s1 === null) continue;
      let s2 = unifyTerm(g.o, xs[i], s1);
      if (s2 === null) continue;
      outs.push(s2);
    }
    return outs;
  }

  // list:remove
  // true iff $s.1 is a list and $o is that list with all occurrences of $s.2 removed.
  // Schema: ( $s.1+ $s.2+ )+ list:remove $o-
  if (g.p instanceof Iri && g.p.value === LIST_NS + "remove") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const [listTerm, itemTerm] = g.s.elems;
    if (!(listTerm instanceof ListTerm)) return [];
    const xs = listTerm.elems;
    const filtered = [];
    for (const e of xs) {
      if (!termsEqual(e, itemTerm)) filtered.push(e);
    }
    const resList = new ListTerm(filtered);
    const s2 = unifyTerm(g.o, resList, subst);
    return s2 !== null ? [s2] : [];
  }

  // list:member
  if (g.p instanceof Iri && g.p.value === LIST_NS + "member") {
    if (!(g.s instanceof ListTerm)) return [];
    const outs = [];
    for (const x of g.s.elems) {
      const s2 = unifyTerm(g.o, x, subst);
      if (s2 !== null) outs.push(s2);
    }
    return outs;
  }

  // list:in
  if (g.p instanceof Iri && g.p.value === LIST_NS + "in") {
    if (!(g.o instanceof ListTerm)) return [];
    const outs = [];
    for (const x of g.o.elems) {
      const s2 = unifyTerm(g.s, x, subst);
      if (s2 !== null) outs.push(s2);
    }
    return outs;
  }

  // list:length
  if (g.p instanceof Iri && g.p.value === LIST_NS + "length") {
    if (!(g.s instanceof ListTerm)) return [];
    const nTerm = new Literal(String(g.s.elems.length));
    const s2 = unifyTerm(g.o, nTerm, subst);
    return s2 !== null ? [s2] : [];
  }

  // list:notMember
  if (g.p instanceof Iri && g.p.value === LIST_NS + "notMember") {
    if (!(g.s instanceof ListTerm)) return [];
    for (const el of g.s.elems) {
      if (unifyTerm(g.o, el, subst) !== null) return [];
    }
    return [{ ...subst }];
  }

  // list:reverse
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

  // list:sort
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

  // list:map
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

  // list:firstRest
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
  // 4.5 log: builtins
  // -----------------------------------------------------------------

  // log:equalTo
  if (g.p instanceof Iri && g.p.value === LOG_NS + "equalTo") {
    const s2 = unifyTerm(goal.s, goal.o, subst);
    return s2 !== null ? [s2] : [];
  }

  // log:notEqualTo
  if (g.p instanceof Iri && g.p.value === LOG_NS + "notEqualTo") {
    const s2 = unifyTerm(goal.s, goal.o, subst);
    if (s2 !== null) return [];
    return [{ ...subst }];
  }

  // log:implies — expose internal forward rules as data
  if (g.p instanceof Iri && g.p.value === LOG_NS + "implies") {
    const allFw = backRules.__allForwardRules || [];
    const results = [];

    for (const r0 of allFw) {
      if (!r0.isForward) continue;

      // fresh copy of the rule with fresh variable names
      const r = standardizeRule(r0, varGen);

      const premF = new FormulaTerm(r.premise);
      const concTerm = r0.isFuse
        ? new Literal("false")
        : new FormulaTerm(r.conclusion);

      // unify subject with the premise formula
      let s2 = unifyTerm(goal.s, premF, subst);
      if (s2 === null) continue;

      // unify object with the conclusion formula
      s2 = unifyTerm(goal.o, concTerm, s2);
      if (s2 === null) continue;

      results.push(s2);
    }

    return results;
  }

  // log:impliedBy — expose internal backward rules as data
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

  // log:notIncludes
  if (g.p instanceof Iri && g.p.value === LOG_NS + "notIncludes") {
    if (!(g.o instanceof FormulaTerm)) return [];
    const body = g.o.triples;
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

  // log:collectAllIn
  if (g.p instanceof Iri && g.p.value === LOG_NS + "collectAllIn") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 3) return [];
    const [valueTempl, clauseTerm, listTerm] = g.s.elems;
    if (!(clauseTerm instanceof FormulaTerm)) return [];
    const body = clauseTerm.triples;
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

  // log:forAllIn
  if (g.p instanceof Iri && g.p.value === LOG_NS + "forAllIn") {
    // Subject: list with two clauses (where-clause, then-clause)
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];
    const [whereClause, thenClause] = g.s.elems;
    if (!(whereClause instanceof FormulaTerm)) return [];
    if (!(thenClause instanceof FormulaTerm)) return [];

    // 1. Find all substitutions that make the first clause true
    const visited1 = [];
    const sols1 = proveGoals(
      Array.from(whereClause.triples),
      {},
      facts,
      backRules,
      depth + 1,
      visited1,
      varGen
    );

    // 2. For every such substitution, check that the second clause holds too.
    //    If there are no matches for the first clause, this is vacuously true.
    for (const s1 of sols1) {
      const visited2 = [];
      const sols2 = proveGoals(
        Array.from(thenClause.triples),
        s1,
        facts,
        backRules,
        depth + 1,
        visited2,
        varGen
      );
      // Found a counterexample: whereClause holds but thenClause does not
      if (!sols2.length) return [];
    }

    // All matches pass (or there were no matches) → builtin succeeds as a pure test.
    return [{ ...subst }];
  }

  // log:skolem
  if (g.p instanceof Iri && g.p.value === LOG_NS + "skolem") {
    // Subject must be ground; commonly a list, but we allow any ground term.
    if (!isGroundTerm(g.s)) return [];

    const key = skolemKeyFromTerm(g.s);
    let iri = skolemCache.get(key);
    if (!iri) {
      const id = deterministicSkolemIdFromKey(key);
      iri = new Iri(SKOLEM_NS + id);
      skolemCache.set(key, iri);
    }

    const s2 = unifyTerm(goal.o, iri, subst);
    return s2 !== null ? [s2] : [];
  }

  // log:uri
  if (g.p instanceof Iri && g.p.value === LOG_NS + "uri") {
    // Direction 1: subject is an IRI -> object is its string representation
    if (g.s instanceof Iri) {
      const uriStr = g.s.value;           // raw IRI string, e.g. "https://www.w3.org"
      const lit = makeStringLiteral(uriStr); // "https://www.w3.org"
      const s2 = unifyTerm(goal.o, lit, subst);
      return s2 !== null ? [s2] : [];
    }

    // Direction 2: object is a string literal -> subject is the corresponding IRI
    if (g.o instanceof Literal) {
      const uriStr = termToJsString(g.o); // JS string from the literal
      if (uriStr === null) return [];
      const iri = new Iri(uriStr);
      const s2 = unifyTerm(goal.s, iri, subst);
      return s2 !== null ? [s2] : [];
    }

    // If neither side is sufficiently instantiated (both vars, or wrong types),
    // we don't enumerate URIs; the builtin just fails.
    return [];
  }

  // -----------------------------------------------------------------
  // 4.6 string: builtins
  // -----------------------------------------------------------------

  // string:concatenation
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

  // string:contains
  if (g.p instanceof Iri && g.p.value === STRING_NS + "contains") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.includes(oStr) ? [{ ...subst }] : [];
  }

  // string:containsIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "containsIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase().includes(oStr.toLowerCase())
      ? [{ ...subst }]
      : [];
  }

  // string:endsWith
  if (g.p instanceof Iri && g.p.value === STRING_NS + "endsWith") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.endsWith(oStr) ? [{ ...subst }] : [];
  }

  // string:equalIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "equalIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase() === oStr.toLowerCase()
      ? [{ ...subst }]
      : [];
  }

  // string:format
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

  // string:jsonPointer
  // Schema: ( $jsonText $pointer ) string:jsonPointer $value
  if (g.p instanceof Iri && g.p.value === STRING_NS + "jsonPointer") {
    if (!(g.s instanceof ListTerm) || g.s.elems.length !== 2) return [];

    const jsonText = termToJsonText(g.s.elems[0]);     // <-- changed
    const ptr      = termToJsStringDecoded(g.s.elems[1]);
    if (jsonText === null || ptr === null) return [];

    const valTerm = jsonPointerLookup(jsonText, ptr);
    if (valTerm === null) return [];

    const s2 = unifyTerm(g.o, valTerm, subst);
    return s2 !== null ? [s2] : [];
  }

  // string:greaterThan
  if (g.p instanceof Iri && g.p.value === STRING_NS + "greaterThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr > oStr ? [{ ...subst }] : [];
  }

  // string:lessThan
  if (g.p instanceof Iri && g.p.value === STRING_NS + "lessThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr < oStr ? [{ ...subst }] : [];
  }

  // string:matches
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

  // string:notEqualIgnoringCase
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notEqualIgnoringCase") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.toLowerCase() !== oStr.toLowerCase()
      ? [{ ...subst }]
      : [];
  }

  // string:notGreaterThan  (≤ in Unicode code order)
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notGreaterThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr <= oStr ? [{ ...subst }] : [];
  }

  // string:notLessThan  (≥ in Unicode code order)
  if (g.p instanceof Iri && g.p.value === STRING_NS + "notLessThan") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr >= oStr ? [{ ...subst }] : [];
  }

  // string:notMatches
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

  // string:replace
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

  // string:scrape
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

  // string:startsWith
  if (g.p instanceof Iri && g.p.value === STRING_NS + "startsWith") {
    const sStr = termToJsString(g.s);
    const oStr = termToJsString(g.o);
    if (sStr === null || oStr === null) return [];
    return sStr.startsWith(oStr) ? [{ ...subst }] : [];
  }

  // Unknown builtin
  return [];
}

function isBuiltinPred(p) {
  if (!(p instanceof Iri)) return false;
  const v = p.value;

  // Treat RDF Collections as list-term builtins too.
  if (v === RDF_NS + "first" || v === RDF_NS + "rest") {
    return true;
  }

  return (
    v.startsWith(CRYPTO_NS) ||
    v.startsWith(MATH_NS)   ||
    v.startsWith(LOG_NS)    ||
    v.startsWith(STRING_NS) ||
    v.startsWith(TIME_NS)   ||
    v.startsWith(LIST_NS)
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
  return new Rule(
    premise,
    conclusion,
    rule.isForward,
    rule.isFuse,
    rule.headBlankLabels
  );
}

function listHasTriple(list, tr) {
  return list.some(t => triplesEqual(t, tr));
}

// ============================================================================
// Substitution compaction (to avoid O(depth^2) in deep backward chains)
// ============================================================================
//
// Why: backward chaining with standardizeRule introduces fresh variables at
// each step. composeSubst frequently copies a growing substitution object.
// For deep linear recursions this becomes quadratic.
//
// Strategy: when the substitution is "large" or search depth is high,
// keep only bindings that are still relevant to:
//   - variables appearing in the remaining goals
//   - variables from the original goals (answer vars)
// plus the transitive closure of variables that appear inside kept bindings.
//
// This is semantics-preserving for the ongoing proof state.

function gcCollectVarsInTerm(t, out) {
  if (t instanceof Var) { out.add(t.name); return; }
  if (t instanceof ListTerm) { for (const e of t.elems) gcCollectVarsInTerm(e, out); return; }
  if (t instanceof OpenListTerm) {
    for (const e of t.prefix) gcCollectVarsInTerm(e, out);
    out.add(t.tailVar);
    return;
  }
  if (t instanceof FormulaTerm) { for (const tr of t.triples) gcCollectVarsInTriple(tr, out); return; }
}

function gcCollectVarsInTriple(tr, out) {
  gcCollectVarsInTerm(tr.s, out);
  gcCollectVarsInTerm(tr.p, out);
  gcCollectVarsInTerm(tr.o, out);
}

function gcCollectVarsInGoals(goals, out) {
  for (const g of goals) gcCollectVarsInTriple(g, out);
}

function substSizeOver(subst, limit) {
  let c = 0;
  for (const _k in subst) {
    if (++c > limit) return true;
  }
  return false;
}

function gcCompactForGoals(subst, goals, answerVars) {
  const keep = new Set(answerVars);
  gcCollectVarsInGoals(goals, keep);

  const expanded = new Set();
  const queue = Array.from(keep);

  while (queue.length) {
    const v = queue.pop();
    if (expanded.has(v)) continue;
    expanded.add(v);

    const bound = subst[v];
    if (bound === undefined) continue;

    const before = keep.size;
    gcCollectVarsInTerm(bound, keep);
    if (keep.size !== before) {
      for (const nv of keep) {
        if (!expanded.has(nv)) queue.push(nv);
      }
    }
  }

  const out = {};
  for (const k of Object.keys(subst)) {
    if (keep.has(k)) out[k] = subst[k];
  }
  return out;
}

function maybeCompactSubst(subst, goals, answerVars, depth) {
  // Keep the fast path fast.
  // Only compact when the substitution is clearly getting large, or
  // we are in a deep chain (where the quadratic behavior shows up).
  if (depth < 128 && !substSizeOver(subst, 256)) return subst;
  return gcCompactForGoals(subst, goals, answerVars);
}


function proveGoals( goals, subst, facts, backRules, depth, visited, varGen ) {
  // Iterative DFS over proof states using an explicit stack.
  // Each state carries its own substitution and remaining goals.
  const results = [];

  const initialGoals = Array.isArray(goals) ? goals.slice() : [];
  const initialSubst = subst ? { ...subst } : {};
  const initialVisited = visited ? visited.slice() : [];


  // Variables from the original goal list (needed by the caller to instantiate conclusions)
  const answerVars = new Set();
  gcCollectVarsInGoals(initialGoals, answerVars);
  if (!initialGoals.length) {
    results.push(gcCompactForGoals(initialSubst, [], answerVars));
    return results;
  }

  const stack = [
    { goals: initialGoals, subst: initialSubst, depth: depth || 0, visited: initialVisited }
  ];

  while (stack.length) {
    const state = stack.pop();

    if (!state.goals.length) {
      results.push(gcCompactForGoals(state.subst, [], answerVars));
      continue;
    }

    const rawGoal = state.goals[0];
    const restGoals = state.goals.slice(1);
    const goal0 = applySubstTriple(rawGoal, state.subst);

    // 1) Builtins
    if (isBuiltinPred(goal0.p)) {
      const deltas = evalBuiltin(goal0, {}, facts, backRules, state.depth, varGen);
      for (const delta of deltas) {
        const composed = composeSubst(state.subst, delta);
        if (composed === null) continue;

        if (!restGoals.length) {
          results.push(gcCompactForGoals(composed, [], answerVars));
        } else {
          const nextSubst = maybeCompactSubst(composed, restGoals, answerVars, state.depth + 1);
          stack.push({
            goals: restGoals,
            subst: nextSubst,
            depth: state.depth + 1,
            visited: state.visited
          });
        }
      }
      continue;
    }

    // 2) Loop check for backward reasoning
    if (listHasTriple(state.visited, goal0)) continue;
    const visitedForRules = state.visited.concat([goal0]);

    // 3) Try to satisfy the goal from known facts (NOW indexed by (p,o) when possible)
    if (goal0.p instanceof Iri) {
      const candidates = candidateFacts(facts, goal0);
      for (const f of candidates) {
        const delta = unifyTriple(goal0, f, {});
        if (delta === null) continue;

        const composed = composeSubst(state.subst, delta);
        if (composed === null) continue;

        if (!restGoals.length) {
          results.push(gcCompactForGoals(composed, [], answerVars));
        } else {
          const nextSubst = maybeCompactSubst(composed, restGoals, answerVars, state.depth + 1);
          stack.push({
            goals: restGoals,
            subst: nextSubst,
            depth: state.depth + 1,
            visited: state.visited
          });
        }
      }
    } else {
      // Non-IRI predicate → must try all facts.
      for (const f of facts) {
        const delta = unifyTriple(goal0, f, {});
        if (delta === null) continue;

        const composed = composeSubst(state.subst, delta);
        if (composed === null) continue;

        if (!restGoals.length) {
          results.push(gcCompactForGoals(composed, [], answerVars));
        } else {
          const nextSubst = maybeCompactSubst(composed, restGoals, answerVars, state.depth + 1);
          stack.push({
            goals: restGoals,
            subst: nextSubst,
            depth: state.depth + 1,
            visited: state.visited
          });
        }
      }
    }

    // 4) Backward rules (indexed by head predicate)
    if (goal0.p instanceof Iri) {
      ensureBackRuleIndexes(backRules);
      const candRules =
        (backRules.__byHeadPred.get(goal0.p.value) || []).concat(backRules.__wildHeadPred);

      for (const r of candRules) {
        if (r.conclusion.length !== 1) continue;

        const rawHead = r.conclusion[0];
        if (rawHead.p instanceof Iri && rawHead.p.value !== goal0.p.value) continue;

        const rStd = standardizeRule(r, varGen);
        const head = rStd.conclusion[0];
        const deltaHead = unifyTriple(head, goal0, {});
        if (deltaHead === null) continue;

        const body = rStd.premise.map(b => applySubstTriple(b, deltaHead));
        const composed = composeSubst(state.subst, deltaHead);
        if (composed === null) continue;

        const newGoals = body.concat(restGoals);
        const nextSubst = maybeCompactSubst(composed, newGoals, answerVars, state.depth + 1);
        stack.push({
          goals: newGoals,
          subst: nextSubst,
          depth: state.depth + 1,
          visited: visitedForRules
        });
      }
    }
  }

  return results;
}

// ============================================================================
// Forward chaining to fixpoint
// ============================================================================

function forwardChain(facts, forwardRules, backRules) {
  ensureFactIndexes(facts);
  ensureBackRuleIndexes(backRules);

  const factList = facts.slice();
  const derivedForward = [];
  const varGen = [0];
  const skCounter = [0];

  // Make rules visible to introspection builtins
  backRules.__allForwardRules = forwardRules;
  backRules.__allBackwardRules = backRules;

  while (true) {
    let changed = false;

    for (let i = 0; i < forwardRules.length; i++) {
      const r = forwardRules[i];
      const empty = {};
      const visited = [];

      const sols = proveGoals(r.premise.slice(), empty, facts, backRules, 0, visited, varGen);

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
            (
              (instantiated.s instanceof FormulaTerm && instantiated.o instanceof FormulaTerm) ||
              (instantiated.s instanceof Literal && instantiated.s.value === "true" && instantiated.o instanceof FormulaTerm) ||
              (instantiated.s instanceof FormulaTerm && instantiated.o instanceof Literal && instantiated.o.value === "true")
            );

          const isBwRuleTriple =
            isLogImpliedBy(instantiated.p) &&
            (
              (instantiated.s instanceof FormulaTerm && instantiated.o instanceof FormulaTerm) ||
              (instantiated.s instanceof FormulaTerm && instantiated.o instanceof Literal && instantiated.o.value === "true") ||
              (instantiated.s instanceof Literal && instantiated.s.value === "true" && instantiated.o instanceof FormulaTerm)
            );

          if (isFwRuleTriple || isBwRuleTriple) {
            if (!hasFactIndexed(facts, instantiated)) {
              factList.push(instantiated);
              pushFactIndexed(facts, instantiated);
              derivedForward.push(new DerivedFact(instantiated, r, instantiatedPremises.slice(), { ...s }));
              changed = true;
            }

            // Promote rule-producing triples to live rules, treating literal true as {}.
            const left =
              instantiated.s instanceof FormulaTerm ? instantiated.s.triples :
              (instantiated.s instanceof Literal && instantiated.s.value === "true") ? [] :
              null;

            const right =
              instantiated.o instanceof FormulaTerm ? instantiated.o.triples :
              (instantiated.o instanceof Literal && instantiated.o.value === "true") ? [] :
              null;

            if (left !== null && right !== null) {
              if (isFwRuleTriple) {
                const [premise0, conclusion] = liftBlankRuleVars(left, right);
                const premise = reorderPremiseForConstraints(premise0);

                const headBlankLabels = collectBlankLabelsInTriples(conclusion);
                const newRule = new Rule(premise, conclusion, true, false, headBlankLabels);

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

                const headBlankLabels = collectBlankLabelsInTriples(conclusion);
                const newRule = new Rule(premise, conclusion, false, false, headBlankLabels);

                const already = backRules.some(
                  rr =>
                    rr.isForward === newRule.isForward &&
                    rr.isFuse === newRule.isFuse &&
                    triplesListEqual(rr.premise, newRule.premise) &&
                    triplesListEqual(rr.conclusion, newRule.conclusion)
                );
                if (!already) {
                  backRules.push(newRule);
                  indexBackRule(backRules, newRule);
                }
              }
            }

            continue; // skip normal fact handling
          }

          // Only skolemize blank nodes that occur explicitly in the rule head
          const skMap = {};
          const inst = skolemizeTripleForHeadBlanks(instantiated, r.headBlankLabels, skMap, skCounter);

          if (!isGroundTriple(inst)) continue;
          if (hasFactIndexed(facts, inst)) continue;

          factList.push(inst);
          pushFactIndexed(facts, inst);

          derivedForward.push(new DerivedFact(inst, r, instantiatedPremises.slice(), { ...s }));
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
 if (t instanceof Literal) {
   const [lex, dt] = literalParts(t.value);

   // Pretty-print xsd:boolean as bare true/false
   if (dt === XSD_NS + "boolean") {
     const v = stripQuotes(lex);
     if (v === "true" || v === "false") return v;
     // optional: normalize 1/0 too
     if (v === "1") return "true";
     if (v === "0") return "false";
   }

   if (!dt) return t.value; // keep numbers, booleans, lang-tagged strings, etc.
   const qdt = pref.shrinkIri(dt);
   if (qdt !== null) return `${lex}^^${qdt}`;   // e.g. ^^rdf:JSON
   return `${lex}^^<${dt}>`;                   // fallback
 }
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
  const p =
    isRdfTypePred(tr.p) ? "a"
    : isOwlSameAsPred(tr.p) ? "="
    : termToN3(tr.p, prefixes);
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

// Turn RDF Collections described with rdf:first/rdf:rest (+ rdf:nil) into ListTerm terms.
// This mutates triples/rules in-place so list:* builtins work on RDF-serialized lists too.
function materializeRdfLists(triples, forwardRules, backwardRules) {
  const RDF_FIRST = RDF_NS + "first";
  const RDF_REST  = RDF_NS + "rest";
  const RDF_NIL   = RDF_NS + "nil";

  function nodeKey(t) {
    if (t instanceof Blank) return "B:" + t.label;
    if (t instanceof Iri) return "I:" + t.value;
    return null;
  }

  // Collect first/rest arcs from *input triples*
  const firstMap = new Map(); // key(subject) -> Term (object)
  const restMap  = new Map(); // key(subject) -> Term (object)
  for (const tr of triples) {
    if (!(tr.p instanceof Iri)) continue;
    const k = nodeKey(tr.s);
    if (!k) continue;
    if (tr.p.value === RDF_FIRST) firstMap.set(k, tr.o);
    else if (tr.p.value === RDF_REST) restMap.set(k, tr.o);
  }
  if (!firstMap.size && !restMap.size) return;

  const cache = new Map();     // key(node) -> ListTerm
  const visiting = new Set();  // cycle guard

  function buildListForKey(k) {
    if (cache.has(k)) return cache.get(k);
    if (visiting.has(k)) return null; // cycle => not a well-formed list
    visiting.add(k);

    // rdf:nil => ()
    if (k === "I:" + RDF_NIL) {
      const empty = new ListTerm([]);
      cache.set(k, empty);
      visiting.delete(k);
      return empty;
    }

    const head = firstMap.get(k);
    const tail = restMap.get(k);
    if (head === undefined || tail === undefined) {
      visiting.delete(k);
      return null; // not a full cons cell
    }

    const headTerm = rewriteTerm(head);

    let tailListElems = null;
    if (tail instanceof Iri && tail.value === RDF_NIL) {
      tailListElems = [];
    } else {
      const tk = nodeKey(tail);
      if (!tk) {
        visiting.delete(k);
        return null;
      }
      const tailList = buildListForKey(tk);
      if (!tailList) {
        visiting.delete(k);
        return null;
      }
      tailListElems = tailList.elems;
    }

    const out = new ListTerm([headTerm, ...tailListElems]);
    cache.set(k, out);
    visiting.delete(k);
    return out;
  }

  function rewriteTerm(t) {
    // Replace list nodes (Blank/Iri) by their constructed ListTerm when possible
    const k = nodeKey(t);
    if (k) {
      const built = buildListForKey(k);
      if (built) return built;
      // Also rewrite rdf:nil even if not otherwise referenced
      if (t instanceof Iri && t.value === RDF_NIL) return new ListTerm([]);
      return t;
    }
    if (t instanceof ListTerm) {
      let changed = false;
      const elems = t.elems.map(e => {
        const r = rewriteTerm(e);
        if (r !== e) changed = true;
        return r;
      });
      return changed ? new ListTerm(elems) : t;
    }
    if (t instanceof OpenListTerm) {
      let changed = false;
      const prefix = t.prefix.map(e => {
        const r = rewriteTerm(e);
        if (r !== e) changed = true;
        return r;
      });
      return changed ? new OpenListTerm(prefix, t.tailVar) : t;
    }
    if (t instanceof FormulaTerm) {
      for (const tr of t.triples) rewriteTriple(tr);
      return t;
    }
    return t;
  }

  function rewriteTriple(tr) {
    tr.s = rewriteTerm(tr.s);
    tr.p = rewriteTerm(tr.p);
    tr.o = rewriteTerm(tr.o);
  }

  // Pre-build all reachable list heads
  for (const k of firstMap.keys()) buildListForKey(k);

  // Rewrite input triples + rules in-place
  for (const tr of triples) rewriteTriple(tr);
  for (const r of forwardRules) {
    for (const tr of r.premise) rewriteTriple(tr);
    for (const tr of r.conclusion) rewriteTriple(tr);
  }
  for (const r of backwardRules) {
    for (const tr of r.premise) rewriteTriple(tr);
    for (const tr of r.conclusion) rewriteTriple(tr);
  }
}

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
  // Drop "node" and script name; keep only user-provided args
  const argv = process.argv.slice(2);

  // --------------------------------------------------------------------------
  // Global options
  // --------------------------------------------------------------------------

  // --version / -v: print version and exit
  if (argv.includes("--version") || argv.includes("-v")) {
    console.log(`eyeling v${version}`);
    process.exit(0);
  }

  // --no-proof-comments / -n: disable proof explanations
  if (argv.includes("--no-proof-comments") || argv.includes("-n")) {
    proofCommentsEnabled = false;
  }

  // --------------------------------------------------------------------------
  // Positional args (the N3 file)
  // --------------------------------------------------------------------------
  const positional = argv.filter(a => !a.startsWith("-"));

  if (positional.length !== 1) {
    console.error(
      "Usage: eyeling.js [--version|-v] [--no-proof-comments|-n] <file.n3>"
    );
    process.exit(1);
  }

  const path = positional[0];
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
  // console.log(JSON.stringify([prefixes, triples, frules, brules], null, 2));

  // Build internal ListTerm values from rdf:first/rdf:rest (+ rdf:nil) input triples
  materializeRdfLists(triples, frules, brules);

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
    if (proofCommentsEnabled) {
      printExplanation(df, prefixes);
      console.log(tripleToN3(df.fact, prefixes));
      console.log();
    } else {
      console.log(tripleToN3(df.fact, prefixes));
    }
  }
}

if (require.main === module) {
  main();
}

