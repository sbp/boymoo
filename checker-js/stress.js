// Exercise deep terms, long lists, independent API calls and file inputs.
"use strict";

const assert = require("assert");
const fs = require("fs");
const vm = require("vm");
const {execFileSync} = require("child_process");

const engine = process.argv[2] || "node";
const depth = 14000;
const width = 80000;
const nil = "COMMON-LISP::NIL";
const truth = "COMMON-LISP::T";
const x = "ACL2::X";
const y = "ACL2::Y";
const a = "ACL2::";
const form = (...items) => "(" + items.join(" ") + ")";
const quote = value => form("COMMON-LISP::QUOTE", value);
const equal = (left, right) => form("COMMON-LISP::EQUAL", left, right);
const car = value => form("COMMON-LISP::CAR", value);
const nest = term => "(COMMON-LISP::CAR ".repeat(depth) + term + ")".repeat(depth);
const source = fs.readFileSync("checker-js/check.js", "ascii");
const ground = fs.readFileSync("spec/ground.txt", "latin1");
const statements = [], proofs = [];

function axiom(name, term) {
    statements.push(form("axiom", a + name, term));
}

function prove(name, term, ...steps) {
    statements.push(form("theorem", a + name, term));
    proofs.push(form("theorem", a + name), ...steps, "(qed)");
}

function computed(name, term, result) {
    prove(name, equal(term, quote(result)), form("compute", term));
}

const deepDatum = "(1 ".repeat(depth) + "2" + ")".repeat(depth);
const longList = "(" + "0 ".repeat(width - 1) + "0)";
computed("STRESS-DATA", equal(quote(deepDatum), quote(deepDatum)), truth);
computed("STRESS-LIST", equal(quote(longList), quote(longList)), truth);

const nestedTerm = nest(x);
const nestedAfter = nest(y);
const lambda = form(form("COMMON-LISP::LAMBDA", form(x), nestedTerm), y);
prove("STRESS-BETA", equal(lambda, nestedAfter), form("beta", lambda));
axiom("STRESS-EQUALITY", equal(x, y));
axiom("STRESS-BEFORE", nestedTerm);
prove("STRESS-SUBSTITUTE", nestedAfter, "(fact ACL2::STRESS-EQUALITY)", "(fact ACL2::STRESS-BEFORE)",
    "(substitute 1 2 1" + " 1".repeat(depth) + ")");

axiom("STRESS-ORDINAL", form(a + "O-P", x));
axiom("STRESS-DECREASES", form(a + "O<", car(x), x));
const selfCall = form(a + "STRESS-FUNCTION", car(x));
statements.push(form("define", "KEYWORD::ALL", form(a + "STRESS-FUNCTION", form(x), nest(selfCall))));
proofs.push("(measure ACL2::STRESS-FUNCTION ACL2::X)", "(fact ACL2::STRESS-ORDINAL)", "(qed)",
    "(fact ACL2::STRESS-DECREASES)", "(qed)");

fs.mkdirSync("build", {recursive: true});
const scratch = fs.mkdtempSync("build/checker-js-stress-");
try {
    const files = ["library", "statements", "proofs"].map(name => scratch + "/" + name);
    ["", statements.join("\n") + "\n", proofs.join("\n") + "\n"].forEach((text, index) => {
        fs.writeFileSync(files[index], text, "ascii");
    });
    const verdict = execFileSync("sh", ["checker-js/check.sh", ...files, engine], {encoding: "utf8"});
    assert.strictEqual(verdict, "provisional skipped 0 assumed 4 given-definitions 0 given-facts 0\n");
} finally {
    fs.rmSync(scratch, {recursive: true, force: true});
}

const context = vm.createContext({});
vm.runInContext(source, context);
const check = context.checkBoymoo;
assert.strictEqual(check(ground, "", '(package "DYNAMIC" COMMON-LISP::NIL)\n', ""), "accepted\n");
assert.match(check(ground, "", "(reserve DYNAMIC::X)\n", ""), /^rejected statements 1\n/);
assert.strictEqual(check(ground, "", "", ""), "accepted\n");
assert.throws(() => check("", "", "", ""), /Invalid ground theory/);

async function browserAdapter() {
    const elements = {
        inputs: {addEventListener(name, handler) { this[name] = handler; }},
        check: {},
        verdict: {textContent: ""},
        ground: {files: [fs.readFileSync("spec/ground.txt")]},
        library: {files: []},
        statements: {files: [fs.readFileSync("spec/example/statements.txt")]},
        proofs: {files: [fs.readFileSync("spec/example/proofs.txt")]}
    };
    class FileReader {
        readAsArrayBuffer(bytes) {
            this.result = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
            setImmediate(() => this.onload());
        }
    }
    context.document = {getElementById: id => elements[id]};
    context.FileReader = FileReader;
    vm.runInContext(fs.readFileSync("checker-js/check-page.js", "utf8"), context);
    elements.inputs.submit({preventDefault() {}});
    await new Promise(resolve => setImmediate(resolve));
    assert.strictEqual(elements.verdict.textContent, "accepted\n");
    assert.strictEqual(elements.check.disabled, false);
    elements.statements.files = [Buffer.from([0, 10])];
    elements.inputs.submit({preventDefault() {}});
    await new Promise(resolve => setImmediate(resolve));
    assert.match(elements.verdict.textContent, /^rejected statements 1\n/);
}

browserAdapter().then(() => {
    process.stdout.write("all stress tests passed (" + depth + " levels, " + width + " elements)\n");
}).catch(error => {
    process.stderr.write(error.stack + "\n");
    process.exitCode = 1;
});
