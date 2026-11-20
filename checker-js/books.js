// Run the checker on exported books with every proof obligation skipped.
"use strict";

const fs = require("fs");
const path = require("path");
const vm = require("vm");
const {spawnSync} = require("child_process");
const {performance} = require("perf_hooks");
const skips = require("./skips.js");

const [host, engine = host] = process.argv.slice(2);
if (process.argv.length > 4 || !["node", "jsc", "duk"].includes(host) ||
        (host === "node" && process.argv.length > 3)) {
    process.stderr.write("Usage: node checker-js/books.js node | jsc [ENGINE] | duk [ENGINE]\n");
    process.exit(2);
}

const output = "build/checker-js";
const groundPath = "spec/ground.txt";
const libraryPath = "build/export/library.statements";
const core = "checker-js/check.js";
const empty = output + "/empty";
const read = name => fs.readFileSync(name, "latin1");
const ground = read(groundPath);
const library = read(libraryPath);
const libraryLines = library.split("\n");
const names = read("export/books.txt").split("\n").map(line => line.split("#")[0].trim()).filter(Boolean);
const books = names.map(name => {
    const file = "build/export/books/" + name + ".statements";
    return {name, file, bytes: fs.statSync(file).size, proofs: output + "/skips/" + name};
});
const check = vm.runInThisContext(read(core) + "\ncheckBoymoo;");
const started = performance.now();
const metrics = ["book\tstatement-bytes\tcheck-ms\tpeak-rss-bytes"];
const verdicts = [];
const failures = [];
let scratch, shared, current, timer, report;

fs.mkdirSync(output, {recursive: true});
fs.writeFileSync(empty, "");

function encode(text) {
    const parts = [];
    for (let offset = 0; offset < text.length; offset += 4096) {
        const part = text.slice(offset, offset + 4096);
        parts.push('"' + part.replace(/[^ -~]|["\\]/g, c =>
            "\\x" + c.charCodeAt(0).toString(16).padStart(2, "0")) + '"');
    }
    return "boymooInputs.push([" + parts.join(",\n") + '].join(""));\n';
}

function command(file, args, options) {
    const child = spawnSync(file, args, {encoding: "utf8", ...options});
    if (child.error) {
        throw child.error;
    }
    if (child.status !== 0) {
        throw new Error(file + " exited with " + (child.signal || child.status) + "\n" +
            child.stdout + child.stderr);
    }
    return child;
}

function sampleBooks() {
    if (host !== "duk") {
        return books;
    }
    const sorted = books.slice().sort((a, b) => a.bytes - b.bytes);
    const sample = new Set(Array.from({length: 20}, (_, index) =>
        sorted[Math.round(index * (sorted.length - 1) / 19)]));
    return books.filter(book => sample.has(book));
}

function prepareDuktape() {
    scratch = fs.mkdtempSync(output + "/bench-");
    shared = scratch + "/shared.js";
    current = scratch + "/book.js";
    timer = scratch + "/peak-rss";
    report = scratch + "/report.js";
    const env = {...process.env, TMPDIR: path.resolve(scratch)};
    command(process.env.BOYMOO_CC || "cc", ["-O2", "-o", timer, "checker-js/peak-rss.c"], {env});
    fs.writeFileSync(shared, "var boymooInputs = [];\n" + encode(ground) + encode(library));
    fs.writeFileSync(report, [
        "var started = Date.now();",
        "var verdict = checkBoymoo.apply(null, boymooInputs);",
        "var elapsed = Date.now() - started;",
        "print(verdict.slice(0, -1));",
        "print(elapsed);"
    ].join("\n"));
}

function run(book, statementText, proofText) {
    let child, before, resident = "";
    if (host === "node") {
        before = performance.now();
        const verdict = check(ground, library, statementText, proofText);
        return {verdict: verdict.trimEnd(), ms: performance.now() - before, resident};
    }
    if (host === "jsc") {
        child = command(engine, [core, "checker-js/check-jsc.js", "--",
            groundPath, libraryPath, book ? book.file : empty, book ? book.proofs : empty, "--timed"]);
    } else {
        fs.writeFileSync(current, encode(statementText) + encode(proofText));
        child = command(timer, [engine, core, shared, current, report]);
        const match = /peak-rss-bytes (\d+)/.exec(child.stderr);
        if (!match || Number(match[1]) === 0) {
            throw new Error("Duktape peak resident set size is unavailable");
        }
        resident = match[1];
    }
    const lines = child.stdout.trimEnd().split("\n");
    const ms = Number(lines.pop());
    if (!Number.isFinite(ms)) {
        throw new Error("Missing checker time");
    }
    return {verdict: lines.join("\n"), ms, resident};
}

function record(book, result) {
    metrics.push([book ? book.name : "(library)", book ? book.bytes : library.length,
        result.ms.toFixed(3), result.resident].join("\t"));
    const verdict = result.verdict.split("\n")[0];
    if (book) {
        verdicts.push(book.name + "\t" + verdict);
    }
    if (!verdict.startsWith("provisional ")) {
        failures.push([book ? book.name : "(library)", result.verdict].join("\t"));
    }
    return verdict;
}

try {
    if (host === "duk") {
        if (process.platform !== "darwin" && process.platform !== "linux") {
            throw new Error("Peak resident set size is supported on macOS and Linux");
        }
        prepareDuktape();
    }
    const admitted = run(null, "", "");
    const libraryVerdict = record(null, admitted);
    let bookTime = 0;
    const selected = sampleBooks();
    for (const book of selected) {
        const statementText = read(book.file);
        const proofText = skips(libraryLines, statementText);
        fs.mkdirSync(path.dirname(book.proofs), {recursive: true});
        fs.writeFileSync(book.proofs, proofText, "ascii");
        const result = run(book, statementText, proofText);
        record(book, result);
        bookTime += result.ms;
    }
    const verdictPath = output + "/books" + (host === "node" ? "" : "-" + host) + ".txt";
    fs.writeFileSync(verdictPath, verdicts.join("\n") + "\n");
    fs.writeFileSync(output + "/times-" + host + ".tsv", metrics.join("\n") + "\n");
    const summary = [
        "library\t" + libraryVerdict + "\t" + admitted.ms.toFixed(3) + " ms",
        "books\t" + selected.length + "\t" + bookTime.toFixed(3) + " ms of checking",
        "elapsed\t" + (performance.now() - started).toFixed(3) + " ms",
        "failures\t" + failures.length
    ];
    fs.writeFileSync(output + "/summary-" + host + ".txt", summary.join("\n") + "\n");
    process.stdout.write(summary.join("\n") + "\n");
    if (failures.length) {
        fs.writeFileSync(output + "/failures-" + host + ".txt", failures.join("\n") + "\n");
        process.exitCode = 1;
    } else {
        fs.rmSync(output + "/failures-" + host + ".txt", {force: true});
    }
} finally {
    if (scratch) {
        fs.rmSync(scratch, {recursive: true, force: true});
    }
}
