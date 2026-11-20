// This tool takes exported statements and writes the skips for a book.
"use strict";

const fs = require("fs");

function readExportedForm(line) {
    const lists = [];
    let position = 0;
    while (position < line.length) {
        const byte = line[position];
        if (byte === " ") {
            position += 1;
        } else if (byte === "(") {
            lists.push([]);
            position += 1;
        } else if (byte === ")") {
            const form = lists.pop();
            position += 1;
            if (!lists.length) {
                return form;
            }
            lists[lists.length - 1].push(form);
        } else {
            const start = position;
            if (line.startsWith("#C(", position)) {
                const end = line.indexOf(")", position);
                if (end < 0) {
                    throw new Error("Unterminated complex rational in exported form");
                }
                position = end + 1;
            } else {
                let delimiter = "";
                while (position < line.length) {
                    const current = line[position];
                    if (delimiter) {
                        position += current === "\\" ? 3 : 1;
                        if (current === delimiter) {
                            delimiter = "";
                        }
                    } else if (current === " " || current === "(" || current === ")") {
                        break;
                    } else {
                        if (current === '"' || current === "|") {
                            delimiter = current;
                        }
                        position += 1;
                    }
                }
            }
            lists[lists.length - 1].push(line.slice(start, position));
        }
    }
    throw new Error("Expected an exported form");
}

function callsDefinedFunction(definitions) {
    const names = new Set(definitions.map(definition => definition[0]));
    const pending = definitions.map(definition => definition[2]);
    while (pending.length) {
        const term = pending.pop();
        if (!Array.isArray(term) || term[0] === "COMMON-LISP::QUOTE") {
            continue;
        }
        const operator = term[0];
        if (names.has(operator)) {
            return true;
        }
        if (operator === "ACL2::RETURN-LAST" && Array.isArray(term[1]) &&
                term[1][0] === "COMMON-LISP::QUOTE" && term[1][1] === "ACL2::MBE1-RAW") {
            pending.push(term[3]);
            continue;
        }
        if (Array.isArray(operator)) {
            pending.push(operator[2]);
        }
        for (let argument = 1; argument < term.length; argument += 1) {
            pending.push(term[argument]);
        }
    }
    return false;
}

function skips(libraryLines, book) {
    const seen = new Set(libraryLines);
    const entries = [];
    for (const line of book.split("\n")) {
        if (seen.has(line)) {
            continue;
        }
        seen.add(line);
        if (line.startsWith("(theorem ")) {
            entries.push(readExportedForm(line)[1]);
        } else if (line.startsWith("(define ")) {
            const definitions = readExportedForm(line).slice(2);
            if (callsDefinedFunction(definitions)) {
                entries.push(definitions[0][0]);
            }
        } else if (line.startsWith("(constrain ")) {
            const form = readExportedForm(line);
            if (Array.isArray(form[2]) && form[2].length) {
                entries.push(form[1][0][0]);
            }
        }
    }
    return entries.map(name => "(skip " + name + ")\n").join("");
}

module.exports = skips;

if (require.main === module) {
    if (process.argv.length !== 4) {
        process.stderr.write("Usage: node checker-js/skips.js LIBRARY STATEMENTS\n");
        process.exitCode = 2;
    } else {
        const library = fs.readFileSync(process.argv[2], "latin1").split("\n");
        const book = fs.readFileSync(process.argv[3], "latin1");
        process.stdout.write(skips(library, book));
    }
}
