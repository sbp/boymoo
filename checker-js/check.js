"use strict";

function checkBoymoo(ground, library, statements, proofs) {
    var PAIR = 1, SYMBOL = 2, STRING = 3, RATIONAL = 4, COMPLEX = 5, CHARACTER = 6;
    var limit = 67108864, over = limit + 1;
    var maxExact = 9007199254740991;
    var base = 10000000, digitsPerLimb = 7, one = [1];
    var zero = rational(0, [], one);
    var serial = 0, place;
    var packages = table(), symbols = table(), names = table(), functions = table();
    var primitives = table(), specials = table(), facts = table(), stringFacts = table();
    var seen = table();
    var skipped = 0, assumed = 0, givenDefinitions = 0, givenFacts = 0;
    var cl = "COMMON-LISP", acl2 = "ACL2", keyword = "KEYWORD";
    var nil = symbol(cl, "NIL"), truth = symbol(cl, "T");
    var quote = symbol(cl, "QUOTE"), lambda = symbol(cl, "LAMBDA");
    var equal = symbol(cl, "EQUAL"), not = symbol(cl, "NOT"), ifSymbol = symbol(cl, "IF");
    var listSymbol = symbol(cl, "LIST"), implies = symbol(acl2, "IMPLIES");
    var ord = symbol(acl2, "O-P"), lessOrd = symbol(acl2, "O<");
    var returnLast = symbol(acl2, "RETURN-LAST"), mbeRaw = symbol(acl2, "MBE1-RAW");
    var all = symbol(keyword, "ALL"), lambdas = symbol(keyword, "LAMBDAS");
    var pkgImports = symbol(acl2, "PKG-IMPORTS"), witnessName = "ACL2-PKG-WITNESS";
    var quotedNil, quotedTrue;
    var plain = [];
    var plainAlphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-+*/<=>!?$%&_^~.@";
    var i;

    nil.length = 0;
    names[nil.id] = names[truth.id] = true;
    quotedNil = quoted(nil);
    quotedTrue = quoted(truth);
    for (i = 0; i < plainAlphabet.length; i += 1) {
        plain[plainAlphabet.charCodeAt(i)] = true;
    }

    function table() {
        return Object.create(null);
    }

    function need(condition, message) {
        if (!condition) {
            reject(message);
        }
    }

    function reject(message) {
        if (place.input === "ground") {
            throw new Error("Invalid ground theory at line " + place.number + ". " + message);
        }
        throw {
            rejection: reject,
            text: "rejected " + place.input + " " + place.number + "\n" + message + "\n"
        };
    }

    function freshId() {
        if (serial === maxExact) {
            throw new RangeError("Too many data nodes");
        }
        serial += 1;
        return serial;
    }

    function symbol(pkg, name) {
        var entries = symbols[pkg];
        if (!entries) {
            entries = table();
            symbols[pkg] = entries;
        }
        if (!entries[name]) {
            entries[name] = {kind: SYMBOL, pkg: pkg, name: name, id: freshId(), size: 1};
        }
        return entries[name];
    }

    function string(value) {
        return {kind: STRING, value: value, size: 1};
    }

    function character(code) {
        return {kind: CHARACTER, value: code, size: 1};
    }

    // A size above either format budget has the single value 'over'.
    function cons(car, cdr) {
        return {
            kind: PAIR, car: car, cdr: cdr, id: freshId(),
            size: Math.min(over, 1 + car.size + cdr.size),
            length: cdr.length >= 0 ? cdr.length + 1 : -1
        };
    }

    function list(items, tail) {
        var index;
        for (index = items.length - 1; index >= 0; index -= 1) {
            tail = cons(items[index], tail);
        }
        return tail;
    }

    function call(head, args) {
        return cons(head, list(args, nil));
    }

    function quoted(datum) {
        return call(quote, [datum]);
    }

    function items(datum) {
        need(datum.length >= 0, "Expected a true list");
        var result = [];
        while (datum !== nil) {
            result.push(datum.car);
            datum = datum.cdr;
        }
        return result;
    }

    function isCall(datum, head, arity) {
        return datum.kind === PAIR && datum.car === head && datum.length === arity + 1;
    }

    function isQuote(datum, value) {
        return isCall(datum, quote, 1) && datum.cdr.car === value;
    }

    function isMbe(term) {
        return isCall(term, returnLast, 3) && isQuote(term.cdr.car, mbeRaw);
    }

    function clauseSize(clause) {
        var index, size = 0;
        for (index = 0; index < clause.length && size < over; index += 1) {
            size += clause[index].size;
        }
        return Math.min(over, size);
    }

    function sameDatum(left, right) {
        var stack = [left, right], compared;
        var key;
        while (stack.length) {
            right = stack.pop();
            left = stack.pop();
            if (left === right) {
                continue;
            }
            if (left.kind !== right.kind || left.size !== right.size) {
                return false;
            }
            switch (left.kind) {
            case PAIR:
                if (!compared) {
                    compared = table();
                }
                key = left.id + "," + right.id;
                if (!compared[key]) {
                    compared[key] = true;
                    stack.push(left.cdr, right.cdr, left.car, right.car);
                }
                break;
            case STRING:
            case CHARACTER:
                if (left.value !== right.value) {
                    return false;
                }
                break;
            case RATIONAL:
                if (!sameRational(left, right)) {
                    return false;
                }
                break;
            case COMPLEX:
                if (!sameRational(left.real, right.real) || !sameRational(left.imag, right.imag)) {
                    return false;
                }
                break;
            default:
                return false; // Distinct interned symbols.
            }
        }
        return true;
    }

    function sameClause(left, right) {
        var index;
        if (left.length !== right.length) {
            return false;
        }
        for (index = 0; index < left.length; index += 1) {
            if (!sameDatum(left[index], right[index])) {
                return false;
            }
        }
        return true;
    }

    // Magnitudes are little-endian limbs in base 10^7, with no high zero.
    // Each limb product together with its carries is below 2^53.
    function trim(magnitude) {
        while (magnitude.length && magnitude[magnitude.length - 1] === 0) {
            magnitude.pop();
        }
        return magnitude;
    }

    function compareMagnitude(left, right) {
        var index;
        if (left.length !== right.length) {
            return left.length - right.length;
        }
        for (index = left.length - 1; index >= 0; index -= 1) {
            if (left[index] !== right[index]) {
                return left[index] - right[index];
            }
        }
        return 0;
    }

    function addMagnitude(left, right) {
        var result = [], carry = 0, index, sum;
        var length = Math.max(left.length, right.length);
        for (index = 0; index < length; index += 1) {
            sum = (left[index] || 0) + (right[index] || 0) + carry;
            carry = Math.floor(sum / base);
            result.push(sum - carry * base);
        }
        if (carry) {
            result.push(carry);
        }
        return result;
    }

    function subtractMagnitude(left, right) {
        var result = [], borrow = 0, index, difference;
        for (index = 0; index < left.length; index += 1) {
            difference = left[index] - (right[index] || 0) - borrow;
            borrow = difference < 0 ? 1 : 0;
            result.push(difference + borrow * base);
        }
        return trim(result);
    }

    function multiplyMagnitude(left, right) {
        var result = [], index, j, carry, product;
        if (!left.length || !right.length) {
            return result;
        }
        for (index = 0; index < left.length; index += 1) {
            carry = 0;
            for (j = 0; j < right.length; j += 1) {
                product = left[index] * right[j] + (result[index + j] || 0) + carry;
                carry = Math.floor(product / base);
                result[index + j] = product - carry * base;
            }
            result[index + right.length] = carry;
        }
        return trim(result);
    }

    function divideByLimb(numerator, denominator) {
        var quotient = [], remainder = 0, index, part;
        for (index = numerator.length - 1; index >= 0; index -= 1) {
            part = remainder * base + numerator[index];
            quotient[index] = Math.floor(part / denominator);
            remainder = part - quotient[index] * denominator;
        }
        return {quotient: trim(quotient), remainder: remainder ? [remainder] : []};
    }

    function divideMagnitude(numerator, denominator) {
        var width = denominator.length, quotient = [];
        var factor, dividend, divisor, column, top, digit, remainder;
        var index, product, borrow, difference, carry, sum;
        if (compareMagnitude(numerator, denominator) < 0) {
            return {quotient: [], remainder: numerator};
        }
        if (width === 1) {
            return divideByLimb(numerator, denominator[0]);
        }

        // Normalize the leading divisor limb to at least half the base.
        // The leading two limbs estimate one quotient digit at a time.
        factor = Math.floor(base / (denominator[width - 1] + 1));
        dividend = multiplyMagnitude(numerator, [factor]);
        divisor = multiplyMagnitude(denominator, [factor]);
        dividend[numerator.length] = dividend[numerator.length] || 0;
        for (column = numerator.length - width; column >= 0; column -= 1) {
            top = dividend[column + width] * base + dividend[column + width - 1];
            digit = Math.min(base - 1, Math.floor(top / divisor[width - 1]));
            remainder = top - digit * divisor[width - 1];
            while (remainder < base &&
                    digit * divisor[width - 2] > remainder * base + dividend[column + width - 2]) {
                digit -= 1;
                remainder += divisor[width - 1];
            }
            borrow = 0;
            for (index = 0; index < width; index += 1) {
                product = digit * divisor[index] + borrow;
                borrow = Math.floor(product / base);
                difference = dividend[column + index] - (product - borrow * base);
                if (difference < 0) {
                    difference += base;
                    borrow += 1;
                }
                dividend[column + index] = difference;
            }
            top = dividend[column + width] - borrow;
            if (top < 0) {
                digit -= 1;
                carry = 0;
                for (index = 0; index < width; index += 1) {
                    sum = dividend[column + index] + divisor[index] + carry;
                    carry = Math.floor(sum / base);
                    dividend[column + index] = sum - carry * base;
                }
                top += carry;
            }
            dividend[column + width] = top;
            quotient[column] = digit;
        }
        return {
            quotient: trim(quotient),
            remainder: divideByLimb(dividend.slice(0, width), factor).quotient
        };
    }

    function gcd(left, right) {
        var remainder;
        while (right.length) {
            remainder = divideMagnitude(left, right).remainder;
            left = right;
            right = remainder;
        }
        return left;
    }

    function rational(sign, numerator, denominator) {
        return {kind: RATIONAL, sign: sign, n: numerator, d: denominator, size: 1};
    }

    function integer(value) {
        var magnitude = [], rest = Math.abs(value), next;
        while (rest) {
            next = Math.floor(rest / base);
            magnitude.push(rest - next * base);
            rest = next;
        }
        return value ? rational(value < 0 ? -1 : 1, magnitude, one) : zero;
    }

    function isInteger(value) {
        return value.kind === RATIONAL && compareMagnitude(value.d, one) === 0;
    }

    function natural(value) {
        var index, limb, result = 0;
        if (!isInteger(value) || value.sign < 0) {
            return -1;
        }
        for (index = value.n.length - 1; index >= 0; index -= 1) {
            limb = value.n[index];
            if (result > Math.floor((maxExact - limb) / base)) {
                return -1;
            }
            result = result * base + limb;
        }
        return result;
    }

    function sameRational(left, right) {
        return left.sign === right.sign && compareMagnitude(left.n, right.n) === 0 &&
            compareMagnitude(left.d, right.d) === 0;
    }

    function reduced(sign, numerator, denominator) {
        var common;
        if (!numerator.length) {
            return zero;
        }
        if (compareMagnitude(denominator, one) !== 0) {
            common = gcd(numerator, denominator);
            if (compareMagnitude(common, one) !== 0) {
                numerator = divideMagnitude(numerator, common).quotient;
                denominator = divideMagnitude(denominator, common).quotient;
            }
        }
        return rational(sign, numerator, denominator);
    }

    function negative(value) {
        return value.sign ? rational(-value.sign, value.n, value.d) : value;
    }

    function addRational(left, right) {
        if (!left.sign || !right.sign) {
            return left.sign ? left : right;
        }
        var a = multiplyMagnitude(left.n, right.d);
        var b = multiplyMagnitude(right.n, left.d);
        var denominator = multiplyMagnitude(left.d, right.d);
        if (left.sign === right.sign) {
            return reduced(left.sign, addMagnitude(a, b), denominator);
        }
        if (compareMagnitude(a, b) < 0) {
            return reduced(right.sign, subtractMagnitude(b, a), denominator);
        }
        return reduced(left.sign, subtractMagnitude(a, b), denominator);
    }

    function multiplyRational(left, right) {
        return reduced(left.sign * right.sign, multiplyMagnitude(left.n, right.n),
            multiplyMagnitude(left.d, right.d));
    }

    function divideRational(left, right) {
        return reduced(left.sign * right.sign, multiplyMagnitude(left.n, right.d),
            multiplyMagnitude(left.d, right.n));
    }

    function compareRational(left, right) {
        if (left.sign !== right.sign) {
            return left.sign - right.sign;
        }
        return left.sign * compareMagnitude(multiplyMagnitude(left.n, right.d),
            multiplyMagnitude(right.n, left.d));
    }

    function numberp(value) {
        return value.kind === RATIONAL || value.kind === COMPLEX;
    }

    function real(value) {
        return value.kind === COMPLEX ? value.real : fixedRational(value);
    }

    function imag(value) {
        return value.kind === COMPLEX ? value.imag : zero;
    }

    function fixedRational(value) {
        return value.kind === RATIONAL ? value : zero;
    }

    function complex(r, j) {
        return j.sign ? {kind: COMPLEX, real: r, imag: j, size: 1} : r;
    }

    function magnitude(text) {
        var result = [], end, start;
        if (text !== "0") {
            for (end = text.length; end > 0; end = start) {
                start = Math.max(0, end - digitsPerLimb);
                result.push(Number(text.slice(start, end)));
            }
        }
        return result;
    }

    function readRational(token) {
        var slash = token.indexOf("/");
        var numerator = slash < 0 ? token : token.slice(0, slash);
        var sign = numerator.charAt(0) === "-" ? -1 : 1;
        if (sign < 0) {
            numerator = numerator.slice(1);
        }
        need(/^(0|[1-9][0-9]*)$/.test(numerator) && (sign > 0 || numerator !== "0"),
            "Invalid integer spelling");
        var n = magnitude(numerator), d = one, denominator;
        if (slash >= 0) {
            denominator = token.slice(slash + 1);
            need(n.length && /^[1-9][0-9]*$/.test(denominator) && denominator !== "1",
                "Invalid fraction spelling");
            d = magnitude(denominator);
            need(compareMagnitude(gcd(n, d), one) === 0, "Fraction is not in lowest terms");
        }
        return n.length ? rational(sign, n, d) : zero;
    }

    function exists(datum) {
        var pkg = packages[datum.pkg];
        return pkg && !pkg.imported[datum.name];
    }

    function parseLine(raw, checkSymbols) {
        var pos = 1, end = raw.length - 1, start, code, word, data = [];
        need(raw.charAt(0) === "(" && raw.charAt(end) === ")" && !/[^ -~]/.test(raw),
            "Expected a parenthesized printable ASCII line");
        code = raw.charCodeAt(pos);
        while ((code >= 97 && code <= 122) || code === 45) {
            pos += 1;
            code = raw.charCodeAt(pos);
        }
        need(pos > 1, "Expected a format word");
        word = raw.slice(1, pos);
        while (pos < end) {
            need(raw.charCodeAt(pos) === 32, "Expected a single space before a datum");
            pos += 1;
            data.push(datum());
        }
        need(pos === end, "Unexpected end of line");
        return {word: word, data: data};

        function hex() {
            var a = "0123456789ABCDEF".indexOf(raw.charAt(pos));
            var b = "0123456789ABCDEF".indexOf(raw.charAt(pos + 1));
            need(pos + 1 < end && a >= 0 && b >= 0, "Expected two uppercase hexadecimal digits");
            pos += 2;
            return a * 16 + b;
        }

        function plainRun() {
            var begin = pos;
            while (plain[raw.charCodeAt(pos)]) {
                pos += 1;
            }
            need(pos > begin, "Expected a plain token");
            return raw.slice(begin, pos);
        }

        function delimited(delimiter) {
            var chunks = [], begin, c;
            pos += 1;
            begin = pos;
            while (pos < end) {
                c = raw.charCodeAt(pos);
                if (c === delimiter) {
                    chunks.push(raw.slice(begin, pos));
                    pos += 1;
                    return chunks.join("");
                }
                if (c === 92) {
                    chunks.push(raw.slice(begin, pos));
                    pos += 1;
                    c = hex();
                    need(c < 32 || c > 126 || c === 92 || c === delimiter,
                        "Escape of a character that can be written literally");
                    chunks.push(String.fromCharCode(c));
                    begin = pos;
                } else {
                    pos += 1;
                }
            }
            reject("Unterminated string or symbol part");
        }

        function symbolPart() {
            var part, index;
            if (raw.charCodeAt(pos) !== 124) {
                return plainRun();
            }
            part = delimited(124);
            for (index = 0; index < part.length; index += 1) {
                if (!plain[part.charCodeAt(index)]) {
                    return part;
                }
            }
            need(!part.length, "Bars around a plain symbol part");
            return part;
        }

        function atom() {
            var c = raw.charCodeAt(pos), part, pkg, item, r, j;
            if (c === 34) {
                return string(delimited(34));
            }
            if (c === 35) {
                if (raw.substr(pos, 2) === "#\\") {
                    pos += 2;
                    return character(hex());
                }
                need(raw.substr(pos, 3) === "#C(", "Expected a character or complex rational");
                pos += 3;
                r = readRational(plainRun());
                need(raw.charCodeAt(pos) === 32, "Expected one space between complex parts");
                pos += 1;
                j = readRational(plainRun());
                need(j.sign && raw.charCodeAt(pos) === 41, "Invalid complex rational");
                pos += 1;
                return complex(r, j);
            }
            start = pos;
            part = symbolPart();
            if (raw.substr(pos, 2) !== "::") {
                need(c !== 124, "Expected a symbol after a delimited package name");
                return readRational(part);
            }
            pkg = part;
            pos += 2;
            part = symbolPart();
            item = symbol(pkg, part);
            if (checkSymbols && !exists(item)) {
                reject("Symbol does not exist: " + raw.slice(start, pos));
            }
            return item;
        }

        function datum() {
            var nesting = [], value, elements, tail;
            while (true) {
                while (raw.charCodeAt(pos) === 40) {
                    pos += 1;
                    nesting.push([]);
                }
                value = atom();
                while (nesting.length) {
                    elements = nesting[nesting.length - 1];
                    elements.push(value);
                    tail = nil;
                    if (raw.substr(pos, 3) === " . ") {
                        pos += 3;
                        tail = atom();
                        need(tail !== nil && raw.charCodeAt(pos) === 41,
                            "Expected an atom other than NIL as the final cdr");
                    } else if (raw.charCodeAt(pos) !== 41) {
                        need(raw.charCodeAt(pos) === 32, "Expected one space or a closing parenthesis");
                        pos += 1;
                        break;
                    }
                    pos += 1;
                    value = list(elements, tail);
                    nesting.pop();
                }
                if (!nesting.length) {
                    return value;
                }
            }
        }
    }

    function input(name, source) {
        return {input: name, source: source, start: 0, number: 0};
    }

    function locate(source, number) {
        place = {input: source.input, number: number};
    }

    function nextLine(source, admitted) {
        var end, raw;
        while (source.start < source.source.length) {
            source.number += 1;
            locate(source, source.number);
            end = source.source.indexOf("\n", source.start);
            need(end >= 0, "Line has no final line feed");
            raw = source.source.slice(source.start, end);
            source.start = end + 1;
            if (admitted && admitted[raw]) {
                continue;
            }
            if (admitted) {
                admitted[raw] = true;
            }
            return parseLine(raw, source.input !== "ground");
        }
        return null;
    }

    function variable(datum) {
        if (datum.kind !== SYMBOL || datum === nil || datum === truth || datum.pkg === keyword) {
            return false;
        }
        var name = datum.name;
        return name.charAt(0) !== "&" && !(name.charAt(0) === "*" &&
            name.charAt(name.length - 1) === "*") &&
            (datum.pkg !== cl || (packages[acl2].imported[name] === datum && !specials[datum.id]));
    }

    function variableList(datum) {
        var allVariables = items(datum), scope = table(), index, v;
        for (index = 0; index < allVariables.length; index += 1) {
            v = allVariables[index];
            need(variable(v) && !scope[v.id], "Expected distinct variables");
            scope[v.id] = true;
        }
        return {items: allVariables, scope: scope};
    }

    function arity(value) {
        need(isInteger(value) && value.sign >= 0, "Expected a nonnegative integer arity");
        var count = natural(value);
        return count >= 0 ? count : value;
    }

    function sameArity(left, right) {
        return left === right || (typeof left === "object" && typeof right === "object" &&
            sameRational(left, right));
    }

    function checkTerm(root, scope, pending, findRecursiveCalls) {
        var stack = [root, scope, findRecursiveCalls], recursive = false;
        var term, detect, operator, actuals, count, formals, executable;
        while (stack.length) {
            detect = stack.pop();
            scope = stack.pop();
            term = stack.pop();
            if (term.kind === SYMBOL) {
                need(variable(term) && (!scope || scope[term.id]), "Illegal or out-of-scope variable");
                continue;
            }
            need(term.kind === PAIR && term.length >= 0, "Expected a term that is a true list");
            operator = term.car;
            if (operator === quote) {
                need(term.length === 2, "QUOTE takes one datum");
                continue;
            }
            if (operator.kind === PAIR) {
                need(isCall(operator, lambda, 2), "Invalid lambda operator");
                formals = variableList(operator.cdr.car);
                count = formals.items.length;
                stack.push(operator.cdr.cdr.car, formals.scope, detect);
            } else {
                need(operator.kind === SYMBOL, "Expected a function name");
                count = pending ? pending[operator.id] : undefined;
                if (count === undefined) {
                    count = functions[operator.id];
                } else if (detect) {
                    recursive = true;
                }
            }
            need(term.length - 1 === count, "Unknown function or wrong number of arguments");
            executable = detect && isMbe(term) ? term.cdr.cdr : null;
            for (actuals = term.cdr; actuals !== nil; actuals = actuals.cdr) {
                stack.push(actuals.car, scope, detect && actuals !== executable);
            }
        }
        return recursive;
    }

    function properSymbols(datum) {
        var result = items(datum), index;
        for (index = 0; index < result.length; index += 1) {
            need(result[index].kind === SYMBOL, "Expected a list of symbols");
        }
        return result;
    }

    function fields(datum, length) {
        need(datum.length === length, "Wrong number of elements in a list");
        return items(datum);
    }

    function freshName(datum, isFunction, allowLisp) {
        need(datum.kind === SYMBOL && datum.pkg !== keyword, "Name must be a symbol other than a keyword");
        need(!names[datum.id], "Name is already in use");
        if (isFunction) {
            need(datum !== quote && (allowLisp || datum.pkg !== cl), "Illegal function name");
        }
        names[datum.id] = true;
    }

    function intern(pkg, name) {
        return packages[pkg].imported[name] || symbol(pkg, name);
    }

    function declarePackage(data, hidden, isGround) {
        need(data.length === 2 && data[0].kind === STRING, "Expected a package name and imports");
        var name = data[0].value, earlier = packages[name], imports = properSymbols(data[1]);
        var index, previous, imported = table(), item;
        need(name.length && !/[a-z]/.test(name) && name !== "LISP" && name.indexOf("ACL2_*1*_") !== 0,
            "Illegal package name");
        need(!earlier || (!hidden && earlier.hidden && sameDatum(earlier.list, data[1])),
            "Package is already declared with this visibility or with different imports");
        for (index = 0; index < imports.length; index += 1) {
            item = imports[index];
            need(exists(item), "Imported symbol does not exist");
            need(item.name !== witnessName && !imported[item.name], "Duplicate import or witness import");
            need(isGround || previous === undefined || previous < item.name,
                "Imports are out of order by name");
            imported[item.name] = item;
            previous = item.name;
        }
        packages[name] = {hidden: hidden, imported: imported, list: data[1]};
        if (!hidden && !isGround) {
            packageFact(name);
        }
    }

    function packageFact(name) {
        var rule = intern(acl2, name + "-PACKAGE");
        freshName(rule, false, false);
        facts[rule.id] = [call(equal, [call(pkgImports, [quoted(string(name))]),
            quoted(packages[name].list)])];
    }

    function prepareDefine(data, allowLisp) {
        need(data.length >= 2, "Expected ruler-extenders and one or more definitions");
        var rulers = data[0], extenders = table(), pending = table();
        var definitions = [], known = [], definitionsFacts = [], recursive = false;
        var index, def, formals, fn;
        if (rulers !== all) {
            rulers = properSymbols(rulers);
            for (index = 0; index < rulers.length; index += 1) {
                extenders[rulers[index].id] = true;
            }
        }
        for (index = 1; index < data.length; index += 1) {
            def = fields(data[index], 3);
            fn = def[0];
            freshName(fn, true, allowLisp);
            formals = variableList(def[1]);
            known.push(fn);
            pending[fn.id] = formals.items.length;
            definitions.push({fn: fn, formals: formals, body: def[2]});
        }
        for (index = 0; index < definitions.length; index += 1) {
            def = definitions[index];
            if (checkTerm(def.body, def.formals.scope, pending, true)) {
                recursive = true;
            }
            definitionsFacts.push([def.fn, [call(equal, [call(def.fn, def.formals.items), def.body])]]);
        }
        return {
            head: known[0], entry: recursive ? "measure" : null, known: known,
            pending: pending, facts: definitionsFacts, definitions: definitions,
            allRulers: rulers === all, extenders: extenders
        };
    }

    function prepareConstrain(data, allowLisp) {
        need(data.length === 2, "Expected function signatures and constraint formulas");
        var signatures = items(data[0]), formulas = items(data[1]);
        var known = [], pending = table(), newFacts = [], index, entry;
        need(signatures.length, "Expected at least one constrained function");
        for (index = 0; index < signatures.length; index += 1) {
            entry = fields(signatures[index], 2);
            freshName(entry[0], true, allowLisp);
            known.push(entry[0]);
            pending[entry[0].id] = arity(entry[1]);
        }
        for (index = 0; index < formulas.length; index += 1) {
            entry = fields(formulas[index], 2);
            freshName(entry[0], false, false);
            checkTerm(entry[1], null, pending, false);
            newFacts.push([entry[0], [entry[1]]]);
        }
        return {
            head: known[0], entry: formulas.length ? "witness" : null,
            known: known, pending: pending, facts: newFacts
        };
    }

    function bind(formals, actuals) {
        var bindings = table(), index;
        for (index = 0; index < formals.length; index += 1) {
            bindings[formals[index].id] = actuals[index];
        }
        return bindings;
    }

    // Traverse the term positions in postorder. Reuse a result for every
    // shared subterm. Substituting variables leaves a closed lambda body alone.
    function rewrite(root, bindings, renames, sizeOnly) {
        var tasks = [root], values = [], memo = table(), task, term, result;
        var actuals, body, index, start, head, rebuilt, used;
        while (tasks.length) {
            task = tasks.pop();
            if (task.term) {
                term = task.term;
                actuals = task.actuals;
                start = task.start;
                if (sizeOnly) {
                    result = term.car.size + actuals.length + 2;
                    for (index = 0; index < actuals.length && result < over; index += 1) {
                        result += values[start + index];
                    }
                    result = Math.min(over, result);
                } else {
                    head = term.car;
                    if (task.body) {
                        body = values[start + actuals.length];
                        if (body !== task.body) {
                            head = call(lambda, [head.cdr.car, body]);
                        }
                    } else if (renames && head.kind === SYMBOL && renames[head.id]) {
                        head = renames[head.id];
                    }
                    used = changedPrefixLength(actuals, values, start);
                    if (head === term.car && used === 0) {
                        result = term;
                    } else {
                        rebuilt = term.cdr;
                        for (index = 0; index < used; index += 1) {
                            rebuilt = rebuilt.cdr;
                        }
                        for (index = used - 1; index >= 0; index -= 1) {
                            rebuilt = cons(values[start + index], rebuilt);
                        }
                        result = cons(head, rebuilt);
                    }
                }
                memo[term.id] = result;
                values.length = start;
            } else if (task.kind === SYMBOL) {
                result = (bindings && bindings[task.id]) || task;
                if (sizeOnly) {
                    result = result.size;
                }
            } else if (task.car === quote) {
                result = sizeOnly ? task.size : task;
            } else if (memo[task.id] !== undefined) {
                result = memo[task.id];
            } else {
                actuals = items(task.cdr);
                body = renames && task.car.kind === PAIR ? task.car.cdr.cdr.car : null;
                tasks.push({term: task, actuals: actuals, body: body, start: values.length});
                if (body) {
                    tasks.push(body);
                }
                for (index = actuals.length - 1; index >= 0; index -= 1) {
                    tasks.push(actuals[index]);
                }
                continue;
            }
            values.push(result);
        }
        return values[0];
    }

    function changedPrefixLength(before, after, start) {
        var end = before.length;
        while (end > 0 && before[end - 1] === after[start + end - 1]) {
            end -= 1;
        }
        return end;
    }

    function applyBindings(term, bindings) {
        return bindings ? rewrite(term, bindings, null, false) : term;
    }

    function instantiatedSize(term, bindings) {
        return bindings ? rewrite(term, bindings, null, true) : term.size;
    }

    // A value too large for any obligation can still be passed through a
    // lambda formal that no obligation uses.
    var oversized = {size: over};

    function boundedInstance(term, bindings) {
        return instantiatedSize(term, bindings) <= limit ? applyBindings(term, bindings) : oversized;
    }

    function chooseArguments(bound, invocation) {
        if (bound.length === 1) {
            return bind(bound, [invocation]);
        }
        var actuals = [], index, mvNth = symbol(acl2, "MV-NTH");
        for (index = 0; index < bound.length; index += 1) {
            actuals.push(call(mvNth, [quoted(integer(index)), invocation]));
        }
        return bind(bound, actuals);
    }

    function admitChoose(data, allowLisp) {
        need(data.length === 5, "Expected a choice name, bound variables, free variables, body and FREE2");
        var fn = data[0], bound = variableList(data[1]), free = variableList(data[2]);
        var body = data[3], free2 = variableList(data[4]).items;
        var index, v, invocation, substitution, basic, body1, invocation2;
        var substitution2, body2, d1, d2, d3;
        freshName(fn, true, allowLisp);
        need(bound.items.length && (data[4] === nil || free2.length === free.items.length),
            "Expected bound variables and a matching FREE2 list");
        for (index = 0; index < free.items.length; index += 1) {
            v = free.items[index];
            need(!bound.scope[v.id], "A variable is both bound and free");
            bound.scope[v.id] = true;
        }
        for (index = 0; index < free2.length; index += 1) {
            need(!bound.scope[free2[index].id], "A FREE2 variable occurs in BOUND or FREE");
        }
        checkTerm(body, bound.scope, null, false);
        invocation = call(fn, free.items);
        substitution = chooseArguments(bound.items, invocation);
        body1 = applyBindings(body, substitution);
        basic = call(implies, [body, body1]);
        if (bound.items.length > 1) {
            basic = call(ifSymbol, [call(symbol(acl2, "TRUE-LISTP"), [invocation]), basic, quotedNil]);
        }
        if (free2.length) {
            invocation2 = call(fn, free2);
            substitution2 = chooseArguments(bound.items, invocation2);
            body2 = applyBindings(body, bind(free.items, free2));
            d1 = call(equal, [invocation, invocation2]);
            d2 = call(ifSymbol, [body1, call(not, [applyBindings(body2, substitution)]), quotedNil]);
            d3 = call(ifSymbol, [applyBindings(body2, substitution2),
                call(not, [applyBindings(body, substitution2)]), quotedNil]);
            basic = call(ifSymbol, [basic, call(ifSymbol, [d1, d1, call(ifSymbol, [d2, d2, d3])]),
                quotedNil]);
        }
        functions[fn.id] = free.items.length;
        facts[fn.id] = [basic];
    }

    function activate(definition) {
        var known = definition.known || [], index, fn;
        for (index = 0; index < known.length; index += 1) {
            fn = known[index];
            functions[fn.id] = definition.pending[fn.id];
        }
    }

    function establish(statement) {
        var index, fact;
        activate(statement);
        for (index = 0; index < statement.facts.length; index += 1) {
            fact = statement.facts[index];
            facts[fact[0].id] = fact[1];
        }
    }

    function exactData(line, count) {
        need(line.data.length === count, "Wrong number of data on a " + line.word + " line");
    }

    function loadGround(source) {
        var line, data, values, index, pkg;
        locate(source, 1);
        while ((line = nextLine(source))) {
            data = line.data;
            switch (line.word) {
            case "package":
                declarePackage(data, false, true);
                break;
            case "specials":
                exactData(line, 1);
                values = properSymbols(data[0]);
                for (index = 0; index < values.length; index += 1) {
                    need(values[index].pkg === cl, "A special name must belong to COMMON-LISP");
                    specials[values[index].id] = true;
                }
                break;
            case "primitive":
                exactData(line, 2);
                freshName(data[0], true, true);
                functions[data[0].id] = arity(data[1]);
                primitives[data[0].id] = true;
                break;
            case "define":
                establish(prepareDefine(data, true));
                break;
            case "clause":
                need(data.length, "Expected a ground fact name");
                if (data[0].kind === STRING) {
                    need(!stringFacts[data[0].value], "Ground fact is already in use");
                    stringFacts[data[0].value] = data.slice(1);
                } else {
                    freshName(data[0], false, true);
                    facts[data[0].id] = data.slice(1);
                }
                for (index = 1; index < data.length; index += 1) {
                    checkTerm(data[index], null, null, false);
                }
                break;
            default:
                reject("Unexpected ground word");
            }
        }
        need(packages[cl] && packages[acl2] && packages[keyword] &&
            packages["ACL2-INPUT-CHANNEL"] && packages["ACL2-OUTPUT-CHANNEL"], "Missing ground package");
        for (pkg in packages) {
            if (pkg !== cl) {
                packageFact(pkg);
            }
        }
    }

    function admit(line, given, proofInput) {
        var data = line.data, statement;
        switch (line.word) {
        case "package":
        case "hidden-package":
            declarePackage(data, line.word === "hidden-package", false);
            return;
        case "reserve":
            exactData(line, 1);
            freshName(data[0], false, given);
            return;
        case "define":
            statement = prepareDefine(data, given);
            break;
        case "constrain":
            statement = prepareConstrain(data, given);
            break;
        case "choose":
            admitChoose(data, given);
            return;
        case "theorem":
        case "axiom":
            exactData(line, 2);
            freshName(data[0], false, given);
            checkTerm(data[1], null, null, false);
            if (given) {
                givenFacts += 1;
            } else if (line.word === "axiom") {
                assumed += 1;
            }
            statement = {head: data[0], entry: line.word === "theorem" ? "theorem" : null,
                facts: [[data[0], [data[1]]]]};
            break;
        default:
            reject("Word is not a statement");
        }
        if (statement.entry) {
            if (given) {
                if (statement.entry !== "theorem") {
                    givenDefinitions += 1;
                }
            } else {
                checkStatementEntry(statement, proofInput);
            }
        }
        establish(statement);
    }

    function truthValue(condition) {
        return condition ? truth : nil;
    }

    function coerce(value, type) {
        var result, index, characters;
        if (type === listSymbol) {
            result = nil;
            if (value.kind === STRING) {
                for (index = value.value.length - 1; index >= 0; index -= 1) {
                    result = cons(character(value.value.charCodeAt(index)), result);
                }
            }
            return result;
        }
        characters = [];
        while (value.kind === PAIR) {
            characters.push(String.fromCharCode(value.car.kind === CHARACTER ? value.car.value : 0));
            value = value.cdr;
        }
        return string(characters.join(""));
    }

    function primitive(fn, args) {
        var x = args[0], y = args[1], comparison, pkg, a, b, c, d, norm;
        switch (fn.name) {
        case "ACL2-NUMBERP":
            return truthValue(numberp(x));
        case "BAD-ATOM<=":
            return nil;
        case "BINARY-+":
            return complex(addRational(real(x), real(y)), addRational(imag(x), imag(y)));
        case "BINARY-*":
            a = real(x);
            b = imag(x);
            c = real(y);
            d = imag(y);
            return complex(addRational(multiplyRational(a, c), negative(multiplyRational(b, d))),
                addRational(multiplyRational(a, d), multiplyRational(b, c)));
        case "UNARY--":
            return complex(negative(real(x)), negative(imag(x)));
        case "UNARY-/":
            if (x.kind === COMPLEX) {
                a = x.real;
                b = x.imag;
                norm = addRational(multiplyRational(a, a), multiplyRational(b, b));
                return complex(divideRational(a, norm), divideRational(negative(b), norm));
            }
            return x.kind === RATIONAL && x.sign ? rational(x.sign, x.d, x.n) : zero;
        case "<":
            comparison = compareRational(real(x), real(y));
            return truthValue(comparison < 0 || (comparison === 0 && compareRational(imag(x), imag(y)) < 0));
        case "CAR":
            return x.kind === PAIR ? x.car : nil;
        case "CDR":
            return x.kind === PAIR ? x.cdr : nil;
        case "CHAR-CODE":
            return integer(x.kind === CHARACTER ? x.value : 0);
        case "CHARACTERP":
            return truthValue(x.kind === CHARACTER);
        case "CODE-CHAR":
            a = natural(x);
            return character(a >= 0 && a <= 255 ? a : 0);
        case "COMPLEX":
            return complex(fixedRational(x), fixedRational(y));
        case "COMPLEX-RATIONALP":
            return truthValue(x.kind === COMPLEX);
        case "COERCE":
            return coerce(x, y);
        case "CONS":
            return cons(x, y);
        case "CONSP":
            return truthValue(x.kind === PAIR);
        case "DENOMINATOR":
            return rational(1, x.kind === RATIONAL ? x.d : one, one);
        case "EQUAL":
            return truthValue(sameDatum(x, y));
        case "IF":
            return x === nil ? args[2] : y;
        case "IMAGPART":
            return imag(x);
        case "INTEGERP":
            return truthValue(isInteger(x));
        case "INTERN-IN-PACKAGE-OF-SYMBOL":
            return x.kind === STRING && y.kind === SYMBOL ? intern(y.pkg, x.value) : nil;
        case "NUMERATOR":
            return x.kind === RATIONAL ? rational(x.sign, x.n, one) : zero;
        case "PKG-IMPORTS":
        case "PKG-WITNESS":
            if (x.kind !== STRING) {
                return fn === pkgImports ? nil : symbol(acl2, witnessName);
            }
            pkg = packages[x.value];
            need(pkg && !pkg.hidden, "Primitive requires the name of an open package");
            return fn === pkgImports ? pkg.list : symbol(x.value, witnessName);
        case "RATIONALP":
            return truthValue(x.kind === RATIONAL);
        case "REALPART":
            return real(x);
        case "STRINGP":
            return truthValue(x.kind === STRING);
        case "SYMBOL-NAME":
            return string(x.kind === SYMBOL ? x.name : "");
        case "SYMBOL-PACKAGE-NAME":
            need(x.kind !== SYMBOL || !packages[x.pkg].hidden, "Symbol belongs to a hidden package");
            return string(x.kind === SYMBOL ? x.pkg : "");
        case "SYMBOLP":
            return truthValue(x.kind === SYMBOL);
        default:
            reject("Unknown primitive");
        }
    }

    function substitution(datum) {
        var bindings = table(), pairs = items(datum), index, pair, v;
        for (index = 0; index < pairs.length; index += 1) {
            pair = fields(pairs[index], 2);
            v = pair[0];
            need(variable(v) && !bindings[v.id], "Substitution keys must be distinct variables");
            checkTerm(pair[1], null, null, false);
            bindings[v.id] = pair[1];
        }
        return pairs.length ? bindings : null;
    }

    function position(datum, last) {
        var index = natural(datum);
        need(index > 0 && index <= last, "Expected a positive index within range");
        return index - 1;
    }

    function checkBudget(size, available) {
        need(size <= available, "Proof conclusion budget exceeded");
    }

    function instantiateClause(clause, bindings, available) {
        var index, size = 0, conclusion = [];
        for (index = 0; index < clause.length; index += 1) {
            size += instantiatedSize(clause[index], bindings);
            checkBudget(size, available);
        }
        for (index = 0; index < clause.length; index += 1) {
            conclusion.push(applyBindings(clause[index], bindings));
        }
        return conclusion;
    }

    function substituteAt(first, clause, data, available) {
        need(first.length && isCall(first[0], equal, 2), "First premise must start with an equality");
        var left = first[0].cdr.car, right = first[0].cdr.cdr.car;
        var literal = position(data[2], clause.length);
        var term = clause[literal], path = [], preceding = [];
        var args, index, argument, start, frame, tail;
        for (index = 3; index < data.length; index += 1) {
            need(term.kind === PAIR && term.car !== quote, "A place can enter only arguments");
            argument = position(data[index], term.length - 1);
            args = term.cdr;
            start = preceding.length;
            while (argument > 0) {
                preceding.push(args.car);
                args = args.cdr;
                argument -= 1;
            }
            path.push({head: term.car, rest: args.cdr, start: start, end: preceding.length});
            term = args.car;
        }
        need(sameDatum(term, left), "Term at the place differs from the left side");
        var rest = first.slice(1);
        checkBudget(clauseSize(clause) - term.size + right.size + clauseSize(rest), available);
        term = right;
        while (path.length) {
            frame = path.pop();
            tail = cons(term, frame.rest);
            for (index = frame.end - 1; index >= frame.start; index -= 1) {
                tail = cons(preceding[index], tail);
            }
            term = cons(frame.head, tail);
        }
        var result = clause.slice();
        result[literal] = term;
        return result.concat(rest);
    }

    function induction(first, second, phi, measure, substitutions, available) {
        var index, bindings, smaller, instance, hypothesis, expectedSize;
        checkTerm(phi, null, null, false);
        checkTerm(measure, null, null, false);
        checkBudget(phi.size, available);
        need(first.length === 1 && isCall(first[0], ord, 1) && sameDatum(first[0].cdr.car, measure),
            "First induction premise must establish the measure is an ordinal");
        need(second.length === substitutions.length + 1 &&
            sameDatum(second[substitutions.length], phi), "Wrong induction premise");
        for (index = 0; index < substitutions.length; index += 1) {
            bindings = substitution(substitutions[index]);
            // A unary, ternary and binary call add 4, 6 and 5 nodes.
            expectedSize = 15 + instantiatedSize(measure, bindings) + measure.size +
                instantiatedSize(phi, bindings) + quotedTrue.size;
            need(expectedSize === second[index].size, "Wrong induction hypothesis");
            smaller = applyBindings(measure, bindings);
            instance = applyBindings(phi, bindings);
            hypothesis = call(not, [call(ifSymbol, [call(lessOrd, [smaller, measure]),
                instance, quotedTrue])]);
            need(sameDatum(second[index], hypothesis), "Wrong induction hypothesis");
        }
        return [phi];
    }

    function step(line, previous, available) {
        var data = line.data, p, q, index, j, term, fn, args, found;
        var bindings, body, value, result;
        switch (line.word) {
        case "fact":
            exactData(line, 1);
            term = data[0];
            need(term.kind === STRING || term.kind === SYMBOL, "Fact name must be a symbol or a string");
            p = term.kind === STRING ? stringFacts[term.value] : facts[term.id];
            need(p, "Fact is not in use");
            return p;
        case "instantiate":
            exactData(line, 2);
            p = previous[position(data[0], previous.length)];
            return instantiateClause(p, substitution(data[1]), available);
        case "subsume":
            need(data.length, "Expected a premise");
            p = previous[position(data[0], previous.length)];
            q = data.slice(1);
            for (index = 0; index < q.length; index += 1) {
                checkTerm(q[index], null, null, false);
            }
            for (index = 0; index < p.length; index += 1) {
                if (isQuote(p[index], nil)) {
                    continue;
                }
                found = false;
                for (j = 0; j < q.length && !found; j += 1) {
                    found = sameDatum(p[index], q[j]);
                }
                need(found, "A premise literal is missing from the conclusion");
            }
            return q;
        case "cut":
            exactData(line, 2);
            p = previous[position(data[0], previous.length)];
            q = previous[position(data[1], previous.length)];
            need(p.length && q.length && isCall(q[0], not, 1) && sameDatum(p[0], q[0].cdr.car),
                "First literals must be a term and its negation, in that order");
            checkBudget(clauseSize(p) - p[0].size + clauseSize(q) - q[0].size, available);
            return p.slice(1).concat(q.slice(1));
        case "substitute":
            need(data.length >= 3, "Expected two premises and a place");
            p = previous[position(data[0], previous.length)];
            q = previous[position(data[1], previous.length)];
            return substituteAt(p, q, data, available);
        case "beta":
            exactData(line, 1);
            term = data[0];
            checkTerm(term, null, null, false);
            need(term.kind === PAIR && term.car.kind === PAIR, "Expected a lambda application");
            bindings = bind(items(term.car.cdr.car), items(term.cdr));
            body = term.car.cdr.cdr.car;
            checkBudget(5 + term.size + instantiatedSize(body, bindings), available);
            return [call(equal, [term, applyBindings(body, bindings)])];
        case "compute":
            exactData(line, 1);
            term = data[0];
            checkTerm(term, null, null, false);
            need(term.kind === PAIR && term.car.kind === SYMBOL && primitives[term.car.id],
                "Expected a primitive call");
            fn = term.car;
            args = items(term.cdr);
            for (index = 0; index < args.length; index += 1) {
                need(isCall(args[index], quote, 1), "Expected a constant argument");
                args[index] = args[index].cdr.car;
            }
            // These are the only primitives that allocate new conses.
            if (fn.name === "CONS") {
                checkBudget(10 + term.size + args[0].size + args[1].size, available);
            }
            if (fn.name === "COERCE" && args[0].kind === STRING && args[1] === listSymbol) {
                checkBudget(10 + term.size + 2 * args[0].value.length, available);
            }
            value = primitive(fn, args);
            checkBudget(9 + term.size + value.size, available);
            result = call(equal, [term, quoted(value)]);
            return [result];
        case "induct":
            exactData(line, 5);
            p = previous[position(data[0], previous.length)];
            q = previous[position(data[1], previous.length)];
            return induction(p, q, data[2], data[3], items(data[4]), available);
        default:
            reject("Word is not a proof step");
        }
    }

    function prove(readProofLine, goal) {
        var previous = [], available = limit, line, conclusion, size;
        while (true) {
            line = readProofLine("Proof ended before its qed");
            if (line.word === "qed") {
                exactData(line, 0);
                need(previous.length && sameClause(previous[previous.length - 1], goal),
                    "Proof does not end with the required clause");
                return;
            }
            conclusion = step(line, previous, available);
            size = clauseSize(conclusion);
            checkBudget(size, available);
            available -= size;
            previous.push(conclusion);
        }
    }

    function bindInstances(formals, actuals, bindings) {
        var index, mapped = table();
        for (index = 0; index < formals.length; index += 1) {
            mapped[formals[index].id] = boundedInstance(actuals[index], bindings);
        }
        return mapped;
    }

    function callObligations(definition, measures, record) {
        var tasks, index, owner, term, walk, rulers, bindings;
        var actuals, fn, formals, test, next, size, literal, cursor;
        var byFunction = table();
        for (index = 0; index < definition.known.length; index += 1) {
            byFunction[definition.known[index].id] = index;
        }
        for (owner = 0; owner < definition.definitions.length; owner += 1) {
            tasks = [definition.definitions[owner].body, null, null, true];
            while (tasks.length) {
                walk = tasks.pop();
                bindings = tasks.pop();
                rulers = tasks.pop();
                term = tasks.pop();
                if (term.kind === SYMBOL || term.car === quote) {
                    continue;
                }
                fn = term.car;
                actuals = items(term.cdr);
                if (fn.kind === PAIR) {
                    formals = items(fn.cdr.car);
                    next = bindInstances(formals, actuals, bindings);
                    tasks.push(fn.cdr.cdr.car, rulers, next, walk);
                    walk = walk && (definition.allRulers || definition.extenders[lambdas.id]);
                } else if (isMbe(term)) {
                    tasks.push(actuals[2], rulers, bindings, walk);
                    continue;
                } else if (walk && fn === ifSymbol) {
                    test = boundedInstance(actuals[0], bindings);
                    size = rulers ? rulers.size : 0;
                    next = {term: test, prior: rulers, positive: false, size: Math.min(over, size + test.size)};
                    tasks.push(actuals[2], next, bindings, true);
                    next = {term: test, prior: rulers, positive: true, size: Math.min(over, size + test.size + 4)};
                    tasks.push(actuals[1], next, bindings, true);
                    tasks.push(actuals[0], rulers, bindings, definition.allRulers || definition.extenders[fn.id]);
                    continue;
                } else {
                    index = byFunction[fn.id];
                    if (index !== undefined) {
                        formals = definition.definitions[index].formals.items;
                        next = bindInstances(formals, actuals, bindings);
                        var smaller = boundedInstance(measures[index], next);
                        size = (rulers ? rulers.size : 0) + 5 + smaller.size + measures[owner].size;
                        need(size <= limit, "Termination obligation budget exceeded");
                        var clause = [];
                        for (cursor = rulers; cursor; cursor = cursor.prior) {
                            literal = cursor.positive ? call(not, [cursor.term]) : cursor.term;
                            clause.push(literal);
                        }
                        clause.reverse();
                        clause.push(call(lessOrd, [smaller, measures[owner]]));
                        record(clause, size);
                    }
                    walk = walk && (definition.allRulers || definition.extenders[fn.id]);
                }
                for (index = actuals.length - 1; index >= 0; index -= 1) {
                    tasks.push(actuals[index], rulers, bindings, walk);
                }
            }
        }
    }

    function measures(definition, terms, readProofLine) {
        var clauses = [], bySize = table(), total = 0, index;
        for (index = 0; index < terms.length; index += 1) {
            checkTerm(terms[index], definition.definitions[index].formals.scope, null, false);
            need(terms[index].size + 4 <= limit, "Termination obligation budget exceeded");
            record([call(ord, [terms[index]])], terms[index].size + 4);
        }
        callObligations(definition, terms, record);
        activate(definition);
        for (index = 0; index < clauses.length; index += 1) {
            prove(readProofLine, clauses[index]);
        }

        function record(clause, size) {
            var key = size + "," + clause.length, bucket = bySize[key], j;
            if (bucket) {
                for (j = 0; j < bucket.length; j += 1) {
                    if (sameClause(clause, bucket[j])) {
                        return;
                    }
                }
            } else {
                bucket = [];
                bySize[key] = bucket;
            }
            total += size;
            need(total <= limit, "Termination obligation budget exceeded");
            clauses.push(clause);
            bucket.push(clause);
        }
    }

    function witness(definition, witnesses, readProofLine) {
        var renames = table(), index, fn, target, fact;
        for (index = 0; index < witnesses.length; index += 1) {
            fn = witnesses[index];
            target = definition.known[index];
            need(fn.kind === SYMBOL && sameArity(functions[fn.id], definition.pending[target.id]),
                "Witness must be a function in use with the same arity");
            renames[target.id] = fn;
        }
        for (index = 0; index < definition.facts.length; index += 1) {
            fact = definition.facts[index][1][0];
            prove(readProofLine, [rewrite(fact, null, renames, false)]);
        }
    }

    function finishEntry(definition, line, readProofLine) {
        var data = line.data;
        need((line.word === definition.entry || line.word === "skip") && data[0] === definition.head,
            "Expected " + definition.entry + " or skip for the pending statement");
        if (line.word === "skip") {
            exactData(line, 1);
            skipped += 1;
        } else if (line.word === "theorem") {
            exactData(line, 1);
            prove(readProofLine, definition.facts[0][1]);
        } else {
            exactData(line, definition.known.length + 1);
            if (line.word === "measure") {
                measures(definition, data.slice(1), readProofLine);
            } else {
                witness(definition, data.slice(1), readProofLine);
            }
        }
    }

    function localDefinition(line, readProofLine) {
        var definition = prepareDefine(line.data, false), head;
        if (definition.entry) {
            head = readProofLine("Recursive proof definition needs a measure or skip");
            finishEntry(definition, head, readProofLine);
        }
        establish(definition);
    }

    function lemma(line, readProofLine) {
        need(line.data.length >= 2, "Expected a lemma name and one or more literals");
        var name = line.data[0], literals = line.data.slice(1), index;
        freshName(name, false, false);
        for (index = 0; index < literals.length; index += 1) {
            checkTerm(literals[index], null, null, false);
        }
        prove(readProofLine, literals);
        facts[name.id] = literals;
    }

    function checkStatementEntry(definition, proofInput) {
        var statementPlace = place, head;
        while (true) {
            head = readProofLine("Missing entry for a statement with obligations");
            if (head.word === "define") {
                localDefinition(head, readProofLine);
            } else if (head.word === "lemma") {
                lemma(head, readProofLine);
            } else {
                finishEntry(definition, head, readProofLine);
                return;
            }
        }

        function readProofLine(message) {
            place = statementPlace;
            var line = nextLine(proofInput);
            need(line, message);
            return line;
        }
    }

    try {
        loadGround(input("ground", ground));
        var libraryInput = input("library", library);
        var statementInput = input("statements", statements);
        var proofInput = input("proofs", proofs);
        var line;
        while ((line = nextLine(libraryInput, seen))) {
            admit(line, true);
        }
        while ((line = nextLine(statementInput, seen))) {
            admit(line, false, proofInput);
        }
        locate(proofInput, proofInput.number + 1);
        need(proofInput.start === proofs.length, "Proof input remains after the last statement");
        if (skipped || assumed || givenDefinitions || givenFacts) {
            return "provisional skipped " + skipped + " assumed " + assumed +
                " given-definitions " + givenDefinitions + " given-facts " + givenFacts + "\n";
        }
        return "accepted\n";
    } catch (error) {
        if (error && error.rejection === reject) {
            return error.text;
        }
        throw error;
    }
}
