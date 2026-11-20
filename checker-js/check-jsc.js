(function (paths) {
    "use strict";

    var inputs = [], path, bytes, parts, offset;
    for (path = 0; path < 4; path += 1) {
        bytes = readFile(paths[path], "binary");
        if (!(bytes instanceof Uint8Array)) {
            bytes = new Uint8Array(bytes);
        }
        parts = [];
        for (offset = 0; offset < bytes.length; offset += 4096) {
            parts.push(String.fromCharCode.apply(null, bytes.subarray(offset, offset + 4096)));
        }
        inputs.push(parts.join(""));
    }
    var start = Date.now();
    var verdict = checkBoymoo.apply(null, inputs);
    var elapsed = Date.now() - start;
    print(verdict.slice(0, -1));
    if (paths[4] === "--timed") {
        print(elapsed);
    }
}(arguments));
