(function () {
    "use strict";

    var verdict = checkBoymoo.apply(null, boymooInputs);
    if (typeof print === "function") {
        print(verdict.slice(0, -1));
    } else {
        process.stdout.write(verdict);
    }
}());
