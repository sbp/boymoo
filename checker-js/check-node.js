"use strict";

var fs = require("fs");
var vm = require("vm");

var check = vm.runInThisContext(fs.readFileSync("checker-js/check.js", "ascii") + "\ncheckBoymoo;");
var paths = ["spec/ground.txt"].concat(process.argv.slice(2));
var inputs = paths.map(function (path) {
    return fs.readFileSync(path, "latin1");
});
process.stdout.write(check.apply(null, inputs));
