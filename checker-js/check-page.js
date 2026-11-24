(function () {
    "use strict";

    var form = document.getElementById("inputs");
    var button = document.getElementById("check");
    var verdict = document.getElementById("verdict");
    var fields = ["ground", "library", "statements", "proofs", "library-proofs"];

    form.addEventListener("submit", function (event) {
        event.preventDefault();
        var inputs = [], index;
        var pending = fields.length;
        var finished = false;
        button.disabled = true;
        verdict.textContent = "Reading files…";

        function finish(message) {
            if (finished) {
                return;
            }
            finished = true;
            verdict.textContent = message;
            button.disabled = false;
        }

        function ready(position, text) {
            if (finished) {
                return;
            }
            inputs[position] = text;
            pending -= 1;
            if (pending === 0) {
                try {
                    finish(checkBoymoo.apply(null, inputs));
                } catch (error) {
                    finish(error.message);
                }
            }
        }

        function read(position, file) {
            if (!file) {
                ready(position, "");
                return;
            }
            var reader = new FileReader();
            reader.onload = function () {
                var bytes = new Uint8Array(reader.result), offset, parts = [];
                for (offset = 0; offset < bytes.length; offset += 4096) {
                    parts.push(String.fromCharCode.apply(null, bytes.subarray(offset, offset + 4096)));
                }
                ready(position, parts.join(""));
            };
            reader.onerror = function () {
                finish("Could not read the " + fields[position] + " file.");
            };
            reader.readAsArrayBuffer(file);
        }

        for (index = 0; index < fields.length; index += 1) {
            read(index, document.getElementById(fields[index]).files[0]);
        }
    });
}());
