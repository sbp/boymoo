# Certify the guard proofs and audit the checks from the repository root.

set -eu

dir=build/checker/acl2
core='base read terms rules admit check'
books='guards-base guards-read guards-terms guards-admit guards-check
guards-invariants guards-reader-stack guards-admission-invariants
guards-steps guards-termination guards-admission guards-run-invariants guards-entry
guards-equations guards-counterexamples'
log=$dir/guards-tests.out

fail() {
    printf 'guard checks failed (%s)\n' "$1" >&2
    exit 1
}

case ${1-} in
    ''|--require-all) [ "$#" -le 1 ] || fail 'usage: sh checker/proofs/guards.sh [--require-all]' ;;
    *) fail 'usage: sh checker/proofs/guards.sh [--require-all]' ;;
esac

mkdir -p "$dir"
if [ ! -s build/export/ground-fns.lsp ]; then
    sh export/run.sh std/strings/pretty > "$dir/guards-bootstrap.out" 2>&1 ||
        fail "$dir/guards-bootstrap.out"
fi
sh checker/build.sh || fail 'checker/build.sh'

statements=build/checker/checker.statements
python3 -B checker/closed.py spec/ground.txt build/checker/library.statements "$statements" ||
    fail 'closure of the checker'
python3 -B - "$statements" "$dir/guards-functions.txt" "$dir/guards-ground.txt" <<'PY' || fail 'checker statements'
import hashlib
import sys

sys.path.insert(0, "checks")
from reader import Reader, write

with open(sys.argv[1], "rb") as statements:
    data = statements.read()
print("checker statements SHA-256 " + hashlib.sha256(data).hexdigest())

def definitions(text, primitives=False):
    for line in text.split(b"\n")[:-1]:
        word, fields = Reader(line).line()
        if word == b"define":
            for definition in fields[1:]:
                yield definition[0]
        elif primitives and word == b"primitive":
            yield fields[0]

with open(sys.argv[2], "w") as functions:
    for name in definitions(data):
        print(write(name).decode("ascii"), file=functions)

# The primitives and the functions of the ground theory and of the
# checker's library.
with open(sys.argv[3], "w") as allowed:
    for path in ("spec/ground.txt", "build/checker/library.statements"):
        with open(path, "rb") as text:
            for name in definitions(text.read(), primitives=True):
                print(write(name).decode("ascii"), file=allowed)
PY

for book in $books; do
    cp "checker/proofs/$book.lisp" "$dir/" || fail "$book source"
    rm -f "$dir/$book.cert"
    {
        echo '(ld "checks/version.lsp")'
        echo "(set-ld-error-action '(:exit 1) state)"
        echo '(ld "checker/package.lsp" :ld-error-action :error)'
        printf '(certify-book "%s/%s" 1 nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)\n' "$dir" "$book"
        echo '(good-bye)'
    } | timeout 300 acl2 > "$dir/$book.out" 2>&1 || fail "$dir/$book.out"
    [ -f "$dir/$book.cert" ] || fail "$dir/$book.out"
    seconds=$(awk '/^Time:/ { seconds = $2 } END { print seconds }' "$dir/$book.out")
    printf '%s ok (%s s)\n' "$book" "$seconds"
done

functions=$(cat "$dir/guards-functions.txt")
ground=$(cat "$dir/guards-ground.txt")

cases=build/checker/guard-cases
mkdir -p "$cases"
: > "$cases/empty"
cat > "$cases/car.statements" <<'EOF'
(theorem COMMON-LISP::GUARD-SAMPLE (COMMON-LISP::EQUAL (COMMON-LISP::CAR (COMMON-LISP::QUOTE 42)) (COMMON-LISP::QUOTE COMMON-LISP::NIL)))
EOF
cat > "$cases/car.proofs" <<'EOF'
(theorem COMMON-LISP::GUARD-SAMPLE)
(compute (COMMON-LISP::CAR (COMMON-LISP::QUOTE 42)))
(qed)
EOF
printf '%s\n' '(define COMMON-LISP::NIL 7)' > "$cases/malformed.statements"

{
    echo '(ld "checks/version.lsp")'
    echo "(set-ld-error-action '(:exit 1) state)"
    echo "(set-inhibit-output-lst '(proof-tree prove event summary history))"
    printf '(include-book "%s/check" :uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)\n' "$dir"
    cat <<'LISP'
(defun check-guard-certificate (file state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (erp data state)
    (cert-annotations-and-checksum-from-cert-file file state)
    (if (and (not erp)
             (equal (car data) '((:skipped-proofsp) (:axiomsp) (:ttags))))
        (value t)
      (er soft 'check-guard-certificate "Unexpected annotations in ~x0." file))))

(defun audit-guard-functions (names allowed wrld)
  (declare (xargs :mode :program))
  (if (endp names)
      nil
    (let* ((fn (car names))
           (class (getpropc fn 'symbol-class nil wrld))
           (extra (set-difference-eq (all-fnnames (guard fn nil wrld)) allowed)))
      (if (and (member-eq class '(:ideal :common-lisp-compliant)) (not extra))
          (prog2$ (if (eq class :ideal)
                      (cw "~%guard-unverified ~s0~%" (symbol-name fn))
                    (cw "~%guard-verified ~s0~%" (symbol-name fn)))
                  (audit-guard-functions (cdr names) allowed wrld))
        (cons (list fn class extra)
              (audit-guard-functions (cdr names) allowed wrld))))))

(defun checker-functions-in-world (world acc)
  (declare (xargs :mode :program))
  (cond ((endp world) acc)
        ((and (eq (cadar world) 'formals)
              (equal (symbol-package-name (caar world)) "BOYMOO"))
         (checker-functions-in-world (cdr world) (add-to-set-eq (caar world) acc)))
        (t (checker-functions-in-world (cdr world) acc))))

(assign checker-functions (checker-functions-in-world (w state) nil))
LISP
    printf '(include-book "%s/guards-counterexamples" :uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)\n' "$dir"
    echo '(er-progn'
    for book in $core $books; do
        printf ' (check-guard-certificate "%s/%s.lisp" state)\n' "$dir" "$book"
    done
    echo ' (value (cw "~%guard-certificates ok~%")))'
    printf "(let* ((core '(%s))\n" "$functions"
    printf "        (allowed (append core '(%s)))\n" "$ground"
    cat <<'LISP'
       (wrld (w state))
       (actual (@ checker-functions))
       (omitted (set-difference-eq actual core))
       (unexpected (set-difference-eq core actual)))
  (if (or omitted unexpected)
      (er soft 'audit-guard-functions "Missing functions ~x0. Unexpected functions ~x1."
          omitted unexpected)
    (let ((bad (audit-guard-functions actual allowed wrld)))
      (if bad
          (er soft 'audit-guard-functions "Invalid functions or calls ~x0." bad)
        (value (cw "~%guard-core ok~%"))))))

(let ((wrld (w state)))
  (if (and (equal (untranslate (guard 'boymoo::check nil wrld) nil wrld)
                  '(and (stringp boymoo::ground) (stringp boymoo::library)
                        (stringp boymoo::statements) (stringp boymoo::proofs)))
           (equal (untranslate (guard 'boymoo::check-four nil wrld) nil wrld)
                  '(and (stringp boymoo::ground) (stringp boymoo::library)
                        (stringp boymoo::statements) (stringp boymoo::proofs)
                        (stringp boymoo::library-proofs))))
      (value (cw "~%guard-check-entry ok~%"))
    (er soft 'check "The checker entry guards must require strings.")))
LISP
    echo '(ld "checker/acl2-run.lsp" :ld-error-action :error)'
    echo '(set-guard-checking t)'
    cat <<'LISP'
(defun audit-ground-world (state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (text state)
    (bm-file-string "spec/ground.txt" state)
    (if (and (stringp text)
             (boymoo::guard-world-p
              (boymoo::load-ground (boymoo::lines-of text) (boymoo::initial-world))))
        (value (cw "~%guard-ground-world ok~%"))
      (er soft 'audit-ground-world "The ground theory fails the world invariant."))))
(audit-ground-world state)

(if (equal (boymoo::check "(package 42 COMMON-LISP::NIL)
" "" "" "")
           '("the ground theory could not be read" ""))
    (value (cw "~%guard-ground-shape ok~%"))
  (er soft 'audit-ground-world "A ground package with a numeric name must fail."))
LISP
    printf '(run-case "compute-car" "%s/empty" "%s/car.statements" "%s/car.proofs" state)\n' "$cases" "$cases" "$cases"
    printf '(run-case "malformed-definition" "%s/empty" "%s/malformed.statements" "%s/empty" state)\n' "$cases" "$cases" "$cases"
    library=checker/cases/accept-library-proofs-common-lisp
    printf '(run-case-four "proved-library" "%s/library.txt" "%s/statements.txt" "%s/proofs.txt" "%s/library-proofs.txt" state)\n' \
        "$library" "$library" "$library" "$library"
    echo '(good-bye)'
} | timeout 300 acl2 > "$log" 2>&1 || fail "$log"

grep -Fxq 'guard-certificates ok' "$log" || fail "$log"
grep -Fxq 'guard-core ok' "$log" || fail "$log"
grep -Fxq 'guard-check-entry ok' "$log" || fail "$log"
grep -Fxq 'guard-ground-world ok' "$log" || fail "$log"
grep -Fxq 'guard-ground-shape ok' "$log" || fail "$log"
grep -Fxq "$(printf 'verdict compute-car\taccepted')" "$log" || fail "$log"
grep -Fxq "$(printf 'verdict malformed-definition\trejected statements 1')" "$log" || fail "$log"
grep -Fxq "$(printf 'verdict proved-library\taccepted')" "$log" || fail "$log"
echo 'certificate annotations, ACL2 Core guards, entry guard, ground world and counterexamples ok'

sed -n 's/^guard-unverified //p' "$log" |
    tr '[:upper:]' '[:lower:]' | LC_ALL=C sort > "$dir/guards-unverified.txt"
sed -n '/^## Unverified functions$/,$s/^| `\([a-z0-9-]*\)` |.*/\1/p' checker/proofs/guards.md |
    LC_ALL=C sort > "$dir/guards-expected.txt"
if ! cmp -s "$dir/guards-expected.txt" "$dir/guards-unverified.txt"; then
    diff "$dir/guards-expected.txt" "$dir/guards-unverified.txt" || :
    fail 'guard status differs from the documented obligations'
fi

missing=$(wc -l < "$dir/guards-unverified.txt")
total=$(printf '%s\n' "$functions" | awk 'END {print NR}')
printf '%d of %d checker functions have verified guards\n' "$((total - missing))" "$total"
if [ "$missing" -ne 0 ]; then
    cat "$dir/guards-unverified.txt"
    [ "${1-}" != --require-all ] || fail 'checker functions have unverified guards'
fi
echo 'all checker guard checks passed'
