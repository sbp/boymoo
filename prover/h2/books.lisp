(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro h2-books-out-of-fuel-p (n)
  `(not (o< (nfix (1- ,n)) (nfix ,n))))

(defconst *h2-books-translation*
  '("SYNP" "DOUBLE-REWRITE" "HIDE" "MUST-BE-EQUAL" "THE-CHECK" "CONS-WITH-HINT"))

(defconst *h2-books-arithmetic-defs*
  '("NFIX" "IFIX" "NATP" "POSP" "ZP"))

(defconst *h2-books-boolean-facts*
  (list (cons *proof-consp* "booleanp-consp")
        (cons *proof-integerp* "booleanp-integerp")
        (cons (proof-cl "RATIONALP") "booleanp-rationalp")
        (cons (proof-sym "COMPLEX-RATIONALP" "ACL2") "booleanp-complex-rationalp")
        (cons (proof-sym "ACL2-NUMBERP" "ACL2") "booleanp-acl2-numberp")
        (cons (proof-cl "STRINGP") "booleanp-stringp")
        (cons (proof-cl "SYMBOLP") "booleanp-symbolp")
        (cons *proof-less* "booleanp-<")))


(defun h2-books-ground-imports (names)
  (if (endp names)
      nil
    (cons (proof-cl (car names)) (h2-books-ground-imports (cdr names)))))

; The packages declared in the ground theory, in declaration order.
(defconst *h2-books-ground-packages*
  (list (cons "COMMON-LISP" '(nil nil))
        (cons "ACL2-INPUT-CHANNEL" '(nil nil))
        (cons "ACL2-OUTPUT-CHANNEL" '(nil nil))
        (list "ACL2"
              (h2-books-ground-imports
               '(
     "&ALLOW-OTHER-KEYS" "*PRINT-MISER-WIDTH*" "&AUX" "*PRINT-PPRINT-DISPATCH*" "&BODY"
     "*PRINT-PRETTY*" "&ENVIRONMENT" "*PRINT-RADIX*" "&KEY" "*PRINT-READABLY*" "&OPTIONAL"
     "*PRINT-RIGHT-MARGIN*" "&REST" "*QUERY-IO*" "&WHOLE" "*RANDOM-STATE*" "*" "*READ-BASE*"
     "**" "*READ-DEFAULT-FLOAT-FORMAT*" "***" "*READ-EVAL*" "*BREAK-ON-SIGNALS*"
     "*READ-SUPPRESS*" "*COMPILE-FILE-PATHNAME*" "*READTABLE*" "*COMPILE-FILE-TRUENAME*"
     "*STANDARD-INPUT*" "*COMPILE-PRINT*" "*STANDARD-OUTPUT*" "*COMPILE-VERBOSE*"
     "*TERMINAL-IO*" "*DEBUG-IO*" "*TRACE-OUTPUT*" "*DEBUGGER-HOOK*" "+"
     "*DEFAULT-PATHNAME-DEFAULTS*" "++" "*ERROR-OUTPUT*" "+++" "*FEATURES*" "-"
     "*GENSYM-COUNTER*" "/" "*LOAD-PATHNAME*" "//" "*LOAD-PRINT*" "///" "*LOAD-TRUENAME*"
     "/=" "*LOAD-VERBOSE*" "1+" "*MACROEXPAND-HOOK*" "1-" "*MODULES*" "<" "*PACKAGE*" "<="
     "*PRINT-ARRAY*" "=" "*PRINT-BASE*" ">" "*PRINT-CASE*" ">=" "*PRINT-CIRCLE*" "ABORT"
     "*PRINT-ESCAPE*" "ABS" "*PRINT-GENSYM*" "ACONS" "*PRINT-LENGTH*" "ACOS" "*PRINT-LEVEL*"
     "ACOSH" "*PRINT-LINES*" "ADD-METHOD" "ADJOIN" "ATOM" "BOUNDP" "ADJUST-ARRAY"
     "BASE-CHAR" "BREAK" "ADJUSTABLE-ARRAY-P" "BASE-STRING" "BROADCAST-STREAM"
     "ALLOCATE-INSTANCE" "BIGNUM" "BROADCAST-STREAM-STREAMS" "ALPHA-CHAR-P" "BIT"
     "BUILT-IN-CLASS" "ALPHANUMERICP" "BIT-AND" "BUTLAST" "AND" "BIT-ANDC1" "BYTE" "APPEND"
     "BIT-ANDC2" "BYTE-POSITION" "APPLY" "BIT-EQV" "BYTE-SIZE" "APROPOS" "BIT-IOR" "CAAAAR"
     "APROPOS-LIST" "BIT-NAND" "CAAADR" "AREF" "BIT-NOR" "CAAAR" "ARITHMETIC-ERROR"
     "BIT-NOT" "CAADAR" "ARITHMETIC-ERROR-OPERANDS" "BIT-ORC1" "CAADDR"
     "ARITHMETIC-ERROR-OPERATION" "BIT-ORC2" "CAADR" "ARRAY" "BIT-VECTOR" "CAAR"
     "ARRAY-DIMENSION" "BIT-VECTOR-P" "CADAAR" "ARRAY-DIMENSION-LIMIT" "BIT-XOR" "CADADR"
     "ARRAY-DIMENSIONS" "BLOCK" "CADAR" "ARRAY-DISPLACEMENT" "BOOLE" "CADDAR"
     "ARRAY-ELEMENT-TYPE" "BOOLE-1" "CADDDR" "ARRAY-HAS-FILL-POINTER-P" "BOOLE-2" "CADDR"
     "ARRAY-IN-BOUNDS-P" "BOOLE-AND" "CADR" "ARRAY-RANK" "BOOLE-ANDC1"
     "CALL-ARGUMENTS-LIMIT" "ARRAY-RANK-LIMIT" "BOOLE-ANDC2" "CALL-METHOD"
     "ARRAY-ROW-MAJOR-INDEX" "BOOLE-C1" "CALL-NEXT-METHOD" "ARRAY-TOTAL-SIZE" "BOOLE-C2"
     "CAR" "ARRAY-TOTAL-SIZE-LIMIT" "BOOLE-CLR" "CASE" "ARRAYP" "BOOLE-EQV" "CATCH" "ASH"
     "BOOLE-IOR" "CCASE" "ASIN" "BOOLE-NAND" "CDAAAR" "ASINH" "BOOLE-NOR" "CDAADR" "ASSERT"
     "BOOLE-ORC1" "CDAAR" "ASSOC" "BOOLE-ORC2" "CDADAR" "ASSOC-IF" "BOOLE-SET" "CDADDR"
     "ASSOC-IF-NOT" "BOOLE-XOR" "CDADR" "ATAN" "BOOLEAN" "CDAR" "ATANH" "BOTH-CASE-P"
     "CDDAAR" "CDDADR" "CLEAR-INPUT" "COPY-TREE" "CDDAR" "CLEAR-OUTPUT" "COS" "CDDDAR"
     "CLOSE" "COSH" "CDDDDR" "CLRHASH" "COUNT" "CDDDR" "CODE-CHAR" "COUNT-IF" "CDDR"
     "COERCE" "COUNT-IF-NOT" "CDR" "COMPILATION-SPEED" "CTYPECASE" "CEILING" "COMPILE"
     "DEBUG" "CELL-ERROR" "COMPILE-FILE" "DECF" "CELL-ERROR-NAME" "COMPILE-FILE-PATHNAME"
     "DECLAIM" "CERROR" "COMPILED-FUNCTION" "DECLARATION" "CHANGE-CLASS"
     "COMPILED-FUNCTION-P" "DECLARE" "CHAR" "COMPILER-MACRO" "DECODE-FLOAT" "CHAR-CODE"
     "COMPILER-MACRO-FUNCTION" "DECODE-UNIVERSAL-TIME" "CHAR-CODE-LIMIT" "COMPLEMENT"
     "DEFCLASS" "CHAR-DOWNCASE" "COMPLEX" "DEFCONSTANT" "CHAR-EQUAL" "COMPLEXP" "DEFGENERIC"
     "CHAR-GREATERP" "COMPUTE-APPLICABLE-METHODS" "DEFINE-COMPILER-MACRO" "CHAR-INT"
     "COMPUTE-RESTARTS" "DEFINE-CONDITION" "CHAR-LESSP" "CONCATENATE"
     "DEFINE-METHOD-COMBINATION" "CHAR-NAME" "CONCATENATED-STREAM" "DEFINE-MODIFY-MACRO"
     "CHAR-NOT-EQUAL" "CONCATENATED-STREAM-STREAMS" "DEFINE-SETF-EXPANDER"
     "CHAR-NOT-GREATERP" "COND" "DEFINE-SYMBOL-MACRO" "CHAR-NOT-LESSP" "CONDITION"
     "DEFMACRO" "CHAR-UPCASE" "CONJUGATE" "DEFMETHOD" "CHAR/=" "CONS" "DEFPACKAGE" "CHAR<"
     "CONSP" "DEFPARAMETER" "CHAR<=" "CONSTANTLY" "DEFSETF" "CHAR=" "CONSTANTP" "DEFSTRUCT"
     "CHAR>" "CONTINUE" "DEFTYPE" "CHAR>=" "CONTROL-ERROR" "DEFUN" "CHARACTER" "COPY-ALIST"
     "DEFVAR" "CHARACTERP" "COPY-LIST" "DELETE" "CHECK-TYPE" "COPY-PPRINT-DISPATCH"
     "DELETE-DUPLICATES" "CIS" "COPY-READTABLE" "DELETE-FILE" "CLASS" "COPY-SEQ" "DELETE-IF"
     "CLASS-NAME" "COPY-STRUCTURE" "DELETE-IF-NOT" "CLASS-OF" "COPY-SYMBOL" "DELETE-PACKAGE"
     "DENOMINATOR" "EQ" "DEPOSIT-FIELD" "EQL" "DESCRIBE" "EQUAL" "DESCRIBE-OBJECT" "EQUALP"
     "DESTRUCTURING-BIND" "ERROR" "DIGIT-CHAR" "ETYPECASE" "DIGIT-CHAR-P" "EVAL" "DIRECTORY"
     "EVAL-WHEN" "DIRECTORY-NAMESTRING" "EVENP" "DISASSEMBLE" "EVERY" "DIVISION-BY-ZERO"
     "EXP" "DO" "EXPORT" "DO*" "EXPT" "DO-ALL-SYMBOLS" "EXTENDED-CHAR" "DO-EXTERNAL-SYMBOLS"
     "FBOUNDP" "DO-SYMBOLS" "FCEILING" "DOCUMENTATION" "FDEFINITION" "DOLIST" "FFLOOR"
     "DOTIMES" "FIFTH" "DOUBLE-FLOAT" "FILE-AUTHOR" "DOUBLE-FLOAT-EPSILON" "FILE-ERROR"
     "DOUBLE-FLOAT-NEGATIVE-EPSILON" "FILE-ERROR-PATHNAME" "DPB" "FILE-LENGTH" "DRIBBLE"
     "FILE-NAMESTRING" "DYNAMIC-EXTENT" "FILE-POSITION" "ECASE" "FILE-STREAM" "ECHO-STREAM"
     "FILE-STRING-LENGTH" "ECHO-STREAM-INPUT-STREAM" "FILE-WRITE-DATE"
     "ECHO-STREAM-OUTPUT-STREAM" "FILL" "ED" "FILL-POINTER" "EIGHTH" "FIND" "ELT"
     "FIND-ALL-SYMBOLS" "ENCODE-UNIVERSAL-TIME" "FIND-CLASS" "END-OF-FILE" "FIND-IF" "ENDP"
     "FIND-IF-NOT" "ENOUGH-NAMESTRING" "FIND-METHOD" "ENSURE-DIRECTORIES-EXIST"
     "FIND-PACKAGE" "ENSURE-GENERIC-FUNCTION" "FIND-RESTART" "FIND-SYMBOL"
     "GET-INTERNAL-RUN-TIME" "FINISH-OUTPUT" "GET-MACRO-CHARACTER" "FIRST"
     "GET-OUTPUT-STREAM-STRING" "FIXNUM" "GET-PROPERTIES" "FLET" "GET-SETF-EXPANSION"
     "FLOAT" "GET-UNIVERSAL-TIME" "FLOAT-DIGITS" "GETF" "FLOAT-PRECISION" "GETHASH"
     "FLOAT-RADIX" "GO" "FLOAT-SIGN" "GRAPHIC-CHAR-P" "FLOATING-POINT-INEXACT"
     "HANDLER-BIND" "FLOATING-POINT-INVALID-OPERATION" "HANDLER-CASE"
     "FLOATING-POINT-OVERFLOW" "HASH-TABLE" "FLOATING-POINT-UNDERFLOW" "HASH-TABLE-COUNT"
     "FLOATP" "HASH-TABLE-P" "FLOOR" "HASH-TABLE-REHASH-SIZE" "FMAKUNBOUND"
     "HASH-TABLE-REHASH-THRESHOLD" "FORCE-OUTPUT" "HASH-TABLE-SIZE" "FORMAT"
     "HASH-TABLE-TEST" "FORMATTER" "HOST-NAMESTRING" "FOURTH" "IDENTITY" "FRESH-LINE" "IF"
     "FROUND" "IGNORABLE" "FTRUNCATE" "IGNORE" "FTYPE" "IGNORE-ERRORS" "FUNCALL" "IMAGPART"
     "FUNCTION" "IMPORT" "FUNCTION-KEYWORDS" "IN-PACKAGE" "FUNCTION-LAMBDA-EXPRESSION"
     "INCF" "FUNCTIONP" "INITIALIZE-INSTANCE" "GCD" "INLINE" "GENERIC-FUNCTION"
     "INPUT-STREAM-P" "GENSYM" "INSPECT" "GENTEMP" "INTEGER" "GET" "INTEGER-DECODE-FLOAT"
     "GET-DECODED-TIME" "INTEGER-LENGTH" "GET-DISPATCH-MACRO-CHARACTER" "INTEGERP"
     "GET-INTERNAL-REAL-TIME" "INTERACTIVE-STREAM-P" "INTERN" "LISP-IMPLEMENTATION-TYPE"
     "INTERNAL-TIME-UNITS-PER-SECOND" "LISP-IMPLEMENTATION-VERSION" "INTERSECTION" "LIST"
     "INVALID-METHOD-ERROR" "LIST*" "INVOKE-DEBUGGER" "LIST-ALL-PACKAGES" "INVOKE-RESTART"
     "LIST-LENGTH" "INVOKE-RESTART-INTERACTIVELY" "LISTEN" "ISQRT" "LISTP" "KEYWORD" "LOAD"
     "KEYWORDP" "LOAD-LOGICAL-PATHNAME-TRANSLATIONS" "LABELS" "LOAD-TIME-VALUE" "LAMBDA"
     "LOCALLY" "LAMBDA-LIST-KEYWORDS" "LOG" "LAMBDA-PARAMETERS-LIMIT" "LOGAND" "LAST"
     "LOGANDC1" "LCM" "LOGANDC2" "LDB" "LOGBITP" "LDB-TEST" "LOGCOUNT" "LDIFF" "LOGEQV"
     "LEAST-NEGATIVE-DOUBLE-FLOAT" "LOGICAL-PATHNAME" "LEAST-NEGATIVE-LONG-FLOAT"
     "LOGICAL-PATHNAME-TRANSLATIONS" "LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT" "LOGIOR"
     "LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT" "LOGNAND"
     "LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT" "LOGNOR"
     "LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT" "LOGNOT" "LEAST-NEGATIVE-SHORT-FLOAT"
     "LOGORC1" "LEAST-NEGATIVE-SINGLE-FLOAT" "LOGORC2" "LEAST-POSITIVE-DOUBLE-FLOAT"
     "LOGTEST" "LEAST-POSITIVE-LONG-FLOAT" "LOGXOR" "LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT"
     "LONG-FLOAT" "LEAST-POSITIVE-NORMALIZED-LONG-FLOAT" "LONG-FLOAT-EPSILON"
     "LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT" "LONG-FLOAT-NEGATIVE-EPSILON"
     "LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT" "LONG-SITE-NAME" "LEAST-POSITIVE-SHORT-FLOAT"
     "LOOP" "LEAST-POSITIVE-SINGLE-FLOAT" "LOOP-FINISH" "LENGTH" "LOWER-CASE-P" "LET"
     "MACHINE-INSTANCE" "LET*" "MACHINE-TYPE" "MACHINE-VERSION" "MASK-FIELD"
     "MACRO-FUNCTION" "MAX" "MACROEXPAND" "MEMBER" "MACROEXPAND-1" "MEMBER-IF" "MACROLET"
     "MEMBER-IF-NOT" "MAKE-ARRAY" "MERGE" "MAKE-BROADCAST-STREAM" "MERGE-PATHNAMES"
     "MAKE-CONCATENATED-STREAM" "METHOD" "MAKE-CONDITION" "METHOD-COMBINATION"
     "MAKE-DISPATCH-MACRO-CHARACTER" "METHOD-COMBINATION-ERROR" "MAKE-ECHO-STREAM"
     "METHOD-QUALIFIERS" "MAKE-HASH-TABLE" "MIN" "MAKE-INSTANCE" "MINUSP"
     "MAKE-INSTANCES-OBSOLETE" "MISMATCH" "MAKE-LIST" "MOD" "MAKE-LOAD-FORM"
     "MOST-NEGATIVE-DOUBLE-FLOAT" "MAKE-LOAD-FORM-SAVING-SLOTS" "MOST-NEGATIVE-FIXNUM"
     "MAKE-METHOD" "MOST-NEGATIVE-LONG-FLOAT" "MAKE-PACKAGE" "MOST-NEGATIVE-SHORT-FLOAT"
     "MAKE-PATHNAME" "MOST-NEGATIVE-SINGLE-FLOAT" "MAKE-RANDOM-STATE"
     "MOST-POSITIVE-DOUBLE-FLOAT" "MAKE-SEQUENCE" "MOST-POSITIVE-FIXNUM" "MAKE-STRING"
     "MOST-POSITIVE-LONG-FLOAT" "MAKE-STRING-INPUT-STREAM" "MOST-POSITIVE-SHORT-FLOAT"
     "MAKE-STRING-OUTPUT-STREAM" "MOST-POSITIVE-SINGLE-FLOAT" "MAKE-SYMBOL" "MUFFLE-WARNING"
     "MAKE-SYNONYM-STREAM" "MULTIPLE-VALUE-BIND" "MAKE-TWO-WAY-STREAM" "MULTIPLE-VALUE-CALL"
     "MAKUNBOUND" "MULTIPLE-VALUE-LIST" "MAP" "MULTIPLE-VALUE-PROG1" "MAP-INTO"
     "MULTIPLE-VALUE-SETQ" "MAPC" "MULTIPLE-VALUES-LIMIT" "MAPCAN" "NAME-CHAR" "MAPCAR"
     "NAMESTRING" "MAPCON" "NBUTLAST" "MAPHASH" "NCONC" "MAPL" "NEXT-METHOD-P" "MAPLIST"
     "NIL" "NINTERSECTION" "PACKAGE-ERROR" "NINTH" "PACKAGE-ERROR-PACKAGE"
     "NO-APPLICABLE-METHOD" "PACKAGE-NAME" "NO-NEXT-METHOD" "PACKAGE-NICKNAMES" "NOT"
     "PACKAGE-SHADOWING-SYMBOLS" "NOTANY" "PACKAGE-USE-LIST" "NOTEVERY"
     "PACKAGE-USED-BY-LIST" "NOTINLINE" "PACKAGEP" "NRECONC" "PAIRLIS" "NREVERSE"
     "PARSE-ERROR" "NSET-DIFFERENCE" "PARSE-INTEGER" "NSET-EXCLUSIVE-OR" "PARSE-NAMESTRING"
     "NSTRING-CAPITALIZE" "PATHNAME" "NSTRING-DOWNCASE" "PATHNAME-DEVICE" "NSTRING-UPCASE"
     "PATHNAME-DIRECTORY" "NSUBLIS" "PATHNAME-HOST" "NSUBST" "PATHNAME-MATCH-P" "NSUBST-IF"
     "PATHNAME-NAME" "NSUBST-IF-NOT" "PATHNAME-TYPE" "NSUBSTITUTE" "PATHNAME-VERSION"
     "NSUBSTITUTE-IF" "PATHNAMEP" "NSUBSTITUTE-IF-NOT" "PEEK-CHAR" "NTH" "PHASE" "NTH-VALUE"
     "PI" "NTHCDR" "PLUSP" "NULL" "POP" "NUMBER" "POSITION" "NUMBERP" "POSITION-IF"
     "NUMERATOR" "POSITION-IF-NOT" "NUNION" "PPRINT" "ODDP" "PPRINT-DISPATCH" "OPEN"
     "PPRINT-EXIT-IF-LIST-EXHAUSTED" "OPEN-STREAM-P" "PPRINT-FILL" "OPTIMIZE"
     "PPRINT-INDENT" "OR" "PPRINT-LINEAR" "OTHERWISE" "PPRINT-LOGICAL-BLOCK"
     "OUTPUT-STREAM-P" "PPRINT-NEWLINE" "PACKAGE" "PPRINT-POP" "PPRINT-TAB" "READ-CHAR"
     "PPRINT-TABULAR" "READ-CHAR-NO-HANG" "PRIN1" "READ-DELIMITED-LIST" "PRIN1-TO-STRING"
     "READ-FROM-STRING" "PRINC" "READ-LINE" "PRINC-TO-STRING" "READ-PRESERVING-WHITESPACE"
     "PRINT" "READ-SEQUENCE" "PRINT-NOT-READABLE" "READER-ERROR" "PRINT-NOT-READABLE-OBJECT"
     "READTABLE" "PRINT-OBJECT" "READTABLE-CASE" "PRINT-UNREADABLE-OBJECT" "READTABLEP"
     "PROBE-FILE" "REAL" "PROCLAIM" "REALP" "PROG" "REALPART" "PROG*" "REDUCE" "PROG1"
     "REINITIALIZE-INSTANCE" "PROG2" "REM" "PROGN" "REMF" "PROGRAM-ERROR" "REMHASH" "PROGV"
     "REMOVE" "PROVIDE" "REMOVE-DUPLICATES" "PSETF" "REMOVE-IF" "PSETQ" "REMOVE-IF-NOT"
     "PUSH" "REMOVE-METHOD" "PUSHNEW" "REMPROP" "QUOTE" "RENAME-FILE" "RANDOM"
     "RENAME-PACKAGE" "RANDOM-STATE" "REPLACE" "RANDOM-STATE-P" "REQUIRE" "RASSOC" "REST"
     "RASSOC-IF" "RESTART" "RASSOC-IF-NOT" "RESTART-BIND" "RATIO" "RESTART-CASE" "RATIONAL"
     "RESTART-NAME" "RATIONALIZE" "RETURN" "RATIONALP" "RETURN-FROM" "READ" "REVAPPEND"
     "READ-BYTE" "REVERSE" "ROOM" "SIMPLE-BIT-VECTOR" "ROTATEF" "SIMPLE-BIT-VECTOR-P"
     "ROUND" "SIMPLE-CONDITION" "ROW-MAJOR-AREF" "SIMPLE-CONDITION-FORMAT-ARGUMENTS"
     "RPLACA" "SIMPLE-CONDITION-FORMAT-CONTROL" "RPLACD" "SIMPLE-ERROR" "SAFETY"
     "SIMPLE-STRING" "SATISFIES" "SIMPLE-STRING-P" "SBIT" "SIMPLE-TYPE-ERROR" "SCALE-FLOAT"
     "SIMPLE-VECTOR" "SCHAR" "SIMPLE-VECTOR-P" "SEARCH" "SIMPLE-WARNING" "SECOND" "SIN"
     "SEQUENCE" "SINGLE-FLOAT" "SERIOUS-CONDITION" "SINGLE-FLOAT-EPSILON" "SET"
     "SINGLE-FLOAT-NEGATIVE-EPSILON" "SET-DIFFERENCE" "SINH" "SET-DISPATCH-MACRO-CHARACTER"
     "SIXTH" "SET-EXCLUSIVE-OR" "SLEEP" "SET-MACRO-CHARACTER" "SLOT-BOUNDP"
     "SET-PPRINT-DISPATCH" "SLOT-EXISTS-P" "SET-SYNTAX-FROM-CHAR" "SLOT-MAKUNBOUND" "SETF"
     "SLOT-MISSING" "SETQ" "SLOT-UNBOUND" "SEVENTH" "SLOT-VALUE" "SHADOW" "SOFTWARE-TYPE"
     "SHADOWING-IMPORT" "SOFTWARE-VERSION" "SHARED-INITIALIZE" "SOME" "SHIFTF" "SORT"
     "SHORT-FLOAT" "SPACE" "SHORT-FLOAT-EPSILON" "SPECIAL" "SHORT-FLOAT-NEGATIVE-EPSILON"
     "SPECIAL-OPERATOR-P" "SHORT-SITE-NAME" "SPEED" "SIGNAL" "SQRT" "SIGNED-BYTE"
     "STABLE-SORT" "SIGNUM" "STANDARD" "SIMPLE-ARRAY" "STANDARD-CHAR" "SIMPLE-BASE-STRING"
     "STANDARD-CHAR-P" "STANDARD-CLASS" "SUBLIS" "STANDARD-GENERIC-FUNCTION" "SUBSEQ"
     "STANDARD-METHOD" "SUBSETP" "STANDARD-OBJECT" "SUBST" "STEP" "SUBST-IF"
     "STORAGE-CONDITION" "SUBST-IF-NOT" "STORE-VALUE" "SUBSTITUTE" "STREAM" "SUBSTITUTE-IF"
     "STREAM-ELEMENT-TYPE" "SUBSTITUTE-IF-NOT" "STREAM-ERROR" "SUBTYPEP"
     "STREAM-ERROR-STREAM" "SVREF" "STREAM-EXTERNAL-FORMAT" "SXHASH" "STREAMP" "SYMBOL"
     "STRING" "SYMBOL-FUNCTION" "STRING-CAPITALIZE" "SYMBOL-MACROLET" "STRING-DOWNCASE"
     "SYMBOL-NAME" "STRING-EQUAL" "SYMBOL-PACKAGE" "STRING-GREATERP" "SYMBOL-PLIST"
     "STRING-LEFT-TRIM" "SYMBOL-VALUE" "STRING-LESSP" "SYMBOLP" "STRING-NOT-EQUAL"
     "SYNONYM-STREAM" "STRING-NOT-GREATERP" "SYNONYM-STREAM-SYMBOL" "STRING-NOT-LESSP" "T"
     "STRING-RIGHT-TRIM" "TAGBODY" "STRING-STREAM" "TAILP" "STRING-TRIM" "TAN"
     "STRING-UPCASE" "TANH" "STRING/=" "TENTH" "STRING<" "TERPRI" "STRING<=" "THE" "STRING="
     "THIRD" "STRING>" "THROW" "STRING>=" "TIME" "STRINGP" "TRACE" "STRUCTURE"
     "TRANSLATE-LOGICAL-PATHNAME" "STRUCTURE-CLASS" "TRANSLATE-PATHNAME" "STRUCTURE-OBJECT"
     "TREE-EQUAL" "STYLE-WARNING" "TRUENAME" "TRUNCATE" "VALUES-LIST" "TWO-WAY-STREAM"
     "VARIABLE" "TWO-WAY-STREAM-INPUT-STREAM" "VECTOR" "TWO-WAY-STREAM-OUTPUT-STREAM"
     "VECTOR-POP" "TYPE" "VECTOR-PUSH" "TYPE-ERROR" "VECTOR-PUSH-EXTEND" "TYPE-ERROR-DATUM"
     "VECTORP" "TYPE-ERROR-EXPECTED-TYPE" "WARN" "TYPE-OF" "WARNING" "TYPECASE" "WHEN"
     "TYPEP" "WILD-PATHNAME-P" "UNBOUND-SLOT" "WITH-ACCESSORS" "UNBOUND-SLOT-INSTANCE"
     "WITH-COMPILATION-UNIT" "UNBOUND-VARIABLE" "WITH-CONDITION-RESTARTS"
     "UNDEFINED-FUNCTION" "WITH-HASH-TABLE-ITERATOR" "UNEXPORT" "WITH-INPUT-FROM-STRING"
     "UNINTERN" "WITH-OPEN-FILE" "UNION" "WITH-OPEN-STREAM" "UNLESS" "WITH-OUTPUT-TO-STRING"
     "UNREAD-CHAR" "WITH-PACKAGE-ITERATOR" "UNSIGNED-BYTE" "WITH-SIMPLE-RESTART" "UNTRACE"
     "WITH-SLOTS" "UNUSE-PACKAGE" "WITH-STANDARD-IO-SYNTAX" "UNWIND-PROTECT" "WRITE"
     "UPDATE-INSTANCE-FOR-DIFFERENT-CLASS" "WRITE-BYTE"
     "UPDATE-INSTANCE-FOR-REDEFINED-CLASS" "WRITE-CHAR" "UPGRADED-ARRAY-ELEMENT-TYPE"
     "WRITE-LINE" "UPGRADED-COMPLEX-PART-TYPE" "WRITE-SEQUENCE" "UPPER-CASE-P"
     "WRITE-STRING" "USE-PACKAGE" "WRITE-TO-STRING" "USE-VALUE" "Y-OR-N-P"
     "USER-HOMEDIR-PATHNAME" "YES-OR-NO-P" "VALUES" "ZEROP"))
              nil)
        (cons "KEYWORD" '(nil nil))))


(defun h2-books-make-rule-index (claims equations formulas)
  (list :h2-rule-index claims equations formulas))

(defun h2-books-rule-index-init ()
  (h2-books-make-rule-index nil nil nil))

(defun h2-books-rule-index-claims (index) (cadr index))
(defun h2-books-rule-index-equations (index) (caddr index))
(defun h2-books-rule-index-formulas (index) (cadddr index))

(defun h2-books-make-book-proof (recipes fuel dynamic arithmetic fixed-calls
                                        library-rules book-rules packages list-rules
                                        math-rules names-as-written)
  (list :h2-book-proof recipes fuel dynamic arithmetic fixed-calls
        library-rules book-rules packages list-rules math-rules names-as-written))

(defun h2-books-book-proof-recipes (proof) (nth 1 proof))
(defun h2-books-book-proof-fuel (proof) (nth 2 proof))
(defun h2-books-book-proof-dynamic (proof) (nth 3 proof))
(defun h2-books-book-proof-arithmetic (proof) (nth 4 proof))
(defun h2-books-book-proof-fixed-calls (proof) (nth 5 proof))
(defun h2-books-book-proof-library-rules (proof) (nth 6 proof))
(defun h2-books-book-proof-book-rules (proof) (nth 7 proof))
(defun h2-books-book-proof-packages (proof) (nth 8 proof))
(defun h2-books-book-proof-list-rules (proof) (nth 9 proof))
(defun h2-books-book-proof-math-rules (proof) (nth 10 proof))
(defun h2-books-book-proof-names-as-written (proof) (nth 11 proof))

(defun h2-books-book-proof-search (proof)
  (h2-recipes-recipes-search (h2-books-book-proof-recipes proof)))

(defun h2-books-book-proof-library (proof)
  (h2-search-search-library (h2-books-book-proof-search proof)))

(defun h2-books-book-proof-names (proof)
  (h2-recipes-recipes-names (h2-books-book-proof-recipes proof)))

(defun h2-books-book-proof-core (proof)
  (library-library-proof (h2-books-book-proof-library proof)))

(defun h2-books-book-proof-facts (proof)
  (proof-proof-facts (h2-books-book-proof-core proof)))

(defun h2-books-book-proof-definitions (proof)
  (proof-proof-definitions (h2-books-book-proof-core proof)))

(defun h2-books-book-proof-with-recipes (proof recipes) (update-nth 1 recipes proof))
(defun h2-books-book-proof-with-fuel (proof fuel) (update-nth 2 fuel proof))
(defun h2-books-book-proof-with-dynamic (proof dynamic) (update-nth 3 dynamic proof))
(defun h2-books-book-proof-with-arithmetic (proof arithmetic) (update-nth 4 arithmetic proof))
(defun h2-books-book-proof-with-fixed-calls (proof fixed-calls) (update-nth 5 fixed-calls proof))
(defun h2-books-book-proof-with-library-rules (proof index) (update-nth 6 index proof))
(defun h2-books-book-proof-with-book-rules (proof index) (update-nth 7 index proof))
(defun h2-books-book-proof-with-packages (proof packages) (update-nth 8 packages proof))
(defun h2-books-book-proof-with-list-rules (proof rules) (update-nth 9 rules proof))
(defun h2-books-book-proof-with-math-rules (proof rules) (update-nth 10 rules proof))
(defun h2-books-book-proof-with-names-as-written (proof names) (update-nth 11 names proof))

(defun h2-books-book-proof-with-search (proof search)
  (h2-books-book-proof-with-recipes
   proof (h2-recipes-recipes-with-search (h2-books-book-proof-recipes proof) search)))

(defun h2-books-book-proof-with-library (proof library)
  (h2-books-book-proof-with-search
   proof (h2-search-search-with-library (h2-books-book-proof-search proof) library)))

(defun h2-books-book-proof-with-facts (proof facts)
  (h2-books-book-proof-with-library
   proof (library-library-with-proof (h2-books-book-proof-library proof)
                                    (proof-proof-with-facts (h2-books-book-proof-core proof) facts))))

(defun h2-books-context-evidence-init (proof context)
  (list :h2-context-evidence proof context))

(defun h2-books-context-evidence-proof (evidence) (cadr evidence))
(defun h2-books-context-evidence-context (evidence) (caddr evidence))

(defun h2-books-make-certificate (entries reason)
  (list :h2-certificate entries reason))

(defun h2-books-certificate-entries (certificate) (cadr certificate))
(defun h2-books-unproved-p (value)
  (and (failure-p value) (equal (cadr value) "unproved")))

(defconst *h2-books-unproved* '(:failure "unproved" ""))

(mutual-recursion
 (defun h2-books-calls-in (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((endp term) '(:failure "failure" ""))
         (t
          (proof-with-checked-results
              ((first (if (proof-compound (car term))
                          (if (consp (cddar term))
                              (h2-books-calls-in (caddar term))
                            '(:failure "failure" ""))
                        (list term)))
               (rest (h2-books-calls-in-arguments (cdr term))))
            (append first rest)))))
 (defun h2-books-calls-in-arguments (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results ((first (h2-books-calls-in (car args)))
                                  (rest (h2-books-calls-in-arguments (cdr args))))
       (append first rest)))))

(mutual-recursion
 (defun h2-books-symbols (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((proof-compound value) (h2-books-symbols-in-list value))
         ((and (consp value) (equal (car value) "sym")) (list value))
         (t nil)))
 (defun h2-books-symbols-in-list (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (append (h2-books-symbols (car items))
             (h2-books-symbols-in-list (cdr items))))))

(defun h2-books-signature (term)
  (if (not (proof-compound term))
      '(nil)
    (proof-with-checked-results ((fn (proof-term-at term 0)))
      (case (len (cdr term))
        (0 (list fn))
        (1 (proof-with-checked-results ((arg (h2-search-head (cadr term))))
             (list fn arg)))
        (otherwise
         (proof-with-checked-results ((left (h2-search-head (cadr term)))
                                      (right (h2-search-head (caddr term))))
           (list fn left right)))))))

(defun h2-books-rule-index-keys (args)
  (if (endp args)
      (list nil)
    (let* ((tail (h2-books-rule-index-keys (cdr args)))
           (wild (pairlis$ (make-list (len tail) :initial-element nil) tail)))
      (if (car args)
          (append (pairlis$ (make-list (len tail) :initial-element (car args)) tail) wild)
        wild))))

(defun h2-books-rule-index-lookup-keys (keys fn buckets)
  (if (endp keys)
      (if fn (table-get buckets '(nil) nil) nil)
    (append (table-get buckets (cons fn (car keys)) nil)
            (h2-books-rule-index-lookup-keys (cdr keys) fn buckets))))

(defun h2-books-rule-index-lookup (index buckets term)
  (declare (ignore index))
  (if (endp buckets)
      nil
    (proof-with-checked-results ((key (h2-books-signature term)))
      (h2-books-rule-index-lookup-keys (h2-books-rule-index-keys (cdr key)) (car key) buckets))))

(defun h2-books-rule-index-candidates (index term rewrite)
  (h2-books-rule-index-lookup
   index (if rewrite (h2-books-rule-index-equations index) (h2-books-rule-index-claims index)) term))

(defun h2-books-append-to-bucket (buckets key item)
  (table-put buckets key (append (table-get buckets key nil) (list item))))

(defun h2-books-rule-index-add-equation (index pattern rule)
  (proof-with-checked-results ((sides (proof-list-of-length (cdr pattern) 2)))
    (let ((left (car sides)) (right (cadr sides)))
      (if (not (proof-compound left))
          index
        (proof-with-checked-results ((left-size (h2-search-size left))
                                     (right-size (h2-search-size right)))
          (if (<= left-size right-size)
              index
            (proof-with-checked-results ((key (h2-books-signature left)))
              (h2-books-make-rule-index
               (h2-books-rule-index-claims index)
               (h2-books-append-to-bucket (h2-books-rule-index-equations index) key rule)
               (h2-books-rule-index-formulas index)))))))))

(defun h2-books-rule-index-add (index rule)
  (let ((pattern (h2-search-rule-pattern rule)))
    (proof-with-checked-results ((needed (h2-search-variables pattern)))
      (if (not (equal (h2-search-rule-required rule) needed))
          index
        (proof-with-checked-results ((key (h2-books-signature pattern)))
          (let ((next (h2-books-make-rule-index
                       (h2-books-append-to-bucket (h2-books-rule-index-claims index) key rule)
                       (h2-books-rule-index-equations index)
                       (h2-books-rule-index-formulas index))))
            (if (proof-is-call pattern *proof-equal*)
                (h2-books-rule-index-add-equation next pattern rule)
              next)))))))

(defun h2-books-rule-index-add-rules (rules index identity number)
  (if (endp rules)
      index
    (proof-with-checked-results
        ((next (h2-books-rule-index-add
                index (h2-search-rule-with-id (car rules) (append identity (list number))))))
      (h2-books-rule-index-add-rules (cdr rules) next identity (1+ number)))))

(defun h2-books-rule-index-add-fact-in (index proof name section)
  (let ((entry (assoc-equal name (h2-books-book-proof-facts proof))))
    (if (not entry)
        '(:failure "failure" "")
      (proof-with-checked-results ((formula (proof-term-at (cdr entry) 0))
                                   (key (h2-books-signature formula))
                                   (rules (h2-search-rule-from-fact (h2-books-book-proof-core proof) name)))
        (let* ((formulas (h2-books-rule-index-formulas index))
               (identity (list :h2-rule-index section key (len (table-get formulas key nil)))))
          (h2-books-rule-index-add-rules
           rules (h2-books-make-rule-index
                  (h2-books-rule-index-claims index)
                  (h2-books-rule-index-equations index)
                  (h2-books-append-to-bucket formulas key (list name formula)))
           identity 0))))))

(defun h2-books-rule-index-add-fact (index proof name)
  (h2-books-rule-index-add-fact-in index proof name :book))

(defun h2-books-negative-quote-p (args)
  (if (endp args)
      nil
    (if (proof-is-call (car args) *proof-quote*)
        (proof-with-checked-results ((value (proof-term-at (car args) 1)))
          (if (and (integerp value) (< value 0))
              t
            (h2-books-negative-quote-p (cdr args))))
      (h2-books-negative-quote-p (cdr args)))))

(defun h2-books-appropriate-descent (variable term)
  (declare (xargs :measure (acl2-count term)))
  (cond ((or (proof-is-call term *library-car*) (proof-is-call term *library-cdr*))
         (cond ((endp (cdr term)) '(:failure "tactic-inapplicable" ""))
               ((equal (cadr term) variable) t)
               (t (h2-books-appropriate-descent variable (cadr term)))))
        ((and (proof-is-call term *proof-plus*) (member-equal variable (cdr term)))
         (h2-books-negative-quote-p (cdr term)))
        (t nil)))

(defun h2-books-subtraction (variable term)
  (and (proof-is-call term *proof-plus*)
       (proof-with-checked-results ((first (proof-term-at term 1)))
         (and (equal first variable)
              (proof-with-checked-results ((second (proof-term-at term 2)))
                (proof-is-call second *proof-minus*))))))

(defun h2-books-statement-name (kind data)
  (cond ((equal kind "theorem") (proof-term-at data 0))
        ((equal kind "define")
         (proof-with-checked-results ((definition (proof-term-at data 1)))
           (proof-term-at definition 0)))
        ((equal kind "constrain")
         (proof-with-checked-results ((functions (proof-term-at data 0))
                                      (function (proof-term-at functions 0)))
           (proof-term-at function 0)))
        (t nil)))

(defun h2-books-book-proof-fork (proof)
  (h2-books-book-proof-with-book-rules proof (h2-books-rule-index-init)))

(defun h2-books-book-proof-note-package (proof kind data)
  (if (not (member-equal kind '("package" "hidden-package")))
      proof
    (proof-with-checked-results ((fields (proof-list-of-length data 2))
                                 (name (proof-term-at (car fields) 1)))
      (let ((imports (cadr fields)))
        (h2-books-book-proof-with-packages
         proof (table-put (h2-books-book-proof-packages proof) name
                            (list (if (equal imports *proof-nil*) nil imports)
                                  (equal kind "hidden-package"))))))))

(defun h2-books-book-proof-admit (proof kind data)
  (if (equal kind "choose")
      (proof-with-checked-results ((formula (h2-book-logic-choice-axiom data))
                                   (name (proof-term-at data 0)))
        (h2-books-book-proof-with-facts
         proof (table-put (h2-books-book-proof-facts proof) name (list formula))))
    (proof-with-checked-results
        ((recipes (h2-recipes-recipes-admit (h2-books-book-proof-recipes proof) kind data)))
      (h2-books-book-proof-with-recipes proof recipes))))

(defun h2-books-string-set-key (value)
  (text-replace (text-replace value "\\" "\\\\") "\"" "\\\""))

(defun h2-books-string-set-add (value key names)
  (cond ((endp names) (list value))
        ((equal value (car names)) names)
        ((string< key (concatenate 'string (h2-books-string-set-key (car names)) "\""))
         (cons value names))
        (t (cons (car names) (h2-books-string-set-add value key (cdr names))))))

(defun h2-books-written-name-index (names tree)
  (if (endp names)
      tree
    (let* ((name (car names))
           (key (concatenate 'string (h2-books-string-set-key name) "\"")))
      (h2-books-written-name-index (cdr names) (h2-search-index-put key name tree)))))

(defun h2-books-book-proof-index-prefix-names (proof lines)
  (if (consp (nthcdr 31 lines))
      (h2-books-book-proof-with-names-as-written
       proof (cons :h2-written-name-index
                   (h2-books-written-name-index (h2-books-book-proof-names-as-written proof) nil)))
    proof))

(defun h2-books-book-proof-restore-written-names (proof)
  (let ((names (h2-books-book-proof-names-as-written proof)))
    (if (eq (car names) :h2-written-name-index)
        (h2-books-book-proof-with-names-as-written proof (h2-search-index-values (cdr names) nil))
      proof)))

(defun h2-books-remember-written-name (proof name)
  (proof-with-checked-results ((written (proof-write name)))
    (let ((key (concatenate 'string (h2-books-string-set-key written) "\""))
          (names (h2-books-book-proof-names-as-written proof)))
      (h2-books-book-proof-with-names-as-written
       proof (if (eq (car names) :h2-written-name-index)
                 (cons :h2-written-name-index (h2-search-index-put key written (cdr names)))
               (h2-books-string-set-add written key names))))))

(defun h2-books-add-book-fact (proof name)
  (proof-with-checked-results
      ((index (h2-books-rule-index-add-fact (h2-books-book-proof-book-rules proof) proof name)))
    (h2-books-remember-written-name (h2-books-book-proof-with-book-rules proof index) name)))

(defun h2-books-add-definition-names (definitions proof)
  (if (endp definitions)
      proof
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0))
                                 (next (h2-books-remember-written-name proof name)))
      (h2-books-add-definition-names (cdr definitions) next))))

(defun h2-books-add-constraint-facts (constraints proof)
  (if (endp constraints)
      proof
    (proof-with-checked-results ((constraint (proof-list-of-length (car constraints) 2))
                                 (next (h2-books-add-book-fact proof (car constraint))))
      (h2-books-add-constraint-facts (cdr constraints) next))))

(defun h2-books-book-proof-add-statement (proof kind data)
  (proof-with-checked-results ((admitted (h2-books-book-proof-admit proof kind data))
                               (next (h2-books-book-proof-note-package admitted kind data)))
    (cond ((member-equal kind '("theorem" "axiom" "choose"))
           (proof-with-checked-results ((name (proof-term-at data 0)))
             (h2-books-add-book-fact next name)))
          ((equal kind "define") (h2-books-add-definition-names (cdr data) next))
          ((equal kind "constrain")
           (proof-with-checked-results ((constraints (proof-term-at data 1)))
             (if (equal constraints *proof-nil*) next
               (h2-books-add-constraint-facts constraints next))))
          (t next))))

(defun h2-books-book-proof-spent (proof)
  (let ((fuel (h2-books-book-proof-fuel proof)))
    (if (null fuel) proof
      (h2-books-book-proof-with-fuel proof (1- fuel)))))

(defun h2-books-budget-exhausted-p (proof)
  (let ((fuel (h2-books-book-proof-fuel proof)))
    (and fuel (< fuel 0))))

(defun h2-books-book-proof-boolean-value (proof term evidence)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (let ((fact (assoc-equal head *h2-books-boolean-facts*)))
      (if (not fact)
          '(:failure "tactic-inapplicable" "")
        (proof-with-checked-results
            ((typed (proof-proof-fact (h2-books-book-proof-core proof) (cdr fact)
                                      (seq-zip (list *library-x* *library-y*) (cdr term)))))
          (library-library-cite (h2-books-book-proof-library proof) "H2-TRUE-BOOLEAN"
                                (list term) (list evidence typed)))))))

(defun h2-books-book-proof-lookup (proof term context)
  (h2-search-search-lookup
   (h2-search-search-with-hooks (h2-books-book-proof-search proof) '(:cons-lookup))
   term context))

(defun h2-books-context-evidence-find (evidence term)
  (h2-books-book-proof-lookup (h2-books-context-evidence-proof evidence) term
                              (h2-books-context-evidence-context evidence)))

(defun h2-books-quoted-arguments-p (args)
  (or (endp args)
      (and (proof-is-call (car args) *proof-quote*)
           (h2-books-quoted-arguments-p (cdr args)))))

(defun h2-books-quotation-values (args)
  (if (endp args)
      nil
    (proof-with-checked-results ((value (proof-term-at (car args) 1))
                                 (rest (h2-books-quotation-values (cdr args))))
      (cons value rest))))

(defun h2-books-primitive-boolean (proof term cons-term)
  (proof-with-checked-results
      ((evidence (proof-proof-fact (h2-books-book-proof-core proof) "consp-cons"
                                  (seq-zip (list *library-x* *library-y*) (cdr cons-term)))))
    (h2-books-book-proof-boolean-value proof term evidence)))

(defun h2-books-primitive-compute (proof term function)
  (proof-with-checked-results ((args (h2-books-quotation-values (cdr term))))
    (let ((value (h2-computation-primitive-value function args (h2-books-book-proof-packages proof))))
      (cond ((h2-books-unproved-p value) nil)
            ((failure-p value) value)
            (t (proof-proof-compute (h2-books-book-proof-core proof) term value))))))

(defun h2-books-primitive-before (proof term)
  (proof-with-checked-results ((cons-arg (if (proof-is-call term *proof-consp*) (proof-term-at term 1) nil)))
    (if (proof-is-call cons-arg *proof-cons*)
        (list :return (h2-books-primitive-boolean proof term cons-arg))
      (proof-with-checked-results ((function (proof-term-at term 0)))
        (if (and (member-equal function (proof-proof-primitives (h2-books-book-proof-core proof)))
                 (h2-books-quoted-arguments-p (cdr term)))
            (list :return (h2-books-primitive-compute proof term function))
          :base)))))

(defun h2-books-all-counts-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *library-count*) (h2-books-all-counts-p (cdr terms)))))

(defun h2-books-descent-query (n recipe args hypotheses evidence replies)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      '(:failure "fuel" "h2-books-descent-query")
    (let* ((proof (h2-books-context-evidence-proof evidence))
           (result (descent-query-recipe recipe (h2-books-book-proof-library proof) args hypotheses replies)))
      (cond ((failure-p result) result)
            ((descent-request-p result)
             (let ((term (descent-request-term result)))
               (proof-with-checked-results ((answer (h2-books-context-evidence-find evidence term)))
                 (h2-books-descent-query (1- n) recipe args hypotheses evidence
                                          (table-put replies term (cons answer nil))))))
            (t (car result))))))

(defun h2-books-selector-rule (proof term context)
  (let ((library (h2-books-book-proof-library proof))
        (evidence (h2-books-context-evidence-init proof context)))
    (proof-with-checked-results
        ((hypotheses (descent-hypotheses-init library nil nil))
         (direct (h2-books-descent-query 1000000 :direct-builtin (list (list term)) hypotheses evidence nil)))
      (if direct
          direct
        (proof-with-checked-results
            ((parent (proof-term-at term 2))
             (parent (proof-term-at parent 1))
             (child (proof-term-at term 1))
             (child (proof-term-at child 1))
             (has-cons (h2-books-context-evidence-find evidence (list *proof-consp* parent)))
             (appropriate (and has-cons (h2-books-appropriate-descent parent child))))
          (if (not appropriate)
              nil
            (let ((result (h2-books-descent-query 1000000 :selector-decrease (list term) hypotheses evidence nil)))
              (if (and (failure-p result)
                       (member-equal (cadr result) '("assertion" "value" "index" "key")))
                  nil
                result))))))))

(defun h2-books-integer-steps (literals)
  (cond ((endp literals) nil)
        ((proof-is-call (caar literals) *proof-integerp*)
         (cons (cdar literals) (h2-books-integer-steps (cdr literals))))
        (t (h2-books-integer-steps (cdr literals)))))

(defun h2-books-any-call-p (terms functions)
  (and (consp terms)
       (or (and (consp (car terms)) (proof-compound (car terms))
                (member-equal (caar terms) functions))
           (h2-books-any-call-p (cdr terms) functions))))

(defun h2-books-finite-order-step (library sides integers)
  (proof-with-checked-results ((left (library-library-type-of library (car sides) integers))
                               (right (library-library-type-of library (cadr sides) integers)))
    (library-library-cite library "FINITE-ORDER" sides (list left right))))

(defun h2-books-finite-rule (proof term context active)
  (proof-with-checked-results ((sides (proof-list-of-length (cdr term) 2)))
    (let ((numeric (if (h2-books-book-proof-arithmetic proof)
                       (list *library-len* *proof-plus* *library-count* *library-nfix*)
                     (list *library-len* *proof-plus*))))
      (and (h2-books-any-call-p sides numeric) (<= (len active) 1)
           (let ((order (h2-books-finite-order-step (h2-books-book-proof-library proof) sides
                                                   (h2-books-integer-steps (h2-search-context-literals context)))))
             (if (and (failure-p order) (member-equal (cadr order) '("value" "key")))
                 nil
               order))))))

(defun h2-books-arithmetic-goal-p (term)
  (proof-with-checked-results ((atom (if (proof-is-call term *proof-not*) (proof-term-at term 1) term)))
    (and (or (proof-is-call atom *proof-equal*) (proof-is-call atom *proof-less*))
         (h2-books-any-call-p (cdr atom) (list *proof-plus* *proof-times* *proof-minus*)))))

(defconst *h2-books-arithmetic*
  (append *h2-recipes-countdown* *h2-arithmetic-integer-rules* *h2-arithmetic-index-rules*
          '("SELF-H2-LESS-IMPLIES-UNEQUAL" "SELF-H2-INTEGER-NONNIL" "SELF-H2-SUB1-ADD1"
            "SELF-H2-PREDECESSOR-BOUND" "SELF-H2-INTEGER-EQUAL-WHEN-NEITHER-LESS"
            "SELF-H2-LESS-POSITIVE-PRODUCT" "SELF-H2-LESS-CANCEL-PRODUCT"
            "SELF-H2-INTEGER-ZERO-PRODUCT")))

(defun h2-books-existing-names (names map)
  (if (endp names)
      nil
    (let ((entry (assoc-equal (car names) map)))
      (if entry
          (cons (cdr entry) (h2-books-existing-names (cdr names) map))
        (h2-books-existing-names (cdr names) map)))))

(defun h2-books-builtin-rule-names (numbers)
  (if (endp numbers)
      nil
    (cons (concatenate 'string "built-in-clause-" (decimal-text (car numbers)))
          (h2-books-builtin-rule-names (cdr numbers)))))

(defconst *h2-books-builtin-rule-names* (h2-books-builtin-rule-names (seq-range 1 24 1)))

(defun h2-books-existing-arithmetic (rules facts)
  (cond ((endp rules) nil)
        ((assoc-equal (proof-sym (car rules) "ACL2") facts)
         (cons (car rules) (h2-books-existing-arithmetic (cdr rules) facts)))
        (t (h2-books-existing-arithmetic (cdr rules) facts))))

(defun h2-books-book-proof-configure-book (proof definitions repeat facts dynamic)
  (let* ((defaults (h2-books-existing-names (append *h2-books-translation* *h2-books-arithmetic-defs*)
                                           (h2-books-book-proof-names proof)))
         (math-rules (and (h2-books-book-proof-arithmetic proof) (h2-books-book-proof-math-rules proof)))
         (arithmetic (h2-books-existing-arithmetic *h2-books-arithmetic* (h2-books-book-proof-facts proof)))
         (facts (append *h2-books-builtin-rule-names* arithmetic math-rules
                        (h2-books-book-proof-list-rules proof) facts
                        '("SELF-H2-EMPTY-COUNT-LESS" "SELF-LEN-CDR-LESS" "SELF-LESS-SHIFT"))))
    (proof-with-checked-results
        ((recipes (h2-recipes-recipes-set-rules (h2-books-book-proof-recipes proof) "" facts "" 80)))
      (let* ((proof (h2-books-book-proof-with-dynamic proof dynamic))
             (search (h2-recipes-recipes-search recipes))
             (opened (append (h2-search-search-opened search) defaults definitions)))
        (h2-books-book-proof-with-search
         proof (h2-search-search-with-configuration search opened repeat 16))))))

(defun h2-books-book-proof-keep-folded (proof terms)
  (h2-books-book-proof-with-fixed-calls proof (h2-search-set terms (h2-books-book-proof-fixed-calls proof))))

(defun h2-books-book-proof-empty-count-bound (proof)
  (let* ((library (h2-books-book-proof-library proof))
         (core (library-library-proof library))
         (empty (list *library-count* *proof-false*))
         (tail (list *library-count* (list *library-cdr* *library-x*)))
         (parent (list *library-count* *library-x*))
         (cons-term (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((cons-step (proof-proof-assume core cons-term t))
         (builtin (library-library-builtin library 3 *library-x*))
         (smaller (proof-proof-discharge core builtin cons-step))
         (order (library-library-ordinal-comparison library tail parent))
         (smaller (proof-proof-rewrite core smaller order '(1)))
         (nat-tail (library-library-natural library tail))
         (empty-value (proof-proof-simplify core empty nil (list *library-count*)))
         (tail-bound (library-library-cite library "NATURAL-NONNEGATIVE" (list tail) (list nat-tail)))
         (empty-reverse (proof-proof-symmetric core empty-value))
         (nonnegative (proof-proof-rewrite core tail-bound empty-reverse '(1 1 2)))
         (strict (library-library-compare-chain library nonnegative smaller))
         (order (library-library-ordinal-comparison library empty parent))
         (result (proof-proof-transport core strict order))
         (claim (proof-step-first result))
         (library (library-library-lemma library "H2-EMPTY-COUNT-LESS" claim result (list (proof-neg cons-term)))))
      (h2-books-book-proof-with-library proof library))))

(defconst *h2-books-search-hooks*
  '(:reduce :can-open :cons-lookup :learn-selectors :primitive
    :set-fuel :keep-folded :restore-fixed-calls))

(defun h2-books-search-call (operation search args)
  (case operation
    (:solve (h2-search-search-solve search (car args) (cadr args) (caddr args)))
    (:list-induction (h2-search-search-list-induction search (car args) (cadr args)
                                                        (caddr args) (cadddr args)))
    (:induction (h2-search-search-induction search (nth 0 args) (nth 1 args) (nth 2 args)
                                           (nth 3 args) (nth 4 args)))
    (:truth (h2-search-search-truth search (car args) (cadr args) (caddr args)))
    (:evaluate (h2-computation-evaluate search (car args) (cadr args) (caddr args)))
    (:deduce (h2-search-search-deduce search (car args) (cadr args) (caddr args)))
    (:reduce (h2-search-search-reduce search (car args) (cadr args) (caddr args) (cadddr args)))
    (:learn (h2-search-search-learn search (car args) (cadr args) (caddr args) (cadddr args)))
    (:primitive (h2-search-search-primitive search (car args) (cadr args)))
    (:apply-rules (h2-search-search-apply-rules search (car args) (cadr args) (caddr args) (cadddr args)))
    (:rule-apply (h2-search-rule-apply (nth 0 args) search (nth 1 args) (nth 2 args)
                                         (nth 3 args) (nth 4 args)))
    (:equality-equivalence (h2-equivalence-equality-equivalence search (car args)))
    (:cons-implies-truth (h2-book-logic-cons-implies-truth search))
    (:remainder-step (h2-modular-remainder-step (h2-recipes-recipes-with-search (car args) search)))
    (:remainder-count-bound (h2-modular-remainder-count-bound (h2-recipes-recipes-with-search (car args) search)))
    (:recipe-theorem (h2-recipes-recipes-prove-theorem (h2-recipes-recipes-with-search (car args) search)
                                                     (cadr args) (caddr args)))
    (:book-recipe (h2-book-recipes-search-call search (car args) (cdr args)))
    (:compression-search (h2-compression-lookup-search-call search (car args) (cdr args)))
    (:book-recipes (h2-book-recipes-recipes-call (h2-recipes-recipes-with-search (car args) search)
                                                (cadr args) (cddr args)))
    (otherwise '(:failure "failure" ""))))

(defun h2-books-search-strip-hooks (search)
  (h2-search-search-with-hooks (h2-search-search-with-replies search nil) nil))

(defun h2-books-search-finish (operation result proof)
  (let ((proof (h2-books-book-proof-with-search
                proof (h2-books-search-strip-hooks (h2-books-book-proof-search proof)))))
    (cond ((failure-p result) (cons result proof))
          ((member-eq operation '(:equality-equivalence :book-recipe :compression-search))
           (cons (car result) (h2-books-book-proof-with-search proof (h2-books-search-strip-hooks (cdr result)))))
          ((member-eq operation '(:remainder-step :remainder-count-bound :recipe-theorem :book-recipes))
           (let* ((recipes (cdr result))
                  (search (h2-books-search-strip-hooks (h2-recipes-recipes-search recipes))))
             (cons (car result) (h2-books-book-proof-with-recipes proof (h2-recipes-recipes-with-search recipes search)))))
          ((eq operation :cons-implies-truth)
           (cons nil (h2-books-book-proof-with-search proof (h2-books-search-strip-hooks result))))
          ((eq operation :evaluate)
           (cons (car result) (h2-books-book-proof-with-fuel proof (cdr result))))
          (t (cons result proof)))))

(defun h2-books-reduce-before (proof term context)
  (let ((evidence (and (proof-compound term)
                       (assoc-equal (car term) *h2-books-boolean-facts*)
                       (assoc-equal term (h2-search-context-literals context)))))
    (cond ((h2-books-budget-exhausted-p proof)
           (list :return *h2-books-unproved*))
          (evidence
           (let ((step (h2-books-book-proof-boolean-value proof term (cdr evidence))))
             (list :return (if (failure-p step) step (cons step context)))))
          (t :base))))

(defun h2-books-search-simple-before (proof method args)
  (case method
    (:can-open (if (member-equal (car args) (h2-books-book-proof-fixed-calls proof)) '(:return nil) :base))
    (:primitive (h2-books-primitive-before proof (car args)))
    (:learn
     (let ((literal (proof-step-first (car args)))
           (context (cadr args))
           (seen (cadddr args)))
       (cond ((failure-p literal) literal)
             ((or (h2-search-seen-p literal seen) (h2-search-context-contradiction context))
              (list :return (cons context seen)))
             (t :after))))
    (:apply-rules :after)
    (otherwise :base)))

(defun h2-books-rules-result (step proof context)
  (cons step (cons proof context)))

(mutual-recursion
 (defun h2-books-run-search (n proof operation args)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:failure "fuel" "h2-books-run-search") proof)
     (let* ((rule-hook (if (or (h2-books-book-proof-dynamic proof) (h2-books-book-proof-arithmetic proof))
                           :apply-rules :book-ordinal-rules))
            (hooks (cons rule-hook *h2-books-search-hooks*))
            (search (h2-search-search-with-hooks (h2-books-book-proof-search proof) hooks))
            (replies (and (or (and (h2-search-search-indexes search)
                                   (member-eq operation '(:solve :induction :list-induction :truth :deduce
                                                          :reduce :learn :primitive :apply-rules :rule-apply)))
                              (eq operation :recipe-theorem)
                              (and (eq operation :book-recipe) (eq (car args) :pack-characters)))
                          (h2-search-reply-transcript nil nil))))
       (h2-books-replay-search (1- n) search proof operation args replies))))

 (defun h2-books-replay-search (n search proof operation args replies)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:failure "fuel" "h2-books-replay-search") proof)
     (let* ((result (h2-books-search-call operation (h2-search-search-with-replies search replies) args))
            (request (cond ((h2-search-request-p result) result)
                           ((h2-search-request-p (car result)) (car result))
                           (t nil))))
       (if request
           (let* ((actual (h2-search-request-search request))
                  (reply (h2-books-search-answer (1- n)
                                                  (if actual (h2-books-book-proof-with-search proof actual) proof)
                                                  request)))
             (h2-books-replay-search (1- n) search (cdr reply) operation args
                                     (h2-search-replay-replies replies request (car reply))))
         (h2-books-search-finish operation result proof)))))

 (defun h2-books-search-answer (n proof request)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:return (:failure "fuel" "h2-books-search-answer")) proof)
     (let ((method (h2-search-request-method request))
           (args (h2-search-request-args request))
           (result (h2-search-request-result request)))
       (cond
        ((eq (h2-search-request-phase request) :before)
         (case method
           (:reduce
            (let ((proof (h2-books-book-proof-spent proof)))
              (cons (h2-books-reduce-before proof (car args) (cadr args)) proof)))
           (:set-fuel (cons '(:return nil) (h2-books-book-proof-with-fuel proof (car args))))
           (:keep-folded (cons (list :return (h2-books-book-proof-fixed-calls proof))
                               (h2-books-book-proof-keep-folded proof (car args))))
           (:restore-fixed-calls (cons '(:return nil) (h2-books-book-proof-with-fixed-calls proof (car args))))
           (otherwise
            (let ((reply (h2-books-search-simple-before proof method args)))
              (cons (if (failure-p reply) (list :return reply) reply) proof)))))
        ((eq method :learn)
         (let ((learned (h2-books-learn-after (1- n) proof (car args) (car result) (caddr args) (cdr result))))
           (cons (list :return (car learned)) (cdr learned))))
        ((eq method :apply-rules)
         (let* ((new (h2-books-apply-rules-after (1- n) proof (car args) (cdr result)
                                                 (caddr args) (cadddr args) (car result)))
                (step (car new)))
           (cons (list :return (if (failure-p step) step (cons step (cddr new)))) (cadr new))))
        (t (cons :base proof))))))

 (defun h2-books-learn-after (n proof step context opened seen)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:failure "fuel" "h2-books-learn-after") proof)
     (let ((literal (proof-step-first step)))
       (cond ((failure-p literal) (cons literal proof))
             ((proof-is-call literal *proof-equal*)
              (h2-books-learn-selectors (1- n) proof (cdr literal) 1 step nil context opened seen))
             (t (cons (cons context seen) proof))))))

 (defun h2-books-learn-selectors (n proof args index step changed context opened seen)
   (declare (xargs :measure (nfix n)))
   (cond
    ((h2-books-out-of-fuel-p n) (cons '(:failure "fuel" "h2-books-learn-selectors") proof))
    ((endp args)
     (if (not changed)
         (cons (cons context seen) proof)
       (let ((tidied (proof-proof-tidy (h2-books-book-proof-core proof) step)))
         (if (failure-p tidied)
             (cons tidied proof)
           (h2-books-run-search (1- n) proof :learn (list tidied context opened seen))))))
    ((or (proof-is-call (car args) *library-car*) (proof-is-call (car args) *library-cdr*))
     (let* ((result (h2-books-run-search (1- n) proof :primitive (list (car args) context)))
            (value (car result))
            (proof (cdr result)))
       (if (failure-p value)
           result
         (let ((step (if value (proof-proof-rewrite (h2-books-book-proof-core proof) step value (list 1 index)) step)))
           (if (failure-p step)
               (cons step proof)
             (h2-books-learn-selectors (1- n) proof (cdr args) (1+ index) step (or changed value)
                                       context opened seen))))))
    (t (h2-books-learn-selectors (1- n) proof (cdr args) (1+ index) step changed context opened seen))))

 (defun h2-books-apply-rules-after (n proof term context active rewrite result)
   (declare (xargs :measure (nfix n)))
   (cond ((h2-books-out-of-fuel-p n) (h2-books-rules-result '(:failure "fuel" "h2-books-apply-rules-after") proof context))
         ((or result (equal term *proof-false*) (<= 4 (len active)))
          (h2-books-rules-result result proof context))
         (t
          (let* ((ordinal (and (not rewrite) (proof-is-call term *proof-ordinal-less*)))
                 (selector (and ordinal (h2-books-all-counts-p (cdr term))
                                (h2-books-selector-rule proof term context))))
            (if selector
                (h2-books-rules-result selector proof context)
              (h2-books-apply-finite-rule (1- n) proof term context active rewrite ordinal))))))

 (defun h2-books-apply-finite-rule (n proof term context active rewrite ordinal)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (h2-books-rules-result '(:failure "fuel" "h2-books-apply-finite-rule") proof context)
     (let ((order (and ordinal (h2-books-finite-rule proof term context active))))
       (cond ((failure-p order) (h2-books-rules-result order proof context))
             (order
              (let* ((result (h2-books-run-search (1- n) proof :deduce
                                                  (list (library-lt (cadr term) (caddr term)) context
                                                        (append active (list nil)))))
                     (value (car result))
                     (proof (cdr result)))
                (cond ((failure-p value) (h2-books-rules-result value proof context))
                      ((car value)
                       (h2-books-rules-result
                        (proof-proof-transport (h2-books-book-proof-core proof) (car value) order) proof (cdr value)))
                      (t (h2-books-apply-calculation (1- n) proof term (cdr value) active rewrite)))))
             (t (h2-books-apply-calculation (1- n) proof term context active rewrite))))))

 (defun h2-books-apply-calculation (n proof term context active rewrite)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (h2-books-rules-result '(:failure "fuel" "h2-books-apply-calculation") proof context)
     (let ((eligible (and (not rewrite) (h2-books-book-proof-arithmetic proof)
                          (h2-books-arithmetic-goal-p term))))
       (cond ((failure-p eligible) (h2-books-rules-result eligible proof context))
             (eligible
              (let ((proof (h2-books-book-proof-spent proof)))
                (if (h2-books-budget-exhausted-p proof)
                    (h2-books-rules-result *h2-books-unproved* proof context)
                  (let ((result (h2-books-run-calculation (1- n) proof (h2-books-book-proof-search proof)
                                                          term context nil)))
                    (if (car result)
                        result
                      (h2-books-apply-dynamic-rules (1- n) (cadr result) term (cddr result) active rewrite))))))
             (t (h2-books-apply-dynamic-rules (1- n) proof term context active rewrite))))))

 (defun h2-books-run-calculation (n proof search term context replies)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (h2-books-rules-result '(:failure "fuel" "h2-books-run-calculation") proof context)
     (let ((result (h2-calculation-calculate-with-replies search term context replies)))
       (cond
        ((failure-p result) (h2-books-rules-result result proof context))
        ((h2-calculation-request-p result)
         (let* ((answer (h2-books-answer-calculation (1- n) proof result))
                (step (car answer))
                (proof (cadr answer)))
           (if (failure-p step)
               answer
             (h2-books-run-calculation
              (1- n) proof search term context
              (append replies (list (cons step (cons (h2-books-book-proof-search proof) (cddr answer)))))))))
        (t (h2-books-rules-result (car result) (h2-books-book-proof-with-search proof (cadr result)) (cddr result)))))))

 (defun h2-books-answer-calculation (n proof request)
   (declare (xargs :measure (nfix n)))
   (let* ((search (h2-calculation-request-proof request))
          (context (h2-calculation-request-context request))
          (args (h2-calculation-request-arguments request))
          (operation (h2-calculation-request-operation request))
          (proof (h2-books-book-proof-with-search proof search)))
     (cond
      ((h2-books-out-of-fuel-p n) (h2-books-rules-result '(:failure "fuel" "h2-books-answer-calculation") proof context))
      ((eq operation :spend)
       (let ((proof (h2-books-book-proof-spent proof)))
         (h2-books-rules-result (and (h2-books-budget-exhausted-p proof)
                                     *h2-books-unproved*) proof context)))
      ((eq operation :primitive)
       (let ((result (h2-books-run-search (1- n) proof :primitive (list (car args) context))))
         (h2-books-rules-result (car result) (cdr result) context)))
      ((eq operation :deduce)
       (let* ((result (h2-books-run-search (1- n) proof :deduce (list (car args) context (cadr args))))
              (value (car result)))
         (if (failure-p value)
             (h2-books-rules-result value (cdr result) context)
           (h2-books-rules-result (car value) (cdr result) (cdr value)))))
      (t (h2-books-rules-result '(:failure "failure" "") proof context)))))

 (defun h2-books-apply-dynamic-rules (n proof term context active rewrite)
   (declare (xargs :measure (nfix n)))
   (cond
    ((h2-books-out-of-fuel-p n) (h2-books-rules-result '(:failure "fuel" "h2-books-apply-dynamic-rules") proof context))
    ((not (h2-books-book-proof-dynamic proof)) (h2-books-rules-result nil proof context))
    (t
     (let* ((indexes (list (h2-books-book-proof-book-rules proof) (h2-books-book-proof-library-rules proof)))
            (result (h2-books-dynamic-indexes (1- n) proof term context active rewrite indexes))
            (proof (cadr result))
            (context (cddr result)))
       (if (or (car result) rewrite (not (h2-books-book-proof-arithmetic proof))
               (not (proof-is-call term *proof-equal*)))
           result
         (let ((left (proof-term-at term 1)) (right (proof-term-at term 2)))
           (cond ((failure-p left) (h2-books-rules-result left proof context))
                 ((failure-p right) (h2-books-rules-result right proof context))
                 ((equal left right) result)
                 (t (let* ((result (h2-books-dynamic-indexes (1- n) proof (proof-eq right left) context active nil indexes))
                           (step (car result))
                           (proof (cadr result)))
                      (if (or (not step) (failure-p step))
                          result
                        (h2-books-rules-result (proof-proof-symmetric (h2-books-book-proof-core proof) step)
                                               proof (cddr result))))))))))))

 (defun h2-books-dynamic-indexes (n proof term context active rewrite indexes)
   (declare (xargs :measure (nfix n)))
   (cond ((h2-books-out-of-fuel-p n) (h2-books-rules-result '(:failure "fuel" "h2-books-dynamic-indexes") proof context))
         ((endp indexes) (h2-books-rules-result nil proof context))
         (t (let ((rules (h2-books-rule-index-candidates (car indexes) term rewrite)))
              (if (failure-p rules)
                  (h2-books-rules-result rules proof context)
                (let ((result (h2-books-dynamic-candidates (1- n) proof term context active rewrite rules)))
                  (if (car result)
                      result
                    (h2-books-dynamic-indexes (1- n) (cadr result) term (cddr result) active rewrite (cdr indexes)))))))))

 (defun h2-books-dynamic-candidates (n proof term context active rewrite rules)
   (declare (xargs :measure (nfix n)))
   (cond
    ((h2-books-out-of-fuel-p n) (h2-books-rules-result '(:failure "fuel" "h2-books-dynamic-candidates") proof context))
    ((endp rules) (h2-books-rules-result nil proof context))
    (t
     (let ((proof (h2-books-book-proof-spent proof)))
       (if (h2-books-budget-exhausted-p proof)
           (h2-books-rules-result *h2-books-unproved* proof context)
         (let* ((result (h2-books-run-search (1- n) proof :rule-apply (list (car rules) term context active rewrite)))
                (value (car result))
                (proof (cdr result)))
           (if (failure-p value)
               (h2-books-rules-result value proof context)
             (let* ((step (car value))
                    (context (cdr value))
                    (right (and step rewrite
                                (proof-with-checked-results ((literal (proof-step-first step)))
                                  (proof-term-at literal 2)))))
               (cond ((failure-p right) (h2-books-rules-result right proof context))
                     ((and step (or (not rewrite) (not (equal right term))))
                      (h2-books-rules-result step proof context))
                     (t (h2-books-dynamic-candidates (1- n) proof term context active rewrite (cdr rules)))))))))))))

(defun h2-books-run-indexed-search (n proof operation args)
  (let ((search (h2-books-book-proof-search proof)))
    (if (or (not (h2-search-object-p search)) (< 11 (len search)))
        (h2-books-run-search n proof operation args)
      (let* ((indexed (h2-books-book-proof-with-search proof (h2-search-search-with-indexes search)))
             (result (h2-books-run-search n indexed operation args))
             (proof (cdr result)))
        (cons (car result)
              (h2-books-book-proof-with-search
               proof (h2-search-search-without-indexes (h2-books-book-proof-search proof))))))))

(defun h2-books-book-proof-solve (proof formula seeds cases)
  (h2-books-run-indexed-search 1000000 proof :solve (list formula seeds cases)))

(defun h2-books-book-proof-prove-theorem (proof label formula)
  (let ((result (h2-books-run-indexed-search 1000000 proof :recipe-theorem
                                              (list (h2-books-book-proof-recipes proof) label formula))))
    (if (failure-p (car result)) (car result) result)))

(defun h2-books-call-derive (proof args)
  (let ((recipes (h2-recipes-recipes-set-rules (h2-books-book-proof-recipes proof)
                                               (nth 1 args) (nth 2 args) (nth 5 args) (nth 8 args))))
    (if (failure-p recipes)
        (cons recipes proof)
      (let* ((proof (h2-books-book-proof-with-recipes proof recipes))
             (formula (car args))
             (variable (nth 3 args)))
        (if (and variable (not (equal variable "")))
            (h2-books-run-indexed-search 1000000 proof :list-induction
                                 (list formula (proof-sym variable "ACL2") nil (nth 4 args)))
          (h2-books-book-proof-solve proof formula (nth 6 args) (nth 7 args)))))))

(defun h2-books-add-lemma (proof name claim step conditions)
  (proof-with-checked-results
      ((library (library-library-lemma (h2-books-book-proof-library proof) name claim step conditions)))
    (h2-books-book-proof-with-library proof library)))

(defun h2-books-call-auxiliary (proof name formula derive-args)
  (let* ((lemma (concatenate 'string "H2-" name))
         (label (concatenate 'string "SELF-" lemma)))
    (if (assoc-equal (proof-sym label "ACL2") (h2-books-book-proof-facts proof))
        (cons label proof)
      (let* ((result (h2-books-call-derive proof (cons formula derive-args)))
             (step (car result))
             (proof (cdr result)))
        (if (failure-p step)
            result
          (let ((next (h2-books-add-lemma proof lemma formula step nil)))
            (if (failure-p next) (cons next proof) (cons label next))))))))

(defun h2-books-run-index-lemmas (n proof replies)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      '(:failure "fuel" "h2-books-run-index-lemmas")
    (let ((result (h2-arithmetic-index-lemmas (h2-books-book-proof-library proof) replies)))
      (cond ((failure-p result) result)
            ((h2-alists-request-p (car result))
             (let* ((proof (h2-books-book-proof-with-library proof (cdr result)))
                    (answer (h2-books-call-derive proof (h2-alists-request-arguments (car result)))))
               (if (failure-p (car answer))
                   (car answer)
                 (h2-books-run-index-lemmas
                  (1- n) (cdr answer)
                  (list (cons (car answer) (h2-books-book-proof-library (cdr answer))))))))
            (t (h2-books-book-proof-with-library proof result))))))

(defun h2-books-book-proof-index-lemmas (proof)
  (h2-books-run-index-lemmas 1000000 proof nil))

(defun h2-books-admit-library (lines proof)
  (if (endp lines)
      proof
    (proof-with-checked-results ((record (proof-list-of-length (car lines) 3))
                                 (admitted (h2-books-book-proof-admit proof (cadr record) (caddr record)))
                                 (next (h2-books-book-proof-note-package admitted (cadr record) (caddr record))))
      (h2-books-admit-library (cdr lines) next))))

(defun h2-books-index-library (facts proof index)
  (if (endp facts)
      index
    (let* ((name (caar facts))
           (definition (assoc-equal name (h2-books-book-proof-definitions proof))))
      (proof-with-checked-results
          ((tag (and (not definition) (proof-term-at name 0)))
           (next (if (and (not definition) (equal tag "sym") (equal (len (cdar facts)) 1))
                     (h2-books-rule-index-add-fact-in index proof name :library)
                   index)))
        (h2-books-index-library (cdr facts) proof next)))))

(defun h2-books-written-pairs (facts reversed)
  (if (endp facts)
      reversed
    (proof-with-checked-results ((written (proof-write (caar facts))))
      (h2-books-written-pairs
       (cdr facts) (cons (cons (concatenate 'string (h2-books-string-set-key written) "\"") written) reversed)))))

(defun h2-books-distinct-written-names (pairs previous)
  (cond ((endp pairs) nil)
        ((equal (cdar pairs) previous) (h2-books-distinct-written-names (cdr pairs) previous))
        (t (cons (cdar pairs) (h2-books-distinct-written-names (cdr pairs) (cdar pairs))))))

(defun h2-books-build-list-rules (proof)
  (let* ((listp (proof-sym "TRUE-LISTP" "ACL2"))
         (tail-test (list listp *library-y*))
         (cons-test (list listp (list *proof-cons* *library-x* *library-y*)))
         (cons-result (h2-books-call-auxiliary proof "TRUE-LISTP-OF-CONS" (proof-eq cons-test tail-test)
                                               '("TRUE-LISTP" nil nil 1 "" nil nil 80))))
    (proof-with-checked-results
        ((cons-name (car cons-result))
         (cdr-result (h2-books-call-auxiliary (cdr cons-result) "TRUE-LISTP-OF-CDR"
                                              (list *library-implies* (list listp *library-x*)
                                                    (list listp (list *library-cdr* *library-x*)))
                                              '("TRUE-LISTP" nil nil 1 "" nil nil 80)))
         (cdr-name (car cdr-result)))
      (h2-books-book-proof-with-list-rules (cdr cdr-result) (list cons-name cdr-name)))))

(defun h2-books-add-initial-logic (proof)
  (let ((cons-proof (h2-books-run-search 1000000 proof :cons-implies-truth nil)))
    (if (failure-p (car cons-proof))
        (car cons-proof)
      (let ((proof (cdr cons-proof)))
        (proof-with-checked-results
            ((search (h2-book-logic-nil-test (h2-books-book-proof-search proof)))
             (search (h2-book-logic-true-boolean search)))
          (h2-books-book-proof-with-search proof search))))))

(defun h2-books-add-initial-arithmetic (proof)
  (proof-with-checked-results
      ((library (h2-arithmetic-integer-order (h2-books-book-proof-library proof)))
       (proof (h2-books-book-proof-with-library proof library))
       (proof (if (assoc-equal (proof-sym "NFIX" "ACL2") (h2-books-book-proof-definitions proof))
                  (h2-books-book-proof-index-lemmas proof)
                proof))
       (library (h2-division-product-order (h2-books-book-proof-library proof))))
    (h2-books-book-proof-with-library proof library)))

(defun h2-books-add-math-rules (proof)
  (proof-with-checked-results
      ((library (h2-calculation-number-sums (h2-books-book-proof-library proof)))
       (subtraction (h2-division-subtraction-descent library))
       (count (h2-division-count-of-natural (cdr subtraction))))
    (h2-books-book-proof-with-math-rules
     (h2-books-book-proof-with-library proof (cdr count))
     (append *h2-calculation-number-rules* (list (car subtraction) (car count))))))

(defun h2-books-book-proof-init (library)
  (proof-with-checked-results
      ((recipes (h2-recipes-recipes-init))
       (empty (h2-books-rule-index-init))
       (proof (h2-books-make-book-proof recipes nil nil nil nil empty empty *h2-books-ground-packages* nil nil nil))
       (proof (h2-books-admit-library library proof))
       (proof (h2-books-add-initial-logic proof))
       (proof (h2-books-add-initial-arithmetic proof))
       (proof (h2-books-build-list-rules proof))
       (proof (h2-books-book-proof-empty-count-bound proof))
       (index (h2-books-index-library (h2-books-book-proof-facts proof) proof (h2-books-book-proof-library-rules proof)))
       (proof (h2-books-book-proof-with-library-rules proof index))
       (proof (h2-books-add-math-rules proof))
       (written (h2-books-written-pairs (h2-books-book-proof-facts proof) nil)))
    (h2-books-book-proof-with-names-as-written
     proof (h2-books-distinct-written-names (acl2::merge-sort-lexorder written) nil))))

(defun h2-books-unchanged-calls (calls variable definitions)
  (if (endp calls)
      nil
    (let* ((call (car calls))
           (unchanged (and (member-equal (car call) definitions)
                           (not (member-equal variable (h2-search-variables call)))))
           (rest (h2-books-unchanged-calls (cdr calls) variable definitions)))
      (if unchanged (cons call rest) rest))))

(defun h2-books-induct-folded (proof formula variable definitions)
  (let ((calls (h2-books-calls-in formula))
        (saved (h2-books-book-proof-fixed-calls proof)))
    (if (failure-p calls)
        (cons calls proof)
      (let* ((folded (h2-books-book-proof-keep-folded proof (h2-books-unchanged-calls calls variable definitions)))
             (result (h2-books-run-indexed-search 1000000 folded :list-induction (list formula variable nil 1))))
        (cons (car result) (h2-books-book-proof-with-fixed-calls (cdr result) saved))))))

(defun h2-books-book-proof-calls-of (proof function)
  (let ((definition (assoc-equal function (h2-books-book-proof-definitions proof))))
    (if definition
        (termination-recursive-calls *proof-nil* (list definition))
      '(:failure "failure" ""))))

(defun h2-books-index-definition-calls (definitions index)
  (if (endp definitions)
      index
    (let* ((definition (car definitions))
           (name (car definition))
           (formals (if (equal (cadr definition) *proof-nil*) nil (cadr definition)))
           (definition (list name formals (caddr definition)))
           (calls (termination-recursive-calls *proof-nil* (list definition))))
      (h2-books-index-definition-calls
       (cdr definitions) (cons (list name (cdr definition) calls) index)))))

(defun h2-books-book-proof-prepare-calls (proof)
  (let ((calls (h2-books-index-definition-calls (h2-books-book-proof-definitions proof) nil)))
    (update-nth 12 (cons :h2-recursions calls) proof)))

(defun h2-books-book-proof-note-definition-calls (proof definitions)
  (let ((calls (h2-books-index-definition-calls definitions (cdr (nth 12 proof)))))
    (update-nth 12 (cons :h2-recursions calls) proof)))

(defun h2-books-prepared-calls-of (proof function)
  (let* ((index (nth 12 proof))
         (record (and (eq (car index) :h2-recursions) (assoc-equal function (cdr index))))
         (definition (and record (assoc-equal function (h2-books-book-proof-definitions proof)))))
    (if (and definition (equal (cdr definition) (cadr record)))
        (caddr record)
      (h2-books-book-proof-calls-of proof function))))

(defun h2-books-bindings (pairs bindings)
  (if (endp pairs)
      bindings
    (h2-books-bindings (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun h2-books-call-updates (pairs bindings)
  (cond ((endp pairs) nil)
        ((proof-compound (caar pairs)) (h2-books-call-updates (cdr pairs) bindings))
        (t
         (proof-with-checked-results ((actual (termination-logical-body (cadar pairs)))
                                      (new (proof-subst actual bindings))
                                      (rest (h2-books-call-updates (cdr pairs) bindings)))
           (if (equal (caar pairs) new) rest (cons (list (caar pairs) new) rest))))))

(defun h2-books-distinct-update-variables-p (updates seen)
  (or (endp updates)
      (and (not (member-equal (caar updates) seen))
           (h2-books-distinct-update-variables-p (cdr updates) (cons (caar updates) seen)))))

(defun h2-books-update-measure (old new)
  (proof-with-checked-results ((selector (h2-books-appropriate-descent old new)))
    (if selector
        (list *library-count* old)
      (proof-with-checked-results ((subtracts (h2-books-subtraction old new)))
        (and subtracts (list *library-nfix* old))))))

; A pending item visits terms, the calls for one term, or the updates of one call.
(defun h2-books-next-induction-plan (n proof pending seen)
  (declare (xargs :measure (nfix n)))
  (cond
   ((h2-books-out-of-fuel-p n) '(:failure "fuel" "h2-books-next-induction-plan"))
   ((endp pending) nil)
   (t
    (let* ((item (car pending))
           (rest (cdr pending))
           (contents (cadr item)))
      (cond
       ((endp contents) (h2-books-next-induction-plan (1- n) proof rest seen))
       ((eq (car item) :terms)
        (let* ((term (car contents))
               (definition (assoc-equal (car term) (h2-books-book-proof-definitions proof)))
               (rest (cons (list :terms (cdr contents)) rest)))
          (if (not definition)
              (h2-books-next-induction-plan (1- n) proof rest seen)
            (proof-with-checked-results ((calls (h2-books-prepared-calls-of proof (car term))))
              (h2-books-next-induction-plan
               (1- n) proof (cons (list :calls calls (cdr term) (cadr definition)) rest) seen)))))
       ((eq (car item) :calls)
        (let* ((actuals (caddr item))
               (formals (cadddr item))
               (bindings (h2-books-bindings (seq-zip formals actuals) nil))
               (rest (cons (list :calls (cdr contents) actuals formals) rest)))
          (proof-with-checked-results
              ((updates (h2-books-call-updates (seq-zip actuals (termination-call-actuals (car contents))) bindings)))
            (let* ((updates (proof-unique updates))
                   (next (if (h2-books-distinct-update-variables-p updates nil)
                             (cons (list :updates updates updates) rest)
                           rest)))
              (h2-books-next-induction-plan (1- n) proof next seen)))))
       (t
        (let* ((update (car contents))
               (updates (caddr item))
               (rest (cons (list :updates (cdr contents) updates) rest)))
          (proof-with-checked-results ((measure (h2-books-update-measure (car update) (cadr update))))
            (let ((candidate (and measure (list measure updates))))
              (if (and candidate (not (member-equal candidate seen)))
                  (list candidate rest (cons candidate seen))
                (h2-books-next-induction-plan (1- n) proof rest seen)))))))))))

(defun h2-books-statement-assumptions (clause core)
  (if (endp clause)
      nil
    (let ((literal (car clause)))
      (proof-with-checked-results
          ((step (if (proof-is-call literal *proof-not*)
                     (proof-with-checked-results ((test (proof-term-at literal 1)))
                       (proof-proof-assume core test t))
                   (proof-proof-assume core literal nil)))
           (rest (h2-books-statement-assumptions (cdr clause) core)))
        (cons step rest)))))

(defun h2-books-subsume-result (result clause)
  (let ((step (car result)) (proof (cdr result)))
    (if (failure-p step) result
      (cons (proof-proof-subsume (h2-books-book-proof-core proof) step clause) proof))))

(defun h2-books-ordinality-fallback (proof measure goal clause)
  (let ((library (h2-books-book-proof-library proof)))
    (cond ((proof-is-call measure *library-nfix*)
           (cons (library-library-cite library "NFIX-ORDINAL" (cdr measure) nil) proof))
          ((proof-is-call measure *h2-ranges-book-nfix*)
           (cons
            (proof-with-checked-results
                ((ordinal (library-library-cite library "NFIX-ORDINAL" (cdr measure) nil))
                 (fixer (h2-ranges-numeric-fixer (h2-books-book-proof-search proof) measure)))
              (library-library-transport-argument library ordinal fixer 1))
            proof))
          (t (h2-books-subsume-result (h2-books-book-proof-solve proof goal nil nil) clause)))))

(defun h2-books-termination-ordinality (proof goal clause)
  (let ((measure (proof-term-at goal 1)))
    (if (failure-p measure)
        (cons measure proof)
      (let ((step (proof-with-checked-results ((ordinal (descent-measure-ordinal (h2-books-book-proof-library proof) measure)))
                    (proof-proof-subsume (h2-books-book-proof-core proof) ordinal clause))))
        (if (and (failure-p step) (member-equal (cadr step) '("value" "key")))
            (h2-books-ordinality-fallback proof measure goal clause)
          (cons step proof))))))

(defun h2-books-termination-decrease (proof goal clause)
  (let* ((core (h2-books-book-proof-core proof))
         (assumptions (h2-books-statement-assumptions (butlast clause 1) core)))
    (if (failure-p assumptions)
        (cons assumptions proof)
      (let* ((builtin (descent-direct-builtin (h2-books-book-proof-library proof) clause nil))
             (direct (cond ((failure-p builtin) builtin)
                           ((car builtin) (car builtin))
                           (t (h2-ranges-affine-decrease (h2-books-book-proof-search proof) goal assumptions)))))
        (h2-books-subsume-result
         (if direct (cons direct proof) (h2-books-book-proof-solve proof goal assumptions nil)) clause)))))

(defun h2-books-termination-clause (proof clause)
  (if (endp clause)
      (cons '(:failure "failure" "") proof)
    (let* ((goal (car (last clause)))
           (head (and (endp (cdr clause)) (proof-term-at goal 0))))
      (cond ((failure-p head) (cons head proof))
            ((equal head *proof-ordinalp*) (h2-books-termination-ordinality proof goal clause))
            (t (h2-books-termination-decrease proof goal clause))))))

(defun h2-books-mentions-mod-p (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((calls (h2-books-calls-in (car terms))))
      (or (h2-books-any-call-p calls (list *h2-modular-mod*))
          (h2-books-mentions-mod-p (cdr terms))))))

(defun h2-books-call-mentions-mod-p (calls)
  (if (endp calls)
      nil
    (proof-with-checked-results ((mentions (h2-books-mentions-mod-p (termination-call-actuals (car calls)))))
      (or mentions (h2-books-call-mentions-mod-p (cdr calls))))))

(defun h2-books-definition-facts (proof names recorded)
  (let ((recipe (if (member-equal *h2-modular-mod* names)
                    :remainder-step
                  (and (assoc-equal *h2-modular-mod* (h2-books-book-proof-definitions proof))
                       (proof-with-checked-results ((uses-mod (h2-books-call-mentions-mod-p recorded)))
                         (and uses-mod :remainder-count-bound))))))
    (cond ((failure-p recipe) (cons recipe proof))
          ((not recipe) (cons nil proof))
          (t
           (let ((result (h2-books-run-search 1000000 proof recipe (list (h2-books-book-proof-recipes proof)))))
             (if (failure-p (car result)) result (cons (list (car result)) (cdr result))))))))

(defun h2-books-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0))
                                 (rest (h2-books-definition-names (cdr definitions))))
      (cons name rest))))

(defun h2-books-definition-ordinal-measures-p (names measures)
  (if (endp names)
      t
    (let ((extra (assoc-equal (car names) measures)))
      (and extra
           (proof-with-checked-results ((relation (proof-term-at (cdr extra) 1)))
             (and (equal relation *proof-ordinal-less*)
                  (h2-books-definition-ordinal-measures-p (cdr names) measures)))))))

(defun h2-books-definition-measure-aids (names measures)
  (if (endp names)
      nil
    (proof-with-checked-results ((measure (proof-term-at (table-get measures (car names) nil) 0))
                                 (rest (h2-books-definition-measure-aids (cdr names) measures)))
      (cons measure rest))))

(defun h2-books-definition-arities-product (definitions)
  (if (endp definitions)
      1
    (proof-with-checked-results ((fields (proof-list-of-length (car definitions) 3))
                                 (rest (h2-books-definition-arities-product (cdr definitions))))
      (let ((formals (cadr fields)))
        (* rest (if (equal formals *proof-nil*) 0 (len formals)))))))

(defun h2-books-definition-selector-measures (names selectors)
  (if (endp names)
      nil
    (let ((selector (assoc-equal (car names) selectors)))
      (if (not selector)
          '(:failure "failure" "")
        (proof-with-checked-results ((rest (h2-books-definition-selector-measures (cdr names) selectors)))
          (cons (list *library-count* (cdr selector)) rest))))))

(defun h2-books-definition-call-measure-p (calls formal position subtraction)
  (if (endp calls)
      t
    (proof-with-checked-results
        ((actual (proof-term-at (termination-call-actuals (car calls)) position))
         (actual (termination-logical-body actual))
         (matches (if subtraction (h2-books-subtraction formal actual)
                    (h2-books-appropriate-descent formal actual))))
      (and matches (h2-books-definition-call-measure-p (cdr calls) formal position subtraction)))))

(defun h2-books-definition-formal-plans (formals position recorded)
  (if (endp formals)
      nil
    (let ((formal (car formals)))
      (proof-with-checked-results
          ((descends (h2-books-definition-call-measure-p recorded formal position nil))
           (subtracts (h2-books-definition-call-measure-p recorded formal position t))
           (rest (h2-books-definition-formal-plans (cdr formals) (1+ position) recorded)))
        (append (and descends (list (list (list *library-count* formal))))
                (and subtracts (list (list (list *library-nfix* formal))))
                rest)))))

(defun h2-books-definition-plans (definitions names recorded measures)
  (proof-with-checked-results
      ((supplied (h2-books-definition-ordinal-measures-p names measures))
       (plan (and supplied (h2-books-definition-measure-aids names measures)))
       (arities (h2-books-definition-arities-product definitions))
       (selectors (and (<= arities 4096) (termination-selector-plan definitions recorded)))
       (selector-plan (and selectors (h2-books-definition-selector-measures names selectors)))
       (formals (and (consp names) (endp (cdr names)) (cadar definitions)))
       (formal-plans (and (not (equal formals *proof-nil*)) (h2-books-definition-formal-plans formals 0 recorded))))
    (proof-unique (append (and supplied (list plan)) (and selectors (list selector-plan)) formal-plans))))

(defun h2-books-termination-proofs (clauses proof reversed)
  (if (endp clauses)
      (cons (reverse reversed) proof)
    (let ((result (h2-books-termination-clause proof (car clauses))))
      (if (failure-p (car result))
          result
        (h2-books-termination-proofs (cdr clauses) (cdr result) (cons (car result) reversed))))))

(defun h2-books-prove-measure-plan (proof plan definitions names recorded)
  (let* ((map (h2-books-bindings (seq-zip names plan) nil))
         (clauses (termination-obligations definitions map recorded)))
    (if (failure-p clauses)
        (cons clauses proof)
      (let ((result (h2-books-termination-proofs clauses proof nil)))
        (if (failure-p (car result))
            result
          (let ((entry (proof-with-checked-results ((name (proof-term-at names 0)))
                         (proof-proof-entry "measure" name (cons name plan) (car result)))))
            (cons entry (cdr result))))))))

(defun h2-books-try-definition-plans (plans proof facts definitions names recorded)
  (if (endp plans)
      (cons *h2-books-unproved* proof)
    (let* ((plan (car plans))
           (arithmetic (h2-books-any-call-p plan (list *library-nfix*)))
           (proof (h2-books-book-proof-with-arithmetic proof arithmetic))
           (configured (h2-books-book-proof-configure-book proof (list (proof-sym "HARD-ERROR" "ACL2"))
                                                           nil facts arithmetic)))
      (if (failure-p configured)
          (cons configured proof)
        (let ((result (h2-books-prove-measure-plan (h2-books-book-proof-with-fuel configured 13000)
                                                    plan definitions names recorded)))
          (if (h2-books-unproved-p (car result))
              (h2-books-try-definition-plans (cdr plans) (cdr result) facts definitions names recorded)
            result))))))

(defun h2-books-prove-definition (proof data measures)
  (let* ((proof (h2-books-book-proof-with-arithmetic proof nil))
         (definitions (cdr data))
         (prepared (if (endp data)
                       '(:failure "failure" "")
                     (proof-with-checked-results ((recorded (termination-recursive-calls (car data) definitions))
                                                  (names (h2-books-definition-names definitions)))
                       (list recorded names)))))
    (if (failure-p prepared)
        (cons prepared proof)
      (let* ((recorded (car prepared))
             (names (cadr prepared))
             (result (h2-books-definition-facts proof names recorded))
             (facts (car result))
             (proof (cdr result)))
        (if (failure-p facts)
            result
          (let ((plans (h2-books-definition-plans definitions names recorded measures)))
            (if (failure-p plans)
                (cons plans proof)
              (h2-books-try-definition-plans plans proof facts definitions names recorded))))))))

(defun h2-books-focused-updated (proof updated)
  (if (failure-p updated) (cons updated proof) (cons nil updated)))

(mutual-recursion
 (defun h2-books-answer-operation (n proof operation args)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:failure "fuel" "h2-books-answer-operation") proof)
     (case operation
       (:library (cons (h2-books-book-proof-library proof) proof))
       (:with-library (cons nil (h2-books-book-proof-with-library proof (car args))))
       (:list-rules (cons (h2-books-book-proof-list-rules proof) proof))
       (:configure
        (let* ((search (h2-books-book-proof-search proof))
               (configured (h2-search-search-configure search (car args) (cadr args) (caddr args) (cadddr args))))
          (if (failure-p configured) (cons configured proof)
            (cons nil (h2-books-book-proof-with-search proof configured)))))
       (:configure-book
        (h2-books-focused-updated proof (h2-books-book-proof-configure-book proof (car args) (cadr args) (caddr args) (cadddr args))))
       (:set-fuel (cons nil (h2-books-book-proof-with-fuel proof (car args))))
       (:induct-with-folded-calls (h2-books-induct-folded proof (car args) (cadr args) (caddr args)))
       (:keep-folded (cons (h2-books-book-proof-fixed-calls proof) (h2-books-book-proof-keep-folded proof (car args))))
       (:restore-fixed-calls (cons nil (h2-books-book-proof-with-fixed-calls proof (car args))))
       (:derive (h2-books-call-derive proof args))
       (:auxiliary (h2-books-call-auxiliary proof (car args) (cadr args) (cddr args)))
       (:solve (h2-books-book-proof-solve proof (car args) (cadr args) (caddr args)))
       (:lemma (h2-books-focused-updated proof (h2-books-add-lemma proof (car args) (cadr args) (caddr args) (cadddr args))))
       (:search
        (let ((recipe (if (member-eq (car args) '(:compression-lookup-assoc-returned-key
                                                 :compression-lookup-range-decrease :compression-lookup-list-parts
                                                 :compression-lookup-lookup-singleton :compression-lookup-compression-laws))
                          :compression-search :book-recipe)))
          (h2-books-run-search 1000000 proof recipe args)))
       (:recipes (h2-books-run-search 1000000 proof :book-recipes (cons (h2-books-book-proof-recipes proof) args)))
       ((:compression-lookup-theorem :compressed-aref)
        (h2-books-run-compression (1- n) proof operation args nil))
       (otherwise (cons '(:failure "failure" "") proof)))))

 (defun h2-books-run-compression (n proof operation args replies)
   (declare (xargs :measure (nfix n)))
   (if (h2-books-out-of-fuel-p n)
       (cons '(:failure "fuel" "h2-books-run-compression") proof)
     (let ((result (h2-compression-lookup-call-with-replies proof operation args replies)))
       (cond ((failure-p result) (cons result proof))
             ((h2-compression-lookup-request-p result)
              (let ((reply (h2-books-answer-operation (1- n) (h2-compression-lookup-request-proof result)
                                                      (h2-compression-lookup-request-operation result)
                                                      (h2-compression-lookup-request-args result))))
                (h2-books-run-compression (1- n) proof operation args (append replies (list reply)))))
             (t result))))))

(defun h2-books-answer-focused (request)
  (h2-books-answer-operation 1000000 (h2-book-recipes-request-proof request)
                             (h2-book-recipes-request-operation request)
                             (h2-book-recipes-request-args request)))

(defun h2-books-run-focused (n proof name formula replies)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      (cons '(:failure "fuel" "h2-books-run-focused") proof)
    (let ((result (h2-book-recipes-focused-proof-with-replies proof name formula replies)))
      (cond ((failure-p result) (cons result proof))
            ((h2-book-recipes-request-p result)
             (h2-books-run-focused (1- n) proof name formula
                                    (append replies (list (h2-books-answer-focused result)))))
            (t result)))))

(defun h2-books-match-formulas (formulas proof formula)
  (if (endp formulas)
      nil
    (let ((row (car formulas)))
      (proof-with-checked-results ((match (h2-search-match (cadr row) formula nil)))
        (if (car match)
            (proof-proof-fact (h2-books-book-proof-core proof) (car row) (table-items (cdr match)))
          (h2-books-match-formulas (cdr formulas) proof formula))))))

(defun h2-books-find-matching-formula (indexes proof formula)
  (if (endp indexes)
      nil
    (let ((index (car indexes)))
      (proof-with-checked-results ((formulas (h2-books-rule-index-lookup index (h2-books-rule-index-formulas index) formula)))
        (or (h2-books-match-formulas formulas proof formula)
            (h2-books-find-matching-formula (cdr indexes) proof formula))))))

(defun h2-books-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h2-books-evaluate-theorem (proof formula)
  (let* ((proof (h2-books-book-proof-with-fuel proof 2300))
         (result (h2-books-run-search 1000000 proof :evaluate
                                      (list formula (h2-books-book-proof-packages proof) 2300)))
         (evaluation (car result))
         (proof (cdr result))
         (value (if (failure-p evaluation) evaluation (h2-books-step-right evaluation))))
    (cond ((failure-p value) (cons value proof))
          ((equal value *proof-false*) (cons nil proof))
          (t
           (let* ((result (h2-books-run-search 1000000 proof :truth (list value (h2-search-context-init) nil)))
                  (truth (car result))
                  (proof (cdr result)))
             (if (failure-p truth) result
               (cons (proof-proof-transport (h2-books-book-proof-core proof) (car truth) evaluation) proof)))))))

(defun h2-books-signed-derive (proof search request)
  (let* ((proof (h2-books-book-proof-with-search proof search))
         (saved (h2-books-book-proof-fixed-calls proof))
         (proof (h2-books-book-proof-keep-folded proof (h2-alist-recognizers-request-folded request)))
         (result (h2-books-call-derive proof (h2-alist-recognizers-request-arguments request))))
    (cons (car result) (h2-books-book-proof-with-fixed-calls (cdr result) saved))))

(defun h2-books-run-signed-identity (n proof search formula replies)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      (cons '(:failure "fuel" "h2-books-run-signed-identity") proof)
    (let ((result (h2-calculation-signed-identity-with-replies search formula replies)))
      (cond ((failure-p result) (cons result proof))
            ((h2-alist-recognizers-request-p (car result))
             (let ((answer (h2-books-signed-derive proof (cdr result) (car result))))
               (if (failure-p (car answer))
                   answer
                 (h2-books-run-signed-identity
                  (1- n) (cdr answer) search formula
                  (append replies (list (cons (car answer) (h2-books-book-proof-search (cdr answer)))))))))
            (t (cons (car result) (h2-books-book-proof-with-search proof (cdr result))))))))

(defun h2-books-specialized-theorem (stages proof name formula)
  (if (endp stages)
      (cons nil proof)
    (let* ((stage (car stages))
           (result (case stage
                     (:signed-identity (h2-books-run-signed-identity 1000000 proof (h2-books-book-proof-search proof) formula nil))
                     (:canonical-argument
                      (cons (h2-equivalence-canonical-argument
                             (h2-books-book-proof-library proof) formula
                             (h2-books-rule-index-formulas (h2-books-book-proof-book-rules proof))
                             (h2-books-rule-index-formulas (h2-books-book-proof-library-rules proof)))
                            proof))
                     (:focused (h2-books-run-focused 1000000 proof name formula nil))
                     (otherwise (h2-books-run-search 1000000 proof stage (list formula))))))
      (if (car result) result (h2-books-specialized-theorem (cdr stages) (cdr result) name formula)))))

(defun h2-books-functions-in (calls definitions)
  (if (endp calls)
      nil
    (let ((function (caar calls)))
      (if (assoc-equal function definitions)
          (cons function (h2-books-functions-in (cdr calls) definitions))
        (h2-books-functions-in (cdr calls) definitions)))))

(defun h2-books-short-functions (functions proof)
  (if (endp functions)
      nil
    (let* ((name (car functions))
           (definition (assoc-equal name (h2-books-book-proof-definitions proof)))
           (short (and (< (h2-search-size (caddr definition)) 90) t)))
      (proof-with-checked-results
          ((calls (and short (h2-books-prepared-calls-of proof name)))
           (rest (h2-books-short-functions (cdr functions) proof)))
        (if (and short (not calls))
            (cons name rest)
          rest)))))

(defun h2-books-small-definitions (names definitions maximum)
  (if (endp names)
      nil
    (let ((definition (assoc-equal (car names) definitions)))
      (if (and definition (<= (h2-search-size (caddr definition)) maximum))
          (cons (car names) (h2-books-small-definitions (cdr names) definitions maximum))
        (h2-books-small-definitions (cdr names) definitions maximum)))))

(defun h2-books-theorem-hint-facts (hints definitions facts)
  (if (endp hints)
      nil
    (let ((name (car hints)))
      (if (and (assoc-equal name facts) (not (assoc-equal name definitions)))
          (cons name (h2-books-theorem-hint-facts (cdr hints) definitions facts))
        (h2-books-theorem-hint-facts (cdr hints) definitions facts)))))

(defun h2-books-open-functions (functions definitions)
  (if (endp functions)
      nil
    (let* ((name (car functions))
           (body (caddr (assoc-equal name definitions))))
      (if (<= (h2-search-size body) 160)
          (proof-with-checked-results ((calls (h2-books-calls-in body))
                                       (rest (h2-books-open-functions (cdr functions) definitions)))
            (cons name (append (h2-books-small-definitions (h2-books-functions-in calls definitions) definitions 48) rest)))
        (h2-books-open-functions (cdr functions) definitions)))))

(defun h2-books-repeat-functions (functions)
  (if (endp functions)
      nil
    (if (member-equal (car functions) (list (proof-cl "NTH") (proof-sym "MV-NTH" "ACL2") *library-len*))
        (cons (car functions) (h2-books-repeat-functions (cdr functions)))
      (h2-books-repeat-functions (cdr functions)))))

(defun h2-books-theorem-settings (proof target hints)
  (let ((definitions (h2-books-book-proof-definitions proof)))
    (proof-with-checked-results
        ((calls (h2-books-calls-in target))
         (functions (proof-unique (h2-books-functions-in calls definitions)))
         (short (h2-books-short-functions functions proof))
         (facts (h2-books-theorem-hint-facts hints definitions (h2-books-book-proof-facts proof)))
         (open (h2-books-open-functions functions definitions)))
      (let ((opened (proof-unique (append short (h2-books-small-definitions hints definitions 240) open))))
        (list short opened (h2-books-repeat-functions opened) facts calls)))))

(defun h2-books-wrap-theorem-result (result wrappers)
  (let ((step (car result)) (proof (cdr result)))
    (if (or (not wrappers) (not step) (failure-p step))
        result
      (cons (proof-proof-transport (h2-books-book-proof-core proof) step wrappers) proof))))

(defun h2-books-solve-theorem-attempt (proof target wrappers opened repeat facts fuel dynamic)
  (let ((configured (h2-books-book-proof-configure-book proof opened repeat facts dynamic)))
    (if (failure-p configured)
        (cons configured proof)
      (h2-books-wrap-theorem-result
       (h2-books-book-proof-solve (h2-books-book-proof-with-fuel configured fuel) target nil nil)
       wrappers))))

(defun h2-books-try-theorem-solves (attempts proof target wrappers repeat facts)
  (if (endp attempts)
      (cons nil proof)
    (let* ((attempt (car attempts))
           (result (h2-books-solve-theorem-attempt proof target wrappers (car attempt) repeat facts
                                                   (cadr attempt) (caddr attempt))))
      (if (h2-books-unproved-p (car result))
          (h2-books-try-theorem-solves (cdr attempts) (cdr result) target wrappers repeat facts)
        result))))

(defun h2-books-prove-theorem-induction (proof target wrappers plan)
  (let* ((measure (car plan))
         (substitutions (cadr plan))
         (library (h2-books-book-proof-library proof))
         (ordinal (if (equal (car measure) *library-count*)
                      (library-library-builtin library 1 (cadr measure))
                    (library-library-cite library "NFIX-ORDINAL" (list (cadr measure)) nil))))
    (if (failure-p ordinal)
        (cons ordinal proof)
      (h2-books-wrap-theorem-result
       (h2-books-run-indexed-search 1000000 proof :induction (list target measure (list substitutions) ordinal nil))
       wrappers))))

(defun h2-books-try-count-inductions (remaining proof target wrappers opened repeat facts pending seen)
  (declare (xargs :measure (nfix remaining)))
  (let ((next (h2-books-next-induction-plan 1000000 proof pending seen)))
    (cond ((failure-p next) (cons next proof))
          ((or (h2-books-out-of-fuel-p remaining) (not next)) (cons nil proof))
          ((not (equal (caar (car next)) *library-count*))
           (h2-books-try-count-inductions (1- remaining) proof target wrappers opened repeat facts (cadr next) (caddr next)))
          (t
           (let ((configured (h2-books-book-proof-configure-book proof opened repeat facts nil)))
             (if (failure-p configured)
                 (cons configured proof)
               (let ((result (h2-books-prove-theorem-induction (h2-books-book-proof-with-fuel configured 2300)
                                                               target wrappers (car next))))
                 (if (h2-books-unproved-p (car result))
                     (h2-books-try-count-inductions (1- remaining) (cdr result) target wrappers opened repeat facts
                                                     (cadr next) (caddr next))
                   result))))))))

(defun h2-books-try-nfix-induction (n proof target wrappers pending seen)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      (cons '(:failure "fuel" "h2-books-try-nfix-induction") proof)
    (let ((next (h2-books-next-induction-plan 1000000 proof pending seen)))
      (cond ((failure-p next) (cons next proof))
            ((not next) (cons nil proof))
            ((equal (caar (car next)) *library-nfix*)
             (let ((result (h2-books-prove-theorem-induction (h2-books-book-proof-with-fuel proof 3000)
                                                             target wrappers (car next))))
               (if (h2-books-unproved-p (car result)) (cons nil (cdr result)) result)))
            (t (h2-books-try-nfix-induction (1- n) proof target wrappers (cadr next) (caddr next)))))))

(defun h2-books-try-arithmetic-theorem (proof formula target wrappers opened repeat facts pending)
  (let ((calls (h2-books-calls-in formula)))
    (cond ((failure-p calls) (cons calls proof))
          ((not (h2-books-any-call-p calls (list *proof-plus* *proof-minus* *proof-times* *proof-less*)))
           (cons nil proof))
          (t
           (let* ((proof (h2-books-book-proof-with-arithmetic proof t))
                  (result (h2-books-solve-theorem-attempt proof target wrappers opened repeat facts 4800 t)))
             (if (h2-books-unproved-p (car result))
                 (h2-books-try-nfix-induction 1000000 (cdr result) target wrappers pending nil)
               result))))))

(defun h2-books-search-theorem (proof formula hints)
  (let* ((wrappers (h2-search-search-remove-wrappers (h2-books-book-proof-search proof) formula))
         (target (if wrappers (if (failure-p wrappers) wrappers (h2-books-step-right wrappers)) formula))
         (settings (if (failure-p target) target (h2-books-theorem-settings proof target hints))))
    (if (failure-p settings)
        (cons settings proof)
      (let* ((short (nth 0 settings))
             (opened (nth 1 settings))
             (repeat (nth 2 settings))
             (facts (nth 3 settings))
             (pending (list (list :terms (nth 4 settings))))
             (attempts (list (list short 1200 nil) (list opened 2100 nil) (list opened 2200 t)))
             (solved (h2-books-try-theorem-solves attempts proof target wrappers repeat facts))
             (result (if (car solved) solved
                       (h2-books-try-count-inductions 2 (cdr solved) target wrappers opened repeat facts pending nil)))
             (result (if (car result) result
                       (h2-books-try-arithmetic-theorem (cdr result) formula target wrappers opened repeat facts pending))))
        (if (car result)
            result
          (cons *h2-books-unproved* (cdr result)))))))

(defun h2-books-prove-book-theorem (proof name formula hints)
  (let* ((proof (h2-books-book-proof-with-fuel (h2-books-book-proof-with-arithmetic proof nil) 7500))
         (indexes (list (h2-books-book-proof-book-rules proof) (h2-books-book-proof-library-rules proof)))
         (matched (h2-books-find-matching-formula indexes proof formula)))
    (if matched
        (cons matched proof)
      (let* ((closed (if (h2-search-variables formula) (cons nil proof) (h2-books-evaluate-theorem proof formula)))
             (value (car closed)))
        (if (and value (not (h2-books-unproved-p value)))
            closed
          (let* ((proof (h2-books-book-proof-with-fuel (h2-books-book-proof-with-dynamic (cdr closed) nil) 14000))
                 (result (h2-books-specialized-theorem
                          '(:signed-identity :equality-equivalence :canonical-argument :focused) proof name formula)))
            (if (and (car result) (not (h2-books-unproved-p (car result))))
                result
              (h2-books-search-theorem (cdr result) formula hints))))))))

(defun h2-books-answer-witness (proof request)
  (let* ((proof (h2-books-book-proof-with-search proof (h2-witnesses-request-proof request)))
         (args (h2-witnesses-request-args request)))
    (case (h2-witnesses-request-operation request)
      (:calls-in (cons (h2-books-calls-in (car args)) proof))
      (:configure-book
       (let ((configured (h2-books-book-proof-configure-book proof (car args) nil nil (cadr args))))
         (if (failure-p configured)
             (cons configured proof)
           (cons (h2-books-book-proof-search configured) configured))))
      (:solve
       (let ((result (h2-books-book-proof-solve (h2-books-book-proof-with-fuel proof (cadr args)) (car args) nil nil)))
         (cons (cons (car result) (h2-books-book-proof-search (cdr result))) (cdr result))))
      (otherwise (cons '(:failure "failure" "") proof)))))

(defun h2-books-witness-work (data)
  (proof-with-checked-results
      ((data (h2-witnesses-pair data))
       (functions (car data))
       (formulas (cadr data))
       (first (proof-term-at functions 0))
       (root (proof-term-at first 0))
       (text (proof-write root))
       (identifier (text-upper (seq-slice (siphash-hexdigest text) 0 16)))
       (witnesses (h2-witnesses-names functions identifier 0))
       (replacement (h2-witnesses-replacements functions witnesses nil))
       (candidates (h2-witnesses-candidates functions formulas replacement))
       (goals (h2-witnesses-goals formulas replacement)))
    (list root witnesses goals (h2-witnesses-assignments functions candidates))))

(defun h2-books-run-witness (n proof search work count replies)
  (declare (xargs :measure (nfix n)))
  (if (h2-books-out-of-fuel-p n)
      (cons '(:failure "fuel" "h2-books-run-witness") proof)
    (let* ((witnesses (cadr work))
           (result (h2-witnesses-prove-assignments search (cadddr work) (caddr work)
                                                    (car work) witnesses count replies)))
      (cond ((h2-books-unproved-p result)
             (cons result (h2-books-book-proof-with-search
                           proof (h2-witnesses-rollback (h2-books-book-proof-search proof) witnesses count))))
            ((failure-p result) (cons result proof))
            ((h2-witnesses-request-p result)
             (let ((reply (h2-books-answer-witness proof result)))
               (h2-books-run-witness (1- n) (cdr reply) search work count (append replies (list (car reply))))))
            (t (cons (car result) (h2-books-book-proof-with-search proof (cdr result))))))))

(defun h2-books-prove-witness (proof data)
  (let ((work (h2-books-witness-work data)))
    (if (failure-p work)
        (cons work proof)
      (let ((count (len (library-library-entries (h2-books-book-proof-library proof))))
            (proof (h2-books-book-proof-with-arithmetic proof nil)))
        (h2-books-run-witness 1000000 proof (h2-books-book-proof-search proof) work count nil)))))

(defun h2-books-theorem-entry (proof data name hints)
  (let ((formula (proof-term-at data 1)))
    (if (failure-p formula)
        (cons formula proof)
      (let ((result (h2-books-prove-book-theorem proof name formula (table-get hints name nil))))
        (if (failure-p (car result)) result
          (cons (proof-proof-entry "theorem" name (list name) (list (car result))) (cdr result)))))))

(defun h2-books-obligation-entry (proof kind data name measures hints)
  (cond ((equal kind "theorem") (h2-books-theorem-entry proof data name hints))
        ((equal kind "define") (h2-books-prove-definition proof data measures))
        ((equal kind "constrain") (h2-books-prove-witness proof data))
        (t (cons '(:failure "failure" "") proof))))

(defun h2-books-find-certificate (proof kind data name measures hints)
  (let* ((result (h2-books-obligation-entry proof kind data name measures hints))
         (entry (car result))
         (proof (cdr result))
         (entries (if (failure-p entry)
                      entry
                    (h2-recipes-recipes-dependencies (h2-books-book-proof-recipes proof) entry))))
    (cond ((h2-books-unproved-p entries)
           (cons (h2-books-make-certificate nil (caddr entries)) proof))
          ((failure-p entries) entries)
          (t (cons (h2-books-make-certificate entries "") proof)))))

