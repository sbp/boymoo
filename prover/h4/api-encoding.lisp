(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-api-encoding-prefix* "H4")
(defconst *h4-api-encoding-owned* "PROVER-H4-")
(defconst *h4-api-encoding-quote-opening* (coerce "(COMMON-LISP::QUOTE " 'list))
(defconst *h4-api-encoding-self-stem* (coerce "ACL2::SELF-" 'list))
(defconst *h4-api-encoding-h4-stem* (coerce "ACL2::H4-" 'list))

(defun h4-api-encoding-ascii-chars-p (chars)
  (or (endp chars)
      (and (< (char-code (car chars)) 128)
           (h4-api-encoding-ascii-chars-p (cdr chars)))))

(defun h4-api-encoding-ascii-text (source)
  (if (h4-api-encoding-ascii-chars-p (coerce source 'list))
      source
    '(:failure "failure" "")))

(defun h4-api-encoding-name-stem (chars)
  (cond ((reader-prefix-p *h4-api-encoding-self-stem* chars) *h4-api-encoding-self-stem*)
        ((reader-prefix-p *h4-api-encoding-h4-stem* chars) *h4-api-encoding-h4-stem*)
        (t nil)))

(defun h4-api-encoding-contains-name-stem-p (chars)
  (and (consp chars)
       (or (and (eql (car chars) #\A) (consp (h4-api-encoding-name-stem chars)))
           (h4-api-encoding-contains-name-stem-p (cdr chars)))))

(defun h4-api-encoding-delimiter-width (chars delimiter width)
  (cond ((endp chars) nil)
        ((eql (car chars) delimiter) width)
        (t (h4-api-encoding-delimiter-width (cdr chars) delimiter (1+ width)))))

; A failed name also gives the width up to the boundary. Every stem
; within that span would have the same invalid end.
(defun h4-api-encoding-name-end (chars width has-suffix)
  (if (endp chars)
      (cons :skip width)
    (case (car chars)
      ((#\Space #\)) (cons (if has-suffix :text :skip) width))
      ((#\( #\Newline) (cons :skip width))
      (otherwise (h4-api-encoding-name-end (cdr chars) (1+ width) t)))))

(defun h4-api-encoding-name-token (chars)
  (let ((stem (h4-api-encoding-name-stem chars)))
    (and stem
         (let ((width (len stem)))
           (h4-api-encoding-name-end (nthcdr width chars) width nil)))))

(defun h4-api-encoding-token (chars previous names-only)
  (let ((current (car chars)))
    (cond
     ((eql current #\A)
      (and (or names-only (eql previous #\Space) (eql previous #\())
           (let ((token (h4-api-encoding-name-token chars)))
             (and (or names-only (eq (car token) :text)) token))))
     (names-only nil)
     ((eql current #\()
      (if (reader-prefix-p *h4-api-encoding-quote-opening* chars)
          (cons :quotation (len *h4-api-encoding-quote-opening*))
        '(:open . 1)))
     ((eql current #\)) '(:close . 1))
     ((or (eql current #\") (eql current #\|))
      (let ((width (h4-api-encoding-delimiter-width (cdr chars) current 2)))
        (and width (cons :text width))))
     (t nil))))

(defun h4-api-encoding-join-pieces (pieces chars)
  (if (endp pieces)
      chars
    (h4-api-encoding-join-pieces (cdr pieces) (append (car pieces) chars))))

; CHARS is the unscanned suffix. SKIP counts bytes already recognized as
; part of a token. CHUNK starts after the last replacement, and WIDTH
; counts its unchanged bytes through the last recognized token.
(defun h4-api-encoding-rename-scan
    (chars aliases names-only previous skip depth quotation chunk width pieces)
  (cond
   ((endp chars)
    (and (consp pieces) (coerce (h4-api-encoding-join-pieces pieces chunk) 'string)))
   ((< 0 skip)
    (h4-api-encoding-rename-scan
     (cdr chars) aliases names-only (car chars) (1- skip) depth quotation chunk width pieces))
   (t
    (let* ((token (h4-api-encoding-token chars previous names-only))
           (kind (car token))
           (token-width (if token (cdr token) 1))
           (change (and (eq kind :text) (not quotation)
                        (assoc-equal (coerce (take token-width chars) 'string) aliases))))
      (h4-api-encoding-rename-scan
       (cdr chars) aliases names-only (car chars) (1- token-width)
       (cond ((or (eq kind :quotation) (eq kind :open)) (1+ depth))
             ((eq kind :close) (1- depth))
             (t depth))
       (cond ((and (eq kind :quotation) (not quotation)) (1+ depth))
             ((and (eq kind :close) (equal quotation depth)) nil)
             (t quotation))
       (if change (nthcdr token-width chars) chunk)
       (if change 0 (+ width token-width))
       (if change (list* (coerce (cdr change) 'list) (take width chunk) pieces) pieces))))))

(defun h4-api-encoding-rename (source aliases names-only)
  (or (and aliases
           (let ((chars (coerce source 'list)))
             (and (h4-api-encoding-contains-name-stem-p chars)
                  (h4-api-encoding-rename-scan chars aliases names-only nil 0 0 nil chars 0 nil))))
      source))

(defun h4-api-encoding-mentions (chars skip mentions)
  (cond
   ((endp chars) mentions)
   ((< 0 skip) (h4-api-encoding-mentions (cdr chars) (1- skip) mentions))
   (t
    (let* ((token (and (eql (car chars) #\A) (h4-api-encoding-name-token chars)))
           (width (if token (cdr token) 1)))
      (h4-api-encoding-mentions
       (cdr chars) (1- width)
       (if (eq (car token) :text)
           (cons (coerce (take width chars) 'string) mentions)
         mentions))))))

(defun h4-api-encoding-alias-table (pairs aliases)
  (if (endp pairs)
      aliases
    (h4-api-encoding-alias-table
     (cdr pairs) (table-put aliases (caar pairs) (cadar pairs)))))

(defun h4-api-encoding-dependencies (aliases mentions)
  (cond ((endp aliases) nil)
        ((member-equal (caar aliases) mentions)
         (cons (list (caar aliases) (cdar aliases))
               (h4-api-encoding-dependencies (cdr aliases) mentions)))
        (t (h4-api-encoding-dependencies (cdr aliases) mentions))))

(defun h4-api-encoding-lemma-text (content old new)
  (let ((chars (coerce content 'list))
        (header (coerce (concatenate 'string "(lemma " old " ") 'list)))
    (if (reader-prefix-p header chars)
        (coerce (append (coerce (concatenate 'string "(lemma " new " ") 'list)
                        (nthcdr (len header) chars))
                'string)
      '(:failure "failure" ""))))

(defun h4-api-encoding-owned-entry (kind name source dependencies names-only)
  (proof-with-checked-results
   ((old (proof-write name))
    (content (h4-api-encoding-rename
              source (h4-api-encoding-alias-table dependencies nil) names-only))
    (digest (text-upper (siphash-hexdigest content)))
    (parts (text-split-max old "::" 1))
    (namespace (if (consp (cdr parts))
                   (car parts)
                 '(:failure "failure" "")))
    (label (text-split-max (cadr parts) "-" 1))
    (stem (if (consp (cdr label))
              (cadr label)
            '(:failure "failure" ""))))
   (let ((new (concatenate 'string namespace "::" *h4-api-encoding-owned* stem "-" digest)))
     (proof-with-checked-results
      ((output (cond ((equal kind "lemma")
                      (h4-api-encoding-lemma-text content old new))
                     ((equal kind "define")
                      (h4-api-encoding-rename content (list (cons old new)) names-only))
                     (t '(:failure "failure" ""))))
       (text (h4-api-encoding-ascii-text output)))
      (list new text)))))

(defun h4-api-encoding-remember (key value cache capacity)
  (let ((rest (table-without cache key)))
    (acons key value (take (min (1- capacity) (len rest)) rest))))

(defun h4-api-encoding-owned-request (entry aliases names-only)
  (proof-with-checked-results
      ((entry (proof-list-of-length entry 4))
       (kind (car entry))
       (name (cadr entry))
       (source (cadddr entry))
       (old (proof-write name))
       (mentions (and aliases (h4-api-encoding-mentions (coerce source 'list) 0 nil)))
       (dependencies (h4-api-encoding-dependencies aliases mentions)))
    (cons old (list kind name source dependencies names-only))))

(defun h4-api-encoding-owned-entries-loop-with-cache (entries aliases names-only output cache)
  (if (endp entries)
      (cons (list (reverse output) (table-items aliases)) cache)
    (let ((request (h4-api-encoding-owned-request (car entries) aliases names-only)))
      (if (failure-p request)
          (cons request cache)
        (let* ((key (cdr request))
               (hit (and (not (eq cache :uncached)) (assoc-equal key cache)))
               (owned (if hit
                          (cdr hit)
                        (h4-api-encoding-owned-entry
                         (car key) (cadr key) (caddr key) (cadddr key) (nth 4 key)))))
          (if (failure-p owned)
              (cons owned cache)
            (h4-api-encoding-owned-entries-loop-with-cache
             (cdr entries) (table-put aliases (car request) (car owned)) names-only
             (cons (cadr owned) output)
             (if (eq cache :uncached)
                 cache
               (h4-api-encoding-remember key owned cache 512)))))))))

(defun h4-api-encoding-owned-entries-loop (entries aliases names-only output)
  (car (h4-api-encoding-owned-entries-loop-with-cache entries aliases names-only output :uncached)))

(defun h4-api-encoding-owned-entries (entries inherited names-only)
  (h4-api-encoding-owned-entries-loop
   entries (h4-api-encoding-alias-table inherited nil) names-only nil))

(defun h4-api-encoding-owned-entries-with-cache (entries inherited names-only cache)
  (h4-api-encoding-owned-entries-loop-with-cache
   entries (h4-api-encoding-alias-table inherited nil) names-only nil cache))
