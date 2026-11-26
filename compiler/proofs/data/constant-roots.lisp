(in-package "BOYMOO-PROOFS")

(include-book "map-views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::table-tree-get data-search-tree-p
                     boymoo-compiler::low-bits boymoo-compiler::text-hash ash)))

(local
 (defthm association-occurs-in-the-alist
   (implies (and key (assoc-equal key entries))
            (member-equal (cons key (cdr (assoc-equal key entries))) entries))
   :hints (("Goal" :induct (assoc-equal key entries)))))

(local
 (defthm membership-of-table-enumeration-append
   (iff (member-equal binding (append left right))
        (or (member-equal binding left) (member-equal binding right)))))

(defthmd data-table-lookup-is-an-enumerated-binding
  (let ((value (boymoo-compiler::table-get key hash bits table)))
    (implies (and (data-table-p table bits) (data-table-key-p key) value)
             (member-equal (cons key value) (data-table-bindings table bits))))
  :hints (("Goal" :induct (boymoo-compiler::table-get key hash bits table)
                  :in-theory (enable data-tree-get-is-assoc))))

(defthmd data-index-lookup-is-an-enumerated-binding
  (let ((value (boymoo-compiler::index-get text index)))
    (implies (and (data-table-p index 12) (stringp text) value)
             (member-equal (cons text value) (data-table-bindings index 12))))
  :hints (("Goal" :use ((:instance data-table-lookup-is-an-enumerated-binding
                                   (key text) (hash (boymoo-compiler::text-hash text))
                                   (bits 12) (table index)))
                  :in-theory (disable data-table-bindings data-table-p boymoo-compiler::table-get))))

(local
 (in-theory (disable boymoo-compiler::index-get data-table-bindings data-table-p proof-constant-word
                     proof-view-step proof-view data-static-image-map data-static-word-present-p)))

(local
 (defthm enumerated-word-is-present
   (implies (and (data-static-constant-words-present-p bindings base objects)
                 (member-equal binding bindings))
            (data-static-word-present-p (proof-constant-word (cdr binding)) base objects))
   :hints (("Goal" :induct (data-static-constant-words-present-p bindings base objects)))))

(defthmd data-indexed-constant-word-is-present
  (let* ((entry (boymoo-compiler::index-get text index))
         (word (proof-constant-word entry)))
    (implies (and (data-table-p index 12) (stringp text) word
                  (data-static-constant-words-present-p (data-table-bindings index 12) base objects))
             (data-static-word-present-p word base objects)))
  :hints (("Goal" :use (data-index-lookup-is-an-enumerated-binding
                        (:instance enumerated-word-is-present
                                   (binding (cons text (boymoo-compiler::index-get text index)))
                                   (bindings (data-table-bindings index 12))))
                  :in-theory (e/d (proof-constant-word)
                                 (enumerated-word-is-present data-static-constant-words-present-p)))))

(defun data-constant-binding-texts-p (bindings)
  (if (atom bindings)
      (null bindings)
    (and (stringp (caar bindings)) (data-constant-binding-texts-p (cdr bindings)))))

(defthmd data-constant-map-agreement-transfers-to-discovered-records
  (implies (and (data-table-p index 12) (data-constant-binding-texts-p bindings)
                (data-static-constant-words-present-p (data-table-bindings index 12) base objects)
                (data-static-known-records-p objects witness)
                (data-static-records-children-present-p objects base objects machine))
           (equal (proof-constant-map-p bindings index base objects packages machine)
                  (proof-constant-map-p bindings index base witness packages machine)))
  :hints (("Goal" :induct (data-constant-binding-texts-p bindings)
                  :in-theory (disable data-static-constant-words-present-p
                                      data-static-known-records-p data-static-records-children-present-p))
          ("Subgoal *1/2"
           :use ((:instance data-indexed-constant-word-is-present (text (caar bindings)))
                 (:instance data-view-agrees-with-witness-map
                            (word (proof-constant-word (boymoo-compiler::index-get (caar bindings) index)))))
           :in-theory (disable data-static-constant-words-present-p
                               data-static-known-records-p data-static-records-children-present-p))))

(defthmd data-image-scan-preserves-witness-constant-map
  (implies (and (data-static-image-witness-p base image index machine witness)
                (data-table-p index 12) (data-constant-binding-texts-p bindings))
           (mv-let (ok objects) (data-static-image-map base image index machine)
             (and ok (equal (proof-constant-map-p bindings index base objects packages machine)
                            (proof-constant-map-p bindings index base witness packages machine)))))
  :hints (("Goal" :use ((:instance data-static-image-map-succeeds-for-ranked-graph (constants index))
                        (:instance data-static-map-on-success-covers-roots (constants index))
                        (:instance data-static-image-map-on-success-closes-object-children (constants index))
                        (:instance data-constant-map-agreement-transfers-to-discovered-records
                                   (objects (mv-nth 1 (data-static-image-map base image index machine)))))
                  :in-theory (disable data-static-image-witness-p proof-constant-map-p
                                      data-static-constant-words-present-p data-static-known-records-p
                                      data-static-records-children-present-p))))
