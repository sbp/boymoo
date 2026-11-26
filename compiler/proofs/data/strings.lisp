(in-package "BOYMOO-PROOFS")

(include-book "reader")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable char floor mod length)))

(local
 (defthm hexadecimal-character-cannot-be-delimiter
   (implies (and (natp digit) (< digit 16) (member-equal delimiter '(#\" #\|)))
            (not (equal (data-hex-digit-character digit) delimiter)))
   :hints (("Goal" :use ((:instance acl2::char-code-code-char-is-identity (acl2::n (+ 48 digit)))
                        (:instance acl2::char-code-code-char-is-identity (acl2::n (+ 55 digit))))
                   :in-theory (disable acl2::char-code-code-char-is-identity)))))

(local
 (defthm hexadecimal-digit-pair-in-range
   (implies (characterp byte)
            (and (natp (floor (char-code byte) 16)) (< (floor (char-code byte) 16) 16)
                 (natp (mod (char-code byte) 16)) (< (mod (char-code byte) 16) 16)))
   :hints (("Goal" :use ((:instance data-floor-bounds (x (char-code byte)) (d 16)))
                   :in-theory (enable mod)))))

(local
 (defthm find-char-skips-three
   (implies (and (integerp count) (<= 3 count)
                 (not (equal (char text start) wanted))
                 (not (equal (char text (+ 1 start)) wanted))
                 (not (equal (char text (+ 2 start)) wanted)))
            (equal (boymoo-compiler::find-char text start count wanted)
                   (boymoo-compiler::find-char text (+ 3 start) (- count 3) wanted)))
   :rule-classes nil
   :hints (("Goal" :expand ((boymoo-compiler::find-char text start count wanted)
                            (boymoo-compiler::find-char text (+ 1 start) (1- count) wanted)
                            (boymoo-compiler::find-char text (+ 2 start) (- count 2) wanted))))))

(defthmd data-canonical-content-has-no-raw-delimiter
  (implies (and (data-escaped-spelling-p characters text start count delimiter)
                (member-equal delimiter '(#\" #\|)) (natp start))
           (equal (boymoo-compiler::find-char text start count delimiter) nil))
  :hints (("Goal" :induct (data-escaped-spelling-p characters text start count delimiter)
                  :in-theory (disable data-hex-digit-character))
          ("Subgoal *1/6" :use ((:instance find-char-skips-three (wanted delimiter))
                                (:instance hexadecimal-digit-pair-in-range (byte (car characters))))
                          :in-theory (disable data-hex-digit-character hexadecimal-digit-pair-in-range))))

(local
 (defthm string-car-of-suffix
   (equal (car (nthcdr index characters)) (nth index characters))
   :hints (("Goal" :induct (nthcdr index characters)))))

(local
 (defthm string-cdr-of-suffix
   (implies (natp index)
            (equal (nthcdr (1+ index) characters) (cdr (nthcdr index characters))))
   :hints (("Goal" :induct (nthcdr index characters)))))

(local
 (defthm string-take-one-step
   (implies (posp count)
            (equal (take count characters) (cons (car characters) (take (1- count) (cdr characters)))))
   :hints (("Goal" :expand ((take count characters))))))

(defthmd data-canonical-content-without-escapes-is-slice
  (implies (and (data-escaped-spelling-p characters text start count delimiter)
                (natp start) (stringp text)
                (not (boymoo-compiler::find-char text start count #\\)))
           (equal (take count (nthcdr start (coerce text 'list))) characters))
  :hints (("Goal" :induct (data-escaped-spelling-p characters text start count delimiter)
                  :in-theory (enable char))))

(defun data-delimited-text-p (text start end characters)
  (let ((delimiter (char text start)))
    (and (stringp text) (natp start) (natp end) (< (+ 1 start) end)
         (<= end (length text))
         (member-equal delimiter '(#\" #\|))
         (equal (char text (1- end)) delimiter)
         (data-escaped-spelling-p characters text (1+ start) (- (- end start) 2) delimiter))))

(defthmd data-decode-canonical-delimited-text
  (implies (data-delimited-text-p text start end characters)
           (equal (boymoo-compiler::decode-part text start end) (coerce characters 'string)))
  :hints (("Goal" :use ((:instance data-canonical-content-has-no-raw-delimiter
                                   (delimiter (char text start)) (start (1+ start))
                                   (count (- (- end start) 2)))
                       (:instance data-canonical-content-without-escapes-is-slice
                                  (delimiter (char text start)) (start (1+ start))
                                  (count (- (- end start) 2)))
                       (:instance data-decode-canonical-escaped-characters
                                  (delimiter (char text start)) (start (1+ start))
                                  (count (- (- end start) 2)) (acc nil)))
                  :in-theory (disable boymoo-compiler::find-char boymoo-compiler::decode-characters
                                      data-escaped-spelling-p nthcdr))))

(defthmd data-decode-canonical-barred-symbol-part
  (let ((part (coerce characters 'string)))
    (implies (and (data-delimited-text-p text start end characters) (equal (char text start) #\|)
                  (or (equal (length part) 0)
                      (not (boymoo-compiler::plain-symbol-part-p part 0 (length part)))))
             (equal (boymoo-compiler::decode-symbol-part text start end) part)))
  :hints (("Goal" :in-theory (e/d (data-decode-canonical-delimited-text)
                                 (data-delimited-text-p boymoo-compiler::decode-part
                                  boymoo-compiler::plain-symbol-part-p)))))
