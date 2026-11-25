(in-package "BOYMOO-MODEL")

(include-book "a64-decode")

(logic)
(set-verify-guards-eagerness 0)

(defun a64-condition (condition nzcv)
  (let* ((n (logbitp 3 nzcv))
         (z (logbitp 2 nzcv))
         (c (logbitp 1 nzcv))
         (v (logbitp 0 nzcv))
         (holds (case (a64-field condition 1 3)
                  (0 z)
                  (1 c)
                  (2 n)
                  (3 v)
                  (4 (and c (not z)))
                  (5 (equal n v))
                  (6 (and (equal n v) (not z)))
                  (otherwise t))))
    (if (and (logbitp 0 condition) (/= condition 15))
        (not holds)
      holds)))

(defun a64-shift (kind width value amount)
  (a64-unsigned width
                (case kind
                  (0 (ash value amount))
                  (1 (ash value (- amount)))
                  (2 (ash (a64-signed width value) (- amount)))
                  (otherwise (a64-ror width value amount)))))

(defun a64-result-flags (width result carry overflow)
  (+ (if (logbitp (1- width) result) 8 0)
     (if (= result 0) 4 0)
     (if carry 2 0)
     (if overflow 1 0)))

(defun a64-exec-move-wide (opc width rd imm position machine)
  (let* ((bits (ash imm position))
         (result (case opc
                   (0 (lognot bits))
                   (2 bits)
                   (otherwise
                    (logior bits
                            (logand (lognot (ash #xffff position))
                                    (a64-read-reg rd width nil machine)))))))
    (a64-write-reg rd width nil result machine)))

(defun a64-exec-arithmetic (opc width rd rn right immediate machine)
  (let* ((left (a64-read-reg rn width immediate machine))
         (subtract (logbitp 1 opc))
         (set-flags (logbitp 0 opc))
         (sum (+ left (if subtract (logxor right (a64-ones width)) right)
                 (if subtract 1 0)))
         (result (a64-unsigned width sum))
         (machine (a64-write-reg rd width (and immediate (not set-flags))
                                 result machine)))
    (if set-flags
        (let* ((signed-right (a64-signed width right))
               (signed-sum (+ (a64-signed width left)
                              (if subtract (- signed-right) signed-right))))
          (a64-set-nzcv (a64-result-flags width result (logbitp width sum)
                                         (/= signed-sum (a64-signed width result)))
                        machine))
      machine)))

(defun a64-exec-logical (opc width rd rn right immediate machine)
  (let* ((left (a64-read-reg rn width nil machine))
         (result (case opc
                   (1 (logior left right))
                   (2 (logxor left right))
                   (otherwise (logand left right))))
         (set-flags (= opc 3))
         (machine (a64-write-reg rd width (and immediate (not set-flags))
                                 result machine)))
    (if set-flags
        (a64-set-nzcv (a64-result-flags width result nil nil) machine)
      machine)))

(defun a64-exec-bitfield (opc width rd rn immr imms wmask tmask machine)
  (let* ((source (a64-read-reg rn width nil machine))
         (low (logand (a64-ror width source immr) wmask))
         (high (if (and (= opc 0) (logbitp imms source))
                   (lognot tmask)
                 0)))
    (a64-write-reg rd width nil (logior high (logand low tmask)) machine)))

(defun a64-register-offset (rm option shift machine)
  (let ((value (a64-read-reg rm (if (logbitp 0 option) 64 32) nil machine)))
    (ash (case option
           (6 (a64-signed 32 value))
           (7 (a64-signed 64 value))
           (otherwise value))
         shift)))

(defun a64-exec-single (opc count rn rt mode offset option shift machine)
  (let* ((base (a64-read-reg rn 64 t machine))
         (delta (if (eq mode :register)
                    (a64-register-offset offset option shift machine)
                  offset))
         (updated (+ base delta))
         (address (if (eq mode :post) base updated))
         (width (* 8 count))
         (machine (if (= opc 1)
                      (a64-write-reg rt width nil (a64-load count address machine)
                                     machine)
                    (a64-store count address (a64-read-reg rt width nil machine)
                               machine))))
    (if (or (eq mode :pre) (eq mode :post))
        (a64-write-reg rn 64 t updated machine)
      machine)))

(defun a64-exec-pair (load rn rt rt2 mode delta machine)
  (let* ((base (a64-read-reg rn 64 t machine))
         (updated (+ base delta))
         (first (if (eq mode :post) base updated))
         (second (+ first 8))
         (machine (if load
                      (a64-write-reg rt2 64 nil (a64-load 8 second machine)
                        (a64-write-reg rt 64 nil (a64-load 8 first machine) machine))
                    (a64-store 8 second (a64-read-reg rt2 64 nil machine)
                      (a64-store 8 first (a64-read-reg rt 64 nil machine) machine)))))
    (if (or (eq mode :pre) (eq mode :post))
        (a64-write-reg rn 64 t updated machine)
      machine)))

(defun a64-exec-branch (target link next)
  (a64-set-pc target
              (if link (a64-write-reg 30 64 nil (a64-pc next) next) next)))

(defun a64-execute (instruction machine)
  (let* ((pc (a64-pc machine))
         (next (a64-set-pc (+ pc 4) machine))
         (args (cdr instruction)))
    (case (car instruction)
      (:address
       (let ((delta (nth 1 args)))
         (a64-write-reg (nth 0 args) 64 nil
                        (if (nth 2 args)
                            (+ (ash (ash pc -12) 12) (ash delta 12))
                          (+ pc delta))
                        next)))
      (:move-wide
       (a64-exec-move-wide (nth 0 args) (nth 1 args) (nth 2 args)
                           (nth 3 args) (nth 4 args) next))
      (:arithmetic-imm
       (a64-exec-arithmetic (nth 0 args) (nth 1 args) (nth 2 args)
                            (nth 3 args) (nth 4 args) t next))
      (:arithmetic-reg
       (let* ((width (nth 1 args))
              (source (a64-read-reg (nth 4 args) width nil machine))
              (right (a64-shift (nth 5 args) width source (nth 6 args))))
         (a64-exec-arithmetic (nth 0 args) width (nth 2 args)
                              (nth 3 args) right nil next)))
      (:logical-imm
       (a64-exec-logical (nth 0 args) (nth 1 args) (nth 2 args)
                         (nth 3 args) (nth 4 args) t next))
      (:logical-reg
       (let* ((width (nth 1 args))
              (source (a64-read-reg (nth 4 args) width nil machine))
              (shifted (a64-shift (nth 5 args) width source (nth 6 args)))
              (right (if (nth 7 args) (logxor shifted (a64-ones width)) shifted)))
         (a64-exec-logical (nth 0 args) width (nth 2 args) (nth 3 args)
                           right nil next)))
      (:bitfield
       (a64-exec-bitfield (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args)
                          (nth 4 args) (nth 5 args) (nth 6 args) (nth 7 args) next))
      (:shift-variable
       (let* ((width (nth 1 args))
              (source (a64-read-reg (nth 3 args) width nil machine))
              (amount (mod (a64-read-reg (nth 4 args) width nil machine) width)))
         (a64-write-reg (nth 2 args) width nil
                        (a64-shift (nth 0 args) width source amount) next)))
      ((:multiply :signed-multiply-high :multiply-subtract :divide)
       (let* ((left (a64-read-reg (nth 1 args) 64 nil machine))
              (right (a64-read-reg (nth 2 args) 64 nil machine))
              (result (case (car instruction)
                        (:multiply (* left right))
                        (:signed-multiply-high
                         (ash (* (a64-signed 64 left) (a64-signed 64 right)) -64))
                        (:multiply-subtract
                         (- (a64-read-reg (nth 3 args) 64 nil machine) (* left right)))
                        (otherwise
                         (cond ((= right 0) 0)
                               ((nth 3 args) (truncate (a64-signed 64 left)
                                                       (a64-signed 64 right)))
                               (t (floor left right)))))))
         (a64-write-reg (nth 0 args) 64 nil result next)))
      (:select
       (let* ((width (nth 0 args))
              (value (if (a64-condition (nth 4 args) (a64-nzcv machine))
                         (a64-read-reg (nth 2 args) width nil machine)
                       (+ (a64-read-reg (nth 3 args) width nil machine)
                          (if (nth 5 args) 1 0)))))
         (a64-write-reg (nth 1 args) width nil value next)))
      (:single
       (a64-exec-single (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args)
                        (nth 4 args) (nth 5 args) (nth 6 args) (nth 7 args) next))
      (:pair
       (a64-exec-pair (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args)
                      (nth 4 args) (nth 5 args) next))
      (:branch
       (a64-exec-branch (+ pc (nth 0 args)) (nth 1 args) next))
      (:branch-cond
       (if (a64-condition (nth 1 args) (a64-nzcv machine))
           (a64-set-pc (+ pc (nth 0 args)) next)
         next))
      (:branch-zero
       (let ((zero (= (a64-read-reg (nth 2 args) (nth 1 args) nil machine) 0)))
         (if (if (nth 3 args) (not zero) zero)
             (a64-set-pc (+ pc (nth 0 args)) next)
           next)))
      (:branch-reg
       (a64-exec-branch (a64-read-reg (nth 0 args) 64 nil machine) (nth 1 args)
                       next))
      (:svc
       (list :svc (nth 0 args) (a64-read-reg 16 64 nil machine)
             (a64-read-reg 8 64 nil machine)))
      (otherwise :undefined))))

(defun a64-step (machine)
  (a64-execute (a64-decode (a64-load 4 (a64-pc machine) machine)) machine))

(defun a64-run (steps start end return-pc machine)
  (declare (xargs :measure (nfix steps)
                  :hints (("Goal" :in-theory (disable a64-step)))))
  (let ((pc (a64-pc machine)))
    (cond ((equal pc return-pc) (mv :return machine))
          ((and start end (or (< pc start) (<= end pc))) (mv :outside machine))
          ((zp steps) (mv :limit machine))
          (t (let ((next (a64-step machine)))
               (cond ((eq next :undefined) (mv :undefined machine))
                     ((eq (car next) :svc) (mv next machine))
                     (t (a64-run (1- steps) start end return-pc next))))))))
