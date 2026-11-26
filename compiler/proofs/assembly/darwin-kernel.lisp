(in-package "BOYMOO-PROOFS")

(include-book "macho-handoff")

(logic)
(set-verify-guards-eagerness 0)

; A reply is a success value or a positive error number. A returning
; SVC consumes the reply and changes X0 and the carry flag.
(defun assembly-darwin-reply-p (reply)
  (and (consp reply)
       (case (car reply)
         (:ok (unsigned-byte-p 64 (cdr reply)))
         (:error (and (posp (cdr reply)) (<= (cdr reply) 4095)))
         (otherwise nil))))

(defun assembly-darwin-signed-reply (reply)
  (if (eq (car reply) :error) (- (cdr reply)) (cdr reply)))

(defun assembly-darwin-write-register (register value world)
  (update-nth 0 (boymoo-model::a64-write-reg register 64 nil value
                                           (proof-world-machine world))
              world))

(defun assembly-darwin-flags (old error)
  (logior (logand old #xd) (if error 2 0)))

(defun assembly-darwin-return-fields (reply world)
  (let* ((machine (proof-world-machine world))
         (flags (assembly-darwin-flags (boymoo-model::a64-nzcv machine)
                                      (eq (car reply) :error)))
         (machine (boymoo-model::a64-write-reg 0 64 nil (cdr reply) machine)))
    (update-nth 0 (boymoo-model::a64-set-nzcv flags machine) world)))

(defun assembly-darwin-return (reply world)
  (assembly-darwin-return-fields reply (proof-svc-return (cdr reply) world)))

(defun assembly-darwin-finish-syscall (reply before after)
  (if (proof-world-stop after)
      (proof-kernel-fault before)
    (assembly-darwin-return-fields reply after)))

(defun assembly-darwin-data-world (world)
  (update-nth 1 (assembly-macho-data-regions (proof-world-regions world)) world))

(defun assembly-darwin-map-arguments-p (world)
  (and (equal (proof-world-reg 2 world) 3)
       (equal (proof-world-reg 4 world) #xffffffffffffffff)
       (equal (proof-world-reg 5 world) 0)))

(defun assembly-darwin-map (reply world)
  (if (and (equal (proof-world-reg 3 world) #x1002)
           (assembly-darwin-map-arguments-p world)
           (or (eq (car reply) :error)
               (<= *assembly-macho-preferred-base* (cdr reply))))
      (let* ((adapted (assembly-darwin-write-register 3 #x4022 world))
             (after (proof-linux-map (assembly-darwin-signed-reply reply) adapted))
             (after (assembly-darwin-write-register 3 (proof-world-reg 3 world) after)))
        (assembly-darwin-finish-syscall reply world after))
    (proof-kernel-fault world)))

; Fixed mapping replaces an existing writable span with zeroes.
; Unmapping clears the same span and removes the mapping.
(defun assembly-darwin-release (unmap reply world)
  (let* ((base (proof-world-reg 0 world))
         (request (proof-world-reg 1 world))
         (page (proof-world-page-size world))
         (size (proof-align-up request page))
         (regions (proof-world-regions world)))
    (cond
     ((not (and (or unmap
                    (and (equal (proof-world-reg 3 world) #x1012)
                         (assembly-darwin-map-arguments-p world)))
                (proof-page-size-p page)
                (equal (mod base page) 0)
                (posp request)
                (proof-covered-p base size :write regions)))
      (proof-kernel-fault world))
     ((eq (car reply) :error) (assembly-darwin-return reply world))
     ((equal (cdr reply) (if unmap 0 base))
      (let* ((after (proof-clear-span base (+ base size) world))
             (after (if unmap
                        (update-nth 1 (proof-remove-region-span base size regions) after)
                      after)))
        (assembly-darwin-return reply after)))
     (t (proof-kernel-fault world)))))

(defun assembly-darwin-svc (event world)
  (let ((number (caddr event))
        (reply (car (proof-world-replies world))))
    (cond
     ((not (and (eq (car event) :svc) (equal (cadr event) #x80)))
      (proof-kernel-fault world))
     ((equal number 1) (proof-world-exit (proof-world-reg 0 world) world))
     ((not (assembly-darwin-reply-p reply)) (proof-kernel-fault world))
     (t
      (case number
        (3 (assembly-darwin-finish-syscall
            reply world (proof-linux-read (assembly-darwin-signed-reply reply) world)))
        (4 (let* ((readable (assembly-darwin-data-world world))
                  (after (proof-linux-write (assembly-darwin-signed-reply reply) readable))
                  (after (update-nth 1 (proof-world-regions world) after)))
             (assembly-darwin-finish-syscall reply world after)))
        (73 (assembly-darwin-release t reply world))
        (197 (if (equal (proof-world-reg 3 world) #x1012)
                 (assembly-darwin-release nil reply world)
               (assembly-darwin-map reply world)))
        (otherwise (proof-kernel-fault world)))))))

(defun assembly-darwin-instruction-access-p (instruction world)
  (proof-instruction-access-p instruction (assembly-darwin-data-world world)))

(defun assembly-darwin-step (world)
  (let ((pc (proof-world-pc world)))
    (cond
     ((proof-world-stop world) world)
     ((not (proof-fetchable-p pc world)) (update-nth 7 :fault world))
     (t
      (let* ((machine (proof-world-machine world))
             (instruction (proof-decode-at pc machine)))
        (cond ((not (assembly-darwin-instruction-access-p instruction world))
               (update-nth 7 :fault world))
              ((eq (car instruction) :svc)
               (assembly-darwin-svc (proof-execute instruction machine) world))
              (t (proof-instruction-effect instruction world))))))))

(defun assembly-darwin-run (fuel cuts world)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable assembly-darwin-step)))))
  (cond ((proof-world-stop world) (mv (proof-world-stop world) world))
        ((member-equal (proof-world-pc world) cuts) (mv :cut world))
        ((zp fuel) (mv :limit world))
        (t (assembly-darwin-run (1- fuel) cuts (assembly-darwin-step world)))))

(local (in-theory (disable proof-execute proof-decode-at proof-fetchable-p
                           proof-instruction-access-p proof-instruction-effect
                           assembly-darwin-instruction-access-p assembly-darwin-svc)))

(defthm assembly-darwin-step-from-instruction
  (implies (and (not (proof-world-stop world))
                (proof-instruction-at-p instruction (proof-world-pc world) world)
                (assembly-darwin-instruction-access-p instruction world))
           (equal (assembly-darwin-step world)
                  (if (eq (car instruction) :svc)
                      (assembly-darwin-svc
                       (proof-execute instruction (proof-world-machine world)) world)
                    (proof-instruction-effect instruction world))))
  :rule-classes nil)

(defthm assembly-darwin-svc-step-uses-x16
  (let ((instruction '(:svc #x80)))
    (implies (and (not (proof-world-stop world))
                  (proof-instruction-at-p instruction (proof-world-pc world) world)
                  (assembly-darwin-instruction-access-p instruction world))
             (equal (assembly-darwin-step world)
                    (assembly-darwin-svc
                     (list :svc #x80 (proof-world-reg 16 world) (proof-world-reg 8 world)) world))))
  :hints (("Goal"
           :use ((:instance assembly-darwin-step-from-instruction (instruction '(:svc #x80))))
           :in-theory (disable assembly-darwin-step proof-instruction-at-p)))
  :rule-classes nil)

(local (in-theory (disable proof-reg boymoo-model::a64-unsigned boymoo-model::a64-read-bytes
                           boymoo-model::a64-memory proof-world-reg assembly-darwin-flags
                           logand logior acl2::binary-logand acl2::binary-logior)))

(local
 (defthm assembly-darwin-unsigned-idempotent
   (implies (natp width)
            (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned width value))
                   (boymoo-model::a64-unsigned width value)))
   :hints (("Goal"
            :use (assembly-low-bounds
                  (:instance assembly-low-of-fitting-value (value (assembly-low width value))))
            :in-theory (disable assembly-low mod floor)))))

(local
 (defthm assembly-darwin-pc-of-write
   (and (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
               (boymoo-model::a64-unsigned 64 pc))
        (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
               (boymoo-model::a64-pc machine))
        (equal (boymoo-model::a64-pc (boymoo-model::a64-write-reg register width use-sp value machine))
               (boymoo-model::a64-pc machine)))
   :hints (("Goal" :in-theory (disable nth update-nth assembly-a64-unsigned-is-low)))))

(local
 (defthm assembly-darwin-assoc-of-written-register
   (equal (assoc-equal register (put-assoc-equal register value registers))
          (cons register value))))

(defthm assembly-darwin-return-shape
  (let ((after (assembly-darwin-return reply world)))
    (and (equal (proof-world-pc after)
                (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc world))))
         (equal (proof-world-reg 0 after)
                (boymoo-model::a64-unsigned 64 (cdr reply)))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-unsigned
                 4 (assembly-darwin-flags
                    (boymoo-model::a64-nzcv (proof-world-machine world)) (eq (car reply) :error))))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-input after) (proof-world-input world))
         (equal (proof-world-stdout after) (proof-world-stdout world))
         (equal (proof-world-stderr after) (proof-world-stderr world))
         (equal (proof-world-replies after) (cdr (proof-world-replies world)))
         (equal (proof-world-stop after) (proof-world-stop world))))
  :hints (("Goal" :in-theory (e/d (proof-world-reg proof-reg)
                                  (assembly-a64-unsigned-is-low nth update-nth))))
  :rule-classes nil)

(local
 (defthm assembly-darwin-flag-values
   (implies (unsigned-byte-p 4 old)
            (member-equal old '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))
   :hints (("Goal" :induct (assembly-zero-characters old)))
   :rule-classes nil))

(defthm assembly-darwin-carry-conditions
  (let ((flags (boymoo-model::a64-unsigned 4 (assembly-darwin-flags old error))))
    (implies (unsigned-byte-p 4 old)
             (and (equal (boymoo-model::a64-condition 2 flags) (if error t nil))
                  (equal (boymoo-model::a64-condition 3 flags) (not error)))))
  :hints (("Goal"
           :cases (error)
           :use (assembly-darwin-flag-values)
           :in-theory (e/d (assembly-darwin-flags) (assembly-low assembly-high ash mod floor))))
  :rule-classes nil)

(defthm assembly-darwin-exit-svc
  (equal (assembly-darwin-svc (list :svc #x80 1 linux-number) world)
         (proof-world-exit (proof-world-reg 0 world) world))
  :hints (("Goal" :in-theory (enable assembly-darwin-svc))))

(defthm assembly-darwin-map-respects-pagezero
  (implies (and (eq (car reply) :ok)
                (< (cdr reply) *assembly-macho-preferred-base*))
           (equal (assembly-darwin-map reply world) (proof-kernel-fault world)))
  :hints (("Goal"
           :in-theory (disable proof-kernel-fault assembly-darwin-finish-syscall
                               assembly-darwin-map-arguments-p proof-linux-map))))
