(in-package "BOYMOO-PROOFS")

(include-book "machine")

(logic)
(set-verify-guards-eagerness 0)

; A region is (base exclusive-end mode). An environment supplies one
; signed reply for each returning SVC. Exit consumes no reply.
(defun proof-region (base end mode)
  (list base end mode))

(defun proof-region-p (region)
  (and (true-listp region)
       (equal (len region) 3)
       (unsigned-byte-p 64 (car region))
       (natp (cadr region))
       (< (car region) (cadr region))
       (<= (cadr region) (expt 2 64))
       (member-eq (caddr region) '(:rx :rw))))

(defun proof-region-disjoint-p (base end regions)
  (if (atom regions)
      t
    (and (proof-disjoint-p base end (caar regions) (cadar regions))
         (proof-region-disjoint-p base end (cdr regions)))))

(defun proof-regions-p (regions)
  (if (atom regions)
      (null regions)
    (and (proof-region-p (car regions))
         (proof-region-disjoint-p (caar regions) (cadar regions) (cdr regions))
         (proof-regions-p (cdr regions)))))

(defun proof-region-allows-p (mode access)
  (case access
    (:read (member-eq mode '(:rx :rw)))
    (:write (eq mode :rw))
    (:execute (eq mode :rx))
    (otherwise nil)))

(defun proof-covered-p (address size access regions)
  (and (consp regions)
       (or (and (proof-subspan-p address size (caar regions) (cadar regions))
                (proof-region-allows-p (caddar regions) access))
           (proof-covered-p address size access (cdr regions)))))

(defun proof-page-size-p (page-size)
  (member-equal page-size '(4096 16384 65536)))

(defun proof-world (machine regions page-size input stdout stderr replies stop)
  (list machine regions page-size input stdout stderr replies stop))

(defun proof-world-machine (world) (nth 0 world))
(defun proof-world-regions (world) (nth 1 world))
(defun proof-world-page-size (world) (nth 2 world))
(defun proof-world-input (world) (nth 3 world))
(defun proof-world-stdout (world) (nth 4 world))
(defun proof-world-stderr (world) (nth 5 world))
(defun proof-world-replies (world) (nth 6 world))
(defun proof-world-stop (world) (nth 7 world))

(defun proof-world-pc (world)
  (boymoo-model::a64-pc (proof-world-machine world)))

(defun proof-world-reg (register world)
  (proof-reg register (proof-world-machine world)))

(defun proof-world-exit (status world)
  (update-nth 7 (cons :exit (boymoo-model::a64-unsigned 8 status)) world))

(defun proof-kernel-fault (world)
  (update-nth 7 :kernel-contract world))

(defun proof-clear-memory (base end memory)
  (if (atom memory)
      nil
    (if (and (<= base (caar memory)) (< (caar memory) end))
        (proof-clear-memory base end (cdr memory))
      (cons (car memory) (proof-clear-memory base end (cdr memory))))))

(defun proof-clear-span (base end world)
  (let* ((machine (proof-world-machine world))
         (memory (boymoo-model::a64-memory machine)))
    (update-nth 0 (update-nth 4 (proof-clear-memory base end memory) machine)
                world)))

(defun proof-remove-region-span (base size regions)
  (if (atom regions)
      nil
    (let* ((region (car regions))
           (lo (car region))
           (hi (cadr region))
           (mode (caddr region))
           (end (+ base size)))
      (if (and (eq mode :rw) (proof-subspan-p base size lo hi))
          (append (if (< lo base) (list (proof-region lo base mode)) nil)
                  (if (< end hi) (list (proof-region end hi mode)) nil)
                  (cdr regions))
        (cons region (proof-remove-region-span base size (cdr regions)))))))

(defun proof-linux-errno-p (reply)
  (and (integerp reply) (<= -4095 reply) (< reply 0)))

(defun proof-svc-return (reply world)
  (let* ((machine (proof-world-machine world))
         (next (boymoo-model::a64-set-pc (+ 4 (proof-world-pc world)) machine))
         (next (boymoo-model::a64-write-reg 0 64 nil reply next)))
    (update-nth 6 (cdr (proof-world-replies world))
                (update-nth 0 next world))))

(defun proof-linux-map (reply world)
  (let* ((page (proof-world-page-size world))
         (request (proof-world-reg 1 world))
         (size (proof-align-up request page)))
    (cond
     ((not (and (proof-page-size-p page)
                (equal (proof-world-reg 0 world) 0)
                (posp request)
                (equal (proof-world-reg 2 world) 3)
                (equal (proof-world-reg 3 world) #x4022)
                (equal (proof-world-reg 4 world) #xffffffffffffffff)
                (equal (proof-world-reg 5 world) 0)))
      (proof-kernel-fault world))
     ((proof-linux-errno-p reply) (proof-svc-return reply world))
     ((and (posp reply)
           (equal (mod reply page) 0)
           (<= (+ reply size) (expt 2 63))
           (proof-region-disjoint-p reply (+ reply size)
                                    (proof-world-regions world)))
      (let* ((cleared (proof-clear-span reply (+ reply size) world))
             (regions (cons (proof-region reply (+ reply size) :rw)
                            (proof-world-regions cleared))))
        (proof-svc-return reply (update-nth 1 regions cleared))))
     (t (proof-kernel-fault world)))))

(defun proof-linux-release (unmap reply world)
  (let* ((base (proof-world-reg 0 world))
         (request (proof-world-reg 1 world))
         (page (proof-world-page-size world))
         (size (proof-align-up request page))
         (regions (proof-world-regions world)))
    (if (and (proof-page-size-p page)
             (equal (mod base page) 0)
             (posp request)
             (or unmap (equal (proof-world-reg 2 world) 4))
             (proof-covered-p base size :write regions)
             (equal reply 0))
        (let* ((next (proof-clear-span base (+ base size) world))
               (next (if unmap
                         (update-nth 1 (proof-remove-region-span base size regions)
                                     next)
                       next)))
          (proof-svc-return 0 next))
      (proof-kernel-fault world))))

(defun proof-linux-read (reply world)
  (let ((fd (proof-world-reg 0 world))
        (address (proof-world-reg 1 world))
        (count (proof-world-reg 2 world))
        (input (proof-world-input world)))
    (cond
     ((not (and (equal fd 0)
                (proof-covered-p address count :write (proof-world-regions world))))
      (proof-kernel-fault world))
     ((proof-linux-errno-p reply) (proof-svc-return reply world))
     ((and (natp reply)
           (<= reply count)
           (<= reply (len input))
           (or (posp reply) (zp count) (endp input)))
      (let ((machine (proof-store-bytes (take reply input)
                                         address (proof-world-machine world))))
        (proof-svc-return reply
                          (update-nth 3 (nthcdr reply input)
                                      (update-nth 0 machine world)))))
     (t (proof-kernel-fault world)))))

(defun proof-linux-write (reply world)
  (let ((fd (proof-world-reg 0 world))
        (address (proof-world-reg 1 world))
        (count (proof-world-reg 2 world)))
    (cond
     ((not (and (member-equal fd '(1 2))
                (proof-covered-p address count :read (proof-world-regions world))))
      (proof-kernel-fault world))
     ((proof-linux-errno-p reply) (proof-svc-return reply world))
     ((and (natp reply) (<= reply count))
      (let* ((bytes (proof-byte-list reply address (proof-world-machine world)))
             (slot (if (equal fd 1) 4 5)))
        (proof-svc-return reply
                          (update-nth slot (append (nth slot world) bytes) world))))
     (t (proof-kernel-fault world)))))

(defun proof-linux-svc (event world)
  (let ((syscall (cadddr event))
        (replies (proof-world-replies world)))
    (cond
     ((not (equal (cadr event) 0)) (proof-kernel-fault world))
     ((equal syscall 94) (proof-world-exit (proof-world-reg 0 world) world))
     ((atom replies) (proof-kernel-fault world))
     (t (case syscall
          (63 (proof-linux-read (car replies) world))
          (64 (proof-linux-write (car replies) world))
          (215 (proof-linux-release t (car replies) world))
          (222 (proof-linux-map (car replies) world))
          (233 (proof-linux-release nil (car replies) world))
          (otherwise (proof-kernel-fault world)))))))

(defun proof-access-p (rn mode delta width access world)
  (let* ((machine (proof-world-machine world))
         (base (boymoo-model::a64-read-reg rn 64 t machine))
         (address (boymoo-model::a64-unsigned
                   64 (if (eq mode :post) base (+ base delta)))))
    (and (or (not (equal rn 31)) (equal (mod base 16) 0))
         (proof-covered-p address width access (proof-world-regions world)))))

(defun proof-instruction-access-p (instruction world)
  (let ((args (cdr instruction)))
    (case (car instruction)
      (:single
       (let* ((mode (nth 4 args))
              (offset (nth 5 args))
              (delta (if (eq mode :register)
                         (boymoo-model::a64-register-offset
                          offset (nth 6 args) (nth 7 args) (proof-world-machine world))
                       offset)))
         (proof-access-p (nth 2 args) mode delta (nth 1 args)
                         (if (equal (car args) 1) :read :write) world)))
      (:pair
       (proof-access-p (nth 1 args) (nth 4 args) (nth 5 args) 16
                       (if (car args) :read :write) world))
      (otherwise t))))

(defun proof-fetchable-p (address world)
  (and (equal (mod address 4) 0)
       (proof-covered-p address 4 :execute (proof-world-regions world))))

(defun proof-instruction-at-p (instruction address world)
  (and (proof-fetchable-p address world)
       (equal (proof-decode-at address (proof-world-machine world)) instruction)))

(defun proof-instructions-at-p (instructions address world)
  (if (atom instructions)
      (null instructions)
    (and (proof-instruction-at-p (car instructions) address world)
         (proof-instructions-at-p (cdr instructions) (+ 4 address) world))))

; A system call is told by the instruction, not by the shape of the result,
; so that no register file can pass for one.
(defun proof-instruction-effect (instruction world)
  (let ((next (proof-execute instruction (proof-world-machine world))))
    (cond ((eq next :undefined) (update-nth 7 :undefined world))
          ((eq (car instruction) :svc) (proof-linux-svc next world))
          (t (update-nth 0 next world)))))

; The result of an SVC instruction is an event whose first element is :svc.
(defthm proof-execute-of-svc-is-an-event
  (implies (equal (car instruction) :svc)
           (equal (car (proof-execute instruction machine)) :svc))
  :hints (("Goal" :in-theory (enable proof-execute boymoo-model::a64-execute))))

(defun proof-step (world)
  (let ((pc (proof-world-pc world))
        (machine (proof-world-machine world)))
    (cond
     ((proof-world-stop world) world)
     ((not (proof-fetchable-p pc world)) (update-nth 7 :fault world))
     (t
      (let ((instruction (proof-decode-at pc machine)))
        (if (not (proof-instruction-access-p instruction world))
            (update-nth 7 :fault world)
          (proof-instruction-effect instruction world)))))))

(defthm proof-step-from-instruction
  (implies (and (not (proof-world-stop world))
                (proof-instruction-at-p instruction (proof-world-pc world) world)
                (proof-instruction-access-p instruction world))
           (equal (proof-step world) (proof-instruction-effect instruction world)))
  :hints (("Goal" :in-theory (disable proof-fetchable-p proof-decode-at
                                      proof-instruction-access-p proof-instruction-effect))))

(defun proof-run (fuel cuts world)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable proof-step)))))
  (cond ((proof-world-stop world) (mv (proof-world-stop world) world))
        ((member-equal (proof-world-pc world) cuts) (mv :cut world))
        ((zp fuel) (mv :limit world))
        (t (proof-run (1- fuel) cuts (proof-step world)))))

(defun proof-segment-p (fuel cuts before reason after)
  (mv-let (why reached)
    (proof-run fuel cuts before)
    (and (equal why reason) (equal reached after))))
