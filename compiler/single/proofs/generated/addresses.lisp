(in-package "BOYMOO-PROOFS")

(include-book "wide-words")
(include-book "copy-path")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-instruction-effect proof-execute proof-world-reg proof-world-pc
                    proof-world-machine proof-world-stop proof-reg boymoo-model::a64-execute
                    boymoo-model::a64-unsigned generated-wide-word-items
                    generated-move-instructions boymoo-compiler::gen-address generated-sp expt))

(defthm generated-effect-of-add-register
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :arithmetic-reg 0 64 rd rn rm 0 0) world)
                  (generated-set-reg rd (+ (proof-world-reg rn world) (proof-world-reg rm world))
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute proof-world-pc
                                    proof-world-reg proof-reg proof-world-machine boymoo-model::a64-execute
                                    generated-set-machine generated-set-reg generated-set-pc))))

(defthm generated-effect-of-sub-register
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :arithmetic-reg 2 64 rd rn rm 0 0) world)
                  (generated-set-reg rd (- (proof-world-reg rn world) (proof-world-reg rm world))
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute proof-world-pc
                                    proof-world-reg proof-reg proof-world-machine boymoo-model::a64-execute
                                    generated-set-machine generated-set-reg generated-set-pc))))

(defun generated-address-path (rd rn bytes subtract)
  (let ((operation (if subtract 2 0)))
    (if (< bytes 4096)
        (if (and (equal bytes 0) (equal rd rn)) nil
          (list (list :arithmetic-imm operation 64 rd rn bytes)))
      (append (generated-move-instructions (generated-wide-word-items 17 bytes))
              (list (list :arithmetic-reg operation 64 rd rn 17 0 0))))))

(defthm generated-wide-address-emission
  (implies (and (natp bytes) (<= 4096 bytes))
           (equal (boymoo-compiler::gen-address rd rn bytes subtract code)
                  (boymoo-compiler::reverse-onto
                   (append (generated-wide-word-items 17 bytes)
                           (list (list (if subtract :sub-reg :add-reg) rd rn 17 0)))
                   code)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-address))))

(local
 (defthm generated-address-path-append-length
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-address-path-observations
  (let* ((path (generated-address-path rd rn bytes subtract))
         (after (generated-path-after path before))
         (pc (+ (proof-world-pc before) (* 4 (len path))))
         (value (if subtract (- (proof-world-reg rn before) bytes)
                  (+ (proof-world-reg rn before) bytes))))
    (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31) (not (equal rn 17))
                  (unsigned-byte-p 64 bytes) (< pc (expt 2 64)))
             (and (equal (proof-world-reg rd after) (boymoo-model::a64-unsigned 64 value))
                  (equal (proof-world-pc after) pc)
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (equal (generated-sp after) (generated-sp before))
                  (implies (generated-ordinary-machine-p before)
                           (generated-ordinary-machine-p after))
                  (equal (generated-load-word address after) (generated-load-word address before))
                  (equal (generated-read-words count address after)
                         (generated-read-words count address before))
                  (implies (and (not (equal rd other)) (not (equal other 17)))
                           (equal (proof-world-reg other after) (proof-world-reg other before)))
                  (implies (not (member-equal rd '(23 24 25 26 27 28)))
                           (generated-heap-world-equiv after before)))))
  :hints (("Goal" :use (:instance generated-wide-word-loads-value (rd 17) (word bytes)))))

(defthm generated-address-reaches-continuation
  (let* ((path (generated-address-path rd rn bytes subtract))
         (after (generated-path-after path before))
         (pc (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31) (not (equal rn 17))
                  (unsigned-byte-p 64 bytes) (< pc (expt 2 64)) (not (proof-world-stop before))
                  (generated-path-p path (list pc) before))
             (proof-segment-p (len path) (list pc) before :cut after)))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions (generated-address-path rd rn bytes subtract))
                                  (cuts (list (+ (proof-world-pc before)
                                                 (* 4 (len (generated-address-path rd rn bytes subtract)))))))
                  :in-theory (disable generated-address-path generated-path-after generated-path-p
                                      proof-segment-p))))
