;;; This file contains a collection of theories useful for reasoning about
;;; instantiated weakest preconditions.

;;; A generic theory for using loop invariants to prove weakest preconditions.

;;; (wp s) = (if (b s) (qp s) (wp (sigma s)))

;;; (not (b s)) ^ (r s) => (r (sigma s))
;;; (b s) ^ (r s) => (qp s)

(in-package "ACL2")

(encapsulate
  (((measure *) => *)
   ((sigma *) => *)
   ((b *) => *)
   ((qp *) => *)
   ((wp *) => *)
   ((r *) => *))
  (local (defun measure (s) (1+ (nfix (car s)))))
  (local (defun sigma (s) (cons (1- (car s)) (cdr s))))
  (local (defun b (s) (zp (car s))))
  (local (defun qp (s) (declare (ignore s)) t))
  (local (defun wp (s) (declare (ignore s)) t))
  (local (defun r (s) (declare (ignore s)) t))
  (defthm loop-invariant-wp-def-1
    (implies (b s) (equal (wp s) (qp s))))
  (defthm loop-invariant-wp-def-2
    (implies (and (not (b s)) (r s)) (equal (wp (sigma s)) (wp s))))
  (defthm loop-invariant-ordinalp (o-p (measure s)))
  (defthm loop-invariant-ord-<
    (implies (not (b s)) (o< (measure (sigma s)) (measure s))))
  (defthm loop-invariant-r-1
    (implies (and (not (b s)) (r s)) (r (sigma s))))
  (defthm loop-invariant-r-2
    (implies (and (b s) (r s)) (qp s))))

;;; An induct hint

(defun wp-ind (s)
  (declare (xargs :measure (measure s)))
  (if (b s) (qp s) (wp-ind (sigma s))))

;;; The main result derived from the loop-invariant theory.

(defthm wp-is-weakest-invariant
  (implies (r s) (wp s))
  :hints (("Goal"
           :induct (wp-ind s))))

;;; A generic theory for conversion of tail to primitive recursive functions.

;;; (g a s) = (if (bb s) (qt a s) (g (rho a s) (tau s)))
;;; (h s) = (if (bb s) (id) (rhoh (h (tau s)) s))
;;; (rt a s) is an invariant which assures desired properties of rho, op and (id)
;;; (hs s) = (if (bb s) s (hs (tau s))), computes a bottom object under tau

;(set-bind-free-error nil)

(encapsulate
  (((measure-g *) => *)
   ((tau *) => *)
   ((rt * *) => *)
   ((rho * *) => *)
   ((rhoh * *) => *)
   ((bb *) => *)
   ((qt * *) => *)
   ((g * *) => *)
   ((h *) => *)
   ((id) => *)
   ((op * * *) => *)
   ((hs *) => *))
  (local (defun measure-g (s) (1+ (nfix s))))
  (local (defun tau (s) (1- (nfix s))))
  (local (defun qt (a s) (declare (ignore a s)) t))
  (local (defun rho (a s) (declare (ignore a s)) 0))
  (local (defun rhoh (a s) (declare (ignore a s)) 0))
  (local (defun bb (s) (zp s)))
  (local (defun g (a s) (declare (ignore a s)) t))
  (local (defun id () 0))
  (local (defun op (a x s) (if (and (zp s) (equal x 0)) a 0)))
  (local (defun h (s) (declare (ignore s)) 0))
  (local (defun rt (a s) (and (integerp a) (integerp s) (<= 0 a) (<= 0 s))))
  (local (defun hs (s) (if (zp s) s 0)))
  (defthm tail-recursion-g-def-1
    (implies (and (bb s) (rt a s)) (equal (g a s) (qt a s))))
  (defthm tail-recursion-g-def-2
    (implies (and (not (bb s)) (rt a s)) (equal (g (rho a s) (tau s)) (g a s))))
  (defthm tail-recursion-ordinalp
    (o-p (measure-g s)))
  (defthm tail-recursion-ord-<
    (implies (not (bb s))
             (o< (measure-g (tau s)) (measure-g s))))
  (defthm tail-recursion-h-def-1
    (implies (and (bb s) (rt a s)) (equal (h s) (id))))
  (defthm tail-recursion-h-def-2
    (implies (and (not (bb s)) (rt a s)) (equal (rhoh (h (tau s)) s) (h s))))
  (defthm tail-recursion-rt
    (implies (and (not (bb s)) (rt a s))
             (rt (rho a s) (tau s))))
  (defthm tail-recursion-hs-1
    (implies (bb s) (equal (hs s) s)))
  (defthm tail-recursion-hs-2
    (implies (not (bb s)) (equal (hs (tau s)) (hs s))))
  (defthm tail-recursion-op-rho-rhoh ; generated by proof of a-g-as-op-h
    (implies (and (not (bb s)) (rt a s))
             (equal (op (rho a s) (h (tau s)) (tau s))
                    (op a (rhoh (h (tau s)) s) s))))
  (defthm tail-recursion-op-id ; generated by proof of a-g-as-op-h
    (implies (and (bb s) (rt a s))
             (equal (op a (id) s) a))))

(defun a-g (a s)
  (declare (xargs :measure (measure-g s)))
  (if (bb s)
      a
    (a-g (rho a s) (tau s))))

(defthm a-g-as-op-h
  (implies (rt a s)
           (equal (a-g a s)
                  (op a (h s) s)))
  :hints (("Goal"
           :induct (a-g a s))))

(defthm g-as-a-g
  (implies (rt a s)
           (equal (g a s) (qt (a-g a s) (hs s))))
  :hints (("Goal"
           :induct (a-g a s))))

;;; Main result of tail recursion theory

(defthm g=h
  (implies (rt a s)
           (equal (g a s)
                  (if (bb s)
                      (qt a s)
                    (qt (op a (h s) s) (hs s)))))
  :hints (("Goal"
           :induct (a-g a s))))

;;; The following theory can be used to prove equivalence, under the hypothesis
;;; p, between alternative representations fn1 and fn2 of the same function
;;; or in developing induction patterns different from that suggested by the
;;; standard definition.  The function id-alt below has dual roles.  When proving
;;; equivalence between fn1 and fn1, id-alt is the identity function.  Otherwise it
;;; represents the alternative induction.  In this latter case sigma1 = sigma2.
;;;
;;;      (fn1 s) = (if (b1 s) (q1 s) (fn1 (sigma1 s)))
;;;      (fn2 s) = (if (b2 s) (q2 s) (fn2 (sigma2 s)))

(encapsulate
  (((fn1 *) => *)
   ((fn2 *) => *)
   ((b1 *) => *)
   ((b2 *) => *)
   ((q1 *) => *)
   ((q2 *) => *)
   ((p *) => *)
   ((measure1 *) => *)
   ((sigma1 *) => *)
   ((sigma2 *) => *)
   ((id-alt *) => *))
  (local (defun fn1 (s) (declare (ignore s)) t))
  (local (defun fn2 (s) (declare (ignore s)) t))
  (local (defun b1 (s) (zp (car s))))
  (local (defun b2 (s) (zp (cdr s))))
  (local (defun q1 (s) (declare (ignore s)) t))
  (local (defun q2 (s) (declare (ignore s)) t))
  (local (defun p (s) (declare (ignore s)) t))
  (local (defun measure1 (s) (1+ (nfix (car s)))))
  (local (defun sigma1 (s) (cons (1- (nfix (car s))) (cdr s))))
  (local (defun sigma2 (s) (cons (car s) (1- (nfix (cdr s))))))
  (local (defun id-alt (s) (cons (cdr s) (car s))))
  (defthm alternative-induction-fn1-def-1
    (implies (b1 s) (equal (fn1 s) (q1 s))))
  (defthm alternative-induction-fn1-def-2
    (implies (and (not (b1 s)) (p s)) (equal (fn1 (sigma1 s)) (fn1 s))))
  (defthm alternative-induction-fn2-def-1
    (implies (b2 s) (equal (fn2 s) (q2 s))))
  (defthm alternative-induction-fn2-def-2
    (implies (not (b2 s)) (equal (fn2 (sigma2 s)) (fn2 s))))
  (defthm alternative-induction-ordinalp
    (o-p (measure1 s)))
  (defthm alternative-induction-ord-<
    (implies (not (b1 s)) (o< (measure1 (sigma1 s)) (measure1 s))))
  (defthm alternative-induction-id-alt
    (implies (and (p s) (not (b1 s)))
             (equal (id-alt (sigma1 s)) (sigma2 (id-alt s)))))
  (defthm alternative-induction-b2-id-alt
    (implies (p s) (equal (b2 (id-alt s)) (b1 s))))
  (defthm alternative-induction-p
    (implies (and (not (b1 s)) (p s)) (p (sigma1 s))))
  (defthm alternative-induction-q2-id-alt
    (implies (and (b1 s) (p s)) (equal (q2 (id-alt s)) (q1 s)))))

(defun fn1-ind (s)
  (declare (xargs :measure (measure1 s)))
  (if (b1 s) (q1 s) (fn1-ind (sigma1 s))))

;;; This is the main goal of the alternative induction theory.

(defthm fn1-as-fn2
  (implies (p s)
           (equal (fn1 s) (fn2 (id-alt s))))
  :hints (("Goal" :induct (fn1-ind s))))

;;; Define computed hint function for loop invariant theory

;;; Create a substitution that maps ith formal argument to (nth i s).

(defun make-subs (formals i)
  (declare (xargs :mode :program))
  (if (endp formals)
      nil
    (cons (cons (car formals) `(nth ,i s))
          (make-subs (cdr formals) (+ 1 i)))))

;;; Converts a set of arguments to a proper logical expression using the operator op.

(defun set-to-predicate (a op)
  (if (< (length a) 2)
      (car a)
    (cons op a)))

;;; Extract the predicate b from the induction-machine property of wp.

(defun make-b (induction-machine)
  (declare (xargs :mode :program))
  (if (endp induction-machine)
      nil
    (if (and (equal (caar induction-machine) 'tests-and-calls)
             (endp (cddar induction-machine))) ; detects base case predicates
        (cons (set-to-predicate (cadar induction-machine) 'and)
              (make-b (cdr induction-machine)))
      (make-b (cdr induction-machine)))))

;;; Construct the argument for a cond expression that delivers an instance of the
;;; generic substitution sigma.  flat-to-s is the substitution generated by make-subs.

(defun make-sigma (induction-machine flat-to-s)
  (declare (xargs :mode :program))
  (if (endp induction-machine)
      (list (list t 's)) ; default value of cond
    (if (and (equal (caar induction-machine) 'tests-and-calls)
             (consp (cddar induction-machine)))
        (cons (sublis flat-to-s
                      (list (set-to-predicate (cadar induction-machine) 'and)
                            (cons 'list (cdaddr (car induction-machine)))))
              (make-sigma (cdr induction-machine) flat-to-s))
      (make-sigma (cdr induction-machine) flat-to-s))))

(defun build-instance (wp r world)
  (declare (xargs :mode :program))
  (let* ((formals
          (getprop wp 'formals nil '*current-acl2-world* world))
         (flat-to-s ; mapping from flat to structured state space
          (cons (cons wp 'list) (make-subs formals 0))))
    `(:use
      (:instance
       (:functional-instance
        wp-is-weakest-invariant
        (b (lambda (s) ,(set-to-predicate
                         (sublis
                          flat-to-s
                          (make-b (getprop wp
                                           'induction-machine
                                           nil
                                           '*current-acl2-world*
                                           world)))
                         'or)))
        (qp (lambda (s) (,wp ,@(sublis flat-to-s
                                       (getprop wp
                                                'formals
                                                nil
                                                '*current-acl2-world*
                                                world)))))
        (wp (lambda (s) (,wp  ,@(sublis flat-to-s
                                        (getprop wp
                                                 'formals
                                                 nil
                                                 '*current-acl2-world*
                                                 world)))))
; This is probably incomplete.  What is the purpose of the repetition of
; "justification" within the 'justification property?
        (measure (lambda (s) ,(sublis flat-to-s
; Matt K. mod after Version 3.0.1: Replace (car (cddddr (getprop ...))) so that
; we access justification property without relying on its layout.
                                      (let ((j (getprop wp
                                                        'justification
                                                        nil
                                                        '*current-acl2-world*
                                                        world)))
                                        (and j (access justification
                                                       j
                                                       :measure))))))
        (sigma (lambda (s) (cond ,@(make-sigma (getprop wp
                                                        'induction-machine
                                                        nil
                                                        '*current-acl2-world*
                                                        world)
                                               flat-to-s))))
        (r (lambda (s) ,(sublis flat-to-s r))))
       (s (list ,@(getprop wp
                           'formals
                           nil
                           '*current-acl2-world*
                           world)))))))

(defmacro loop-invariant-hint (wp r)
  `(build-instance ,wp ,r world))

;;; A user will include (loop-invariant wp r) within the :hints field of a defthm,
;;; where wp and r are concrete instances of the weakest precondition and loop
;;; invariant respectively.  For example

;;; (defthm foo
;;;  (implies <insert concrete loop invariant here>
;;;           <insert concrete weakest precondition here>)
;;;  :hints
;;;   ((loop-invariant-hint
;;;     '<name of concrete weakest precondition>
;;;     '<concrete loop invariant>)))
