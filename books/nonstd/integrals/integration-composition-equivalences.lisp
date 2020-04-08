(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(include-book "integrable-functions")
(include-book "equivalence-integrals")
(include-book "nonstd/integrals/make-partition" :dir :system)
(local (include-book "integration-composition"))

(encapsulate
 ( ((rifn-classical-small * *) => *)
   ((strict-int-rifn-classical-small * * *) => *)
   ((rifn-classical-big * *) => *)
   ((strict-int-rifn-classical-big * * *) => *)
   ((domain-rifn-classical-cmp) => *)
   )

 (local
  (defun rifn-classical-small (context x)
    (declare (ignore context x))
    0))

 (local
  (defun rifn-classical-big (context x)
    (declare (ignore context x))
    0))

 (defthm rifn-classical-small-real
   (implies (realp x)
	    (realp (rifn-classical-small context x))))
 (defthm rifn-classical-big-real
   (implies (realp x)
	    (realp (rifn-classical-big context x))))

 (local
  (defun strict-int-rifn-classical-small (context a b)
    (declare (ignore context a b))
    0))
 (local
  (defun strict-int-rifn-classical-big (context a b)
    (declare (ignore context a b))
    0))
 (defthm strict-int-rifn-classical-small-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-small context a b))))
 (defthm strict-int-rifn-classical-big-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-big context a b))))

 (local
  (defun domain-rifn-classical-cmp ()
    (interval nil nil)))

 (defthm domain-rifn-classical-cmp-is-non-trivial-interval
   (and (interval-p (domain-rifn-classical-cmp))
	(implies (and (interval-left-inclusive-p (domain-rifn-classical-cmp))
		      (interval-right-inclusive-p (domain-rifn-classical-cmp)))
		 (not (equal (interval-left-endpoint (domain-rifn-classical-cmp))
			     (interval-right-endpoint (domain-rifn-classical-cmp)))))))

 (defun map-rifn-classical-small (context p)
   ;; map rifn-classical over the list p
   (if (consp p)
       (cons (rifn-classical-small context (car p))
	     (map-rifn-classical-small context (cdr p)))
     nil))
  (defun map-rifn-classical-big (context p)
   ;; map rifn-classical over the list p
   (if (consp p)
       (cons (rifn-classical-big context (car p))
	     (map-rifn-classical-big context (cdr p)))
     nil))

  (defun riemann-rifn-classical-small (context p)
   ;; for partition p, take the Riemann sum of rifn-classical over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical-small context (cdr p))))
  (defun riemann-rifn-classical-big (context p)
   ;; for partition p, take the Riemann sum of rifn-classical over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical-big context (cdr p))))

 (defun int-rifn-classical-small (context a b)
   (if (<= a b)
       (strict-int-rifn-classical-small context a b)
     (- (strict-int-rifn-classical-small context b a))))

 (defun int-rifn-classical-big (context a b)
   (if (<= a b)
       (strict-int-rifn-classical-big context a b)
     (- (strict-int-rifn-classical-big context b a))))

 (local
  (defthm map-rifn-classical-small-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-small context p)) 0))))
 (local
  (defthm map-rifn-classical-big-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-big context p)) 0))))

 (local
  (defthm riemann-rifn-classical-small-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-small context p) 0))))
 (local
  (defthm riemann-rifn-classical-big-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-big context p) 0))))

  (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-small (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-small context p)
			       (strict-int-rifn-classical-small context a b)))
		       eps)))
   :rewrite :direct)

  (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big (context a b eps delta)
    (forall (p)
	    (implies (and (<= a b)
			  (partitionp p)
			  (equal (car p) a)
			  (equal (car (last p)) b)
			  (< (mesh p) delta))
		     (< (abs (- (riemann-rifn-classical-big context p)
				(strict-int-rifn-classical-big context a b)))
			eps)))
    :rewrite :direct)

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-small (context a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical-cmp))
			 (inside-interval-p b (domain-rifn-classical-cmp))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-small context a b eps delta)))))

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big (context a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical-cmp))
			 (inside-interval-p b (domain-rifn-classical-cmp))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big context a b eps delta)))))

 (defthm strict-int-rifn-classical-small-is-integral-of-rifn-classical-small
   (implies (and (inside-interval-p a (domain-rifn-classical-cmp))
		 (inside-interval-p b (domain-rifn-classical-cmp))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-small context a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-small-suff
			     (delta 1)))))
   )

 (defthm strict-int-rifn-classical-big-is-integral-of-rifn-classical-big
   (implies (and (inside-interval-p a (domain-rifn-classical-cmp))
		 (inside-interval-p b (domain-rifn-classical-cmp))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big context a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big-suff
			     (delta 1)))))
   )

 (defthm rifn-classical-small-<=-rifn-classical-big
   (implies (inside-interval-p x (domain-rifn-classical-cmp))
	    (<= (rifn-classical-small context x)
		(rifn-classical-big context x))))
 )

(defthm strict-int-rifn-classical-small-is-integral-of-rifn-classical-small-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-cmp))
		(inside-interval-p b (domain-rifn-classical-cmp))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-small context p)
		    (strict-int-rifn-classical-small context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
				     (riemann-rifn-classical riemann-rifn-classical-small)
				     (strict-int-rifn-classical strict-int-rifn-classical-small)
				     (domain-rifn-classical domain-rifn-classical-cmp)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-small)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-small-witness)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-small)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-small-witness)
				     (map-rifn-classical map-rifn-classical-small)
				     (rifn-classical rifn-classical-small)
				     )
	   )
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-small-is-integral-of-rifn-classical-small)))
	  ("Subgoal 4"
	   :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-small-necc)))
	  ))

(defthm strict-int-rifn-classical-big-is-integral-of-rifn-classical-big-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-cmp))
		(inside-interval-p b (domain-rifn-classical-cmp))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-big context p)
		    (strict-int-rifn-classical-big context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
				     (riemann-rifn-classical riemann-rifn-classical-big)
				     (strict-int-rifn-classical strict-int-rifn-classical-big)
				     (domain-rifn-classical domain-rifn-classical-cmp)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big-witness)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big-witness)
				     (map-rifn-classical map-rifn-classical-big)
				     (rifn-classical rifn-classical-big)
				     )
	   )
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-big-is-integral-of-rifn-classical-big)))
	  ("Subgoal 4"
	   :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big-necc)))
	  ))


(defthm realp-riemann-rifn-classical-small
  (implies (partitionp p)
	   (realp (riemann-rifn-classical-small context p))))

(defthm realp-riemann-rifn-classical-big
  (implies (partitionp p)
	   (realp (riemann-rifn-classical-big context p))))

(defthm integral-rifn-classical-small-<=-integral-rifn-classical-big
  (implies (and (inside-interval-p a (domain-rifn-classical-cmp))
		(inside-interval-p b (domain-rifn-classical-cmp))
		(<= a b)
		)
	   (<= (int-rifn-classical-small context a b)
	       (int-rifn-classical-big context a b)
	       ))
  :hints (("Goal"
	   :by (:functional-instance integral-rifn-small-<=-integral-rifn-big
				     (riemann-rifn-classical riemann-rifn-classical-big)
				     (strict-int-rifn-classical strict-int-rifn-classical-big)
				     (domain-rifn-classical domain-rifn-classical-cmp)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-big-witness)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-big-witness)
				     (map-rifn-classical map-rifn-classical-big)
				     (rifn-classical rifn-classical-big)
				     (domain-rifn-cmp domain-rifn-classical-cmp)
				     (int-rifn-small int-rifn-classical-small)
				     (int-rifn-big int-rifn-classical-big)
				     (strict-int-rifn-small strict-int-rifn-classical-small)
				     (strict-int-rifn-big strict-int-rifn-classical-big)
				     (rifn-small rifn-classical-small)
				     (rifn-big rifn-classical-big)
				     (riemann-rifn-big riemann-rifn-classical-big)
				     (riemann-rifn-small riemann-rifn-classical-small)
				     (map-rifn-small map-rifn-classical-small)
				     (map-rifn-big map-rifn-classical-big)
				     ))
	  ("Subgoal 8"
	   :use ((:instance strict-int-rifn-classical-big-is-integral-of-rifn-classical-big-using-nonstandard-criterion)))
	  ("Subgoal 7"
	   :use ((:instance strict-int-rifn-classical-small-is-integral-of-rifn-classical-small-using-nonstandard-criterion)))
	  )
  )

;---------------

(encapsulate
 ( ((rifn-classical-const) => *)
   ((rifn-classical-const-fn * *) => *)
   ((strict-int-rifn-classical-const-fn * * *) => *)
   ((domain-rifn-classical-const-fn) => *)
   )

 (local
  (defun rifn-classical-const ()
    0))

 (local
  (defun rifn-classical-const-fn (context x)
    (declare (ignore context x))
    0))

 (defthm rifn-classical-const-real
   (realp (rifn-classical-const)))

 (defthm rifn-classical-const-fn-real
   (implies (realp x)
	    (realp (rifn-classical-const-fn context x))))

 (local
  (defun domain-rifn-classical-const-fn ()
    (interval nil nil)))

 (defthm domain-rifn-classical-const-fn-is-non-trivial-interval
   (and (interval-p (domain-rifn-classical-const-fn))
	(implies (and (interval-left-inclusive-p (domain-rifn-classical-const-fn))
		      (interval-right-inclusive-p (domain-rifn-classical-const-fn)))
		 (not (equal (interval-left-endpoint (domain-rifn-classical-const-fn))
			     (interval-right-endpoint (domain-rifn-classical-const-fn)))))))

 (defun map-rifn-classical-const-fn (context p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-classical-const-fn context (car p))
	     (map-rifn-classical-const-fn context (cdr p)))
     nil))

 (local
  (defthm map-rifn-classical-const-fn-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-const-fn context p)) 0))))

 (defun riemann-rifn-classical-const-fn (context p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical-const-fn context (cdr p))))

 (local
  (defthm riemann-rifn-classical-const-fn-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-const-fn context p) 0))))

 (local
  (defun-std strict-int-rifn-classical-const-fn (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (domain-rifn-classical-const-fn))
	     (inside-interval-p b (domain-rifn-classical-const-fn))
	     (< a b))
	(standard-part (riemann-rifn-classical-const-fn context (make-small-partition a b)))
      0)))

 (defthm-std strict-int-rifn-classical-const-fn-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-const-fn context a b))))

 (defun int-rifn-classical-const-fn (context a b)
   (if (<= a b)
       (strict-int-rifn-classical-const-fn context a b)
     (- (strict-int-rifn-classical-const-fn context b a))))

 (local
  (defthm map-rifn-classical-const-fn-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-const-fn context p)) 0))))

 (local
  (defthm riemann-rifn-classical-const-fn-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-const-fn context p) 0))))

 (local
  (defthm-std strict-int-rifn-classical-const-fn-zero
    (implies (partitionp p)
	     (equal (strict-int-rifn-classical-const-fn context a b) 0))))

 (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const-fn (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-const-fn context p)
			       (strict-int-rifn-classical-const-fn context a b)))
		       eps)))
   :rewrite :direct)


 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-fn (context a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical-const-fn))
			 (inside-interval-p b (domain-rifn-classical-const-fn))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const-fn context a b eps delta)))))

 (defthm strict-int-rifn-classical-const-fn-is-integral-of-rifn-classical-const-fn
   (implies (and (inside-interval-p a (domain-rifn-classical-const-fn))
		 (inside-interval-p b (domain-rifn-classical-const-fn))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-fn context a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-fn-suff
			     (delta 1)))))
   )
 )


(defthm strict-int-rifn-classical-const-fn-is-integral-of-rifn-classical-const-fn-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-classical-const-fn))
		 (inside-interval-p b (domain-rifn-classical-const-fn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-classical-const-fn context p)
		     (strict-int-rifn-classical-const-fn context a b)))
   :hints (("Goal" :do-not-induct t
	    :by (:functional-instance strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
				      (riemann-rifn-classical riemann-rifn-classical-const-fn)
				      (strict-int-rifn-classical strict-int-rifn-classical-const-fn)
				      (domain-rifn-classical domain-rifn-classical-const-fn)
				      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-fn)
				      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-fn-witness)
				      (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const-fn)
				      (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const-fn-witness)
				      (map-rifn-classical map-rifn-classical-const-fn)
				      (rifn-classical rifn-classical-const-fn)
				      )
	    )
	   ("Subgoal 6"
	    :use ((:instance strict-int-rifn-classical-const-fn-is-integral-of-rifn-classical-const-fn)))
	   ("Subgoal 4"
	    :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const-fn-necc)))
	   ))

(defun rifn-classical-const*const-fn (context x)
  (* (rifn-classical-const)
     (rifn-classical-const-fn context x)))

(defthm realp-rifn-classical-const*const-fn
  (implies (realp x)
           (realp (rifn-classical-const*const-fn context x))))

(defun map-rifn-classical-const*const-fn (context p)
  (if (consp p)
      (cons (rifn-classical-const*const-fn context (car p))
	    (map-rifn-classical-const*const-fn context (cdr p)))
    nil))

(defthm realp-map-rifn-classical-const*const-fn
  (implies (partitionp p)
           (real-listp (map-rifn-classical-const*const-fn context p))))

(defun riemann-rifn-classical-const*const-fn (context p)
  (dotprod (deltas p)
	   (map-rifn-classical-const*const-fn context (cdr p))))

(defthm real-listp-deltas
  (implies (partitionp p)
           (real-listp (deltas p))))

(defthm realp-dotprod
  (implies (and (real-listp xs)
                (real-listp ys))
           (realp (dotprod xs ys))))

(defthm realp-riemann-rifn-classical-const*const-fn
  (implies (partitionp p)
           (realp (riemann-rifn-classical-const*const-fn context p)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable dotprod)))
  )

(defthm limited-riemann-rifn-classical-const*const-fn
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-classical-const-fn))
		(inside-interval-p b (domain-rifn-classical-const-fn)))
	   (i-limited (riemann-rifn-classical-const*const-fn context (make-small-partition a b))))
  :hints (("Goal"
	   :by (:functional-instance limited-riemann-rifn-const*const-fn
				     (domain-rifn-const-fn domain-rifn-classical-const-fn)
				     (rifn-const*const-fn rifn-classical-const*const-fn)
				     (map-rifn-const*const-fn map-rifn-classical-const*const-fn)
				     (riemann-rifn-const*const-fn riemann-rifn-classical-const*const-fn)
				     (rifn-const-fn rifn-classical-const-fn)
				     (rifn-const rifn-classical-const)
				     (strict-int-rifn-const-fn strict-int-rifn-classical-const-fn)
				     (riemann-rifn-const-fn riemann-rifn-classical-const-fn)
				     (map-rifn-const-fn map-rifn-classical-const-fn)
				     )
	   )
	  ("Subgoal 4"
	   :use ((:instance strict-int-rifn-classical-const-fn-is-integral-of-rifn-classical-const-fn-using-nonstandard-criterion)))
	  ))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-classical-const*const-fn)))

 (defun-std strict-int-rifn-classical-const*const-fn (context a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-classical-const-fn))
	    (inside-interval-p b (domain-rifn-classical-const-fn))
	    (< a b))
       (standard-part (riemann-rifn-classical-const*const-fn context (make-small-partition a b)))
     0))

  )


(defthm-std realp-strict-int-rifn-classical-const*const-fn
  (implies (and (realp a) (realp b))
           (realp (strict-int-rifn-classical-const*const-fn context a b)))
  :hints (("Goal"
           :use ((:instance realp-riemann-rifn-classical-const*const-fn
                            (p (make-small-partition a b))))
           :in-theory (disable riemann-rifn-classical-const*const-fn))))


(defun int-rifn-classical-const*const-fn (context a b)
  (if (<= a b)
      (strict-int-rifn-classical-const*const-fn context a b)
    (- (strict-int-rifn-classical-const*const-fn context b a))))

(defthm reduce-integral-rifn-classical-const*const-fn
  (implies (and (inside-interval-p a (domain-rifn-classical-const-fn))
		(inside-interval-p b (domain-rifn-classical-const-fn)))
	   (equal (int-rifn-classical-const*const-fn context a b)
		  (* (rifn-classical-const)
		     (int-rifn-classical-const-fn context a b))))
  :hints (("Goal"
	   :by (:functional-instance reduce-integral-rifn-const*const-fn
				     (domain-rifn-const-fn domain-rifn-classical-const-fn)
				     (int-rifn-const*const-fn int-rifn-classical-const*const-fn)
				     (map-rifn-const*const-fn map-rifn-classical-const*const-fn)
				     (map-rifn-const-fn map-rifn-classical-const-fn)
				     (riemann-rifn-const*const-fn riemann-rifn-classical-const*const-fn)
				     (riemann-rifn-const-fn riemann-rifn-classical-const-fn)
				     (rifn-const rifn-classical-const)
				     (rifn-const*const-fn rifn-classical-const*const-fn)
				     (rifn-const-fn rifn-classical-const-fn)
				     (strict-int-rifn-const*const-fn strict-int-rifn-classical-const*const-fn)
				     (strict-int-rifn-const-fn strict-int-rifn-classical-const-fn)
				     (int-rifn-const-fn int-rifn-classical-const-fn)
				     )
	   )))


(defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const*const-fn (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-const*const-fn context p)
			       (strict-int-rifn-classical-const*const-fn context a b)))
		       eps)))
   :rewrite :direct)

(defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-*const-fn (context a b eps)
  (exists (delta)
          (implies (and (inside-interval-p a (domain-rifn-classical-const-fn))
                        (inside-interval-p b (domain-rifn-classical-const-fn))
                        (<= a b)
                        (realp eps)
                        (< 0 eps))
                   (and (realp delta)
                        (< 0 delta)
                        (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const*const-fn context a b eps delta)))))

(defthm strict-int-rifn-classical-const*const-fn-is-integral-of-rifn-classical-const*const-fn-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-classical-const-fn))
		 (inside-interval-p b (domain-rifn-classical-const-fn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-classical-const*const-fn context p)
		     (strict-int-rifn-classical-const*const-fn context a b)))
   :hints (("Goal" :do-not-induct t
	    :by (:functional-instance
   strict-int-rifn-const*const-fn-is-integral-of-rifn-const*const-fn
				     (domain-rifn-const-fn domain-rifn-classical-const-fn)
				     (int-rifn-const*const-fn int-rifn-classical-const*const-fn)
				     (map-rifn-const*const-fn map-rifn-classical-const*const-fn)
				     (map-rifn-const-fn map-rifn-classical-const-fn)
				     (riemann-rifn-const*const-fn riemann-rifn-classical-const*const-fn)
				     (riemann-rifn-const-fn riemann-rifn-classical-const-fn)
				     (rifn-const rifn-classical-const)
				     (rifn-const*const-fn rifn-classical-const*const-fn)
				     (rifn-const-fn rifn-classical-const-fn)
				     (strict-int-rifn-const*const-fn strict-int-rifn-classical-const*const-fn)
				     (strict-int-rifn-const-fn strict-int-rifn-classical-const-fn)
				     (int-rifn-const-fn int-rifn-classical-const-fn)
				     )
	   )))

(defthm strict-int-rifn-classical-const*const-fn-is-integral-of-rifn-classical-const*const-fn
  (implies (and (inside-interval-p a (domain-rifn-classical-const-fn))
                (inside-interval-p b (domain-rifn-classical-const-fn))
                (<= a b)
                (realp eps)
                (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-*const-fn context a b eps))
   :hints (("Goal"
            :by (:functional-instance rifn-is-integrable-hyperreal
                                      (rifn rifn-classical-const*const-fn)
                                      (strict-int-rifn strict-int-rifn-classical-const*const-fn)
                                      (int-rifn int-rifn-classical-const*const-fn)
                                      (domain-rifn domain-rifn-classical-const-fn)
                                      (riemann-rifn riemann-rifn-classical-const*const-fn)
                                      (map-rifn map-rifn-classical-const*const-fn)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const*const-fn)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const*const-fn-witness)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-*const-fn)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-witness
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-const-*const-fn-witness))
            :in-theory (disable int-rifn-classical-const*const-fn
                                RIEMANN-RIFN-CLASSICAL-CONST*CONST-FN
                                STRICT-INT-RIFN-CLASSICAL-CONST*CONST-FN))
           ("Subgoal 8"
            :use ((:instance
  EXISTS-DELTA-SO-THAT-RIEMANN-SUM-IS-CLOSE-TO-INT-RIFN-CLASSICAL-CONST-*CONST-FN-suff)))
           ("Subgoal 6"
            :use ((:instance
  forall-partitions-riemann-sum-is-close-to-int-rifn-classical-const*const-fn-necc)))
           ("Subgoal 4"
            :use ((:instance
  strict-int-rifn-classical-const*const-fn-is-integral-of-rifn-classical-const*const-fn-using-nonstandard-criterion)))
           ("Subgoal 2"
            :in-theory (enable riemann-rifn-classical-const*const-fn))
	    ))

;--------------------

(encapsulate
 ( ((rifn-classical-left * *) => *)
   ((strict-int-rifn-classical-left * * *) => *)
   ((rifn-classical-right * *) => *)
   ((strict-int-rifn-classical-right * * *) => *)
   ((domain-rifn-classical-op) => *)
   )

 (local
  (defun rifn-classical-left (context x)
    (declare (ignore context x))
    0))

 (local
  (defun rifn-classical-right (context x)
    (declare (ignore context x))
    0))

 (defthm rifn-classical-left-real
   (implies (realp x)
	    (realp (rifn-classical-left context x))))
 (defthm rifn-classical-right-real
   (implies (realp x)
	    (realp (rifn-classical-right context x))))

 (local
  (defun strict-int-rifn-classical-left (context a b)
    (declare (ignore context a b))
    0))
 (local
  (defun strict-int-rifn-classical-right (context a b)
    (declare (ignore context a b))
    0))
 (defthm strict-int-rifn-classical-left-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-left context a b))))
 (defthm strict-int-rifn-classical-right-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-right context a b))))

 (local
  (defun domain-rifn-classical-op ()
    (interval nil nil)))

 (defthm domain-rifn-classical-op-is-non-trivial-interval
   (and (interval-p (domain-rifn-classical-op))
	(implies (and (interval-left-inclusive-p (domain-rifn-classical-op))
		      (interval-right-inclusive-p (domain-rifn-classical-op)))
		 (not (equal (interval-left-endpoint (domain-rifn-classical-op))
			     (interval-right-endpoint (domain-rifn-classical-op)))))))

 (defun map-rifn-classical-left (context p)
   ;; map rifn-classical over the list p
   (if (consp p)
       (cons (rifn-classical-left context (car p))
	     (map-rifn-classical-left context (cdr p)))
     nil))
  (defun map-rifn-classical-right (context p)
   ;; map rifn-classical over the list p
   (if (consp p)
       (cons (rifn-classical-right context (car p))
	     (map-rifn-classical-right context (cdr p)))
     nil))

  (defun riemann-rifn-classical-left (context p)
   ;; for partition p, take the Riemann sum of rifn-classical over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical-left context (cdr p))))
  (defun riemann-rifn-classical-right (context p)
   ;; for partition p, take the Riemann sum of rifn-classical over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical-right context (cdr p))))

 (defun int-rifn-classical-left (context a b)
   (if (<= a b)
       (strict-int-rifn-classical-left context a b)
     (- (strict-int-rifn-classical-left context b a))))

 (defun int-rifn-classical-right (context a b)
   (if (<= a b)
       (strict-int-rifn-classical-right context a b)
     (- (strict-int-rifn-classical-right context b a))))

 (local
  (defthm map-rifn-classical-left-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-left context p)) 0))))
 (local
  (defthm map-rifn-classical-right-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical-right context p)) 0))))

 (local
  (defthm riemann-rifn-classical-left-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-left context p) 0))))
 (local
  (defthm riemann-rifn-classical-right-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical-right context p) 0))))

  (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-left context p)
			       (strict-int-rifn-classical-left context a b)))
		       eps)))
   :rewrite :direct)

  (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-right (context a b eps delta)
    (forall (p)
	    (implies (and (<= a b)
			  (partitionp p)
			  (equal (car p) a)
			  (equal (car (last p)) b)
			  (< (mesh p) delta))
		     (< (abs (- (riemann-rifn-classical-right context p)
				(strict-int-rifn-classical-right context a b)))
			eps)))
    :rewrite :direct)

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left (context a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical-op))
			 (inside-interval-p b (domain-rifn-classical-op))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left context a b eps delta)))))

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-right (context a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical-op))
			 (inside-interval-p b (domain-rifn-classical-op))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-right context a b eps delta)))))

 (defthm strict-int-rifn-classical-left-is-integral-of-rifn-classical-left
   (implies (and (inside-interval-p a (domain-rifn-classical-op))
		 (inside-interval-p b (domain-rifn-classical-op))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left context a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-suff
			     (delta 1)))))
   )

 (defthm strict-int-rifn-classical-right-is-integral-of-rifn-classical-right
   (implies (and (inside-interval-p a (domain-rifn-classical-op))
		 (inside-interval-p b (domain-rifn-classical-op))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-right context a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-right-suff
			     (delta 1)))))
   )

 )

(defthm strict-int-rifn-classical-left-is-integral-of-rifn-classical-left-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-left context p)
		    (strict-int-rifn-classical-left context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
				     (riemann-rifn-classical riemann-rifn-classical-left)
				     (strict-int-rifn-classical strict-int-rifn-classical-left)
				     (domain-rifn-classical domain-rifn-classical-op)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-witness)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-witness)
				     (map-rifn-classical map-rifn-classical-left)
				     (rifn-classical rifn-classical-left)
				     )
	   )
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-left-is-integral-of-rifn-classical-left)))
	  ("Subgoal 4"
	   :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-necc)))
	  ))

(defthm strict-int-rifn-classical-right-is-integral-of-rifn-classical-right-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-right context p)
		    (strict-int-rifn-classical-right context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
				     (riemann-rifn-classical riemann-rifn-classical-right)
				     (strict-int-rifn-classical strict-int-rifn-classical-right)
				     (domain-rifn-classical domain-rifn-classical-op)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-right)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-right-witness)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-right)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness
				      forall-partitions-riemann-sum-is-close-to-int-rifn-classical-right-witness)
				     (map-rifn-classical map-rifn-classical-right)
				     (rifn-classical rifn-classical-right)
				     )
	   )
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-right-is-integral-of-rifn-classical-right)))
	  ("Subgoal 4"
	   :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-right-necc)))
	  ))

(defun rifn-classical-left+right (context x)
  (+ (rifn-classical-left context x)
     (rifn-classical-right context x)))

(defthm realp-rifn-classical-left+right
  (implies (realp x)
           (realp (rifn-classical-left+right context x))))

(defun map-rifn-classical-left+right (context p)
  (if (consp p)
      (cons (rifn-classical-left+right context (car p))
	    (map-rifn-classical-left+right context (cdr p)))
    nil))

(defthm real-listp-map-rifn-classical-left+right
  (implies (partitionp p)
           (real-listp (map-rifn-classical-left+right context p))))

(defun riemann-rifn-classical-left+right (context p)
  (dotprod (deltas p)
	   (map-rifn-classical-left+right context (cdr p))))

(defthm real-riemann-rifn-classical-left
  (implies (partitionp p)
           (realp (riemann-rifn-classical-left context p)))
  )

(defthm real-riemann-rifn-classical-right
  (implies (partitionp p)
         (realp (riemann-rifn-classical-right context p))))

(defthm real-riemann-rifn-classical-left+right
  (implies (partitionp p)
         (realp (riemann-rifn-classical-left+right context p)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable dotprod)))
  )

(defthm limited-riemann-rifn-classical-left+right
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op)))
	   (i-limited (riemann-rifn-classical-left+right context (make-small-partition a b))))
  :hints (("Goal"
	   :by (:functional-instance limited-riemann-rifn-left+right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left+right rifn-classical-left+right)
				     (map-rifn-left+right map-rifn-classical-left+right)
				     (riemann-rifn-left+right riemann-rifn-classical-left+right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     ))
	  ("Subgoal 7"
	   :use ((:instance strict-int-rifn-classical-right-is-integral-of-rifn-classical-right-using-nonstandard-criterion)))
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-left-is-integral-of-rifn-classical-left-using-nonstandard-criterion)))
	  ))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-classical-left+right)))

 (defun-std strict-int-rifn-classical-left+right (context a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-classical-op))
	    (inside-interval-p b (domain-rifn-classical-op))
	    (< a b))
       (standard-part (riemann-rifn-classical-left+right context (make-small-partition a b)))
     0)))

 (defthm reduce-strict-integral-rifn-classical-left+right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(<= a b))
	   (equal (strict-int-rifn-classical-left+right context a b)
		  (+ (strict-int-rifn-classical-left context a b)
		     (strict-int-rifn-classical-right context a b))))
  :hints (("Goal"
	   :by (:functional-instance reduce-strict-integral-rifn-left+right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left+right rifn-classical-left+right)
				     (map-rifn-left+right map-rifn-classical-left+right)
				     (riemann-rifn-left+right riemann-rifn-classical-left+right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     (strict-int-rifn-left+right strict-int-rifn-classical-left+right)
				     )
	   )))

(defthm-std realp-strict-int-rifn-classical-left+right
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-left+right context a b)))
  :hints (("Goal"
           :use ((:instance real-riemann-rifn-classical-left+right
                            (p (make-small-partition a b))))
           :in-theory (disable riemann-rifn-classical-left+right
                               real-riemann-rifn-classical-left+right)))
   )

(defun int-rifn-classical-left+right (context a b)
  (if (<= a b)
      (strict-int-rifn-classical-left+right context a b)
    (- (strict-int-rifn-classical-left+right context b a))))

(defthm reduce-integral-rifn-classical-left+right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op)))
	   (equal (int-rifn-classical-left+right context a b)
		  (+ (int-rifn-classical-left context a b)
		     (int-rifn-classical-right context a b))))
    :hints (("Goal"
	   :by (:functional-instance reduce-integral-rifn-left+right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left+right rifn-classical-left+right)
				     (map-rifn-left+right map-rifn-classical-left+right)
				     (riemann-rifn-left+right riemann-rifn-classical-left+right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     (strict-int-rifn-left+right strict-int-rifn-classical-left+right)
				     (int-rifn-left+right int-rifn-classical-left+right)
				     (int-rifn-left int-rifn-classical-left)
				     (int-rifn-right int-rifn-classical-right)
				     )
	   )))

(defthm strict-int-rifn-classical-left+right-is-integral-of-rifn-classical-left+right-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-left+right context p)
		    (strict-int-rifn-classical-left+right context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-left+right-is-integral-of-rifn-left+right
                                     (domain-rifn-op domain-rifn-classical-op)
                                     (int-rifn-left+right int-rifn-classical-left+right)
                                     (map-rifn-left+right map-rifn-classical-left+right)
                                     (map-rifn-left map-rifn-classical-left)
                                     (map-rifn-right map-rifn-classical-right)
                                     (riemann-rifn-left+right riemann-rifn-classical-left+right)
                                     (riemann-rifn-left riemann-rifn-classical-left)
                                     (riemann-rifn-right riemann-rifn-classical-right)
                                     (rifn-left+right rifn-classical-left+right)
                                     (rifn-left rifn-classical-left)
                                     (rifn-right rifn-classical-right)
                                     (strict-int-rifn-left+right strict-int-rifn-classical-left+right)
                                     (strict-int-rifn-left strict-int-rifn-classical-left)
                                     (strict-int-rifn-right strict-int-rifn-classical-right)
                                     (int-rifn-const-fn int-rifn-classical-const-fn)
                                     (int-rifn-left int-rifn-classical-left)
                                     (int-rifn-right int-rifn-classical-right)
                                     )
	   )))

(defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left+right (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-left+right context p)
			       (strict-int-rifn-classical-left+right context a b)))
		       eps)))
   :rewrite :direct)

(defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left+right (context a b eps)
  (exists (delta)
          (implies (and (inside-interval-p a (domain-rifn-classical-op))
                        (inside-interval-p b (domain-rifn-classical-op))
                        (<= a b)
                        (realp eps)
                        (< 0 eps))
                   (and (realp delta)
                        (< 0 delta)
                        (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left+right context a b eps delta)))))

(defthm strict-int-rifn-classical-left+right-is-integral-of-rifn-classical-left+right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
                (inside-interval-p b (domain-rifn-classical-op))
                (<= a b)
                (realp eps)
                (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left+right context a b eps))
   :hints (("Goal"
            :by (:functional-instance rifn-is-integrable-hyperreal
                                      (rifn rifn-classical-left+right)
                                      (strict-int-rifn strict-int-rifn-classical-left+right)
                                      (int-rifn int-rifn-classical-left+right)
                                      (domain-rifn domain-rifn-classical-op)
                                      (riemann-rifn riemann-rifn-classical-left+right)
                                      (map-rifn map-rifn-classical-left+right)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left+right)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left+right-witness)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left+right)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-witness
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left+right-witness))
            :in-theory (disable int-rifn-classical-left+right
                                RIEMANN-RIFN-CLASSICAL-LEFT+RIGHT
                                STRICT-INT-RIFN-CLASSICAL-LEFT+RIGHT))
           ("Subgoal 8"
            :use ((:instance
                   EXISTS-DELTA-SO-THAT-RIEMANN-SUM-IS-CLOSE-TO-INT-RIFN-CLASSICAL-left+right-suff)))
           ("Subgoal 6"
            :use ((:instance
                   forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left+right-necc)))
           ("Subgoal 4"
            :use ((:instance
                   strict-int-rifn-classical-left+right-is-integral-of-rifn-classical-left+right-using-nonstandard-criterion)))
           ("Subgoal 2"
            :in-theory (enable riemann-rifn-classical-left+right))
	    ))

;----------------

(defun rifn-classical-left-right (context x)
  (- (rifn-classical-left context x)
     (rifn-classical-right context x)))

(defthm realp-rifn-classical-left-right
  (implies (realp x)
           (realp (rifn-classical-left-right context x))))

(defun map-rifn-classical-left-right (context p)
  (if (consp p)
      (cons (rifn-classical-left-right context (car p))
	    (map-rifn-classical-left-right context (cdr p)))
    nil))

(defthm real-listp-map-rifn-classical-left-right
  (implies (partitionp p)
           (real-listp (map-rifn-classical-left-right context p))))

(defun riemann-rifn-classical-left-right (context p)
  (dotprod (deltas p)
	   (map-rifn-classical-left-right context (cdr p))))

(defthm real-riemann-rifn-classical-left
  (implies (partitionp p)
           (realp (riemann-rifn-classical-left context p)))
  )

(defthm real-riemann-rifn-classical-right
  (implies (partitionp p)
         (realp (riemann-rifn-classical-right context p))))

(defthm real-riemann-rifn-classical-left-right
  (implies (partitionp p)
           (realp (riemann-rifn-classical-left-right context p)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable dotprod)))
  )

(defthm limited-riemann-rifn-classical-left-right
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(< a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op)))
	   (i-limited (riemann-rifn-classical-left-right context (make-small-partition a b))))
  :hints (("Goal"
	   :by (:functional-instance limited-riemann-rifn-left-right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left-right rifn-classical-left-right)
				     (map-rifn-left-right map-rifn-classical-left-right)
				     (riemann-rifn-left-right riemann-rifn-classical-left-right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     ))
	  ("Subgoal 7"
	   :use ((:instance strict-int-rifn-classical-right-is-integral-of-rifn-classical-right-using-nonstandard-criterion)))
	  ("Subgoal 6"
	   :use ((:instance strict-int-rifn-classical-left-is-integral-of-rifn-classical-left-using-nonstandard-criterion)))
	  ))

(encapsulate
 nil

 (local (in-theory (disable riemann-rifn-classical-left-right)))

 (defun-std strict-int-rifn-classical-left-right (context a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (domain-rifn-classical-op))
	    (inside-interval-p b (domain-rifn-classical-op))
	    (< a b))
       (standard-part (riemann-rifn-classical-left-right context (make-small-partition a b)))
     0)))

 (defthm reduce-strict-integral-rifn-classical-left-right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(<= a b))
	   (equal (strict-int-rifn-classical-left-right context a b)
		  (- (strict-int-rifn-classical-left context a b)
		     (strict-int-rifn-classical-right context a b))))
  :hints (("Goal"
	   :by (:functional-instance reduce-strict-integral-rifn-left-right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left-right rifn-classical-left-right)
				     (map-rifn-left-right map-rifn-classical-left-right)
				     (riemann-rifn-left-right riemann-rifn-classical-left-right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     (strict-int-rifn-left-right strict-int-rifn-classical-left-right)
				     )
	   )))

(defthm-std realp-strict-int-rifn-classical-left-right
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical-left-right context a b)))
  :hints (("Goal"
           :use ((:instance real-riemann-rifn-classical-left-right
                            (p (make-small-partition a b))))
           :in-theory (disable riemann-rifn-classical-left-right
                               real-riemann-rifn-classical-left-right)))
   )

(defun int-rifn-classical-left-right (context a b)
  (if (<= a b)
      (strict-int-rifn-classical-left-right context a b)
    (- (strict-int-rifn-classical-left-right context b a))))

(defthm reduce-integral-rifn-classical-left-right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op)))
	   (equal (int-rifn-classical-left-right context a b)
		  (- (int-rifn-classical-left context a b)
		     (int-rifn-classical-right context a b))))
    :hints (("Goal"
	   :by (:functional-instance reduce-integral-rifn-left-right
				     (domain-rifn-op domain-rifn-classical-op)
				     (rifn-left-right rifn-classical-left-right)
				     (map-rifn-left-right map-rifn-classical-left-right)
				     (riemann-rifn-left-right riemann-rifn-classical-left-right)
				     (rifn-left rifn-classical-left)
				     (rifn-right rifn-classical-right)
				     (strict-int-rifn-left strict-int-rifn-classical-left)
				     (riemann-rifn-left riemann-rifn-classical-left)
				     (map-rifn-left map-rifn-classical-left)
				     (strict-int-rifn-right strict-int-rifn-classical-right)
				     (riemann-rifn-right riemann-rifn-classical-right)
				     (map-rifn-right map-rifn-classical-right)
				     (strict-int-rifn-left-right strict-int-rifn-classical-left-right)
				     (int-rifn-left-right int-rifn-classical-left-right)
				     (int-rifn-left int-rifn-classical-left)
				     (int-rifn-right int-rifn-classical-right)
				     )
	   )))

(defthm strict-int-rifn-classical-left-right-is-integral-of-rifn-classical-left-right-using-nonstandard-criterion
  (implies (and (standardp context)
                (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (domain-rifn-classical-op))
		(inside-interval-p b (domain-rifn-classical-op))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rifn-classical-left-right context p)
		    (strict-int-rifn-classical-left-right context a b)))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance strict-int-rifn-left-right-is-integral-of-rifn-left-right
                                     (domain-rifn-op domain-rifn-classical-op)
                                     (int-rifn-left-right int-rifn-classical-left-right)
                                     (map-rifn-left-right map-rifn-classical-left-right)
                                     (map-rifn-left map-rifn-classical-left)
                                     (map-rifn-right map-rifn-classical-right)
                                     (riemann-rifn-left-right riemann-rifn-classical-left-right)
                                     (riemann-rifn-left riemann-rifn-classical-left)
                                     (riemann-rifn-right riemann-rifn-classical-right)
                                     (rifn-left-right rifn-classical-left-right)
                                     (rifn-left rifn-classical-left)
                                     (rifn-right rifn-classical-right)
                                     (strict-int-rifn-left-right strict-int-rifn-classical-left-right)
                                     (strict-int-rifn-left strict-int-rifn-classical-left)
                                     (strict-int-rifn-right strict-int-rifn-classical-right)
                                     (int-rifn-const-fn int-rifn-classical-const-fn)
                                     (int-rifn-left int-rifn-classical-left)
                                     (int-rifn-right int-rifn-classical-right)
                                     )
	   )))

(defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-right (context a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical-left-right context p)
			       (strict-int-rifn-classical-left-right context a b)))
		       eps)))
   :rewrite :direct)

(defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-right (context a b eps)
  (exists (delta)
          (implies (and (inside-interval-p a (domain-rifn-classical-op))
                        (inside-interval-p b (domain-rifn-classical-op))
                        (<= a b)
                        (realp eps)
                        (< 0 eps))
                   (and (realp delta)
                        (< 0 delta)
                        (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-right context a b eps delta)))))

(defthm strict-int-rifn-classical-left-right-is-integral-of-rifn-classical-left-right
  (implies (and (inside-interval-p a (domain-rifn-classical-op))
                (inside-interval-p b (domain-rifn-classical-op))
                (<= a b)
                (realp eps)
                (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-right context a b eps))
   :hints (("Goal"
            :by (:functional-instance rifn-is-integrable-hyperreal
                                      (rifn rifn-classical-left-right)
                                      (strict-int-rifn strict-int-rifn-classical-left-right)
                                      (int-rifn int-rifn-classical-left-right)
                                      (domain-rifn domain-rifn-classical-op)
                                      (riemann-rifn riemann-rifn-classical-left-right)
                                      (map-rifn map-rifn-classical-left-right)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-right)
                                      (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
                                       forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-right-witness)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-right)
                                      (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-witness
                                       exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-left-right-witness))
            :in-theory (disable int-rifn-classical-left-right
                                RIEMANN-RIFN-CLASSICAL-LEFT-RIGHT
                                STRICT-INT-RIFN-CLASSICAL-LEFT-RIGHT))
           ("Subgoal 8"
            :use ((:instance
  EXISTS-DELTA-SO-THAT-RIEMANN-SUM-IS-CLOSE-TO-INT-RIFN-CLASSICAL-left-right-suff)))
           ("Subgoal 6"
            :use ((:instance
  forall-partitions-riemann-sum-is-close-to-int-rifn-classical-left-right-necc)))
           ("Subgoal 4"
            :use ((:instance
  strict-int-rifn-classical-left-right-is-integral-of-rifn-classical-left-right-using-nonstandard-criterion)))
           ("Subgoal 2"
            :in-theory (enable riemann-rifn-classical-left-right))
	    ))

;----------------
