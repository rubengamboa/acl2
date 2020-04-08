(in-package "ACL2")

; cert_param: (uses-acl2r)

(defun polynomial-p (poly)
  (if (consp poly)
      (and (acl2-numberp (car poly))
           (polynomial-p (cdr poly)))
    (null poly)))

(defun real-polynomial-p (poly)
  (if (consp poly)
      (and (realp (car poly))
           (real-polynomial-p (cdr poly)))
    (null poly)))

(defun rational-polynomial-p (poly)
  (if (consp poly)
      (and (rationalp (car poly))
           (rational-polynomial-p (cdr poly)))
    (null poly)))

(defun integer-polynomial-p (poly)
  (if (consp poly)
      (and (integerp (car poly))
           (integer-polynomial-p (cdr poly)))
    (null poly)))

(defun non-trivial-polynomial-p (poly)
  (and (polynomial-p poly)
       (< 1 (len poly))
       (not (equal 0 (car (last poly))))))

(defun eval-polynomial (poly x)
  (if (consp poly)
      (+ (* x (eval-polynomial (cdr poly) x))
         (car poly))
    0))

(defun eval-polynomial-expt-aux (poly x n)
  (if (consp poly)
      (+ (* (car poly) (expt x n))
	 (eval-polynomial-expt-aux (cdr poly) x (1+ n)))
    0))

(defun eval-polynomial-expt (poly x)
  (eval-polynomial-expt-aux poly x 0))

(defun polynomial-root-p (poly x)
  (and (realp x)
       (equal (eval-polynomial poly x) 0)))

(defun non-trivial-polynomial-root-p (poly x)
  (and (non-trivial-polynomial-p poly)
       (polynomial-root-p poly x)))

(defun scale-polynomial (poly c)
  (if (consp poly)
      (cons (* c (car poly))
            (scale-polynomial (cdr poly) c))
    nil))

(defun polynomial-+ (poly1 poly2)
  (if (consp poly1)
      (if (consp poly2)
	  (cons (+ (car poly1)
		   (car poly2))
		(polynomial-+ (cdr poly1) (cdr poly2)))
	poly1)
    poly2))

(defun polynomial-* (poly1 poly2)
  (if (consp poly1)
      (polynomial-+ (scale-polynomial poly2 (car poly1))
		    (cons 0 (polynomial-* (cdr poly1) poly2)))
    nil))

